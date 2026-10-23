#!/usr/bin/env python3
"""Certify the original P_DamageMobj armor block and its live Lean helper."""
import argparse
import json
import random
import re
import struct
import subprocess
import tempfile
from pathlib import Path
import verify_original_inline_thrust as extraction

ROOT, require = extraction.ROOT, extraction.require
NAMES = ['bytes_checked', 'armor_checked', 'Doom.Proofs.PlayerArmor.decoded',
         'Doom.Proofs.PlayerArmor.dividend', 'Doom.Proofs.PlayerArmor.third_safe',
         'Doom.Proofs.PlayerArmor.execution', 'Doom.Proofs.PlayerArmor.original_execution',
         'Doom.Proofs.PlayerArmor.live_values', 'Doom.Proofs.PlayerArmor.correspondence',
         'Doom.Proofs.PlayerArmor.memory_frame', 'Doom.Proofs.PlayerArmor.live_inline']


def certificate(raw, digest):
    literal = '['+','.join(hex(b) for b in raw['armorBytes'])+']'
    return f'''-- Original executable SHA-256 {digest}; extraction/loader checked externally.
import Doom.Proofs.OriginalPlayerArmor
namespace Doom.Verification.ExtractedPlayerArmor
def code : List UInt8 := {literal}
theorem bytes_checked : code = Doom.Proofs.PlayerArmor.code := by decide
''' + '''open Doom.Proofs PlayerArmor X86Memory X86Control
theorem armor_checked (s : X86Memory.State) (f : Option Flags) (v : Doom.PlayerDamage.State) (d : Int32)
    (damage : s.regs 7 = d.toBitVec) (points : armor s = v.armor.toBitVec)
    (armorType : kind s = v.armorType.toBitVec) :
    (X86Routine.run (fun pc => if 0x2a5d5 ≤ pc ∧ pc < 0x2a616 then X86Routine.decodeAt code (pc-0x2a5d5) else none)
      [0x2a616] 24 ⟨s,f,0x2a5d5⟩).map
      (fun t => (t.core.regs 7,load32 t.core.memory (pointer s+(36#32)),load32 t.core.memory (pointer s+(40#32)))) =
      let out := Doom.PlayerDamage.absorbArmor v d
      some (out.2.toBitVec,out.1.armor.toBitVec,out.1.armorType.toBitVec) := by
  rw [bytes_checked]
  exact correspondence s f v d damage points armorType
''' + '\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedPlayerArmor\n'


def audit(output):
    rest = output.strip()
    for short in NAMES:
        name = short if '.' in short else 'Doom.Verification.ExtractedPlayerArmor.'+short
        match = re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None, 'missing axiom audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext','Classical.choice','Quot.sound'}, 'unexpected proof axioms')
        rest = rest[match.end():].strip()
    require(not rest,'unexpected certificate output')


def cases():
    edges = [-2**31,-2**31+1,-1000,-20,-3,-2,-1,0,1,2,3,4,5,6,9,10,19,20,21,99,100,199,200,999,1000,2**31-2,2**31-1]
    result = [(d,a,t) for d in edges for a in edges for t in [0,1,2,-1,2**31-1,-2**31]]
    # Equality and +/- one around the exact quotient, for both armor types.
    for d in edges:
        for t,divisor in [(1,3),(2,2)]:
            q = (abs(d)//divisor)*(-1 if d<0 else 1)
            result.extend((d,q+k,t) for k in [-1,0,1])
    rng = random.Random(0x2a5d5)
    result += [(rng.randrange(-2**31,2**31),rng.randrange(-2**31,2**31),rng.choice([0,1,2,rng.randrange(-2**31,2**31)])) for _ in range(8192)]
    return result


def cross_check(raw, spec):
    import capstone
    import unicorn as uc
    from unicorn import x86_const as x
    code = raw['armorBytes']; start = 0x2a5d5; end = 0x2a616
    listing = list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(code,start))
    require(len(listing)==spec['units']['armorBytes']['instructions'] and b''.join(bytes(i.bytes) for i in listing)==code,'decoder mismatch')
    corpus = cases()
    with tempfile.TemporaryDirectory() as directory:
        commands = Path(directory) / 'armor.txt'
        commands.write_text(''.join(f'armor {d} {a} {t}\n' for d,a,t in corpus))
        answers = subprocess.check_output([str(ROOT/'.lake/build/bin/player-damage-probe'),str(commands)],text=True).splitlines()
    require(len(answers)==len(corpus),'probe output count mismatch')
    em=uc.Uc(uc.UC_ARCH_X86,uc.UC_MODE_32)
    em.mem_map(0x20000,0x10000);em.mem_write(start,code)
    for base in [0,0x400000,0xfffff000]:em.mem_map(base,4096)
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[]
    em.hook_add(uc.UC_HOOK_MEM_WRITE,lambda _e,_a,addr,size,_v,_u:writes.append((addr,size)))
    rng=random.Random(0x41524d4f52)
    u32=lambda n:n&0xffffffff
    for i,((damage,armor,kind),answer) in enumerate(zip(corpus,answers)):
        pointer = [0x400100,0x400101,0x400102,0x400103,0xffffffd8][i%5]
        ap,tp=u32(pointer+36),u32(pointer+40)
        em.mem_write(ap,struct.pack('<I',u32(armor)));em.mem_write(tp,struct.pack('<I',u32(kind)))
        before={b:bytearray(em.mem_read(b,4096)) for b in [0,0x400000,0xfffff000]}
        values=[rng.getrandbits(32) for _ in regs];values[5]=pointer;values[7]=u32(damage)
        for r,v in zip(regs,values):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5));writes.clear()
        em.emu_start(start,end,count=24)
        require(em.reg_read(x.UC_X86_REG_EIP)==end,f'run did not finish {i}')
        actual=(em.reg_read(regs[7]),struct.unpack('<I',em.mem_read(ap,4))[0],struct.unpack('<I',em.mem_read(tp,4))[0])
        expected=tuple(u32(int(n)) for n in answer.split())
        require(actual==expected,f'case {i}: {(damage,armor,kind)}: x86 {actual}, Lean {expected}')
        expected_writes=[]
        if kind:
            q=(abs(damage)//(3 if kind==1 else 2))*(-1 if damage<0 else 1)
            if q>=armor:expected_writes.append((tp,4))
            expected_writes.append((ap,4))
        require(writes==expected_writes,f'write order {i}')
        for addr,value in [(ap,expected[1]),(tp,expected[2])]:
            for off,byte in enumerate(struct.pack('<I',value)):
                at=u32(addr+off);before[at&~4095][at&4095]=byte
        require(all(em.mem_read(b,4096)==v for b,v in before.items()),f'memory frame {i}')
        require(all(em.reg_read(regs[r])==values[r] for r in [4,5,6]),f'preserved registers {i}')
    return {'cases':len(corpus),'all_player_memory_checked':True,'exact_write_order':True,
            'unaligned_and_wrapping_player_addresses':True,
            'disassembly':[f'{i.address:#x}: {i.mnemonic} {i.op_str}' for i in listing]}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-player-armor.json').read_text())
    profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec)
    out=ROOT/'artifacts/original-player-armor';out.mkdir(parents=True,exist_ok=True)
    path=out/'Extracted.lean';path.write_text(certificate(raw,profile['exe_sha256']))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalPlayerArmor','player-damage-probe'],cwd=ROOT,check=True)
    result=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(result.stdout)
    report={'exe_sha256':profile['exe_sha256'],'axioms':result.stdout.splitlines(),
            'scope':'Armor block 0x2a5d5..0x2a616, linked to live absorbArmor for all signed 32-bit fields; no damage entry, health, pain, death or handler-return claim.',
            'cross_check':cross_check(raw,spec) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f'PASS: original player armor; {len(NAMES)} audited declarations.')
    if args.cross_check:print('Original-byte/native comparisons:',report['cross_check']['cases'])

if __name__=='__main__':main()
