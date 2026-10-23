#!/usr/bin/env python3
"""Certify contiguous turning + forward guard execution, with optional x86 checks."""
import argparse
import json
import random
import re
import struct
import subprocess
import sys

import verify_original_inline_thrust as extraction
import verify_original_mul as original
from verify_original_thrust import probe

ROOT, require = original.ROOT, original.require
NAMES = ['bytes_checked', 'execution_checked', 'engine_checked',
         'Doom.Proofs.move_entry_final_angle', 'Doom.Proofs.turn_establishes_guard_inputs',
         'Doom.Verification.X86Control.Prefix.run',
         'Doom.Verification.X86Control.runProgram_shift',
         'Doom.Verification.X86Control.runProgram_extend']


def certificate(raw, digest):
    literal = '['+', '.join(hex(b) for b in raw)+']'
    audits = '\n'.join('#print axioms '+n for n in NAMES)
    return f'''-- Contiguous DOOM.EXE bytes, SHA-256 {digest}.
import Doom.Proofs.OriginalMoveEntry
namespace Doom.Verification.ExtractedMoveEntry
open X86Memory X86Control Doom.Proofs
def code : List UInt8 := {literal}
theorem bytes_checked : code = moveEntryBytes := by decide
theorem execution_checked (s : X86Memory.State) (flags : Option Flags) :
    (X86Control.run code [48, 120] 17 ⟨s, flags, 0⟩).map (fun t => (t.pc, t.core.memory)) =
      some (17 + forwardGuardResult (turnEndCore s),
        store32 (turnEndCore s).memory 0x2cf90 (if groundFlag (turnEndCore s) then 1 else 0)) := by
  rw [bytes_checked]
  exact original_move_entry s flags
theorem engine_checked (s : X86Memory.State) (flags : Option Flags) (body : Motion)
    (cmd : Ticcmd) (h : MoveEntryInputs s body cmd) :
    (X86Control.run code [48, 120] 17 ⟨s, flags, 0⟩).map (fun t => (t.pc, t.core.memory)) =
      some (if body.onGround ∧ cmd.forwardMove ≠ 0 then 48 else 120,
        moveEntryResultMemory s body cmd) := by
  rw [bytes_checked]
  exact move_entry_matches_engine s flags body cmd h
{audits}
end Doom.Verification.ExtractedMoveEntry
'''


def audit(output):
    rest = output.strip()
    for short in NAMES:
        name = short if '.' in short else 'Doom.Verification.ExtractedMoveEntry.'+short
        match = re.match(re.escape(f"'{name}'")+
                         r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing axiom audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected proof axioms')
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


def cross_check(raw):
    import capstone
    import unicorn as uc
    from unicorn import x86_const as x
    rng = random.Random(0x33169)
    signed = lambda v: v if v < 2**31 else v-2**32
    signed16 = lambda v: v if v < 32768 else v-65536
    signed8 = lambda v: v if v < 128 else v-256
    edges = [0, 1, 0xffffffff, 0x7fffffff, 0x80000000, 0x80000001, 0x7ffffffe]
    cases = [(rng.getrandbits(32), t, rng.choice(edges), rng.choice(edges), rng.randrange(256))
             for t in range(65536)]
    cases += [(rng.getrandbits(32), rng.randrange(65536), z, f, c)
              for z in edges for f in edges for c in range(256)]
    turns = list(map(int, probe([f'turn {signed(a)} {signed16(t)}' for a,t,z,f,c in cases])))
    guards = [tuple(map(int, line.split())) for line in
              probe([f'move-guards {signed(z)} {signed(f)} {signed8(c)} 0' for a,t,z,f,c in cases])]
    listing = list(capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_32).disasm(raw, 0x33169))
    require(len(listing) == 17 and b''.join(bytes(i.bytes) for i in listing) == raw, 'independent decode mismatch')
    em = uc.Uc(uc.UC_ARCH_X86, uc.UC_MODE_32)
    CODE, DATA, GLOBAL = 0x100000, 0x300000, 0x2cf90
    em.mem_map(CODE,4096); em.mem_map(DATA,4096); em.mem_map(GLOBAL&~4095,4096)
    em.mem_write(CODE,b'\xcc'*4096); em.mem_write(CODE,raw)
    registers = [x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
                 x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[]
    em.hook_add(uc.UC_HOOK_MEM_WRITE,lambda _e,_a,addr,size,_v,_u:writes.append((addr,size)))
    def stop(machine,addr,size,user):
        if addr in [CODE+48,CODE+120]: machine.emu_stop()
    em.hook_add(uc.UC_HOOK_CODE,stop)
    for i,((angle,turn,z,floor,command),newangle,guard) in enumerate(zip(cases,turns,guards)):
        player,obj=DATA+32+i%4,DATA+256+(i//4)%4
        em.mem_write(player,struct.pack('<I',obj)); em.mem_write(player+8,bytes([command,rng.randrange(256)])+struct.pack('<H',turn))
        em.mem_write(obj+20,struct.pack('<I',z)); em.mem_write(obj+32,struct.pack('<I',angle)); em.mem_write(obj+56,struct.pack('<I',floor))
        em.mem_write(GLOBAL,struct.pack('<I',rng.getrandbits(32)))
        before=bytearray(em.mem_read(DATA,4096))
        rs=[rng.getrandbits(32) for _ in registers]; rs[0]=player
        for r,v in zip(registers,rs): em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5))
        writes.clear(); em.emu_start(CODE,0,count=18)
        ground,take,_=guard
        require(ground==int(signed(z)<=signed(floor)), 'ground probe disagreement')
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+(48 if take else 120),f'branch mismatch case {i}')
        struct.pack_into('<I',before,obj+32-DATA,newangle)
        require(em.mem_read(DATA,4096)==before,'angle/memory mismatch')
        require(struct.unpack('<I',em.mem_read(GLOBAL,4))[0]==ground,'cached ground mismatch')
        require(writes==[(obj+32,4),(GLOBAL,4)],'write order mismatch')
        rs[0],rs[1],rs[2],rs[3],rs[6]=ground,player,(rs[2]&0xffffff00)|command,z,player+8
        require([em.reg_read(r) for r in registers]==rs,'register seam mismatch')
        flags=em.reg_read(x.UC_X86_REG_EFLAGS)
        require(((flags>>6)&1,(flags>>7)&1,(flags>>11)&1)==(int(not command or not ground),0,0),'flag seam mismatch')
    return {'cases':len(cases),'all_65536_turn_commands':True,'all_256_forward_commands':True,
            'signed_height_boundaries':True,'unaligned_objects':True,
            'checked':['continuous exit PC','angle','all registers','ZF/SF/OF','dynamic page','write order','cached ground'],
            'disassembly':[f'{i.address:#x}: {i.mnemonic} {i.op_str}' for i in listing]}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-move-entry.json').read_text())
    profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text())
    sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec)['moveEntryBytes']
    out=ROOT/'artifacts/original-move-entry';out.mkdir(parents=True,exist_ok=True)
    source=out/'Extracted.lean';source.write_text(certificate(raw,profile['exe_sha256']))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalMoveEntry','fidelity-probe'],cwd=ROOT,check=True)
    result=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(result.stdout);print(result.stdout,end='',flush=True)
    report={'exe_sha256':profile['exe_sha256'],'unit':spec['units']['moveEntryBytes'],'axioms':result.stdout.splitlines(),
            'scope':'Continuous turn/forward-guard execution under entry memory assumptions; stops at forward thrust entry or side guard entry, not complete movement.',
            'cross_check':cross_check(raw) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: original turning and forward guard compose and match engine angle/decision.')
    if report['cross_check']:print('Independent continuous x86 comparisons:',report['cross_check']['cases'])


if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as e:
        print(e.stdout or '',file=sys.stderr);print(e.stderr or '',file=sys.stderr);raise
