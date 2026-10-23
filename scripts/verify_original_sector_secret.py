#!/usr/bin/env python3
"""Original case-9 secret writes and POP/RET; entry dispatch remains separate."""
import argparse
import json
from pathlib import Path
import random
import re
import struct
import subprocess
import sys
import tempfile
import verify_original_player_joined as shared
ROOT, require = shared.ROOT, shared.require
NAMES = ['bytes_checked', 'execution_checked', 'runtime_checked',
         'Doom.Proofs.SectorSecret.updated_count', 'Doom.Proofs.SectorSecret.updated_special',
         'Doom.Proofs.SectorSecret.updated_frame', 'Doom.Proofs.SectorSecret.saved',
         'Doom.Proofs.SectorSecret.updated_return', 'Doom.Proofs.SectorSecret.updated_restored']


def certificate(raw, digest):
    literal = '[' + ','.join(hex(b) for b in raw['sectorSecretBytes']) + ']'
    return f'''-- Original executable SHA-256 {digest}.
import Doom.Proofs.OriginalSectorSecret
namespace Doom.Verification.ExtractedSectorSecret
open X86Memory X86Control Doom.Proofs.SectorSecret
def extracted : List UInt8 := {literal}
theorem bytes_checked : extracted = code := by decide
theorem execution_checked (s : X86Memory.State) (flags : Option Flags)
    (safe : StackSafe s) (outside : 17 ≤ returnPc s) :
    X86Routine.run (X86Routine.decodeAt extracted) [returnPc s] 7 ⟨s,flags,0⟩ =
      some ⟨final s,none,returnPc s⟩ := by
  rw [bytes_checked]
  exact execution s flags safe outside
theorem runtime_checked (s : X86Memory.State) (flags : Option Flags) (n : Int32) (z floor : Doom.Fixed)
    (onFloor : z = floor) (isSecret : load16 s.memory (specialAddress s) = 9)
    (encoded : count s = n.toBitVec) (separate : Separate s)
    (safe : StackSafe s) (outside : 17 ≤ returnPc s) :
    (X86Routine.run (X86Routine.decodeAt extracted) [returnPc s] 7 ⟨s,flags,0⟩).map (fun t =>
      (t.pc,load16 t.core.memory (specialAddress s),load32 t.core.memory (countAddress s),t.core.regs 4)) =
      some (returnPc s,BitVec.ofNat 16 (Doom.LevelSpecials.secret (load16 s.memory (specialAddress s)).toNat z floor n).1,
        (Doom.LevelSpecials.secret (load16 s.memory (specialAddress s)).toNat z floor n).2.toBitVec,s.regs 4+20) := by
  rw [bytes_checked]
  exact observation s flags n z floor onFloor isSecret encoded separate safe outside
''' + '\n'.join('#print axioms ' + name for name in NAMES) + '\nend Doom.Verification.ExtractedSectorSecret\n'


def audit(output):
    rest = output.strip()
    for short in NAMES:
        name = short if '.' in short else 'Doom.Verification.ExtractedSectorSecret.'+short
        match = re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing axiom audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext','Classical.choice','Quot.sound'}, 'unexpected axioms: '+str(axioms))
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


def cases():
    rng = random.Random(0x2FBDC)
    edge = [0,1,-1,2147483646,2147483647,-2147483648,-2147483647,65535,65536]
    return [(n, z, align) for n in edge for z in edge for align in range(4)] + [
        (rng.randrange(-2**31,2**31),rng.randrange(-2**31,2**31),rng.randrange(4)) for _ in range(16384)]


def cross_check(code):
    import unicorn as uc
    from unicorn import x86_const as x
    import capstone
    decoded = list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(code,0x2fbdc))
    require(len(decoded) == 7 and b''.join(bytes(i.bytes) for i in decoded) == code, 'incomplete disassembly')
    inputs = cases()
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory)/'secrets.txt'
        path.write_text(''.join(f'secret {z} {z} 9 {n}\n' for n,z,_ in inputs))
        result = subprocess.run([str(ROOT/'.lake/build/bin/level-probe'),str(path)],cwd=ROOT,capture_output=True,text=True,check=True)
    require(not result.stderr.strip(), 'unexpected native diagnostics')
    answers = [tuple(map(int,line.split())) for line in result.stdout.splitlines()]
    require(len(answers) == len(inputs), 'wrong native result count')
    em = uc.Uc(uc.UC_ARCH_X86,uc.UC_MODE_32)
    CODE, DATA = 0x100000,0x800000
    em.mem_map(CODE,4096); em.mem_map(DATA,4096)
    em.mem_write(CODE,code)
    regs = [x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
            x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes = []
    em.hook_add(uc.UC_HOOK_MEM_WRITE,lambda _e,_a,addr,size,value,_u: writes.append((addr,size)))
    rng = random.Random(0x5E5A595B)
    for index, ((n,z,align),(special,total)) in enumerate(zip(inputs,answers)):
        player, sector, sp = DATA+32+align,DATA+512+(align+1)%4,DATA+1024+(align+2)%4
        target = CODE+64+index%64
        em.mem_write(DATA,b'\xa5'*4096)
        em.mem_write(player+212,struct.pack('<i',n))
        em.mem_write(sector+14,struct.pack('<H',9))
        saved = [rng.getrandbits(32) for _ in range(4)]
        em.mem_write(sp,struct.pack('<5I',*saved,target))
        initial = [rng.getrandbits(32) for _ in regs]
        initial[1],initial[4],initial[6] = sector,sp,player
        for reg,value in zip(regs,initial): em.reg_write(reg,value)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5))
        expected = bytearray(em.mem_read(DATA,4096))
        struct.pack_into('<i',expected,player+212-DATA,total)
        struct.pack_into('<H',expected,sector+14-DATA,special)
        writes.clear()
        em.emu_start(CODE,target,count=7)
        require(em.reg_read(x.UC_X86_REG_EIP) == target, f'wrong return {index}')
        require(bytes(em.mem_read(DATA,4096)) == bytes(expected), f'memory/native mismatch {index}')
        require(writes == [(player+212,4),(sector+14,2)],f'wrong write sizes/order {index}')
        after = initial.copy()
        after[6],after[2],after[1],after[3] = saved
        after[4] += 20
        require([em.reg_read(reg) for reg in regs] == after,f'register restoration mismatch {index}')
    return {'cases':len(inputs),'unaligned_addresses':True,'checks':['compiled live secret helper','entire memory page',
        'two-byte sector clear','ordered store widths','32-bit count wrap','all registers','stack-supplied RET']}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-sector-secret.json').read_text())
    profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text())
    sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=shared.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=shared.extraction.extract(binary,profile,spec)
    out=ROOT/'artifacts/original-sector-secret';out.mkdir(parents=True,exist_ok=True)
    source=out/'Extracted.lean';source.write_text(certificate(raw,profile['exe_sha256']))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalSectorSecret','level-probe'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout)
    report={'exe_sha256':profile['exe_sha256'],'units':spec['units'],'axioms':checked.stdout.splitlines(),
        'scope':'Original case-9 writes through POP/RET, related to live LevelSpecials.secret under explicit on-floor, secret-kind, count, separation and saved-stack premises. Includes byte-exact external-memory preservation. Handler entry, switch dispatch, outer CALL and full player-tic composition remain separate.',
        'cross_check':cross_check(raw['sectorSecretBytes']) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f'PASS: original secret-case writes and return; {len(NAMES)} audited declarations.')
    if args.cross_check: print('Independent original-byte/native comparisons:',report['cross_check']['cases'])

if __name__=='__main__':
    try: main()
    except subprocess.CalledProcessError as error:
        print(error.stdout or '',file=sys.stderr);print(error.stderr or '',file=sys.stderr);raise
