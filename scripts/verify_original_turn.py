#!/usr/bin/env python3
"""Bind the player-turn theorem to the original executable. Offline by default.

Optional Capstone/Unicorn checks are independent tests, not part of the proof.
The executable hash, LE mapping and relocation checks are external to Lean.
"""
import argparse
import hashlib
import json
from pathlib import Path
import random
import re
import struct
import subprocess
import sys
import tempfile

import verify_original_mul as original

ROOT=original.ROOT
require=original.require


def extract(binary, profile, spec):
    code, offsets, relocations, _=original.inspect_image(binary, profile)
    start=int(spec['code_offset'],16)
    expected=bytes.fromhex(spec['hex'])
    raw=code[start:start+len(expected)]
    require(raw==expected,'player turn bytes mismatch')
    require(offsets[start]==int(spec['file_offset'],16),'turn file mapping mismatch')
    require(not any(max(start,r)<min(start+len(raw),r+w) for r,w in relocations),
            'loader relocation changes turning block')
    return raw


def certificate(raw,digest):
    literal=', '.join(hex(b) for b in raw)
    return f'''-- Actual bytes extracted from DOOM.EXE SHA-256 {digest}.
-- File identity, mapping and access-validity assumptions are external checks.
import Doom.Proofs.OriginalTurn
namespace Doom.Verification.ExtractedTurn
open X86 X86Memory Doom.Proofs
def code : List UInt8 := [{literal}]
theorem bytes_checked : code = Doom19.playerTurnBytes := by decide
theorem angle_checked (s : State) (body : Motion) (amount : Int16)
    (ha : load32 s.memory (load32 s.memory (s.regs eax) + 32) = body.angle.raw.toBitVec)
    (hc : load16 s.memory (s.regs eax + 10) = amount.toBitVec) :
    ((X86Memory.run 6 code s).map (·.memory)).map
      (fun m => load32 m (load32 s.memory (s.regs eax) + 32)) =
      some (body.turn amount).angle.raw.toBitVec := by
  rw [bytes_checked]
  exact player_turn_matches_doom19 s body amount ha hc
#print axioms bytes_checked
#print axioms angle_checked
#print axioms Doom.Proofs.player_turn_preserves_other_bytes
#print axioms Doom.Proofs.player_turn_preserves_register
end Doom.Verification.ExtractedTurn
'''


def audit(text):
    names=['Doom.Verification.ExtractedTurn.bytes_checked',
           'Doom.Verification.ExtractedTurn.angle_checked',
           'Doom.Proofs.player_turn_preserves_other_bytes',
           'Doom.Proofs.player_turn_preserves_register']
    rest=text.strip()
    for name in names:
        pattern=re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)'
        m=re.match(pattern,rest)
        require(m is not None,'missing theorem axiom audit')
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext','Classical.choice','Quot.sound'},f'unexpected proof axioms: {axioms}')
        rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')


def cross_check(raw):
    import capstone
    import unicorn as uc
    from unicorn import x86_const as x
    listing=list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(raw,0x33169))
    require(len(listing)==6 and b''.join(bytes(i.bytes) for i in listing)==raw,'independent decoding mismatch')
    rng=random.Random(0x33169)
    edges=[0,1,0x7fffffff,0x80000000,0xffffffff]
    cases=[(edges[i%len(edges)] if i%2 else rng.getrandbits(32),i-32768) for i in range(65536)]
    cases += [(a,n) for a in edges for n in [-32768,-32767,-1,0,1,32766,32767]]
    with tempfile.TemporaryDirectory() as directory:
        path=Path(directory)/'commands.txt'
        path.write_text(''.join(f'turn {a if a<2**31 else a-2**32} {n}\n' for a,n in cases))
        result=subprocess.run([str(ROOT/'.lake/build/bin/fidelity-probe'),str(path)],capture_output=True,text=True,check=True)
    answers=result.stdout.splitlines()
    require(len(answers)==len(cases),'Lean probe count mismatch')
    em=uc.Uc(uc.UC_ARCH_X86,uc.UC_MODE_32)
    CODE,DATA=0x100000,0x200000
    em.mem_map(CODE,4096);em.mem_write(CODE,raw)
    em.mem_map(DATA,4096);em.mem_write(DATA,bytes((i*37+19)%256 for i in range(4096)))
    registers=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
               x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    for i,((angle,command),answer) in enumerate(zip(cases,answers)):
        player=DATA+64+i%4;body=DATA+256+(i//4)%4
        em.mem_write(player,struct.pack('<I',body))
        em.mem_write(player+10,struct.pack('<h',command))
        em.mem_write(body+32,struct.pack('<I',angle))
        before=bytearray(em.mem_read(DATA,4096))
        regs=[(0x12345678+0x11111111*r+i)&0xffffffff for r in range(8)];regs[0]=player
        for r,v in zip(registers,regs):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2+(i%2))
        em.emu_start(CODE,CODE+len(raw),count=6)
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+len(raw),'block did not finish')
        value=struct.unpack('<I',em.mem_read(body+32,4))[0]
        require(value==int(answer),f'turn mismatch for {angle}, {command}')
        struct.pack_into('<I',before,body+32-DATA,value)
        require(em.mem_read(DATA,4096)==before,'unexpected memory write')
        regs[0]=body;regs[1]=player;regs[3]=(command<<16)&0xffffffff;regs[6]=player+8
        require([em.reg_read(r) for r in registers]==regs,'unexpected register effect')
    return {'cases':len(cases),'all_int16_commands':True,'unaligned_accesses':True,
            'whole_mapped_memory_checked':True,'all_registers_checked':True,
            'disassembly':[f'{i.address:#x}: {i.mnemonic} {i.op_str}' for i in listing]}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cross-check',action='store_true')
    args=p.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-turn.json').read_text())
    profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text())
    shareware=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=original.extract(ROOT/shareware['local_directory']/'doom19s.zip',shareware,profile)
    raw=extract(binary,profile,spec)
    out=ROOT/'artifacts/original-turn';out.mkdir(exist_ok=True,parents=True)
    source=out/'Extracted.lean';source.write_text(certificate(raw,profile['exe_sha256']))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalTurn','fidelity-probe'],check=True,cwd=ROOT)
    result=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],capture_output=True,text=True,check=True,cwd=ROOT)
    audit(result.stdout);print(result.stdout,end='',flush=True)
    report={'exe_sha256':profile['exe_sha256'],'code_offset':spec['code_offset'],'file_offset':spec['file_offset'],
            'bytes':raw.hex(),'instructions':6,'axioms':result.stdout.splitlines(),
            'scope':'Angle result and memory/register footprint under the flat, accessible-memory register projection; excludes flags, fetch, prologue, thrust, collision and whole-game equivalence.',
            'cross_check':cross_check(raw) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: original turning block matches Motion.turn for every related input state.')
    if report['cross_check']:print(json.dumps(report['cross_check']))


if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as e:
        print(e.stdout or '',file=sys.stderr);print(e.stderr or '',file=sys.stderr);raise
