#!/usr/bin/env python3
"""Certify the original dead-player A_Lower action and live Lean height update."""
import argparse
import json
import random
import re
import struct
import subprocess
import tempfile
from pathlib import Path
import verify_original_inline_thrust as extraction
ROOT,require=extraction.ROOT,extraction.require
NAMES=['bytes_checked','live_checked']+['Doom.Proofs.WeaponLower.'+n for n in
       ['decoded','add_high','advance_word','advance_apart','execution','advance_value',
        'final_height','original_execution','result_registers','result_frame','live_correspondence']]

def certificate(raw,digest):
    literal='['+','.join(hex(x) for x in raw['lower'])+']'
    return f'''-- DOOM.EXE SHA-256 {digest}; extraction and loader checked externally.
import Doom.Proofs.OriginalWeaponLower
namespace Doom.Verification.ExtractedWeaponLower
open Doom.Proofs WeaponLower X86 X86Memory X86Control
def lower : List UInt8 := {literal}
theorem bytes_checked : lower=code := by decide
theorem live_checked (s : X86Memory.State) (f : Option Flags) (y : Doom.Fixed) (h : Inputs s y) :
    ∃ t, X86Routine.run (bytesProgram lower) [0x2d095] 9 ⟨s,f,0x2d490⟩=some t ∧
      load32 t.core.memory (yAddress s)=(Doom.Weapon.lowerHeight y true).raw.toBitVec ∧
      t.pc=0x2d095 ∧ t.core.regs=write s.regs 4 (s.regs 4+4) ∧
      PlayerHeight.Frame s.memory t.core.memory [s.regs 4-4,yAddress s] := by
  rw [bytes_checked]
  exact live_correspondence s f y h
'''+ '\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedWeaponLower\n'

def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedWeaponLower.'+short
        match=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+name)
        axioms={a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms))
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def cases():
    rng=random.Random(0x2d490)
    # Every high half, independent fractional parts; explicit signed/clamp edges.
    values=[(hi<<16)|rng.randrange(65536) for hi in range(65536)]
    values += [(n+d)&0xffffffff for n in [0,0x7a0000,0x800000,0x7ffa0000,0x80000000,0xffff0000] for d in [-65536,-1,0,1,65535]]
    values += [rng.getrandbits(32) for _ in range(2048)]
    return values

def cross_check(raw):
    import unicorn as uc
    from unicorn import x86_const as x
    values=cases();signed=lambda n:n if n<2**31 else n-2**32
    with tempfile.TemporaryDirectory() as directory:
        inp=Path(directory)/'commands';out=Path(directory)/'out'
        inp.write_text(''.join(f'reset {i%3} 50 8 1 0 0\nheight {signed(y)}\ndie\n' for i,y in enumerate(values)))
        subprocess.run([str(ROOT/'.lake/build/bin/weapon-probe'),str(inp),str(out)],check=True)
        rows=out.read_text().splitlines();require(len(rows)==3*len(values),'probe length mismatch')
        answers=[list(map(int,r.split('|')[0].split())) for r in rows[2::3]]
    em=uc.Uc(uc.UC_ARCH_X86,uc.UC_MODE_32);CODE=0x100000;DATA=0x600000
    em.mem_map(CODE,0x30000);em.mem_map(DATA,4096);em.mem_map(0,4096);em.mem_map(0xfffff000,4096)
    em.mem_write(CODE+0x2d490,raw['lower'])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];visits=[]
    em.hook_add(uc.UC_HOOK_MEM_WRITE,lambda _e,_a,addr,size,value,_u:writes.append((addr,size,value&((1<<(8*size))-1))))
    def visit(e,addr,_size,_u):
        visits.append(addr-CODE)
        if addr==CODE+0x2d095:e.emu_stop()
    em.hook_add(uc.UC_HOOK_CODE,visit)
    put=lambda addr,v:em.mem_write(addr&0xffffffff,struct.pack('<I',v&0xffffffff))
    rng=random.Random(0x4c4f574552);clamps=0;below=0
    for i,(y,answer) in enumerate(zip(values,answers)):
        player=DATA+64+i%4;psp=DATA+512+i%4;sp=DATA+3072+i%4
        if i%11==0:sp=0
        elif i%13==0:psp=0xfffffff0
        ya=(psp+12)&0xffffffff
        put(player+4,1);put(ya,y);put(sp,CODE+0x2d095)
        rr=[rng.getrandbits(32) for _ in regs];rr[0]=player;rr[2]=psp;rr[4]=sp
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5))
        before={a:bytearray(em.mem_read(a,4096)) for a in [0,DATA,0xfffff000]}
        writes.clear();visits.clear();em.emu_start(CODE+0x2d490,CODE+0x30000,count=10)
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+0x2d095,f'return {i}')
        advanced=(y+0x60000)&0xffffffff;clamp=signed(advanced)>=0x800000
        clamps+=clamp;below+=not clamp
        expected=0x800000 if clamp else advanced
        require(answer[4]==[3,11,19][i%3] and answer[5]==1,'live drop state/tics mismatch')
        require((answer[7]&0xffffffff)==expected,'live Weapon.drop height mismatch')
        require(struct.unpack('<I',em.mem_read(ya,4))[0]==expected,f'height {i}')
        expected_writes=[((sp-4)&0xffffffff,4,rr[3]),((ya+2)&0xffffffff,2,((y>>16)+6)&65535)]
        if clamp:expected_writes.append((ya,4,0x800000))
        require(writes==expected_writes,f'ordered writes {i}')
        for addr,size,value in writes:
            for off,b in enumerate(value.to_bytes(size,'little')):
                p=(addr+off)&0xffffffff;before[p&~4095][p&4095]=b
        require(all(em.mem_read(a,4096)==v for a,v in before.items()),f'memory frame {i}')
        rr[4]=(sp+4)&0xffffffff
        require([em.reg_read(r) for r in regs]==rr,f'register restoration {i}')
        require((0x2d4a5 in visits)==clamp and 0x2d4ae not in visits,'dead-player branch')
    return {'cases':len(values),'below':below,'clamped':clamps,'all_65536_integer_halves':True,
            'actual_Weapon_drop_fist_pistol_shotgun':True,'unaligned_fields':True,'wrapping_stack':True,
            'high_address_height':True,'all_registers_and_ordered_writes_and_memory':True}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--cross-check',action='store_true');args=p.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-weapon-lower.json').read_text())
    profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec)
    out=ROOT/'artifacts/original-weapon-lower';out.mkdir(parents=True,exist_ok=True)
    path=out/'Extracted.lean';path.write_text(certificate(raw,profile['exe_sha256']))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalWeaponLower','weapon-probe'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout)
    report={'exe_sha256':profile['exe_sha256'],'scope':spec['scope'],'axioms':checked.stdout.splitlines(),
            'cross_check':cross_check(raw) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f'PASS: original dead-player weapon lowering; {len(NAMES)} audited declarations.')
    if args.cross_check:print(report['cross_check'])
if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as e:
        print(e.stdout or '');print(e.stderr or '');raise
