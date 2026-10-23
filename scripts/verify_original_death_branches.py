#!/usr/bin/env python3
"""Bind the DOS death branches to Lean proofs and optionally execute their bytes."""
import argparse
import json
import random
import re
import struct
import subprocess
import tempfile
from pathlib import Path
import verify_original_inline_thrust as extraction
import death_branch_continuation
ROOT, require = extraction.ROOT, extraction.require
NAMES = ['guard_checked','choice_checked','joined_checked'] + [
    'Doom.Proofs.DeathAutomap.'+n for n in ['decoded','prologue','execution','live_guard','frame']] + [
    'Doom.Proofs.DeathChoice.'+n for n in ['decoded','prologue','execution','chosen_live','original_execution','frame','live_correspondence']] + [
    'Doom.Proofs.DeathBranches.execution','lethal_checked',
    'Doom.Proofs.KillBookkeeping.joined_execution_detailed',
    'Doom.Proofs.KillWeaponDrop.joined_execution_detailed',
    'Doom.Proofs.KillDeathBranches.joined_execution']

def certificate(raw,digest):
    source=f'''-- DOOM.EXE SHA-256 {digest}. Extraction/loader remain external obligations.
import Doom.Proofs.OriginalKillDeathBranches
set_option linter.unusedSimpArgs false
namespace Doom.Verification.ExtractedDeathBranches
open Doom.Proofs X86 X86Memory X86Control
'''
    for name,module in [('guard','DeathAutomap'),('choice','DeathChoice')]:
        source+=f'def {name} : List UInt8 := ['+','.join(hex(b) for b in raw[name])+f']\ntheorem {name}_checked : {name}={module}.code := by decide\n'
    source+='''theorem joined_checked (s : X86Memory.State) (f : Option Flags) (v : Fin 4) (world : Death.World)
    (hp : Int32) (info : Death.Info)
    (console : load32 s.memory (0x2b3dc#32)=BitVec.ofNat 32 world.console.val)
    (victim : load32 s.memory (s.regs 3+(132#32))=DeathAutomap.player v)
    (auto : (DeathAutomap.active s≠0) ↔ world.automap=true)
    (ins : DeathChoice.Inputs s hp info) :
    ∃ t, X86Routine.run (DeathBranches.bytesProgram guard choice) [0x24f90,0x30ea0] 26 ⟨s,f,0x2a38c⟩=some t ∧
      t.pc=(if Death.shouldStopAutomap v world then 0x24f90 else 0x30ea0) ∧
      (Death.shouldStopAutomap v world=false → t.core.regs 0=s.regs 3 ∧
        t.core.regs 2=BitVec.ofNat 32 (Death.deathState hp info)) ∧
      t.core.regs 3=s.regs 3 ∧ t.core.regs 4=s.regs 4-4 ∧
      load32 t.core.memory (s.regs 4-4)=(if Death.shouldStopAutomap v world then 0x2a3c8 else 0x2a3f1) ∧
      PlayerHeight.Frame s.memory t.core.memory [s.regs 4-4] := by
  rw [guard_checked,choice_checked]
  exact DeathBranches.execution s f v world hp info console victim auto ins
'''
    source+='''theorem lethal_checked (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (rng : DoomRandom) (i : Fin 4) (body : Death.Body) (world : Death.World) (w : Fin 3) (y : Fixed)
    (h : KillDeathBranches.Inputs s v d baby i body world w y)
    (dead : (PlayerDamage.apply v d none false baby rng).killed=true) :
    ∃ t, X86Routine.run (KillDeathBranches.bytesProgram guard choice) [0x24f90,0x30ea0] 239 ⟨s,f,pc⟩=some t ∧
      KillBookkeeping.joinedObservation s i t=KillBookkeeping.joinedLiveObservation
        (PlayerDamage.apply v d none false baby rng) i body world ∧
      load32 t.core.memory (KillBookkeeping.player i+244)=0x15a28+BitVec.ofNat 32 (Weapon.down w.val)*28 ∧
      load32 t.core.memory (KillBookkeeping.player i+248)=1 ∧
      load32 t.core.memory (KillBookkeeping.player i+256)=(Weapon.lowerHeight y true).raw.toBitVec ∧
      t.pc=(if Death.shouldStopAutomap i world then 0x24f90 else 0x30ea0) ∧
      (Death.shouldStopAutomap i world=false → t.core.regs 0=s.regs 0 ∧
        t.core.regs 2=BitVec.ofNat 32 (Death.deathState (PlayerDamage.apply v d none false baby rng).state.health body.info)) ∧
      t.core.regs 3=s.regs 0 ∧ t.core.regs 4=s.regs 4-56 ∧
      load32 t.core.memory (s.regs 4-56)=(if Death.shouldStopAutomap i world then 0x2a3c8 else 0x2a3f1) ∧
      PlayerHeight.Frame s.memory t.core.memory (KillDeathBranches.priorWrites s i ++ [s.regs 4-56]) := by
  rw [guard_checked,choice_checked]
  exact KillDeathBranches.joined_execution s f pc site v d baby rng i body world w y h dead
'''
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedDeathBranches\n'

def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedDeathBranches.'+short
        match=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+name)
        axioms={a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms))
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def choice_cases():
    rng=random.Random(0xDEAD)
    edges=[0,1,2,99,100,101,0x7fffffff,0x80000000,0x80000001,0xffffff9b,0xffffff9c,0xffffff9d,0xfffffffe,0xffffffff]
    cases=[(hp,spawn,17,ex) for hp in edges for spawn in edges for ex in [0,19,0xffffffff]]
    for spawn in list(range(2048))+[rng.getrandbits(32) for _ in range(2048)]:
        for delta in [-1,0,1]:
            for ex in [0,19]:cases.append(((-spawn+delta)&0xffffffff,spawn,17,ex))
    cases += [(rng.getrandbits(32),rng.getrandbits(32),rng.getrandbits(32),rng.getrandbits(32)) for _ in range(2048)]
    return cases

def cross_check(raw,spec, *, e1m1_profile=False):
    import capstone
    import unicorn as uc
    from unicorn import x86_const as x
    rng=random.Random(0x2A3C8);signed=lambda v:v if v<2**31 else v-2**32
    cases=choice_cases()
    if e1m1_profile:
        cases=[(hp,100,158,165) for hp in sorted({row[0] for row in cases})]
    with tempfile.TemporaryDirectory() as directory:
        inp=Path(directory)/'input';out=Path(directory)/'output'
        inp.write_text(''.join(f'{signed(hp)} {signed(spawn)} {normal} {extreme}\n' for hp,spawn,normal,extreme in cases))
        subprocess.run([str(ROOT/'.lake/build/bin/death-probe'),'choice',str(inp),str(out)],check=True)
        answers=list(map(int,out.read_text().splitlines()))
        require(len(answers)==len(cases),'probe row count')
    em=uc.Uc(uc.UC_ARCH_X86,uc.UC_MODE_32);CODE=0x100000;DATA=0x600000
    em.mem_map(CODE,0x40000)
    for addr,size in [(0,0x30000),(DATA,0x1000),(0xfffff000,0x1000)]:em.mem_map(addr,size)
    listings={}
    for name,unit in spec['units'].items():
        offset=int(unit['code_offset'],16);em.mem_write(CODE+offset,raw[name])
        listing=list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(raw[name],offset))
        require(b''.join(bytes(i.bytes) for i in listing)==raw[name],'independent decoder mismatch')
        require(len(listing)=={'guard':13,'choice':16}[name],'instruction count')
        listings[name]=[f'{i.address:#x}: {i.mnemonic} {i.op_str}' for i in listing]
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];visits=[]
    em.hook_add(uc.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_u:writes.append((a,n,v&((1<<(8*n))-1))))
    def visit(e,a,_n,_u):
        visits.append(a-CODE)
        if a-CODE in [0x24f90,0x30ea0]:e.emu_stop()
    em.hook_add(uc.UC_HOOK_CODE,visit)
    put=lambda a,v:em.mem_write(a&0xffffffff,struct.pack('<I',v&0xffffffff))
    page_addrs=[DATA,0xfffff000,0x12000,0x2a000,0x2b000,0]
    branch_counts={'automap':0,'normal':0,'extreme':0}
    for i,((hp,spawn,normal,extreme),answer) in enumerate(zip(cases,answers)):
        obj=DATA+64+i%4;info=DATA+512+(i//4)%4;sp=DATA+3072+i%4 if i%11 else 0
        victim=0 if e1m1_profile else i%4;console=0 if e1m1_profile else (i//4)%4
        active=0 if e1m1_profile else [0,1,0x80000000,0xffffffff][(i//16)%4]
        put(obj+92,info);put(obj+108,hp);put(info+8,spawn);put(info+48,normal);put(info+52,extreme)
        put(obj+132,0x2ae78+280*victim);put(0x2b3dc,console);put(0x12c5c,active)
        # Alternate the joined path and isolated selector so every numeric case
        # executes selection even if its joined path would stop at AM_Stop.
        for joined in [False,True]:
            rr=[rng.getrandbits(32) for _ in regs];rr[3]=obj;rr[4]=sp
            for reg,value in zip(regs,rr):em.reg_write(reg,value)
            em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5))
            before={a:bytearray(em.mem_read(a,4096)) for a in page_addrs}
            writes.clear();visits.clear()
            em.emu_start(CODE+(0x2a38c if joined else 0x2a3c8),CODE+0x40000,count=27)
            stop=joined and victim==console and active!=0
            target=0x24f90 if stop else 0x30ea0;ret=0x2a3c8 if stop else 0x2a3f1
            require(em.reg_read(x.UC_X86_REG_EIP)==CODE+target,f'call boundary {i}')
            if joined:rr[0]=0x2ae78+280*console;rr[2]=0x2ae78+280*victim
            if stop:branch_counts['automap']+=1
            else:
                over=signed(hp)<signed((-spawn)&0xffffffff)
                branch_counts['extreme' if over and extreme else 'normal']+=1
                rr[0]=obj;rr[2]=answer;rr[6]=hp
                if over:rr[7]=extreme
            rr[4]=(sp-4)&0xffffffff
            require([em.reg_read(r) for r in regs]==rr,f'register mismatch {i}, joined={joined}')
            require(writes==[(rr[4],4,CODE+ret)],f'write sequence {i}')
            for a,n,val in writes:
                for byte in range(n):
                    at=(a+byte)&0xffffffff;page=at&~4095
                    before[page][at-page]=(val>>(byte*8))&255
            require(all(em.mem_read(a,4096)==contents for a,contents in before.items()),f'memory frame {i}')
    if e1m1_profile:require(branch_counts['automap']==0 and branch_counts['normal']>0 and branch_counts['extreme']>0,'fixed-profile branches')
    return {'fixed_e1m1_profile':e1m1_profile,'cases':len(cases)*2,'branch_counts':branch_counts,'disassembly':listings,
            'compiled_live_deathState':True,'all_registers_and_write_order_checked':True,
            'unaligned_objects_and_stack':True,'wrapping_stack':True}

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-death-branches.json').read_text())
    profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec)
    out=ROOT/'artifacts/original-death-branches';out.mkdir(parents=True,exist_ok=True)
    source=out/'Extracted.lean';source.write_text(certificate(raw,profile['exe_sha256']))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalKillDeathBranches','death-probe'],cwd=ROOT,check=True)
    subprocess.run([str(ROOT/'scripts/verify-original-weapon-drop')],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout);print(checked.stdout,end='',flush=True)
    report={'exe_sha256':profile['exe_sha256'],'units':spec['units'],'scope':spec['scope']+' Also joined from the three lethal floor CALL sites, with transported initial-memory contracts and a 239-instruction bound.',
            'axioms':checked.stdout.splitlines(),'cross_check':cross_check(raw,spec) if args.cross_check else None,
            'continuous_cross_check':death_branch_continuation.check(binary,profile,raw,spec) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: lethal floor damage is joined through weapon lowering to the original automap/death-state call boundaries.')
    if report['cross_check']:
        print('Independent x86 comparisons:',report['cross_check']['cases'])
        print('Continuous lethal comparisons:',report['continuous_cross_check']['continuous_lethal_cases'])
if __name__=='__main__':main()
