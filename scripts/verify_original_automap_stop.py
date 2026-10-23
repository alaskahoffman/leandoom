#!/usr/bin/env python3
"""Executable-bound automap cache handoff, including the stored DOS event quirk."""
import argparse
import json
import random
import re
import struct
import subprocess
from pathlib import Path
import verify_original_inline_thrust as extraction
import verify_original_weapon_drop as drop
ROOT, require = extraction.ROOT, extraction.require
UNITS = {n:'AutomapStop.'+n+'Code' for n in ['tag','unload','stop','responder','responderReturn']}
UNITS.update(choice='DeathChoice.code',guard='DeathAutomap.code')
NAMES = [n+'_checked' for n in UNITS]+['event_checked','dos_checked','connected_checked','conditional_checked']+[
    'Doom.Proofs.AutomapStop.'+n for n in ['tag_execution','iteration_execution','loop_prefix','unload_execution',
    'responder_execution','stop_execution','stop_frame','stop_flags','dos_frame','dos_responder','dos_execution']]+[
    'Doom.Proofs.DeathAutomapHandoff.execution','Doom.Proofs.AutomapDeathChoice.execution']

def certificate(raw,tables,digest):
    s=f'''-- DOOM.EXE SHA-256 {digest}; flat loader/model remain external obligations.
import Doom.Proofs.OriginalAutomapDeathChoice
import Doom.Proofs.OriginalDeathAutomapHandoff
set_option linter.unusedSimpArgs false
namespace Doom.Verification.ExtractedAutomapStop
open Doom.Proofs X86 X86Memory X86Control BlockSummary
'''
    for name,definition in UNITS.items():
        s+=f'def {name} : List UInt8 := ['+','.join(hex(b) for b in raw[name])+f']\ntheorem {name}_checked : {name}={definition} := by decide\n'
    s+='def event : List UInt8 := ['+','.join(hex(b) for b in tables['event'])+']\n'
    s+='''-- This is NOT the {1, AM_MSGEXITED} contract of the conditional return proof.
theorem event_checked : event=[0,0,0,0,1,0,0,0,0,0x78,0x6d,0x61] := by decide

theorem dos_checked (s : X86Memory.State) (f : Option Flags)
    (cache : AutomapStop.UnloadInputs (AutomapStop.stopUnload s))
    (kind : load32 s.memory (0x12c98#32)=0)
    (safe : ∀ b, b ∈ AutomapStop.dosWrites s → Apart (0x12c98#32) b) :
    X86Routine.run (AutomapStop.bytesProgram tag unload stop responder responderReturn) [0x39af8] 226
      ⟨s,f,0x24f90⟩=some (AutomapStop.dosResponderResult (AutomapStop.stopResponder s)) := by
  rw [tag_checked,unload_checked,stop_checked,responder_checked,responderReturn_checked]
  exact AutomapStop.dos_execution s f cache kind safe

theorem connected_checked :
    DeathAutomapHandoff.bytesProgram guard tag unload stop responder responderReturn=DeathAutomapHandoff.program := by
  rw [guard_checked,tag_checked,unload_checked,stop_checked,responder_checked,responderReturn_checked]; rfl

theorem conditional_checked (s : X86Memory.State) (f : Option Flags)
    (h : AutomapStop.StopInputs s) :
    X86Routine.run (AutomapStop.bytesProgram tag unload stop responder responderReturn) [0x2a3c8] 250
      ⟨s,f,0x24f90⟩=some (AutomapStop.stopResult s) := by
  rw [tag_checked,unload_checked,stop_checked,responder_checked,responderReturn_checked]
  exact AutomapStop.stop_execution s f h
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedAutomapStop\n'

def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedAutomapStop.'+short
        match=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+name)
        axioms={a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms))
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw,tables,spec):
    import capstone
    import unicorn as uc
    from unicorn import x86_const as x
    em=uc.Uc(uc.UC_ARCH_X86,uc.UC_MODE_32);CODE=0x100000;DATA=0x600000;mask=0xffffffff
    for a,n in [(CODE,0x40000),(0,0x80000),(0x400000,0x80000),(DATA,0x10000),(0xfffff000,4096)]:em.mem_map(a,n)
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];visits=[];target=0
    em.hook_add(uc.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_u:writes.append((a,n,v&((1<<(8*n))-1))))
    def visit(e,a,_n,_u):
        visits.append(a-CODE)
        if a-CODE==target:e.emu_stop()
    em.hook_add(uc.UC_HOOK_CODE,visit)
    put=lambda a,v:em.mem_write(a&mask,struct.pack('<I',v&mask))
    signed=lambda v:v if v<2**31 else v-2**32
    rng=random.Random(0x24f90);counts={'stored_dos_event':0,'conditional_exit_event':0};listings={}
    for name,unit in spec['units'].items():
        listing=list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(raw[name],int(unit['code_offset'],16)))
        require(b''.join(bytes(i.bytes) for i in listing)==raw[name],'independent decoding: '+name)
        listings[name]=[f'{i.address:#x}: {i.mnemonic} {i.op_str}' for i in listing]
    for base in [0,0x400000]:
        for name,unit in spec['units'].items():
            code=bytearray(raw[name])
            for r in unit['relocations']:struct.pack_into('<I',code,r['offset'],base+int(r['target'],16))
            em.mem_write(CODE+int(unit['code_offset'],16),bytes(code))
        em.ctl_remove_cache(CODE,CODE+0x40000)
        for i in range(256):
            obj=DATA+64+i%4;info=DATA+512+(i//4)%4;sp=DATA+0xe000+i%4 if i%11 else 0
            hp=[0,0xffffffff,0xffffff9c,0xffffff9b,0x80000000,rng.getrandbits(32)][i%6]
            spawn=[100,0,0x80000000,rng.getrandbits(32)][(i//6)%4]
            normal=rng.getrandbits(32);extreme=[0,19,0xffffffff][i%3]
            for mode in ['dos','guard_dos','conditional','conditional_choice']:
                rr=[rng.getrandbits(32) for _ in regs];rr[3]=obj;rr[4]=sp
                rr0=rr.copy();amsp=(sp-4)&mask if mode=='guard_dos' else sp
                pointers=[]
                for j in range(10):
                    # Include repeated digit pointers as well as unaligned blocks.
                    ptr=DATA+0x1000+(j if i%7 else j%3)*64+i%4;pointers.append(ptr)
                    put(base+0x2b708+4*j,ptr);put(ptr-12,0x1d4a11)
                    put(ptr-20,[256,257,0x80000000,0xffffffff][(i+j)%4]);put(ptr-16,rng.getrandbits(32))
                put(obj+92,info);put(obj+108,hp);put(info+8,spawn);put(info+48,normal);put(info+52,extreme)
                victim=i%4;player=base+0x2ae78+280*victim
                put(obj+132,player);put(base+0x2b3dc,victim);put(base+0x12c5c,[1,0x80000000,0xffffffff][i%3])
                put(base+0x12c94,0x12345678);put(base+0x75434,0x87654321)
                em.mem_write(base+0x12c98,tables['event'])
                conditional=mode.startswith('conditional')
                if conditional:put(base+0x12c98,1);put(base+0x12c9c,0x616d7800)
                put(amsp,CODE+0x2a3c8)
                expected=[]
                def push(a,v):expected.append((a&mask,4,v&mask))
                if mode=='guard_dos':
                    push(amsp,CODE+0x2a3c8);rr[0]=player;rr[2]=player
                push(amsp-4,rr[3]);push(amsp-8,rr[2]);push(amsp-12,CODE+0x24f97)
                push(amsp-16,rr[3]);push(amsp-20,rr[2])
                for j,ptr in enumerate(pointers):
                    push(amsp-24,CODE+0x24e74);push(amsp-28,4*(j+1));push(ptr-16,101)
                push(base+0x12c5c,0);push(amsp-12,CODE+0x24fae)
                for off,val in [(16,1),(20,rr[1]),(24,0),(28,rr[6]),(32,rr[7])]:push(amsp-off,val)
                if conditional:
                    push(base+0x75434,1);push(base+0x12c94,1)
                    rr[0]=0;rr[4]=(amsp+4)&mask
                    target=0x2a3c8
                    if mode=='conditional_choice':
                        over=signed(hp)<signed((-spawn)&mask)
                        rr[0]=obj;rr[2]=extreme if over and extreme else normal;rr[6]=hp
                        if over:rr[7]=extreme
                        rr[4]=amsp;push(amsp,CODE+0x2a3f1);target=0x30ea0
                    counts['conditional_exit_event']+=1
                else:
                    rr[0]=base+0x12c98;rr[2]=0;rr[3]=1;rr[4]=(amsp-40)&mask;rr[7]=base+0x12c98
                    target=0x39af8;counts['stored_dos_event']+=1
                pages={(a&~4095) for a,_,_ in expected}|{((a+3)&mask)&~4095 for a,_,_ in expected}
                before={a:bytearray(em.mem_read(a,4096)) for a in pages}
                for r,v in zip(regs,rr0):em.reg_write(r,v)
                em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5));writes.clear();visits.clear()
                em.emu_start(CODE+(0x2a38c if mode=='guard_dos' else 0x24f90),CODE+0x40000,count=264)
                label=f'{base:x}/{i}/{mode}'
                require(em.reg_read(x.UC_X86_REG_EIP)==CODE+target,'stop '+label)
                require([em.reg_read(r) for r in regs]==rr,'registers '+label)
                require(writes==expected,'ordered writes '+label)
                require(visits.count(0x399b0)==10,'ten real allocator calls '+label)
                require(len(visits)-1 <= {'dos':226,'guard_dos':239,'conditional':250,'conditional_choice':263}[mode], 'instruction bound '+label)
                if not conditional:
                    require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==0x81,'projected comparison flags '+label)
                for a,n,val in expected:
                    for byte in range(n):
                        at=(a+byte)&mask;before[at&~4095][at%4096]=(val>>(8*byte))&255
                require(all(em.mem_read(a,4096)==content for a,content in before.items()),'memory '+label)
                require(all(struct.unpack('<I',em.mem_read(ptr-16,4))[0]==101 for ptr in pointers),'cache tags '+label)
    return {'counts':counts,'cases':sum(counts.values()),'all_registers_and_ordered_writes':True,
            'unaligned_and_wrapping_stack':True,'repeated_cache_pointers':True,'data_bases':[0,0x400000],
            'stored_dos_event_does_not_take_exit_event_path':True,'disassembly':listings}

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-automap-stop.json').read_text())
    profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec);tables=drop.table_data(binary,profile,spec)
    out=ROOT/'artifacts/original-automap-stop';out.mkdir(parents=True,exist_ok=True)
    source=out/'Extracted.lean';source.write_text(certificate(raw,tables,profile['exe_sha256']))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalAutomapDeathChoice','Doom.Proofs.OriginalDeathAutomapHandoff'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True)
    require(checked.returncode==0,checked.stdout+checked.stderr);audit(checked.stdout);print(checked.stdout,end='',flush=True)
    report={'exe_sha256':profile['exe_sha256'],'scope':spec['scope'],'axioms':checked.stdout.splitlines(),
            'cross_check':cross_check(raw,tables,spec) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: original automap cache unloading connected to the actual DOS notification branch.')
    if report['cross_check']:print('Independent x86 comparisons:',report['cross_check']['cases'])
if __name__=='__main__':main()
