#!/usr/bin/env python3
"""Certify original animation selection plus the actual walking-state CALL/RET."""
import argparse
import hashlib
import json
import random
import re
import struct
import subprocess
import sys
import verify_original_mul as original
import verify_original_inline_thrust as extraction
import verify_original_thrust as thrust
from verify_original_arithmetic import fixups

ROOT, require = original.ROOT, original.require
NAMES = ['caller_checked','callee_checked','engine_checked','memory_checked',
         'Doom.Proofs.PlayerAnimation.call_establishes_setter',
         'Doom.Proofs.PlayerAnimation.setter_program',
         'Doom.Proofs.PlayerAnimation.engine_selection',
         'Doom.Proofs.PlayerAnimation.result_fields',
         'Doom.Verification.X86Routine.run_sound']


def table_data(binary, profile, spec):
    le = int(profile['le_offset'],16)
    u32 = lambda p: struct.unpack_from('<I',binary,p)[0]
    data = struct.unpack_from('<6I',binary,le+u32(le+0x40)+48)
    require(data == (0x85e10,0x70000,0x2043,71,38,0),'unexpected data object')
    start = int(spec['run1']['offset'],16); raw = bytearray()
    for p in range(start,start+28):
        entry=le+u32(le+0x48)+4*(70+p//4096)
        require(binary[entry+3]==0,'unsupported table page')
        physical=int.from_bytes(binary[entry:entry+3],'big')
        require(physical>0,'unmapped table page')
        at=int(profile['data_pages_offset'],16)+(physical-1)*4096+p%4096
        require(at<len(binary),'truncated table page');raw.append(binary[at])
    require(raw.hex()==spec['run1']['hex'],'walking state table mismatch')
    relocs=fixups(binary,range(70+start//4096,70+(start+27)//4096+1))
    require(not any(max(70*4096+start,p)<min(70*4096+start+28,p+4) for p,_,_ in relocs),
            'unexpected walking state table relocation')
    require(struct.unpack('<7I',raw)==(28,0,4,0,151,0,0),'walking state fields mismatch')
    return bytes(raw)


def certificate(raw,digest):
    lit=lambda name:'['+', '.join(hex(b) for b in raw[name])+']'
    audits='\n'.join('#print axioms '+n for n in NAMES)
    return f'''-- Original DOOM.EXE SHA-256 {digest}.
import Doom.Proofs.OriginalPlayerAnimation
set_option maxRecDepth 32768
namespace Doom.Verification.ExtractedPlayerAnimation
open X86Memory X86Control Doom.Proofs.PlayerAnimation
def callerCode : List UInt8 := {lit('playerAnimationBytes')}
def calleeCode : List UInt8 := {lit('setMobjStateBytes')}
theorem caller_checked : callerCode = Doom19.playerAnimationBytes := by decide
theorem callee_checked : calleeCode = Doom19.setMobjStateBytes := by decide
theorem memory_checked (s : X86Memory.State) (flags : Option Flags) (h : Inputs s) :
    X86Routine.run (bytesProgram callerCode calleeCode) [0x3325e] 33 ⟨s,flags,0x3323e⟩ = some (result s) := by
  rw [caller_checked,callee_checked]
  exact animation_bytes s flags h
theorem engine_checked (s : X86Memory.State) (flags : Option Flags)
    (a : Doom.PlayerAnim.State) (c : Doom.Ticcmd) (h : EngineInputs s a c) :
    (X86Routine.run (bytesProgram callerCode calleeCode) [0x3325e] 33 ⟨s,flags,0x3323e⟩).map (fun t =>
      (t.pc,load32 t.core.memory (object s+(100#32)),load32 t.core.memory (object s+(96#32)),t.core.regs 4)) =
      some (0x3325e,statePointer (a.startWalking c).frame,(a.startWalking c).tics.toBitVec,s.regs 4) := by
  rw [caller_checked,callee_checked]
  exact animation_engine s flags a c h
{audits}
end Doom.Verification.ExtractedPlayerAnimation
'''


def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedPlayerAnimation.'+short
        match=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing axiom audit: '+name)
        axioms={a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Classical.choice','Quot.sound'},'unexpected proof axioms: '+str(axioms))
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')


def cross_check(raw,table,spec):
    import capstone
    import unicorn as uc
    from unicorn import x86_const as x
    rng=random.Random(0x3323e150)
    signed=lambda v:v if v<2**31 else v-2**32
    signed8=lambda v:v if v<128 else v-256
    cases=[(frame,rng.getrandbits(32),f,c) for frame in [149,150] for f in range(256) for c in range(256)]
    cases += [(frame,rng.getrandbits(32),rng.randrange(256),rng.randrange(256)) for frame in range(65536)]
    answers=[tuple(map(int,line.split())) for line in thrust.probe([
        f'player-animation {frame} {signed(tics)} {signed8(f)} {signed8(c)}' for frame,tics,f,c in cases])]
    md=capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32)
    listing={name:list(md.disasm(code,int(spec['units'][name]['code_offset'],16))) for name,code in raw.items()}
    for name,insts in listing.items():require(b''.join(bytes(i.bytes) for i in insts)==raw[name],'independent decode mismatch')
    em=uc.Uc(uc.UC_ARCH_X86,uc.UC_MODE_32);CODE,DATA=0x100000,0x800000
    em.mem_map(CODE,0x40000);em.mem_map(DATA,0x1000)
    for base in [0,0x400000]:em.mem_map(base+0x15000,0x2000);em.mem_write(base+0x16a90,table)
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
          x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];visited=[]
    em.hook_add(uc.UC_HOOK_MEM_WRITE,lambda _e,_a,addr,size,_v,_u:writes.append((addr,size)))
    def observe(machine,addr,size,user):
        visited.append(addr-CODE)
        if addr==CODE+0x3325e:machine.emu_stop()
    em.hook_add(uc.UC_HOOK_CODE,observe)
    paths={'walk_call':0,'idle_skip':0,'already_animating_skip':0}
    for i,((frame,tics,f,c),(newframe,newtics)) in enumerate(zip(cases,answers)):
        base=[0,0x400000][i%2]
        for name,code in raw.items():
            unit=spec['units'][name];patched=bytearray(code)
            for r in unit['relocations']:struct.pack_into('<I',patched,r['offset'],base+int(r['target'],16))
            em.mem_write(CODE+int(unit['code_offset'],16),bytes(patched))
        em.ctl_remove_cache(CODE,CODE+0x40000)
        player,obj,sp=DATA+32+i%4,DATA+256+(i//4)%4,DATA+768+(i//16)%4
        em.mem_write(DATA,bytes([0xa5])*4096)
        em.mem_write(player,struct.pack('<I',obj));em.mem_write(player+8,bytes([f,c]))
        sprite,display=rng.getrandbits(32),rng.getrandbits(32)
        em.mem_write(obj+36,struct.pack('<II',sprite,display))
        em.mem_write(obj+96,struct.pack('<II',tics,base+0x15a28+28*frame))
        expected=bytearray(em.mem_read(DATA,4096));rs=[rng.getrandbits(32) for _ in regs]
        rs[1],rs[4],rs[6]=player,sp,player+8
        for reg,value in zip(regs,rs):em.reg_write(reg,value)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5))
        writes.clear();visited.clear();em.emu_start(CODE+0x3323e,0,count=34)
        take=bool(frame==149 and (f or c));paths['walk_call' if take else 'idle_skip' if not(f or c) else 'already_animating_skip']+=1
        expected_writes=[]
        if take:
            struct.pack_into('<III',expected,sp-12-DATA,rs[6],rs[3],CODE+0x3325e)
            struct.pack_into('<II',expected,obj+36-DATA,28,0)
            struct.pack_into('<II',expected,obj+96-DATA,newtics&0xffffffff,base+0x15a28+28*newframe)
            expected_writes=[(sp-4,4),(sp-8,4),(sp-12,4),(obj+100,4),(obj+96,4),(obj+36,4),(obj+40,4)]
            rs[0],rs[2]=1,151;expected_flags=(0,0,0)
            require(0x30ea0 in visited and 0x30efa in visited,'call or return was not executed')
        elif f or c:
            rs[0]=obj;a=base+0x15a28+28*frame;b=base+0x16a74;diff=(a-b)&0xffffffff
            expected_flags=(int(diff==0),diff>>31,int(bool(((a^b)&(a^diff))&0x80000000)))
        else:expected_flags=(1,0,0)
        require(newframe==(150 if take else frame) and newtics==(4 if take else signed(tics)),'compiled engine mismatch')
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+0x3325e,f'return mismatch {i}')
        require([em.reg_read(r) for r in regs]==rs,f'register restoration mismatch {i}')
        require(em.mem_read(DATA,4096)==expected,f'animation or stack memory mismatch {i}')
        require(writes==expected_writes,f'store order mismatch {i}')
        flags=em.reg_read(x.UC_X86_REG_EFLAGS)
        require(((flags>>6)&1,(flags>>7)&1,(flags>>11)&1)==expected_flags,f'flag mismatch {i}')
    return {'cases':len(cases),'paths':paths,'all_command_pairs_standing_and_running':True,'all_16bit_state_indices':True,
            'reference':'compiled PlayerAnim.startWalking used by Player.prepareTick','code_base':CODE,'data_bases':[0,0x400000],
            'checks':['state pointer','tics','sprite and display frame','full dynamic memory page','all registers','stack restoration','call and return','write order','ZF/SF/OF'],
            'disassembly':{name:[f'{i.address:#x}: {i.mnemonic} {i.op_str}' for i in insts] for name,insts in listing.items()}}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-player-animation.json').read_text())
    profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec);table=table_data(binary,profile,spec)
    out=ROOT/'artifacts/original-player-animation';out.mkdir(parents=True,exist_ok=True)
    source=out/'Extracted.lean';source.write_text(certificate(raw,profile['exe_sha256']))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalPlayerAnimation','fidelity-probe'],cwd=ROOT,check=True)
    result=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(result.stdout);print(result.stdout,end='',flush=True)
    report={'exe_sha256':profile['exe_sha256'],'units':spec['units'],'axioms':result.stdout.splitlines(),
            'run1_table':{'hex':table.hex(),'sha256':hashlib.sha256(table).hexdigest()},
            'scope':'Animation suffix and the RUN1 state-setting CALL/RET, under a suffix-entry relation. Not yet connected to the preceding motion proof; excludes P_MovePlayer wrapper and other state-setter paths.',
            'cross_check':cross_check(raw,table,spec) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: original animation selection and walking-state call match the runtime helper.')
    if report['cross_check']:print('Independent x86 comparisons:',report['cross_check']['cases'])

if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as e:
        print(e.stdout or '',file=sys.stderr);print(e.stderr or '',file=sys.stderr);raise
