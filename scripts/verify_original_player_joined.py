#!/usr/bin/env python3
"""Certify continuous DOS motion and animation from one pre-turn relation."""
import argparse
import json
import random
import re
import struct
import subprocess
import sys
import verify_original_mul as original
import verify_original_inline_thrust as extraction
import verify_original_thrust as thrust
import verify_original_player_animation as animation

ROOT, require = original.ROOT, original.require
NAMES = ['caller_checked','callee_checked','execution_checked','observation_checked',
         'Doom.Proofs.PlayerJoined.establishes_animation',
         'Doom.Proofs.PlayerJoined.final_motion_fields',
         'Doom.Proofs.motion_full_run','Doom.Proofs.motion_end_pointers',
         'Doom.Verification.X86Routine.lift_control_prefix']


def certificate(raw,digest):
    lit=lambda key:'['+', '.join(hex(b) for b in raw[key])+']'
    audits='\n'.join('#print axioms '+n for n in NAMES)
    return f'''-- Original DOOM.EXE SHA-256 {digest}.
import Doom.Proofs.OriginalPlayerJoined
set_option maxRecDepth 32768
namespace Doom.Verification.ExtractedPlayerJoined
open X86Memory X86Control Doom.Proofs Doom.Proofs.PlayerJoined
def callerCode : List UInt8 := {lit('playerJoinedBytes')}
def calleeCode : List UInt8 := {lit('setMobjStateBytes')}
theorem caller_checked : callerCode = callerBytes := by decide
theorem callee_checked : calleeCode = Doom19.setMobjStateBytes := by decide
theorem execution_checked (s : X86Memory.State) (flags : Option Flags)
    (b : Doom.Motion) (a : Doom.PlayerAnim.State) (c : Doom.Ticcmd) (h : Inputs s b a c) :
    X86Routine.run (bytesProgram callerCode calleeCode) [0x3325e] 102 ⟨s,flags,0x33169⟩ =
      some (PlayerAnimation.result (motionEnd s b c).core) := by
  rw [caller_checked,callee_checked]
  exact joined_execution s flags b a c h
theorem observation_checked (s : X86Memory.State) (flags : Option Flags)
    (b : Doom.Motion) (a : Doom.PlayerAnim.State) (c : Doom.Ticcmd) (h : Inputs s b a c) :
    (X86Routine.run (bytesProgram callerCode calleeCode) [0x3325e] 102 ⟨s,flags,0x33169⟩).map (fun t =>
      (t.pc,(load32 t.core.memory (entryAngleAddress s),load32 t.core.memory (entryObject s+(72#32)),
        load32 t.core.memory (entryObject s+(76#32))),load32 t.core.memory (entryObject s+(100#32)),
        load32 t.core.memory (entryObject s+(96#32)),t.core.regs 4)) =
      some (0x3325e,((b.movePlayer c).angle.raw.toBitVec,(b.movePlayer c).momx.raw.toBitVec,
        (b.movePlayer c).momy.raw.toBitVec),PlayerAnimation.statePointer (a.startWalking c).frame,
        (a.startWalking c).tics.toBitVec,s.regs 4) := by
  rw [caller_checked,callee_checked]
  exact joined_observation s flags b a c h
{audits}
end Doom.Verification.ExtractedPlayerJoined
'''


def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedPlayerJoined.'+short
        match=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing axiom audit: '+name)
        axioms={a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Classical.choice','Quot.sound'},'unexpected proof axioms: '+str(axioms))
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')


def cross_check(raw,sine_table,run_table,spec,*,whole_function=False,caller_context=False,reaction_context=False):
    require(not reaction_context or caller_context,'reaction context requires caller context')
    require(not caller_context or whole_function,'caller context requires the complete function')
    import capstone
    import unicorn as uc
    from unicorn import x86_const as x
    rng=random.Random(0x331693325e)
    signed=lambda v:v if v<2**31 else v-2**32
    signed16=lambda v:v if v<32768 else v-65536
    signed8=lambda v:v if v<128 else v-256
    edges=[0,1,0xffffffff,0x7fffffff,0x80000000,0x80000001,0x7ffffffe]
    def case(turn,z,floor,f,c,frame):
        return (rng.getrandbits(32),turn,z,floor,f,c,rng.getrandbits(32),rng.getrandbits(32),frame,rng.getrandbits(32))
    cases=[case(t,rng.choice(edges),rng.choice(edges),rng.randrange(256),rng.randrange(256),rng.choice([149,150,156,157,65535])) for t in range(65536)]
    cases += [case(rng.randrange(65536),0,0,f,c,state) for state in [149,150] for f in range(256) for c in range(256)]
    cases += [case(rng.randrange(65536),1,0,f,c,state) for state in [149,150] for f in [0,1,127,128,255] for c in range(256)]
    timers=[0]*len(cases)
    if reaction_context:
        extra=[case(rng.randrange(65536),rng.choice(edges),rng.choice(edges),f,c,rng.choice([149,150,156,65535])) for f in range(256) for c in range(256)]
        cases+=extra
        timer_edges=[1,2,3,18,0x7fffffff,0x80000000,0xfffffffe,0xffffffff]
        timers += [timer_edges[i%8] if i%2 else (rng.getrandbits(32) or 1) for i in range(len(extra))]
        # Guarantee the signed boundary and timer-one cases, independent of RNG.
        timers[-8:]=timer_edges
    requests=[]
    for (a,t,z,fl,f,c,mx,my,state,tics),timer in zip(cases,timers):
        prefix=f'player-reaction {signed(timer)}' if reaction_context else 'player-step'
        requests.append(f'{prefix} {signed(a)} {signed16(t)} {signed(z)} {signed(fl)} {signed8(f)} {signed8(c)} {signed(mx)} {signed(my)} {state} {signed(tics)}')
    answers=[tuple(map(int,line.split())) for line in thrust.probe(requests)]
    md=capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32)
    listing={name:list(md.disasm(code,int(spec['units'][name]['code_offset'],16))) for name,code in raw.items()}
    for name,insts in listing.items():require(b''.join(bytes(i.bytes) for i in insts)==raw[name],'independent decode mismatch')
    unit_name='playerFunctionBytes' if whole_function else 'playerJoinedBytes'
    require(len(listing[unit_name])==(93 if whole_function else 78),'wrong contiguous instruction count')
    if caller_context:require(len(listing['playerReactionBytes' if reaction_context else 'playerCallerBytes'])==(10 if reaction_context else 3),'wrong caller instruction count')
    em=uc.Uc(uc.UC_ARCH_X86,uc.UC_MODE_32);CODE,DATA=0x100000,0x800000
    em.mem_map(CODE,0x40000);em.mem_map(DATA,0x1000)
    for base in [0,0x400000]:
        em.mem_map(base,0x2d000);em.mem_write(base+0x5a84,sine_table)
        em.mem_write(base+0x13584,struct.pack('<I',base+0x7a84));em.mem_write(base+0x16a90,run_table)
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
          x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];visited=[]
    em.hook_add(uc.UC_HOOK_MEM_WRITE,lambda _e,_a,addr,size,_v,_u:writes.append((addr,size)))
    def observe(machine,addr,size,user):
        visited.append(addr-CODE)
        if addr==CODE+exit_pc:machine.emu_stop()
    em.hook_add(uc.UC_HOOK_CODE,observe)
    sines=struct.unpack('<10240i',sine_table)
    paths={'forward_taken':0,'side_taken':0,'walk_call':0,'idle_skip':0,'already_animating_skip':0,'airborne_walk_call':0}
    if reaction_context:paths['reaction_skip']=0
    for i,((angle,turn,z,floor,f,c,mx,my,state,tics),answer) in enumerate(zip(cases,answers)):
        newangle,newmx,newmy,newstate,newtics=answer[:5]
        timer=timers[i]
        base=[0,0x400000][i%2];global_addr=base+0x2cf90
        for name,code in raw.items():
            unit=spec['units'][name];patched=bytearray(code)
            for r in unit['relocations']:struct.pack_into('<I',patched,r['offset'],base+int(r['target'],16))
            em.mem_write(CODE+int(unit['code_offset'],16),bytes(patched))
        em.ctl_remove_cache(CODE,CODE+0x40000)
        player,obj,sp=DATA+32+i%4,DATA+256+(i//4)%4,DATA+768+(i//16)%4
        caller_sp=sp
        entry_sp=caller_sp-4 if caller_context else caller_sp
        if whole_function:sp=entry_sp-28
        exit_pc=0x333cb if caller_context else 0x34000+(i%16)*4 if whole_function else 0x3325e
        # A valid one-byte landing pad prevents the JIT translating zero-filled
        # memory past the mapped page before the stop hook can run.
        if whole_function:em.mem_write(CODE+exit_pc,b'\xf4')
        em.mem_write(DATA,bytes([0xa5])*4096)
        em.mem_write(player,struct.pack('<I',obj));em.mem_write(player+8,bytes([f,c])+struct.pack('<H',turn))
        em.mem_write(obj+20,struct.pack('<I',z));em.mem_write(obj+32,struct.pack('<I',angle));em.mem_write(obj+56,struct.pack('<I',floor))
        em.mem_write(obj+72,struct.pack('<II',mx,my));old_ground=rng.getrandbits(32);em.mem_write(global_addr,struct.pack('<I',old_ground))
        em.mem_write(obj+36,struct.pack('<II',rng.getrandbits(32),rng.getrandbits(32)))
        em.mem_write(obj+96,struct.pack('<II',tics,base+0x15a28+28*state))
        if reaction_context:em.mem_write(obj+124,struct.pack('<I',timer))
        if whole_function and not caller_context:em.mem_write(entry_sp,struct.pack('<I',CODE+exit_pc))
        expected=bytearray(em.mem_read(DATA,4096));rs=[rng.getrandbits(32) for _ in regs];rs[0],rs[4]=player,entry_sp
        if caller_context:rs[0],rs[2],rs[4]=rng.getrandbits(32),player,caller_sp
        entry_rs=rs.copy()
        for reg,value in zip(regs,rs):em.reg_write(reg,value)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5))
        writes.clear();visited.clear()
        try:em.emu_start(CODE+(0x333b1 if reaction_context else 0x333c2 if caller_context else 0x33160 if whole_function else 0x33169),0,count=125 if reaction_context else 121 if caller_context else 118 if whole_function else 103)
        except uc.UcError as error:
            raise ValueError(f'x86 case {i}: {error}; last PCs {visited[-12:]}; ESP {em.reg_read(x.UC_X86_REG_ESP):#x}; EIP {em.reg_read(x.UC_X86_REG_EIP):#x}') from error
        if reaction_context and timer:
            paths['reaction_skip']+=1
            newtimer=(timer-1)&0xffffffff
            require(answer==(angle,signed(mx),signed(my),state,signed(tics),signed(newtimer)),f'compiled reaction gate mismatch {i}')
            struct.pack_into('<I',expected,obj+124-DATA,newtimer)
            rs[0],rs[6],rs[7]=player,timer,newtimer
            require(em.reg_read(x.UC_X86_REG_EIP)==CODE+exit_pc,f'reaction exit mismatch {i}')
            require([em.reg_read(r) for r in regs]==rs,f'reaction register mismatch {i}')
            require(em.mem_read(DATA,4096)==expected,f'reaction memory mismatch {i}')
            require(struct.unpack('<I',em.mem_read(global_addr,4))[0]==old_ground,'reaction changed cached ground')
            require(writes==[(obj+124,4)],'reaction skip wrote beyond timer')
            require(0x333c4 not in visited and 0x30ea0 not in visited,'reaction skip called movement or animation')
            flags=em.reg_read(x.UC_X86_REG_EFLAGS)
            require(((flags>>6)&1,(flags>>7)&1,(flags>>11)&1)==(0,timer>>31,0),'reaction flags mismatch')
            continue
        if reaction_context:
            require(answer[5]==0,'zero reaction timer changed')
            rs[6]=0;entry_rs[6]=0
        ground=int(signed(z)<=signed(floor));forward=bool(ground and f);side=bool(ground and c)
        take=bool(state==149 and (f or c))
        paths['forward_taken']+=forward;paths['side_taken']+=side
        paths['walk_call' if take else 'idle_skip' if not(f or c) else 'already_animating_skip']+=1
        paths['airborne_walk_call']+=bool(take and not ground)
        expected_writes=[]
        if caller_context:
            struct.pack_into('<I',expected,entry_sp-DATA,CODE+0x333c9)
            expected_writes.append((entry_sp,4))
        if whole_function:
            for slot,reg in enumerate([3,1,2,6,7,5],1):
                addr=entry_sp-slot*4
                struct.pack_into('<I',expected,addr-DATA,entry_rs[reg]);expected_writes.append((addr,4))
            rs[4]=sp
        expected_writes += [(obj+32,4),(global_addr,4)]
        struct.pack_into('<I',expected,obj+32-DATA,newangle)
        struct.pack_into('<II',expected,obj+72-DATA,newmx&0xffffffff,newmy&0xffffffff)
        rs[0],rs[1],rs[2],rs[3],rs[6]=ground,player,(rs[2]&0xffffff00)|f,z,player+8
        if forward:
            index=newangle>>19;struct.pack_into('<I',expected,sp-DATA,index*4)
            product=signed8(f)*2048*sines[index]
            rs[0],rs[2],rs[3],rs[5],rs[7]=(product>>16)&0xffffffff,(product>>32)&0xffffffff,sines[index]&0xffffffff,obj,(signed8(f)*2048)&0xffffffff
            expected_writes += [(sp,4),(obj+72,4),(obj+76,4)]
        rs[2]=(rs[2]&0xffff00ff)|(c<<8)
        if side:
            index=((newangle-0x40000000)&0xffffffff)>>19;struct.pack_into('<I',expected,sp-DATA,index*4)
            product=signed8(c)*2048*sines[index]
            rs[0],rs[2],rs[3],rs[5],rs[7]=(product>>16)&0xffffffff,(product>>32)&0xffffffff,sines[index]&0xffffffff,obj,(signed8(c)*2048)&0xffffffff
            expected_writes += [(sp,4),(obj+72,4),(obj+76,4)]
        if take:
            struct.pack_into('<III',expected,sp-12-DATA,rs[6],rs[3],CODE+0x3325e)
            struct.pack_into('<II',expected,obj+36-DATA,28,0)
            struct.pack_into('<II',expected,obj+96-DATA,newtics&0xffffffff,base+0x15a28+28*newstate)
            expected_writes += [(sp-4,4),(sp-8,4),(sp-12,4),(obj+100,4),(obj+96,4),(obj+36,4),(obj+40,4)]
            rs[0],rs[2]=1,151;expected_flags=(0,0,0)
            require(0x30ea0 in visited and 0x30efa in visited,'call or return was not executed')
        elif f or c:
            rs[0]=obj;a=base+0x15a28+28*state;b=base+0x16a74;diff=(a-b)&0xffffffff
            expected_flags=(int(diff==0),diff>>31,int(bool(((a^b)&(a^diff))&0x80000000)))
        else:expected_flags=(1,0,0)
        require(newstate==(150 if take else state) and newtics==(4 if take else signed(tics)),'compiled animation mismatch')
        if whole_function:
            for reg in [3,1,2,6,7,5]:rs[reg]=entry_rs[reg]
            rs[4]=entry_sp+4
            # ADD ESP,4 in the epilogue is the last flag-changing instruction.
            a=sp;b=4;value=(a+b)&0xffffffff
            expected_flags=(int(value==0),value>>31,int(bool((~(a^b)&(a^value))&0x80000000)))
            if caller_context:
                rs[0]=player
                require(0x333c4 in visited and 0x33267 in visited and visited[-2]==0x333c9,'outer call/return/resume was not executed')
            else:require(visited[-2]==0x33267,'function RET was not executed')
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+exit_pc,f'exit mismatch {i}')
        require([em.reg_read(r) for r in regs]==rs,f'register restoration mismatch {i}')
        require(em.mem_read(DATA,4096)==expected,f'motion/animation/stack memory mismatch {i}')
        require(struct.unpack('<I',em.mem_read(global_addr,4))[0]==ground,'cached ground mismatch')
        require(writes==expected_writes,f'store order mismatch {i}')
        flags=em.reg_read(x.UC_X86_REG_EFLAGS)
        require(((flags>>6)&1,(flags>>7)&1,(flags>>11)&1)==expected_flags,f'flag mismatch {i}')
    return {'cases':len(cases),'whole_function':whole_function,'caller_context':caller_context,'reaction_context':reaction_context,'paths':paths,'all_command_pairs_standing_and_running':True,'all_signed16_turn_encodings':True,
            'reference':('compiled PlayerReaction.move, animate and remaining, same old timer and unchanged command' if reaction_context else 'compiled Motion.movePlayer and PlayerAnim.State.startWalking, same unchanged command'),
            'code_base':CODE,'data_bases':[0,0x400000],'unaligned_addresses':True,
            'checks':['angle','both momenta','state pointer','tics','sprite/display frame','full dynamic memory page','all registers','stack restoration','call/return','write order','ZF/SF/OF','cached ground']+(['reaction timer','no CALL on nonzero timer'] if reaction_context else []),
            'disassembly':{name:[f'{i.address:#x}: {i.mnemonic} {i.op_str}' for i in insts] for name,insts in listing.items()}}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-player-joined.json').read_text())
    profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec);run_table=animation.table_data(binary,profile,spec)
    _,sine_table=thrust.extract(binary,profile,json.loads((ROOT/'tests/reference/original-thrust.json').read_text()))
    out=ROOT/'artifacts/original-player-joined';out.mkdir(parents=True,exist_ok=True)
    source=out/'Extracted.lean';source.write_text(certificate(raw,profile['exe_sha256']))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalPlayerJoined','fidelity-probe'],cwd=ROOT,check=True)
    result=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(result.stdout);print(result.stdout,end='',flush=True)
    report={'exe_sha256':profile['exe_sha256'],'units':spec['units'],'axioms':result.stdout.splitlines(),
            'sine_table':thrust.check_tables(sine_table),'run1_table':run_table.hex(),
            'scope':'One pre-turn relation; continuous motion and animation including real walking CALL/RET. Excludes P_MovePlayer prologue/epilogue, caller invariant establishment, collision and full tic.',
            'cross_check':cross_check(raw,sine_table,run_table,spec) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: motion and animation joined under one initial-state relation.')
    if report['cross_check']:print('Independent continuous x86 comparisons:',report['cross_check']['cases'])

if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as e:
        print(e.stdout or '',file=sys.stderr);print(e.stderr or '',file=sys.stderr);raise
