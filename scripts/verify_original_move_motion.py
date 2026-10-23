#!/usr/bin/env python3
"""Check the original complete angle-and-momentum proof with one initial relation."""
import argparse
import json
import random
import re
import struct
import subprocess
import sys
import verify_original_inline_thrust as extraction
import verify_original_mul as original
import verify_original_thrust as thrust

ROOT, require = original.ROOT, original.require
NAMES = ['bytes_checked','engine_checked','observation_checked','Doom.Proofs.side_guard_full',
         'Doom.Proofs.motion_establishes_side','Doom.Proofs.joined_tables',
         'Doom.Proofs.completeMotion_engine_projection',
         'Doom.Proofs.entry_establishes_forward_side','Doom.Proofs.entry_tables',
         'Doom.Proofs.table_separation','Doom.Verification.X86Control.runProgram_path',
         'Doom.Verification.X86Control.Prefix.transfer','Doom.Verification.X86Control.Prefix.finish_map']


def certificate(raw,digest):
    literal='['+', '.join(hex(b) for b in raw)+']'
    audits='\n'.join('#print axioms '+n for n in NAMES)
    return f'''-- Contiguous original DOOM.EXE slice, SHA-256 {digest}.
import Doom.Proofs.OriginalMoveMotion
set_option maxRecDepth 4096
namespace Doom.Verification.ExtractedMoveMotion
open X86Memory X86Control Doom.Proofs
def code : List UInt8 := {literal}
theorem bytes_checked : code = moveMotionBytes := by decide
theorem engine_checked (s : X86Memory.State) (flags : Option Flags) (body : Motion)
    (cmd : Ticcmd) (h : MoveMotionInputs s body cmd) :
    (X86Control.run code [213] 69 ⟨s,flags,0⟩).map (fun t => (t.pc,t.core.memory)) =
      some (213, moveMotionResultMemory s body cmd) := by
  rw [bytes_checked]
  exact move_motion_matches_engine s flags body cmd h
theorem observation_checked (s : X86Memory.State) (flags : Option Flags) (body : Motion)
    (cmd : Ticcmd) (h : MoveMotionInputs s body cmd) :
    (X86Control.run code [213] 69 ⟨s,flags,0⟩).map (fun t =>
      (t.pc,load32 t.core.memory (entryAngleAddress s),
        load32 t.core.memory (entryObject s + (72#32)),
        load32 t.core.memory (entryObject s + (76#32)))) =
      some (213,
        (body.movePlayer cmd).angle.raw.toBitVec,
        (body.movePlayer cmd).momx.raw.toBitVec,
        (body.movePlayer cmd).momy.raw.toBitVec) := by
  rw [bytes_checked]
  exact move_motion_player_observation s flags body cmd h
{audits}
end Doom.Verification.ExtractedMoveMotion
'''


def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedMoveMotion.'+short
        match=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing axiom audit: '+name)
        axioms={a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext','Quot.sound','Classical.choice'},'unexpected proof axioms: '+str(axioms))
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')


def cross_check(raw,table,spec):
    import capstone
    import unicorn as uc
    from unicorn import x86_const as x
    rng=random.Random(0x33169136)
    signed=lambda v:v if v<2**31 else v-2**32
    signed16=lambda v:v if v<32768 else v-65536
    signed8=lambda v:v if v<128 else v-256
    edges=[0,1,0xffffffff,0x7fffffff,0x80000000,0x80000001,0x7ffffffe]
    cases=[(rng.getrandbits(32),t,rng.choice(edges),rng.choice(edges),rng.randrange(256),rng.randrange(256),rng.getrandbits(32),rng.getrandbits(32)) for t in range(65536)]
    cases += [(rng.getrandbits(32),rng.randrange(65536),0,0,f,c,rng.getrandbits(32),rng.getrandbits(32)) for f in range(256) for c in range(256)]
    cases += [(rng.getrandbits(32),rng.randrange(65536),1,0,f,c,rng.getrandbits(32),rng.getrandbits(32)) for f in [0,1,127,128,255] for c in range(256)]
    answers=[tuple(map(int,line.split())) for line in thrust.probe([
        f'move-player {signed(a)} {signed16(t)} {signed(z)} {signed(fl)} {signed8(f)} {signed8(c)} {signed(mx)} {signed(my)}'
        for a,t,z,fl,f,c,mx,my in cases])]
    listing=list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(raw,0x33169))
    require(len(listing)==69 and b''.join(bytes(i.bytes) for i in listing)==raw,'independent decode mismatch')
    em=uc.Uc(uc.UC_ARCH_X86,uc.UC_MODE_32);CODE,DATA=0x100000,0x400000
    em.mem_map(CODE,4096);em.mem_map(DATA,4096)
    for base in [0,0x200000]:
        em.mem_map(base,0x2d000);em.mem_write(base+0x5a84,table)
        em.mem_write(base+0x13584,struct.pack('<I',base+0x7a84))
    registers=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
               x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[]
    em.hook_add(uc.UC_HOOK_MEM_WRITE,lambda _e,_a,addr,size,_v,_u:writes.append((addr,size)))
    def stop(machine,addr,size,user):
        if addr == CODE+213:machine.emu_stop()
    em.hook_add(uc.UC_HOOK_CODE,stop)
    sines=struct.unpack('<10240i',table);paths={'forward_taken':0,'forward_skipped':0,'side_taken':0,'side_skipped':0}
    for i,((angle,turn,z,floor,forward,side,mx,my),(newangle,newmx,newmy)) in enumerate(zip(cases,answers)):
        base=[0,0x200000][i%2];global_addr=base+0x2cf90
        code=bytearray(raw)
        for r in spec['relocations']:struct.pack_into('<I',code,r['offset'],base+int(r['target'],16))
        em.mem_write(CODE,b'\xcc'*4096);em.mem_write(CODE,bytes(code));em.ctl_remove_cache(CODE,CODE+4096)
        player,obj,stack=DATA+32+i%4,DATA+256+(i//4)%4,DATA+512+(i//16)%4
        em.mem_write(player,struct.pack('<I',obj));em.mem_write(player+8,bytes([forward,side])+struct.pack('<H',turn))
        em.mem_write(obj+20,struct.pack('<I',z));em.mem_write(obj+32,struct.pack('<I',angle));em.mem_write(obj+56,struct.pack('<I',floor))
        em.mem_write(obj+72,struct.pack('<II',mx,my));em.mem_write(global_addr,struct.pack('<I',rng.getrandbits(32)))
        before=bytearray(em.mem_read(DATA,4096));rs=[rng.getrandbits(32) for _ in registers];rs[0],rs[4]=player,stack
        for r,v in zip(registers,rs):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5))
        writes.clear();em.emu_start(CODE,0,count=70)
        ground=int(signed(z)<=signed(floor));take=bool(ground and forward);side_taken=bool(ground and side)
        paths['forward_taken' if take else 'forward_skipped']+=1;paths['side_taken' if side_taken else 'side_skipped']+=1
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+213,f'animation entry mismatch case {i}')
        struct.pack_into('<I',before,obj+32-DATA,newangle)
        struct.pack_into('<II',before,obj+72-DATA,newmx&0xffffffff,newmy&0xffffffff)
        rs[0],rs[1],rs[2],rs[3],rs[6]=ground,player,(rs[2]&0xffffff00)|forward,z,player+8
        if take:
            index=newangle>>19;struct.pack_into('<I',before,stack-DATA,index*4)
            product=signed8(forward)*2048*sines[index]
            rs[0],rs[2],rs[3],rs[5],rs[7]=(product>>16)&0xffffffff,(product>>32)&0xffffffff,sines[index]&0xffffffff,obj,(signed8(forward)*2048)&0xffffffff
        rs[2]=(rs[2]&0xffff00ff)|(side<<8)
        if side_taken:
            index=((newangle-0x40000000)&0xffffffff)>>19
            struct.pack_into('<I',before,stack-DATA,index*4)
            product=signed8(side)*2048*sines[index]
            rs[0],rs[2],rs[3],rs[5],rs[7]=(product>>16)&0xffffffff,(product>>32)&0xffffffff,sines[index]&0xffffffff,obj,(signed8(side)*2048)&0xffffffff
        require([em.reg_read(r) for r in registers]==rs,'register mismatch')
        require(em.mem_read(DATA,4096)==before,'angle/momentum/memory mismatch')
        require(struct.unpack('<I',em.mem_read(global_addr,4))[0]==ground,'cached ground mismatch')
        expected_writes=[(obj+32,4),(global_addr,4)]+([(stack,4),(obj+72,4),(obj+76,4)] if take else [])+([(stack,4),(obj+72,4),(obj+76,4)] if side_taken else [])
        require(writes==expected_writes,'write ordering mismatch')
        flags=em.reg_read(x.UC_X86_REG_EFLAGS)
        expected_flags=(int(not side or not ground),0,0)
        if side_taken:
            result=newmy&0xffffffff;delta=rs[0];prior=(result-delta)&0xffffffff
            expected_flags=(int(result==0),result>>31,int(bool((~(prior^delta)&(prior^result))&0x80000000)))
        require(((flags>>6)&1,(flags>>7)&1,(flags>>11)&1)==expected_flags,'flag mismatch')
    return {'cases':len(cases),'paths':paths,'all_signed16_turn_encodings':True,'all_forward_side_command_pairs':True,
            'signed_height_extremes':True,'relocation_bases':[0,0x200000],'unaligned_objects_and_stack':True,
            'reference':'compiled Motion.movePlayer with both commands unchanged',
            'checked':['continuous exit','turned angle','combined forward and side momentum','full dynamic page','all registers','ZF/SF/OF','cached ground','write order'],
            'disassembly':[f'{i.address:#x}: {i.mnemonic} {i.op_str}' for i in listing]}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-move-motion.json').read_text())
    profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec)['moveMotionBytes']
    _,table=thrust.extract(binary,profile,json.loads((ROOT/'tests/reference/original-thrust.json').read_text()))
    out=ROOT/'artifacts/original-move-motion';out.mkdir(parents=True,exist_ok=True)
    source=out/'Extracted.lean';source.write_text(certificate(raw,profile['exe_sha256']))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalMoveMotion','fidelity-probe'],cwd=ROOT,check=True)
    result=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(result.stdout);print(result.stdout,end='',flush=True)
    report={'exe_sha256':profile['exe_sha256'],'unit':spec['units']['moveMotionBytes'],'axioms':result.stdout.splitlines(),
            'tables':thrust.check_tables(table),'scope':'One initial relation; continuous turn, both guards, optional forward and side thrust. Angle and both momenta equal actual Motion.movePlayer. Stops before animation, not whole player tic.',
            'cross_check':cross_check(raw,table,spec['units']['moveMotionBytes']) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: complete original motion region matches engine under one initial-state relation.')
    if report['cross_check']:print('Independent continuous x86 comparisons:',report['cross_check']['cases'])


if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as e:
        print(e.stdout or '',file=sys.stderr);print(e.stderr or '',file=sys.stderr);raise
