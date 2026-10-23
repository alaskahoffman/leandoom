#!/usr/bin/env python3
"""Certify the continuous forward-thrust/side-guard slice and both entry paths."""
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
NAMES = ['bytes_checked', 'forward_checked', 'skip_checked',
         'Doom.Proofs.original_forward_side', 'Doom.Proofs.forward_establishes_side_inputs',
         'Doom.Proofs.forward_end_pointers', 'Doom.Verification.X86Control.linear_prefix',
         'Doom.Verification.X86Control.linear_state']


def certificate(raw, digest):
    literal = '['+', '.join(hex(b) for b in raw)+']'
    audits = '\n'.join('#print axioms '+n for n in NAMES)
    return f'''-- Contiguous DOOM.EXE slice, SHA-256 {digest}; data-object-relative addresses.
import Doom.Proofs.OriginalForwardSide
namespace Doom.Verification.ExtractedForwardSide
open X86Memory X86Control Doom.Proofs
def code : List UInt8 := {literal}
theorem bytes_checked : code = forwardSideBytes := by decide
theorem forward_checked (s : X86Memory.State) (flags : Option Flags) (body : Motion)
    (cmd : Ticcmd) (h : ForwardSideInputs s body cmd) :
    (X86Control.run code [88,165] 28 ⟨s,flags,0⟩).map (fun t => (t.pc,t.core.memory)) =
      some (if body.onGround ∧ cmd.sideMove ≠ 0 then 88 else 165,
        inlineThrustResult s body false cmd.forwardMove) := by
  rw [bytes_checked]
  exact forward_side_matches_engine s flags body cmd h
theorem skip_checked (s : X86Memory.State) (flags : Option Flags) (body : Motion) (cmd : Ticcmd)
    (hg : load32 s.memory 0x2cf90 = if body.onGround then 1 else 0)
    (hc : s.memory (s.regs 6 + (1#32)) = cmd.sideMove.toBitVec) :
    (X86Control.run code [88,165] 5 ⟨s,flags,72⟩).map (fun t => (t.pc,t.core.memory)) =
      some (if body.onGround ∧ cmd.sideMove ≠ 0 then 88 else 165, s.memory) := by
  rw [bytes_checked]
  exact skip_forward_side_matches_engine s flags body cmd hg hc
{audits}
end Doom.Verification.ExtractedForwardSide
'''


def audit(output):
    rest = output.strip()
    for short in NAMES:
        name = short if '.' in short else 'Doom.Verification.ExtractedForwardSide.'+short
        match = re.match(re.escape(f"'{name}'")+
                         r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing axiom audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected proof axioms')
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


def cross_check(raw, table, spec):
    import capstone
    import unicorn as uc
    from unicorn import x86_const as x
    rng = random.Random(0x331e1)
    signed = lambda v: v if v < 2**31 else v-2**32
    signed8 = lambda v: v if v < 128 else v-256
    # All command pairs after taking forward, plus independent skip paths and angles.
    cases = [(True,rng.getrandbits(32),f,c,1,rng.getrandbits(32),rng.getrandbits(32))
             for f in range(1,256) for c in range(256)]
    cases += [(True,index<<19,1+(index%255),index%256,1,rng.getrandbits(32),rng.getrandbits(32))
              for index in range(8192)]
    cases += [(False,rng.getrandbits(32),0,c,g,rng.getrandbits(32),rng.getrandbits(32))
              for g in [0,1] for c in range(256)]
    forward_answers = iter(thrust.probe([f'thrust {signed(a)} {signed8(f)*2048} {signed(mx)} {signed(my)}'
                                       for take,a,f,c,g,mx,my in cases if take]))
    guard_answers = iter(tuple(map(int,line.split())) for line in thrust.probe(
        [f'move-guards {0 if g else 1} 0 0 {signed8(c)}' for take,a,f,c,g,mx,my in cases]))
    listing = list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(raw,0x33199))
    require(len(listing)==28 and b''.join(bytes(i.bytes) for i in listing)==raw,'independent decode mismatch')
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
        if addr in [CODE+88,CODE+165]:machine.emu_stop()
    em.hook_add(uc.UC_HOOK_CODE,stop)
    sines=struct.unpack('<10240i',table)
    for i,(take,angle,forward,side,ground,mx,my) in enumerate(cases):
        base=[0,0x200000][i%2];global_addr=base+0x2cf90
        code=bytearray(raw)
        for r in spec['relocations']:struct.pack_into('<I',code,r['offset'],base+int(r['target'],16))
        em.mem_write(CODE,b'\xcc'*4096);em.mem_write(CODE,bytes(code));em.ctl_remove_cache(CODE,CODE+4096)
        player,obj,stack=DATA+32+i%4,DATA+256+(i//4)%4,DATA+512+(i//16)%4
        em.mem_write(player,struct.pack('<I',obj));em.mem_write(player+8,bytes([forward,side]))
        em.mem_write(obj+32,struct.pack('<I',angle));em.mem_write(obj+72,struct.pack('<II',mx,my))
        em.mem_write(global_addr,struct.pack('<I',ground))
        before=bytearray(em.mem_read(DATA,4096))
        rs=[rng.getrandbits(32) for _ in registers];rs[1],rs[4],rs[6]=player,stack,player+8
        rs[2]=(rs[2]&0xffffff00)|forward
        for r,v in zip(registers,rs):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5))
        writes.clear();em.emu_start(CODE+(0 if take else 72),0,count=29)
        _,_,side_taken=next(guard_answers)
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+(88 if side_taken else 165),'side branch mismatch')
        if take:
            expected=tuple(int(v)&0xffffffff for v in next(forward_answers).split())
            struct.pack_into('<II',before,obj+72-DATA,*expected)
            index=angle>>19;struct.pack_into('<I',before,stack-DATA,index*4)
            product=signed8(forward)*2048*sines[index]
            rs[0],rs[2],rs[3],rs[5],rs[7]=(product>>16)&0xffffffff,(product>>32)&0xffffffff,sines[index]&0xffffffff,obj,(signed8(forward)*2048)&0xffffffff
        rs[2]=(rs[2]&0xffff00ff)|(side<<8)
        require([em.reg_read(r) for r in registers]==rs,'register seam mismatch')
        require(em.mem_read(DATA,4096)==before,'memory mismatch')
        require(struct.unpack('<I',em.mem_read(global_addr,4))[0]==ground,'cached ground corrupted')
        require(writes==([(stack,4),(obj+72,4),(obj+76,4)] if take else []),'write order mismatch')
        flags=em.reg_read(x.UC_X86_REG_EFLAGS)
        require(((flags>>6)&1,(flags>>7)&1,(flags>>11)&1)==(int(not side or not ground),0,0),'flags mismatch')
    return {'cases':len(cases),'forward_cases':sum(c[0] for c in cases),'skip_cases':sum(not c[0] for c in cases),
            'all_nonzero_forward_by_side_command_pairs':True,'all_fine_angle_bins':8192,'relocation_bases':[0,0x200000],
            'checked':['continuous exit','engine momentum','all registers','ZF/SF/OF','memory page','cached ground','write order'],
            'disassembly':[f'{i.address:#x}: {i.mnemonic} {i.op_str}' for i in listing]}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-forward-side.json').read_text())
    profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text())
    sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec)['forwardSideBytes']
    _,table=thrust.extract(binary,profile,json.loads((ROOT/'tests/reference/original-thrust.json').read_text()))
    out=ROOT/'artifacts/original-forward-side';out.mkdir(parents=True,exist_ok=True)
    source=out/'Extracted.lean';source.write_text(certificate(raw,profile['exe_sha256']))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalForwardSide','fidelity-probe'],cwd=ROOT,check=True)
    result=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(result.stdout);print(result.stdout,end='',flush=True)
    report={'exe_sha256':profile['exe_sha256'],'unit':spec['units']['forwardSideBytes'],'axioms':result.stdout.splitlines(),
            'tables':thrust.check_tables(table),
            'scope':'Forward thrust through side guard, and skip-forward entry. Entry memory assumptions explicit; preceding turn/guard relation and subsequent side thrust not joined.',
            'cross_check':cross_check(raw,table,spec['units']['forwardSideBytes']) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: continuous forward-thrust/side-guard correspondence for related entry states.')
    if report['cross_check']:print('Independent x86 comparisons:',report['cross_check']['cases'])


if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as e:
        print(e.stdout or '',file=sys.stderr);print(e.stderr or '',file=sys.stderr);raise
