#!/usr/bin/env python3
"""Certify original callback resumption and finite duplicate-list runs."""
import argparse
import json
import random
import re
import subprocess
import verify_original_inline_thrust as extraction
ROOT, require = extraction.ROOT, extraction.require
NAMES = ['finish_checked','cell_checked','lineEntry_checked','lineReturn_checked','execution_checked']
PROOFS = ['OriginalLineResume.'+n for n in ['contains_cell','contains_bounds','exit_execution','execution',
    'memory','continued','stopped','finish_cursor','finish_continue','skip_execution','skip_observe',
    'next_item','sentinel_execution','seen_at','duplicates_from_memory','skip_pc','through_sentinel','sentinel_observe']]
PROOFS += ['E1M1LineResume.'+n for n in ['contains_resume','continue_execution','line_resume_execution','duplicate_run','line_list_return_execution']]

def certificate(raw):
    source = """import Doom.Proofs.E1M1LineResume
set_option maxRecDepth 32768
namespace Doom.Verification.ExtractedLineResume
open Doom Doom.Proofs X86 X86Memory X86Control
"""
    for key,target in [('finish','OriginalLineFinish.code'),('cell','OriginalLineCell.code'),
                       ('lineEntry','OriginalLineBounds.lineEntry'),('lineReturn','OriginalLineBounds.lineReturn')]:
        source += 'def '+key+'Code : List UInt8 := ['+','.join(hex(b) for b in raw[key])+']\n'
        source += 'theorem '+key+'_checked : '+key+'Code='+target+' := by decide\n'
    source += """def extractedProgram (pc : Nat) :=
  match OriginalLineCell.bytesProgram cellCode pc with
  | some op => some op
  | none => OriginalLineBounds.bytesProgram lineEntryCode lineReturnCode pc
theorem execution_checked (s : X86Memory.State) (f : Option Flags) :
    ∃ n≤5, X86Routine.Prefix extractedProgram [] n ⟨s,f,0x2c578⟩ (OriginalLineResume.result s) := by
  have eq : extractedProgram=OriginalLineResume.program := by
    funext pc; simp only [extractedProgram,cell_checked,lineEntry_checked,lineReturn_checked]; rfl
  rw [eq]; exact OriginalLineResume.execution s f
"""
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedLineResume\n'


def audit(output):
    rest = output.strip()
    for name in ['Doom.Verification.ExtractedLineResume.' + n for n in NAMES] + ['Doom.Proofs.' + n for n in PROOFS]:
        match = re.match(re.escape(f"'{name}'") + r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing audit: ' + name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axioms')
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected output')


def extracted():
    spec = json.loads((ROOT / 'tests/reference/original-line-resume.json').read_text())
    profile = json.loads((ROOT / 'tests/reference' / spec['exe_profile']).read_text())
    sw = json.loads((ROOT / 'tests/reference/shareware.json').read_text())
    binary = extraction.original.extract(ROOT / sw['local_directory'] / 'doom19s.zip', sw, profile)
    return spec, profile, extraction.extract(binary, profile, spec)


def cross_check(raw):
    import capstone
    import unicorn as u
    from unicorn import x86_const as x
    CODE, HEAP, MASK = 0x100000, 0x600000, 0xffffffff
    em = u.Uc(u.UC_ARCH_X86, u.UC_MODE_32)
    em.mem_map(CODE, 0x50000)
    for name, start in [('finish',0x2c6bb),('cell',0x2c541),('lineReturn',0x2c587)]:
        code=raw[name]
        listing=list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(code,start))
        require(b''.join(bytes(i.bytes) for i in listing)==code,'decoder mismatch')
        em.mem_write(CODE+start,code)
    addresses=[0,0x13000,0x2c000,HEAP,0xfffff000]
    for a in addresses:em.mem_map(a,4096)
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
          x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    rng=random.Random(0x2c578);writes=[];visits=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _,access,a,size,value,data:writes.append((a&MASK,size,value&MASK)))
    em.hook_add(u.UC_HOOK_CODE,lambda _,a,size,data:visits.append(a-CODE))
    signed=lambda v:v if v<0x80000000 else v-0x100000000
    groups=dict(callback_continue=0,callback_stop=0,duplicate_runs=0,empty_list=0,
                leading_zero=0,negative_id=0,wrapped_list=0,wrapped_stack=0,record_alias=0)
    for i in range(2048):
        pages={a:bytearray(rng.randbytes(4096)) for a in addresses}
        def put(a,v,size=4):
            for k,b in enumerate((v&((1<<(8*size))-1)).to_bytes(size,'little')):
                q=(a+k)&MASK;pages[q&~4095][q&4095]=b
        def get(a,size=4):
            return sum(pages[((a+k)&MASK)&~4095][((a+k)&MASK)&4095]<<(8*k) for k in range(size))
        rr=[rng.getrandbits(32) for _ in regs]
        sp=[HEAP+128,HEAP+131,0xfffffe01,0xfffffff9][i%4]
        rr[4]=sp
        if i<1024:
            rr[0]=[0xffffffff,0x80000000,0,1,65535,65536,65537,0x7fffffff][i%8]
            rr[1]=HEAP+1025
            cur=[HEAP+2049,0xfffffff1,0x2c028,(sp+16)&MASK][(i//8)%4]
            put(0x2c024,0 if (i//32)%2==0 else 1);put(0x2c028,cur)
            put(rr[1]+50,0 if (i//64)%2==0 else HEAP+3000)
            put(sp+24,HEAP+769);put(sp+36,CODE+0x2c578)
            put(sp+48,CODE+0x4f000)
        else:
            n=(i-1024)%8;negative=(i//8)%2==1
            lp=0xfffffffd if (i//16)%2==1 else HEAP+769
            # Keep the wrapping list separate from the saved iterator frame.
            if sp==0xfffffff9:sp=rr[4]=0xfffffe01
            rr[2]=lp
            epoch=rng.getrandbits(32)
            base=HEAP+1024+(124 if negative else 0)
            put(0x13580,epoch);put(0x2c120,base)
            for j in range(n):
                ident=65534 if negative else j%4
                put(lp+2*j,ident,2)
                sid=ident if ident<32768 else ident-65536
                put(base+62*sid+54,epoch)
            put(lp+2*n,65535,2);put(sp+8,CODE+0x4f000)
        for a,page in pages.items():em.mem_write(a,bytes(page))
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,0x8c3 if i%3==0 else 2)
        wanted=rr.copy();expected=[]
        if i<1024:
            active=get(0x2c024)!=0;near=signed(rr[0])<65536;back=get(rr[1]+50)
            append=False
            if signed(rr[0])<0:count,answer=11,1
            elif not active:count,answer,append=19,1,True
            elif not near:count,answer,append=21,1,True
            elif back:count,answer,append=23,1,True
            else:count,answer=17,0
            if append:
                for a,v in [(cur+4,1),(cur,rr[0]),(cur+8,rr[1]),(0x2c028,cur+12)]:
                    expected.append((a&MASK,4,v&MASK));put(a,v)
                groups['record_alias']+=cur in [0x2c028,(sp+16)&MASK]
            wanted[0]=answer;wanted[4]=(sp+40)&MASK
            for off,r in [(16,5),(20,6),(24,2),(28,1),(32,3)]:wanted[r]=get(sp+off)
            if answer==0:
                wanted[7]=get(sp+44);wanted[4]=(sp+52)&MASK
                count+=5;stop=get(sp+48);groups['callback_stop']+=1
            else:
                wanted[2]=(wanted[2]+2)&MASK
                count+=3;stop=CODE+0x2c57f;groups['callback_continue']+=1
            start=0x2c6bb
        else:
            start=0x2c57f;count=10*n+7;stop=get(sp+8)
            wanted[0]=1;wanted[2]=(lp+2*n)&MASK;wanted[4]=(sp+12)&MASK;wanted[7]=get(sp+4)
            if n:wanted[3]=base
            groups['duplicate_runs']+=1;groups['empty_list']+=n==0
            groups['leading_zero']+=n>0 and not negative
            groups['negative_id']+=n>0 and negative
            groups['wrapped_list']+=lp==0xfffffffd
        groups['wrapped_stack']+=sp>=0xfffff000
        writes.clear();visits.clear()
        em.emu_start(CODE+start,0,count=count)
        require(em.reg_read(x.UC_X86_REG_EIP)==stop,f'case {i}: PC')
        require(len(visits)==count,f'case {i}: instruction count')
        require([em.reg_read(r) for r in regs]==wanted,f'case {i}: registers')
        require(writes==expected,f'case {i}: ordered writes')
        for a,page in pages.items():require(em.mem_read(a,4096)==page,f'case {i}: memory')
    require(all(groups.values()),'missing coverage')
    return {'total_cases':2048,'groups':groups,
            'checks':'All eight registers, mapped byte memory, exact instruction count, PC and ordered writes. Original callback suffix through actual iterator resumption; original duplicate-loop instructions through sentinel and RET. No helper stubs.',
            'scope':'Native finite samples supplement the universal kernel theorems. Flags are not compared. Fresh callbacks within repeated iteration are not covered.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cross-check', action='store_true')
    args = parser.parse_args()
    spec, profile, raw = extracted()
    out = ROOT / 'artifacts/original-line-resume'
    out.mkdir(parents=True, exist_ok=True)
    source = out / 'Extracted.lean'
    source.write_text(certificate(raw))
    subprocess.run([str(ROOT / 'scripts/lake'), 'build', 'Doom.Proofs.E1M1LineResume'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT / 'scripts/lake'), 'env', 'lean', str(source)], cwd=ROOT, capture_output=True, text=True, check=True)
    audit(checked.stdout)
    (out / 'axioms.log').write_text(checked.stdout)
    report = {'exe_sha256': profile['exe_sha256'], 'units': spec['units'], 'axioms': checked.stdout.splitlines(),
              'scope': 'Callback return and iterator resumption; arbitrary finite duplicate runs from initial stamped-memory conditions, and sentinel return. Fresh-line callback iteration and full traversal remain open.',
              'cross_check': cross_check(raw) if args.cross_check else None}
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print('PASS: original line iterator resumption; extracted bytes and strict axiom audit.')
    if args.cross_check:
        print('Native iterator cases:', report['cross_check']['total_cases'])


if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as error:
        print(error.stdout or '')
        print(error.stderr or '')
        raise
