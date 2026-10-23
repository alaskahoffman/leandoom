#!/usr/bin/env python3
"""Certify crossing-line arithmetic, insertion, preservation and iterator return."""
import argparse
import json
import random
import re
import subprocess
import verify_original_inline_thrust as extraction
ROOT, require = extraction.ROOT, extraction.require
NAMES = ['finish_checked', 'cell_checked', 'lineEntry_checked', 'lineReturn_checked', 'setup_checked', 'helper_checked', 'division_checked', 'execution_checked']
PROOFS = ['OriginalLineTail.setup_frame', 'OriginalLineTail.fraction_frame', 'OriginalLineTail.fraction_cursor', 'OriginalLineTail.record_safe', 'OriginalLineTail.finished_frame', 'OriginalLineTail.frame', 'OriginalLineTail.callback_return', 'OriginalLineTail.contains_fraction', 'OriginalLineTail.execution', 'OriginalLineTail.finish_inputs', 'OriginalLineTail.continued', 'OriginalLineTail.preserves_seen', 'OriginalLineTail.fraction_encodes', 'OriginalLineTail.inputs', 'OriginalLineTail.arithmetic', 'OriginalLineTail.live_value', 'OriginalLineTail.live_continued', 'OriginalLineTail.live_append', 'OriginalLineTail.following_duplicates', 'OriginalLineTail.through_sentinel', 'E1M1LineTail.contains_prior', 'E1M1LineTail.crossing_list_return_execution']

def certificate(raw):
    source = """import Doom.Proofs.E1M1LineTail
set_option maxRecDepth 32768
namespace Doom.Verification.ExtractedLineTail
open Doom Doom.Proofs X86 X86Memory X86Control
"""
    for key,target in [('finish', 'OriginalLineFinish.code'), ('cell', 'OriginalLineCell.code'), ('lineEntry', 'OriginalLineBounds.lineEntry'), ('lineReturn', 'OriginalLineBounds.lineReturn'), ('setup', 'OriginalLineFraction.code'), ('helper', 'OriginalInterceptVector.code'), ('division', 'Doom19.fixedDivBytes')]:
        source += 'def '+key+'Code : List UInt8 := ['+','.join(hex(b) for b in raw[key])+']\n'
        source += 'theorem '+key+'_checked : '+key+'Code='+target+' := by decide\n'
    source += """theorem execution_checked (s : X86Memory.State) (f : Option Flags)
    (arithmetic : OriginalInterceptVector.Safe (OriginalLineFraction.setup s))
    (layout : OriginalLineTail.Layout s)
    (ret : load32 s.memory (s.regs 4+(36#32))=(0x2c578#32)) :
    ∃ n≤108, X86Routine.Prefix OriginalLineTail.program [] n ⟨s,f,0x2c691⟩ (OriginalLineTail.result s) :=
  OriginalLineTail.execution s f arithmetic layout ret
"""
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedLineTail\n'


def audit(output):
    rest = output.strip()
    for name in ['Doom.Verification.ExtractedLineTail.' + n for n in NAMES] + ['Doom.Proofs.' + n for n in PROOFS]:
        match = re.match(re.escape(f"'{name}'") + r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing audit: ' + name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axioms')
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected output')


def extracted():
    spec = json.loads((ROOT / 'tests/reference/original-line-tail.json').read_text())
    profile = json.loads((ROOT / 'tests/reference' / spec['exe_profile']).read_text())
    sw = json.loads((ROOT / 'tests/reference/shareware.json').read_text())
    binary = extraction.original.extract(ROOT / sw['local_directory'] / 'doom19s.zip', sw, profile)
    return spec, profile, extraction.extract(binary, profile, spec)


def cross_check(raw):
    import capstone
    import unicorn as u
    from unicorn import x86_const as x
    CODE,HEAP,MASK=0x100000,0x600000,0xffffffff
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);em.mem_map(CODE,0x50000)
    starts=dict(finish=0x2c6bb,cell=0x2c541,lineReturn=0x2c587,setup=0x2c691,helper=0x2c2d0,division=0x1d180)
    for name,start in starts.items():
        code=raw[name]
        listing=list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(code,start))
        require(b''.join(bytes(i.bytes) for i in listing)==code,'decoder mismatch')
        em.mem_write(CODE+start,code)
    addresses=[0,0x13000,0x2b000,0x2c000,HEAP,0xfffff000]
    for a in addresses:em.mem_map(a,4096)
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
          x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];visits=[];rng=random.Random(0x2c691)
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _,access,a,size,value,data:writes.append((a&MASK,size,value&MASK)))
    em.hook_add(u.UC_HOOK_CODE,lambda _,a,size,data:visits.append(a-CODE))
    groups=dict(negative=0,early_stop=0,append=0,parallel=0,duplicate_suffix=0,empty_suffix=0,wrapped_stack=0,wrapped_record=0)
    for i in range(2048):
        pages={a:bytearray(rng.randbytes(4096)) for a in addresses}
        def put(a,v,size=4):
            for k,b in enumerate((v&((1<<(8*size))-1)).to_bytes(size,'little')):
                q=(a+k)&MASK;pages[q&~4095][q&4095]=b
        def get(a,size=4):return sum(pages[((a+k)&MASK)&~4095][((a+k)&MASK)&4095]<<(8*k) for k in range(size))
        rr=[rng.getrandbits(32) for _ in regs]
        sp=[HEAP+128,HEAP+131,0xfffffe01,0xfffffff9][i%4]
        p,v,lp=HEAP+1025,HEAP+1281,HEAP+769
        # Keep a wrapping record disjoint from a wrapping frame.
        cur=0xfffffff1 if i%4<2 and (i//4)%2 else HEAP+2049
        wx=[-65536,-32768,0,32768,65536,131072,65535,65537][(i//8)%8]
        parallel=(i//64)%4==0;dy=0 if parallel else 65536
        active=(i//256)%2;back=HEAP+3000 if (i//512)%2 else 0
        n=(i//32)%8;epoch=rng.getrandbits(32);base=HEAP+1408
        rr[4]=sp;rr[1]=p
        for a,value in [(p,v),(p+8,0),(p+12,dy),(p+50,back),(v,wx),(v+4,0),
                        (0x2c024,active),(0x2c028,cur),(0x13580,epoch),(0x2c120,base),
                        (sp+24,lp),(sp+36,CODE+0x2c578),(sp+48,CODE+0x4f000)]:put(a,value)
        for j,value in enumerate([0,0,65536,0]):put(0x2ba10+4*j,value)
        put(lp,9,2)
        for j in range(n):put(lp+2*(j+1),j,2);put(base+62*j+54,epoch)
        put(lp+2*(n+1),65535,2)
        for a,page in pages.items():em.mem_write(a,bytes(page))
        for reg,value in zip(regs,rr):em.reg_write(reg,value)
        em.reg_write(x.UC_X86_REG_EFLAGS,0x8c3 if i%3==0 else 2)
        expected=[];wanted=rr.copy()
        def store(a,value):expected.append((a&MASK,4,value&MASK));put(a,value)
        # Four local divline fields and the actual nested CALL/push footprints.
        for off,value in [(0,wx),(4,0),(8,0),(12,dy),(-4,CODE+0x2c6bb),
                          (-8,rr[3]),(-12,p),(-16,rr[6]),(-20,rr[7]),(-24,rr[5])]:store(sp+off,value)
        frac=0 if parallel else (wx>>8)*256
        count=41 if parallel else 80
        if not parallel:
            for off,value in [(-28,CODE+0x2c32e),(-32,0),(-36,sp),(-40,0x2ba10)]:store(sp+off,value)
        insert=False
        if frac<0:count+=11;answer=1;groups['negative']+=1
        elif not active:count+=19;answer=1;insert=True
        elif frac>=65536:count+=21;answer=1;insert=True
        elif back:count+=23;answer=1;insert=True
        else:count+=17;answer=0;groups['early_stop']+=1
        if insert:
            for a,value in [(cur+4,1),(cur,frac),(cur+8,p),(0x2c028,cur+12)]:store(a,value)
            groups['append']+=1
        wanted[0]=answer;wanted[4]=(sp+40)&MASK
        for off,reg in [(16,5),(20,6),(24,2),(28,1),(32,3)]:wanted[reg]=get(sp+off)
        if answer:
            count+=3+10*n+7
            wanted[0]=1;wanted[2]=(lp+2*(n+1))&MASK
            if n:wanted[3]=base
            groups['duplicate_suffix']+=n>0;groups['empty_suffix']+=n==0
        else:count+=5
        wanted[4]=(sp+52)&MASK;wanted[7]=get(sp+44);stop=get(sp+48)
        groups['parallel']+=parallel;groups['wrapped_stack']+=sp>=0xfffff000;groups['wrapped_record']+=cur==0xfffffff1
        writes.clear();visits.clear();em.emu_start(CODE+0x2c691,0,count=count)
        require(em.reg_read(x.UC_X86_REG_EIP)==stop,f'case {i}: PC')
        require(len(visits)==count,f'case {i}: count')
        require([em.reg_read(r) for r in regs]==wanted,f'case {i}: registers')
        require(writes==expected,f'case {i}: ordered writes')
        for a,page in pages.items():require(em.mem_read(a,4096)==page,f'case {i}: memory')
    require(all(groups.values()),'missing coverage')
    return {'total_cases':2048,'groups':groups,
            'checks':'Original setup, intersection helper, FixedDiv, finish, iterator resumption, duplicate suffix and sentinel with no stubs. All eight registers, mapped memory, ordered writes, PC and instruction count.',
            'scope':'Finite native samples supplement the kernel theorems. Axis-aligned geometry including parallel lines, negative fractions, early stop, append, wrapped frames/records; final flags not compared.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cross-check', action='store_true')
    args = parser.parse_args()
    spec, profile, raw = extracted()
    out = ROOT / 'artifacts/original-line-tail'
    out.mkdir(parents=True, exist_ok=True)
    source = out / 'Extracted.lean'
    source.write_text(certificate(raw))
    subprocess.run([str(ROOT / 'scripts/lake'), 'build', 'Doom.Proofs.E1M1LineTail'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT / 'scripts/lake'), 'env', 'lean', str(source)], cwd=ROOT, capture_output=True, text=True, check=True)
    audit(checked.stdout)
    (out / 'axioms.log').write_text(checked.stdout)
    report = {'exe_sha256': profile['exe_sha256'], 'units': spec['units'], 'axioms': checked.stdout.splitlines(),
              'scope': 'Crossing-line tail from 0x2c691: fraction arithmetic, optional ordered append, preserved data, callback return, finite duplicate suffix and sentinel. Callback-entry invariants, mixed fresh iteration and whole-game equivalence remain open.',
              'cross_check': cross_check(raw) if args.cross_check else None}
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print('PASS: original crossing-line tail; extracted bytes and strict axiom audit.')
    if args.cross_check:
        print('Native crossing-tail cases:', report['cross_check']['total_cases'])


if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as error:
        print(error.stdout or '')
        print(error.stderr or '')
        raise
