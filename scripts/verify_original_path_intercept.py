#!/usr/bin/env python3
"""Certify the first P_PathTraverse grid intercept and Y-axis comparison inputs."""
import argparse
import json
import random
import re
import struct
import subprocess
import verify_original_inline_thrust as extraction
ROOT, require = extraction.ROOT, extraction.require
NAMES = ['bytes_checked', 'execution_checked']
PROOFS = ['PathXStepFrame.'+n for n in ['div_preserves','input_preserves','registers','stack','frame','local_preserved']]
PROOFS += ['OriginalPathIntercept.'+n for n in ['decoded','execution','live','frame']]
PROOFS += ['E1M1PathIntercept.'+n for n in ['first_intercept_execution','inputs_from_xstep','first_intercept_correspondence']]


def certificate(raw):
    source = '''import Doom.Proofs.E1M1PathIntercept
set_option maxRecDepth 32768
namespace Doom.Verification.ExtractedPathIntercept
open Doom Doom.Proofs X86 X86Memory X86Control OriginalPathIntercept
'''
    source += 'def extractedBytes : List UInt8 := ['+','.join(hex(b) for b in raw['intercept'])+']\n'
    source += '''theorem bytes_checked : extractedBytes=code := by decide
def extractedProgram := bytesProgram extractedBytes
theorem execution_checked (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix extractedProgram [] 19 ⟨s,f,0x2c9d3⟩ (result s) := by
  have same : extractedProgram=program := by
    simp only [extractedProgram,program,bytes_checked]
  rw [same]; exact execution s f
'''
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedPathIntercept\n'


def audit(output):
    rest = output.strip()
    for name in ['Doom.Verification.ExtractedPathIntercept.'+n for n in NAMES]+['Doom.Proofs.'+n for n in PROOFS]:
        match = re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest = rest[match.end():].strip()
    require(not rest,'unexpected output')


def cross_check(raw):
    import capstone
    import unicorn as u
    from unicorn import x86_const as x
    CODE, HEAP, MASK = 0x100000, 0x600000, 0xffffffff
    start, end = 0x2c9d3, 0x2ca10
    listing = list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(raw['intercept'],start))
    require(len(listing)==19 and b''.join(bytes(i.bytes) for i in listing)==raw['intercept'],'decoder mismatch')
    em = u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
    em.mem_map(CODE,0x30000);em.mem_write(CODE+start,raw['intercept'])
    bases = [0,HEAP,0xfffff000]
    for a in bases:em.mem_map(a,4096)
    regs = [x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
            x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes, visits = [], []
    em.hook_add(u.UC_HOOK_CODE,lambda _e,a,_n,_d:visits.append(a-CODE))
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&MASK)))
    rng = random.Random(start)
    signed = lambda v:v if v<0x80000000 else v-(1<<32)
    edges = [0,1,0xffff,0x10000,0x7fffffff,0x80000000,0x80000001,0xffffffff]
    groups = dict(negative_start=0,negative_product=0,wrapped_sum=0,unaligned_stack=0,wrapping_stack=0)
    for i in range(1024):
        pages = {a:bytearray(rng.randbytes(4096)) for a in bases}
        def put(a,v):
            for j,b in enumerate(struct.pack('<I',v&MASK)):
                q=(a+j)&MASK;pages[q&~4095][q&4095]=b
        def read(a):
            return int.from_bytes(bytes(pages[((a+j)&MASK)&~4095][((a+j)&MASK)&4095] for j in range(4)),'little')
        rr = [rng.getrandbits(32) for _ in regs]
        sp = [HEAP+1024,HEAP+1025,1,0xfffffffd][i%4];rr[4]=sp
        if i<512:
            rr[0],rr[3],rr[7] = edges[i%8],edges[(i//8)%8],edges[(i//64)%8]
        put(sp+16,edges[(i//7)%8] if i<512 else rng.getrandbits(32))
        put(sp+24,edges[(i//9)%8] if i<512 else rng.getrandbits(32))
        for a,page in pages.items():em.mem_write(a,bytes(page))
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|((i&1)<<6)|((i&2)<<10))
        shift = (signed(rr[7])>>7)&MASK
        product = (signed(rr[3])*signed(rr[0])>>16)&MASK
        yi = (shift+product)&MASK
        expected_writes = [((sp+40)&MASK,4,rr[0]),((sp+4)&MASK,4,shift),((sp+44)&MASK,4,yi)]
        for a,_n,v in expected_writes:put(a,v)
        expected = rr[:]
        expected[0]=(rr[1]-rr[7])&MASK
        expected[1]=read(sp+16);expected[2]=read(sp+24)
        expected[3]=shift&65535;expected[5]=(rr[5]-rr[6])&MASK
        writes.clear();visits.clear()
        em.emu_start(CODE+start,CODE+end,count=20)
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+end,f'case {i}: PC')
        require(visits==[j.address for j in listing],f'case {i}: instruction order')
        require([em.reg_read(r)&MASK for r in regs]==expected,f'case {i}: registers')
        require(writes==expected_writes,f'case {i}: writes')
        for a,page in pages.items():require(bytes(em.mem_read(a,4096))==bytes(page),f'case {i}: memory')
        flags=em.reg_read(x.UC_X86_REG_EFLAGS)
        require(bool(flags&64)==(expected[2]==expected[1]),f'case {i}: comparison equality')
        require((bool(flags&128)!=bool(flags&2048))==(signed(expected[2])<signed(expected[1])),f'case {i}: signed comparison')
        groups['negative_start']+=signed(rr[7])<0
        groups['negative_product']+=signed(rr[3])*signed(rr[0])<0
        groups['wrapped_sum']+=shift+product>MASK
        groups['unaligned_stack']+=sp%4!=0
        groups['wrapping_stack']+=sp>0xfffffff0
    return {'total_cases':1024,**groups,'checked':'all eight registers, all mapped data bytes, exact write and instruction order, final PC and signed comparison flags'}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-path-intercept.json').read_text())
    profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text())
    sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec,allowed_objects=(3,))
    out=ROOT/'artifacts/original-path-intercept';out.mkdir(parents=True,exist_ok=True)
    source=out/'Extracted.lean';source.write_text(certificate(raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1PathIntercept'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout);(out/'axioms.log').write_text(checked.stdout)
    report={'exe_sha256':profile['exe_sha256'],'units':spec['units'],'axioms':checked.stdout.splitlines(),
      'scope':'19-instruction first grid intercept and Y-axis comparison operands; joined firing prefix <=287. Exact arbitrary-memory execution and live pathFirstIntercept equality under explicit coordinate/stack encodings. Prior X-step arithmetic success and earlier prefix obligations remain. Y direction/division, cell traversal, callbacks and whole-game equivalence are still open.',
      'cross_check':cross_check(raw) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: original first grid intercept, preserved geometry, continuous firing join and kernel axiom audit.')
    if args.cross_check:print('Native intercept cases:',report['cross_check']['total_cases'])

if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as error:print(error.stdout or '');print(error.stderr or '');raise
