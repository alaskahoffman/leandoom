#!/usr/bin/env python3
"""Certify DOS aim ray arithmetic and epilogue; traversal between them is open."""
import argparse
import json
import random
import re
import struct
import subprocess
import verify_original_inline_thrust as extraction
import verify_original_thrust as thrust
ROOT,require=extraction.ROOT,extraction.require
NAMES=['ray_bytes_checked','ret_bytes_checked','ray_checked','return_checked']
PROOFS=['OriginalAimQuery.'+n for n in ['decoded','ray_execution','saved_frame','selected_tables','live_endpoint','return_execution','return_memory','return_value','return_miss','return_hit','restores']]
PROOFS+=['E1M1AimQuery.'+n for n in ['first_ray_execution','first_ray_endpoint','return_to_accept','return_to_retry','return_to_last','last_miss_zero','accepted_result']]
PROOFS+=['Collision.Scene.attackPath_original']

def certificate(raw):
    s='''import Doom.Proofs.E1M1AimQuery
namespace Doom.Verification.ExtractedAimQuery
open Doom Doom.Proofs X86 X86Memory X86Control OriginalAimQuery
'''
    for name in ['ray','ret']:
        s+='def '+name+'Extracted : List UInt8 := ['+','.join(hex(b) for b in raw[name])+']\n'
        s+='theorem '+name+'_bytes_checked : '+name+'Extracted='+name+'Bytes := by decide\n'
    s+='''theorem ray_checked (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix (bytesProgram rayExtracted retExtracted) [] 11 ⟨s,f,0x2bb80⟩ (ray s) := by
  rw [ray_bytes_checked,ret_bytes_checked]; exact ray_execution s f
 theorem return_checked (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix (bytesProgram rayExtracted retExtracted) [] 8 ⟨s,f,0x2bbff⟩ (returned s) := by
  rw [ray_bytes_checked,ret_bytes_checked]; exact return_execution s f
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join('#print axioms '+qualified(n) for n in PROOFS)+'\nend Doom.Verification.ExtractedAimQuery\n'

def qualified(n):
    return ('Doom.' if n.startswith('Collision.') else 'Doom.Proofs.')+n

def audit(output):
    rest=output.strip()
    for name in ['Doom.Verification.ExtractedAimQuery.'+n for n in NAMES]+[qualified(n) for n in PROOFS]:
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[m.end():].strip()
    require(not rest,'unexpected output')

def cross_check(raw,table):
    import capstone
    import unicorn as u
    from unicorn import x86_const as x
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
    CODE,HEAP,MASK=0x100000,0x600000,0xffffffff
    bases=list(range(0,0x14000,4096))+[0x2b000,HEAP,0xfffff000]
    em.mem_map(CODE,0x40000)
    for a in bases:em.mem_map(a,4096)
    for name,addr in [('ray',0x2bb80),('ret',0x2bbff)]:
        em.mem_write(CODE+addr,raw[name])
        listing=list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(raw[name],addr))
        require(b''.join(bytes(i.bytes) for i in listing)==raw[name],'undecoded bytes')
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    rng=random.Random(0x2bb80);writes=[];visits=[]
    em.hook_add(u.UC_HOOK_CODE,lambda _e,a,_n,_d:visits.append(a-CODE))
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&MASK)))
    pages={a:bytearray(rng.randbytes(4096)) for a in bases}
    def put(a,v):
        for j,b in enumerate(struct.pack('<I',v&MASK)):
            z=(a+j)&MASK;pages[z&~4095][z&4095]=b
    for i in range(10240):put(0x5a84+4*i,struct.unpack_from('<I',table,4*i)[0])
    put(0x13584,0x7a84)
    for a,b in pages.items():em.mem_write(a,bytes(b))
    def start(rr):
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5))
        writes.clear();visits.clear()
    def check(rr,expected,pc,count):
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+pc,'wrong stop')
        require(len(visits)==count,'wrong instruction count')
        require([em.reg_read(r) for r in regs]==rr,'wrong registers')
        require(writes==expected,'wrong write order')
        for a,b in pages.items():require(em.mem_read(a,4096)==b,'wrong mapped memory')
    edges=[0,1,0xffff,0x10000,0x10001,0x04000000,0x7fffffff,0x80000000,0xffff0000,0xffffffff]
    for i in range(8192):
        rr=[rng.getrandbits(32) for _ in regs];sp=[HEAP+3000+i%4,1,0xfffffffd][i%3]
        angle=(i<<19)|([0,(1<<19)-1,rng.getrandbits(19)][i%3])
        distance=edges[(i//2)%len(edges)] if i%2==0 else rng.getrandbits(32)
        rr[2]=angle;rr[3]=distance;rr[4]=sp;start(rr)
        expected=[]
        for off,r in [(4,1),(8,6),(12,7),(16,5)]:
            a=(sp-off)&MASK;expected.append((a,4,rr[r]));put(a,rr[r])
        signed=distance if distance<0x80000000 else distance-(1<<32)
        units=signed>>16
        rr[1]=(units*struct.unpack_from('<i',table,4*(i+2048))[0])&MASK
        rr[6]=(units*struct.unpack_from('<i',table,4*i)[0])&MASK
        rr[2]=i;rr[4]=(sp-16)&MASK
        em.emu_start(CODE+0x2bb80,CODE+0x2bba0,count=11)
        check(rr,expected,0x2bba0,11)
    for i in range(1024):
        rr=[rng.getrandbits(32) for _ in regs];sp=[HEAP+3001+i%4,0xfffffff1,0xfffffffd][i%3];rr[4]=sp
        target=0 if i%2==0 else [1,0xffffffff,0x80000000][i%3]
        slope=0 if i%3==0 else rng.getrandbits(32)
        put(0x2b9f8,target);put(0x2b9b4,slope)
        restore=[rng.getrandbits(32) for _ in range(4)]
        for j,v in enumerate(restore+[CODE+0x334a9]):put(sp+4*j,v)
        for a,b in pages.items():em.mem_write(a,bytes(b))
        start(rr)
        rr[0]=slope if target else 0;rr[4]=(sp+20)&MASK
        for r,v in zip([5,7,6,1],restore):rr[r]=v
        em.emu_start(CODE+0x2bbff,CODE+0x334a9,count=8)
        check(rr,[],0x334a9,8)
    return {'ray_cases':8192,'return_cases':1024,'checks':'every fine angle index, fractional/signed ranges, unaligned/wrapping stack, registers, all mapped data memory, writes and instruction counts',
            'scope':'two real instruction segments; intervening geometry is neither executed nor verified; flags not compared'}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--cross-check',action='store_true');args=p.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-aim-query.json').read_text());profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile);raw=extraction.extract(binary,profile,spec)
    _,table=thrust.extract(binary,profile,json.loads((ROOT/'tests/reference/original-thrust.json').read_text()))
    out=ROOT/'artifacts/original-aim-query';out.mkdir(parents=True,exist_ok=True)
    source=out/'Extracted.lean';source.write_text(certificate(raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimQuery','fidelity-probe'],cwd=ROOT,check=True)
    result=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(result.stdout);(out/'axioms.log').write_text(result.stdout)
    report={'exe_sha256':profile['exe_sha256'],'units':spec['units'],'axioms':result.stdout.splitlines(),
      'scope':'Ray displacement matches production endpoint under existing sine-table identity and memory separation. Actual epilogue handles hit/miss and restores saved registers. Firing prefix joined through ray multiplications; traversal, remaining setup, table initialization and DOS loader remain obligations.',
      'tables':thrust.check_tables(table),
      'cross_check':cross_check(raw,table) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: original aim ray and return bytes, kernel certificates and axiom audit.')
    if args.cross_check:print('Native segment checks:',report['cross_check']['ray_cases']+report['cross_check']['return_cases'])
if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as e:print(e.stdout or '');print(e.stderr or '');raise
