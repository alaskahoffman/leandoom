#!/usr/bin/env python3
"""Actual allocation frames and side publication to memset entry, not startup."""
import argparse, json, random, re, struct, subprocess, sys
sys.setrecursionlimit(max(sys.getrecursionlimit(),10000))
import verify_e1m1_aim_side_entry as previous
ROOT,require=previous.ROOT,previous.require
MODULE='E1M1AimSidePublish'
NS='Doom.Verification.ExtractedAimSidePublish'
HEADER=previous.HEADER+'open E1M1AimSideEntry (savedMemory)\nopen E1M1AimSideAllocate (allocated candidate selected HeapInitial)\nopen E1M1AimSidePublish\n'
def contracts():
    return re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{MODULE}.lean').read_text(),re.M)
def names():
    return [n for k in contracts() for n in [NS+'.'+k+'_checked','Doom.Proofs.'+MODULE+'.'+k]]
def certificate():
    source='import Doom.Proofs.E1M1AimSidePublish\n'+previous.certificate()
    imports=list(dict.fromkeys(re.findall(r'^import .+$',source,re.M)))
    source='\n'.join(imports)+'\n'+re.sub(r'^import .+\n','',source,flags=re.M)
    source+='\nnamespace '+NS+'\n'+HEADER
    for name in contracts():
        decl,args=previous.contract(MODULE,name)
        decl=decl.replace('theorem '+name,'theorem '+name+'_checked',1)
        changed=decl.replace('Doom.Proofs.E1M1AimSideAllocate.program',previous.NS+'.program')
        source+=changed+' := by\n'
        if changed!=decl:source+='  simp only ['+previous.NS+'.program_checked]\n'
        source+='  exact Doom.Proofs.'+MODULE+'.'+name+' '+args+'\n'
    source+='end '+NS+'\n'
    return source+'\n'.join('#print axioms '+n for n in names())+'\n'
def audit(output):
    marker="'"+names()[0]+"'";require(marker in output,'missing publication audit')
    inherited,rest=output.split(marker,1);previous.audit(inherited);rest=(marker+rest).strip()
    for full in names():
        m=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+full)
        require({a.strip() for a in (m[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check():
    """Uninterrupted CPU entry/length/allocation/publication with an independent write oracle."""
    import capstone, unicorn as u
    from unicorn import x86_const as x
    bs,_,_=previous.entry_data();gr,_,_=previous.group.malloc.extracted();lumps=previous.lump_data()
    require([lumps[k] for k in ['lumpIndex','lumpCount','lumpLength']]==[9,1264,19440],'pinned lump changed')
    ranges=[(0x2e3e0,bs['entry']),(0x38bb0,bs['length']),(0x39690,gr['malloc_entry']),
            (0x396f8,gr['select_split']),(0x39731,gr['allocation'])]
    dec=capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32)
    for pc,blob in ranges:
        require(b''.join(bytes(i.bytes) for i in dec.disasm(blob,pc))==blob,'independent decode failed')
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
          x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    rng=random.Random(0x2e3e0);cases=[]
    for alignment in range(4):
      for previous_free in [False,True]:
       for excess in [0,64,65,4096]:
        for wrapping in [False,True]:
            em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
            regions=[(0,0x1000),(0x2c000,0x1000),(0x74000,0x1000),(0x610000,0x30000),
                     (0x680000,0x1000),(0xfffff000,0x1000)]
            memory={a:bytearray(rng.randbytes(n)) for a,n in regions}
            for a,n in regions:em.mem_map(a,n)
            for a,n in [(0x2e000,0x1000),(0x38000,0x2000),(0x3f000,0x1000)]:em.mem_map(a,n)
            for pc,blob in ranges:em.mem_write(pc,blob)
            mask=0xffffffff
            def locate(a):
                a &= mask
                for b,buf in memory.items():
                    if b<=a<b+len(buf):return buf,a-b
                raise ValueError('unmapped '+hex(a))
            def put(a,v):
                for j in range(4):buf,k=locate(a+j);buf[k]=(v>>(8*j))&255
            def get(a):return sum(locate(a+j)[0][locate(a+j)[1]]<<(8*j) for j in range(4))
            sp=(8 if wrapping else 0x680e00)+alignment
            table,zone,rover,prev,before,nxt=0x610000,0x610800,0x620000+alignment,0x621000+alignment,0x62f000,0x62e000
            block=prev if previous_free else rover;size=11688+excess
            rr=[rng.getrandbits(32) for _ in regs];rr[0]=9;rr[4]=sp
            for a,v in [(0x74fa0,1264),(0x74fa4,table),(table+196,19440),(0x74fe0,zone),
              (zone+28,rover),(rover+20,prev),(prev+4,0 if previous_free else 2),
              (prev+20,before),(block,size),(block+4,0),(block+16,nxt)]:put(a,v)
            for a,buf in memory.items():em.mem_write(a,bytes(buf))
            for r,v in zip(regs,rr):em.reg_write(r,v)
            em.reg_write(x.UC_X86_REG_EFLAGS,0x8d7)
            writes=[]
            def store(a,v):writes.append((a&mask,4,v&mask));put(a,v)
            for off,r in [(4,3),(8,1),(12,2),(16,6),(20,7),(24,5)]:store(sp-off,rr[r])
            store(sp-36,0x2e3f7);store(sp-40,0);store(0x2c11c,648);store(sp-36,0x2e415)
            for off,val in [(40,9),(44,rr[6]),(48,rr[7]),(52,rr[5])]:store(sp-off,val)
            if excess>64:
                remainder=block+11688
                for a,v in [(remainder+4,0),(remainder+8,0),(remainder,excess),(remainder+20,block),
                            (remainder+16,nxt),(nxt+20,remainder),(block+16,remainder),(block,11688)]:store(a,v)
            store(block+4,2);store(block+8,50);store(zone+28,get(block+16));store(block+12,0x1d4a11)
            store(0x2c118,block+24);store(sp-36,0x2e437)
            expected=[block+24,9,0,11664,(sp-36)&mask,rr[5],11664,rr[7]]
            actual=[];pcs=[];requests=[]
            def trace(machine,pc,_n,_d):
                if pc==0x3fe70:machine.emu_stop();return
                pcs.append(pc)
                if pc==0x39690:
                    values=[machine.reg_read(r) for r in regs]
                    require(values==[11664,9,50,0,(sp-36)&mask,rr[5],rr[6],rr[7]],'actual request registers')
                    require(struct.unpack('<I',machine.mem_read(0x2c11c,4))[0]==648,'actual published count')
                    requests.append(pc)
            em.hook_add(u.UC_HOOK_CODE,trace)
            em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:actual.append((a,n,v&mask)))
            em.emu_start(0x2e3e0,0,count=150)
            require(em.reg_read(x.UC_X86_REG_EIP)==0x3fe70,'publication did not call memset')
            require(len(requests)==1,'missing actual allocation request')
            require([em.reg_read(r) for r in regs]==expected,'all register oracle mismatch')
            require(actual==writes,'ordered write oracle mismatch')
            require(all(bytes(em.mem_read(a,len(buf)))==bytes(buf) for a,buf in memory.items()),'full data memory mismatch')
            # Final ADD ESI,ESI has defined flags but the Lean model forgets them.
            require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==0,'actual ADD flags')
            require(get(0x2c118)==block+24 and get(0x2c11c)==648,'publication')
            require(all(get(sp-off)==rr[r] for off,r in [(4,3),(8,1),(12,2),(16,6),(20,7),(24,5)]),'upper saves')
            require(len(pcs)==30+(24 if previous_free else 23)+(19 if excess>64 else 9)+16+10,'instruction count')
            cases.append(dict(alignment=alignment,previous_free=previous_free,excess=excess,wrapping_stack=wrapping,instructions=len(pcs)))
    return dict(cases=len(cases),split=sum(c['excess']>64 for c in cases),unsplit=sum(c['excess']<=64 for c in cases),
                all_registers=True,ordered_writes=True,full_mapped_data=True,modeled_flags=False,actual_add_flags=True,actual_request=True,publication=True,upper_saved_words=True,details=cases,
                scope='Constructed directory/heap placement, continuous actual entry/length/selected first-free allocation, RET and publication/memset CALL. Both predecessor choices, split threshold, unaligned/wrapping stacks. Not reached DOS heap history or startup. Stops at memset entry before executing memset/cache.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    out=ROOT/'artifacts/e1m1-aim-side-publish';out.mkdir(exist_ok=True)
    (out/'Checked.lean').write_text(certificate())
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.'+MODULE],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(out/'Checked.lean')],cwd=ROOT,capture_output=True,text=True,timeout=300)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout);require(not checked.stderr.strip(),'unexpected stderr')
    native=None
    if args.cross_check:
        native=cross_check();(out/'cross-check.json').write_text(json.dumps(native,indent=2)+'\n')
    elif (out/'cross-check.json').exists():native=json.loads((out/'cross-check.json').read_text())
    prior=json.loads((ROOT/'artifacts/e1m1-aim-side-entry/report.json').read_text())
    audits=re.findall(r"^'([^']+)'",checked.stdout,re.M)
    report=dict(exe_sha256=prior['exe_sha256'],wad_sha256=prior['wad_sha256'],units=prior['units'],unique_ranges=prior['unique_ranges'],
      public_theorems=len(contracts()),audited_declarations=len(audits),unique_audited_declarations=len(set(audits)),cross_check=native,
      scope='Continuous actual side entry, length, selected split/no-split allocation and publication/CALL to memset entry0x3fe70. Static allocation frames derive count648, ECX9, allocator-restored registers and upper saved words; arbitrary protected words have frames. Initial directory/heap/placement assumed. No memset body, raw cache/read/gate/loop connection or initialized startup claimed.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: actual allocation frames and publication; cumulative certificate, strict audit and requested CPU checks.')
if __name__=='__main__':main()
