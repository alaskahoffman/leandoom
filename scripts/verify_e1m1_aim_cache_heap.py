#!/usr/bin/env python3
"""Produced next heap, real owned raw allocation and actual W_ReadLump CALL.
No filesystem success, hit-branch completion, gate or initialized startup claim.
"""
import argparse,hashlib,json,random,re,struct,subprocess,sys
sys.setrecursionlimit(max(sys.getrecursionlimit(),10000))
import verify_e1m1_aim_cache_call as previous
ROOT,require=previous.ROOT,previous.require
MODULES=['E1M1AimCacheHeap','E1M1AimCacheAllocate','E1M1AimCacheRead']
NS='Doom.Verification.ExtractedAimCacheHeap'
HEADER='open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary\n'
def contracts():
    return [(m,n) for m in MODULES for n in re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{m}.lean').read_text(),re.M)]
def contract(module,name):
    decl,args=previous.extraction.contract(module,name)
    qualifiers={'View':'OriginalGroupHeap','Separated':'OriginalGroupHeap','rounded':'OriginalGroupMallocEntry',
        'saved':'OriginalGroupMallocEntry','prepared':'OriginalGroupMallocEntry','nextView':'E1M1AimCacheHeap',
        'Local':'E1M1AimCacheAllocate','candidate':'E1M1AimCacheAllocate','selected':'E1M1AimCacheAllocate',
        'result':'E1M1AimCacheAllocate','rawWrites':'E1M1AimCacheAllocate'}
    for token,owner in qualifiers.items():
        decl=re.sub(r'(?<![\w.])'+token+r'\b','Doom.Proofs.'+owner+'.'+token,decl)
    return decl,args
def names():
    return [NS+'.program_checked']+[full for m,n in contracts() for full in [NS+'.'+m+'.'+n+'_checked','Doom.Proofs.'+m+'.'+n]]
def certificate():
    source='import Doom.Proofs.E1M1AimCacheRead\n'+previous.certificate()
    imports=list(dict.fromkeys(re.findall(r'^import .+$',source,re.M)))
    source='\n'.join(imports)+'\n'+re.sub(r'^import .+\n','',source,flags=re.M)
    source+='\nnamespace '+NS+'\nset_option linter.unusedSimpArgs false\n'+HEADER
    source+='''def program := Doom.Verification.ExtractedAimCacheCall.program
theorem program_checked : program=E1M1AimCacheDispatch.program := by
  exact Doom.Verification.ExtractedAimCacheCall.program_checked
'''
    for module,name in contracts():
        decl,args=contract(module,name);decl=decl.replace('theorem '+name,'theorem '+name+'_checked',1)
        changed=decl
        for m in MODULES: changed=changed.replace('Doom.Proofs.'+m+'.program',NS+'.program')
        source+='namespace '+module+'\n'+changed+' := by\n'
        if changed!=decl:source+='  simp only ['+NS+'.program_checked]\n'
        source+='  exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='end '+NS+'\n'
    return source+'\n'.join('#print axioms '+n for n in names())+'\n'
def audit(output):
    marker="'"+names()[0]+"'";require(marker in output,'missing cache heap audit')
    inherited,rest=output.split(marker,1);previous.audit(inherited);rest=(marker+rest).strip()
    for full in names():
        m=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+full)
        require({a.strip() for a in (m[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')
def cross_check():
    import capstone,unicorn as u
    from unicorn import x86_const as x
    bs,_,_=previous.extraction.entry_data();gr,_,_=previous.extraction.group.malloc.extracted()
    fills,_,_=previous.memset.fill_data();cache,_,_=previous.cache_data()
    ranges=[(0x2e3e0,bs['entry']),(0x38bb0,bs['length']),(0x39690,gr['malloc_entry']),
      (0x396f8,gr['select_split']),(0x39731,gr['allocation']),(0x3fe70,fills['memset']),
      (0x418e0,fills['fill']),(0x41917,fills['fill_words']),(0x38d00,cache['cache']),(0x38cab,cache['hit'])]
    dec=capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32)
    for pc,blob in ranges:require(b''.join(bytes(i.bytes) for i in dec.disasm(blob,pc))==blob,'independent decode')
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
          x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    rng=random.Random(0x38d41);mask=0xffffffff;cases=[]
    for alignment in range(0,32,4):
     for previous_free in [False,True]:
      for first_mode in ['nosplit0','nosplit64','split']:
       for excess in [0,64,65,4096]:
        for wrapping in [False,True]:
            em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
            regions=[(0,0x1000),(0x2c000,0x1000),(0x74000,0x1000),(0x610000,0x60000),
                     (0x680000,0x1000),(0xfffff000,0x1000)]
            memory={a:bytearray(rng.randbytes(n)) for a,n in regions}
            for a,n in regions:em.mem_map(a,n)
            for a,n in [(0x2e000,0x1000),(0x38000,0x2000),(0x3f000,0x1000),(0x41000,0x1000)]:em.mem_map(a,n)
            for pc,blob in ranges:em.mem_write(pc,blob)
            def locate(a):
                a &= mask
                for b,buf in memory.items():
                    if b<=a<b+len(buf):return buf,a-b
                raise ValueError('unmapped '+hex(a))
            def put(a,v):
                for j in range(4):buf,k=locate(a+j);buf[k]=(v>>(8*j))&255
            def get(a):return sum(locate(a+j)[0][locate(a+j)[1]]<<(8*j) for j in range(4))
            def cpu_get(a):return sum(em.mem_read((a+j)&mask,1)[0]<<(8*j) for j in range(4))
            sp=(8 if wrapping else 0x680e00)+alignment+1
            table,zone,rover,prev,before,nxt=0x610000,0x610800,0x620000+alignment,0x630000+alignment,0x660000,0x640000+alignment
            cache_table,next_next=0x611001,0x650000
            block=prev if previous_free else rover
            raw_size=19464+excess;first_excess=raw_size if first_mode=='split' else (64 if first_mode=='nosplit64' else 0)
            size=11688+first_excess;raw_block=block+11688 if first_mode=='split' else nxt;raw=raw_block+24
            rr=[rng.getrandbits(32) for _ in regs];rr[0]=9;rr[4]=sp
            for a,v in [(0x74fa0,1264),(0x74fa4,table),(table+196,19440),(0x74fe0,zone),
              (zone+28,rover),(rover+20,prev),(prev+4,0 if previous_free else 2),(prev+20,before),
              (block,size),(block+4,0),(block+16,nxt),(0x74f94,cache_table),(cache_table+36,0),
              (nxt+20,block),(nxt+4,0),(nxt,raw_size),(nxt+16,next_next)]:put(a,v)
            for a,buf in memory.items():em.mem_write(a,bytes(buf))
            for r,v in zip(regs,rr):em.reg_write(r,v)
            em.reg_write(x.UC_X86_REG_EFLAGS,0x8d7)
            writes=[]
            def store(a,v):writes.append((a&mask,4,v&mask));put(a,v)
            for off,r in [(4,3),(8,1),(12,2),(16,6),(20,7),(24,5)]:store(sp-off,rr[r])
            store(sp-36,0x2e3f7);store(sp-40,0);store(0x2c11c,648);store(sp-36,0x2e415)
            for off,val in [(40,9),(44,rr[6]),(48,rr[7]),(52,rr[5])]:store(sp-off,val)
            def split(b,request,extra,successor):
                rem=b+request
                for a,v in [(rem+4,0),(rem+8,0),(rem,extra),(rem+20,b),(rem+16,successor),
                            (successor+20,rem),(b+16,rem),(b,request)]:store(a,v)
            first_start=len(writes)
            if first_mode=='split':split(block,11688,first_excess,nxt)
            store(block+4,2);store(block+8,50);store(zone+28,get(block+16));store(block+12,0x1d4a11)
            first_writes=writes[first_start:]
            view={0x74fe0:zone,zone+28:raw_block,raw_block+20:block,block+4:2,
                  raw_block+4:0,raw_block:raw_size,raw_block+16:(nxt if first_mode=='split' else next_next)}
            require(all(get(a)==v for a,v in view.items()),'produced next view not derived')
            first_header={a:get(a) for a in [block,block+4,block+8,block+12,block+16]}
            store(0x2c118,block+24);store(sp-36,0x2e437);store(sp-40,block+24);store(sp-44,9)
            store(sp-48,0x3fe85);store(sp-52,11664);store(sp-56,0x418fc)
            cursor=block+24;words=2916;heads=0
            while cursor%32:store(cursor,0);cursor+=4;words-=1;heads+=1
            store(sp-60,words)
            for _ in range(words):store(cursor,0);cursor+=4
            store(sp-36,0x2e445)
            for off,val in [(40,11664),(44,9),(48,11664),(52,rr[7])]:store(sp-off,val)
            store(sp-56,0x38d3c);store(sp-60,1);store(sp-56,0x38d41)
            require(all(get(a)==v for a,v in view.items()),'request view frame broken')
            raw_initial=bytes(locate(raw+j)[0][locate(raw+j)[1]] for j in range(19440))
            for off,val in [(60,9),(64,36),(68,0),(72,0)]:store(sp-off,val)
            raw_start=len(writes)
            successor=get(raw_block+16)
            if excess>64:split(raw_block,19464,excess,successor)
            for a,v in [(raw_block+4,cache_table+36),(cache_table+36,raw),(raw_block+8,1),
                        (zone+28,get(raw_block+16)),(raw_block+12,0x1d4a11)]:store(a,v)
            raw_writes=writes[raw_start:]
            raw_metadata={a:get(a) for a,n,_ in raw_writes}
            store(sp-56,0x38d50)
            # Independent nonvacuity checks for new static separation conditions.
            def byteset(a):return {(a+j)&mask for j in range(4)}
            def apart(a,b):return byteset(a).isdisjoint(byteset(b))
            for ws in [first_writes,raw_writes]:
                require(all(apart(a,b) for i,(a,_,_) in enumerate(ws) for b,_,_ in ws[i+1:]),'metadata pairwise guard')
                require(all(apart(0x74fe0,a) for a,_,_ in ws),'zone global guard')
            require(raw_size>=19464 and raw_block!=block,'raw capacity/search guard')
            saved_addresses=[(sp-n)&mask for n in [60,64,68,72]]
            require(all(apart(a,b) for a in view for b in saved_addresses),'next-view prologue frame')
            require(all(apart(a,b) for a in saved_addresses+[(sp-56)&mask,0x74f94,0x2c11c,0x2c118]
                        for b,_,_ in raw_writes),'saved/count/pointer metadata frame')
            zero_set=set(range(block+24,block+24+11664))
            require(all(zero_set.isdisjoint(byteset(a)) for a in saved_addresses+[(sp-56)&mask]+[w[0] for w in raw_writes]),'output byte frame')
            actual=[];pcs=[];requests=[];returned=[]
            def trace(machine,pc,_n,_d):
                if pc==0x38bf0:machine.emu_stop();return
                if pc==0x39690:
                    requests.append(pc)
                    if len(requests)==2:
                        require(all(cpu_get(a)==v for a,v in view.items()),'CPU produced request view')
                        require([machine.reg_read(r) for r in regs]==[19440,9,1,cache_table+36,(sp-56)&mask,0,36,0],'second allocator request')
                if pc==0x38d41:
                    returned.append(pc)
                    require([machine.reg_read(r) for r in regs]==[raw,9,zone,raw_block,(sp-52)&mask,0,36,0],'owned allocator return')
                    require(cpu_get(cache_table+36)==raw,'owner publication before actual read')
                pcs.append(pc)
            em.hook_add(u.UC_HOOK_CODE,trace)
            em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:actual.append((a,n,v&mask)))
            em.emu_start(0x2e3e0,0,count=10000)
            require(em.reg_read(x.UC_X86_REG_EIP)==0x38bf0 and len(requests)==2 and returned==[0x38d41],'continuous allocation/read path')
            require([em.reg_read(r) for r in regs]==[9,9,raw,raw_block,(sp-56)&mask,0,36,0],'read call registers')
            require(actual==writes,'ordered writes')
            require(all(bytes(em.mem_read(a,len(buf)))==bytes(buf) for a,buf in memory.items()),'full mapped memory')
            require(bytes(em.mem_read(block+24,11664))==bytes(11664),'zeroed side payload')
            require(bytes(em.mem_read(raw,19440))==raw_initial,'raw allocation must NOT invent loaded payload')
            require(all(cpu_get(a)==v for a,v in raw_metadata.items()),'raw metadata through CALL')
            require(all(cpu_get(a)==v for a,v in first_header.items()),'first allocated header frame')
            require(cpu_get(0x2c11c)==648 and cpu_get(0x2c118)==block+24,'published count/base')
            require(cpu_get(sp-56)==0x38d50 and cpu_get(sp-36)==0x2e445,'actual nested return addresses')
            require(all(cpu_get(sp-off)==rr[r] for off,r in [(4,3),(8,1),(12,2),(16,6),(20,7),(24,5)]),'upper saved stack')
            require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==0,'TEST-owner flags preserved')
            require(len(pcs)<=5404,'proved bound')
            cases.append(dict(alignment=alignment,previous_free=previous_free,first_mode=first_mode,
              raw_excess=excess,wrapping=wrapping,instructions=len(pcs),head_count=heads,tail=words%4))
    return dict(cases=len(cases),first_modes={m:sum(c['first_mode']==m for c in cases) for m in ['nosplit0','nosplit64','split']},
      raw_modes={m:sum((c['raw_excess']>64)==m for c in cases) for m in [False,True]},
      all_registers=True,ordered_writes=True,full_mapped_data=True,zero_output=True,raw_payload_unchanged=True,
      owner_and_header=True,saved_stack=True,count_base=True,defined_flags=True,static_guard_checks=True,
      head_counts=sorted({c['head_count'] for c in cases}),tails=sorted({c['tail'] for c in cases}),details=cases,
      scope='Constructed original placements, not pinned earlier startup history. Continuous original entry through both allocations and actual W_ReadLump CALL. Stops before W_ReadLump executes: no disk icon/filesystem result or raw payload image supplied.')
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    out=ROOT/'artifacts/e1m1-aim-cache-heap';out.mkdir(exist_ok=True)
    (out/'Checked.lean').write_text(certificate())
    run=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(out/'Checked.lean')],cwd=ROOT,capture_output=True,text=True,timeout=300)
    (out/'axioms.log').write_text(run.stdout+run.stderr)
    require(run.returncode==0,'certificate failed: '+run.stdout+run.stderr);audit(run.stdout);require(not run.stderr.strip(),'unexpected stderr')
    native=None
    if args.cross_check:
        native=cross_check();(out/'cross-check.json').write_text(json.dumps(native,indent=2)+'\n')
    elif (out/'cross-check.json').exists():native=json.loads((out/'cross-check.json').read_text())
    prior=json.loads((ROOT/'artifacts/e1m1-aim-cache-call/report.json').read_text())
    entries=re.findall(r"^'([^']+)'",run.stdout,re.M)
    report=dict(exe_sha256=prior['exe_sha256'],wad_sha256=prior['wad_sha256'],units=prior['units'],unique_ranges=prior['unique_ranges'],
      public_theorems=len(contracts()),audit_entries=len(entries),distinct_declarations=len(set(entries)),cross_check=native,
      scope=__doc__)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: produced heap, actual owned raw allocation, real read CALL; startup incomplete.')
if __name__=='__main__':main()
