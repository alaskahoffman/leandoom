#!/usr/bin/env python3
"""Actual cache CALL, original-cell dispatcher, real length/malloc and hit/tag CALLs.
Not helper completion, filesystem execution, cache history or initialized startup.
"""
import argparse, hashlib, json, random, re, struct, subprocess, sys
sys.setrecursionlimit(max(sys.getrecursionlimit(),10000))
import verify_e1m1_aim_word_aligned as previous
import verify_e1m1_aim_side_entry as extraction
import verify_e1m1_aim_side_memset as memset
ROOT,require=previous.ROOT,previous.require
MODULES=['E1M1AimCacheCall','E1M1AimCacheDispatch']
NS='Doom.Verification.ExtractedAimCacheCall'
HEADER='open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary\n'
def cache_data(spec=None):
    if spec is None: spec=json.loads((ROOT/'tests/reference/original-aim-cache-dispatch.json').read_text())
    return extraction.entry_data(spec)
def contracts():
    return [(m,n) for m in MODULES for n in re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{m}.lean').read_text(),re.M)]
def names():
    return [NS+'.'+n+'_checked' for n in ['cache','hit','callProgram','program']]+[
        full for m,n in contracts() for full in [NS+'.'+m+'.'+n+'_checked','Doom.Proofs.'+m+'.'+n]]
def certificate():
    bs,_,_=cache_data()
    source='import Doom.Proofs.E1M1AimCacheDispatch\n'+previous.certificate()
    imports=list(dict.fromkeys(re.findall(r'^import .+$',source,re.M)))
    source='\n'.join(imports)+'\n'+re.sub(r'^import .+\n','',source,flags=re.M)
    source+='\nnamespace '+NS+'\nset_option linter.unusedSimpArgs false\n'+HEADER
    for name,blob in bs.items():
        source+='def '+name+' : List UInt8 := ['+','.join(hex(b) for b in blob)+']\n'
        source+='theorem '+name+'_checked : '+name+'=Doom.Proofs.E1M1AimCacheDispatch.'+name+'Bytes := by decide +kernel\n'
    source+='''def callProgram := Doom.Verification.ExtractedAimWordAligned.program
theorem callProgram_checked : callProgram=E1M1AimCacheCall.program := by
  exact Doom.Verification.ExtractedAimWordAligned.program_checked
def program := E1M1AimCacheDispatch.extend callProgram cache hit
theorem program_checked : program=E1M1AimCacheDispatch.program := by
  unfold program
  rw [callProgram_checked,cache_checked,hit_checked]; rfl
'''
    for module,name in contracts():
        decl,args=extraction.contract(module,name)
        qualifiers={'Entry32Safe':'E1M1AimWordFill','OutputSafe':'E1M1AimWordFill','zeros':'E1M1AimWordFill',
                    'finished':'E1M1AimWordAligned','entered':'E1M1AimCacheCall','ReadSafe':'E1M1AimCacheCall'}
        for token,owner in qualifiers.items():
            decl=re.sub(r'(?<![\w.])'+token+r'\b','Doom.Proofs.'+owner+'.'+token,decl)
        decl=decl.replace('theorem '+name,'theorem '+name+'_checked',1)
        changed=decl.replace('Doom.Proofs.E1M1AimCacheCall.program',NS+'.callProgram').replace('Doom.Proofs.E1M1AimCacheDispatch.program',NS+'.program')
        source+='namespace '+module+'\n'+changed+' := by\n'
        if changed!=decl: source+='  simp only ['+NS+'.callProgram_checked,'+NS+'.program_checked]\n'
        source+='  exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='end '+NS+'\n'
    return source+'\n'.join('#print axioms '+n for n in names())+'\n'
def audit(output):
    marker="'"+names()[0]+"'"; require(marker in output,'missing cache audit')
    inherited,rest=output.split(marker,1);previous.audit(inherited);rest=(marker+rest).strip()
    for full in names():
        m=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+full)
        assert m is not None
        require({a.strip() for a in (m[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')
def cross_check():
    """Uninterrupted independent CPU execution from original entry; no seam patching."""
    import capstone, unicorn as u
    from unicorn import x86_const as x
    bs,_,_=extraction.entry_data();gr,_,_=extraction.group.malloc.extracted()
    fills,_,_=memset.fill_data();cache,_,_=cache_data()
    ranges=[(0x2e3e0,bs['entry']),(0x38bb0,bs['length']),(0x39690,gr['malloc_entry']),
            (0x396f8,gr['select_split']),(0x39731,gr['allocation']),(0x3fe70,fills['memset']),
            (0x418e0,fills['fill']),(0x41917,fills['fill_words']),(0x38d00,cache['cache']),(0x38cab,cache['hit'])]
    dec=capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32)
    for pc,blob in ranges:
        require(b''.join(bytes(i.bytes) for i in dec.disasm(blob,pc))==blob,'independent decode failed')
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
          x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    rng=random.Random(0x38d00);cases=[];mask=0xffffffff
    for alignment in range(0,32,4):
      for previous_free in [False,True]:
       for excess in [0,64,65,4096]:
        for wrapping in [False,True]:
         for mode in ['miss','hit','bad_signature']:
            em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
            regions=[(0,0x1000),(0x2c000,0x1000),(0x74000,0x1000),(0x610000,0x30000),
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
            sp=(8 if wrapping else 0x680e00)+alignment+1
            table,zone,rover,prev,before,nxt=0x610000,0x610800,0x620000+alignment,0x621000+alignment,0x62f000,0x62e000
            cache_table,raw=0x611001,0 if mode=='miss' else 0x612018
            block=prev if previous_free else rover;size=11688+excess
            rr=[rng.getrandbits(32) for _ in regs];rr[0]=9;rr[4]=sp
            for a,v in [(0x74fa0,1264),(0x74fa4,table),(table+196,19440),(0x74fe0,zone),
              (zone+28,rover),(rover+20,prev),(prev+4,0 if previous_free else 2),
              (prev+20,before),(block,size),(block+4,0),(block+16,nxt),
              (0x74f94,cache_table),(cache_table+36,raw)]:put(a,v)
            if raw:put(raw-12,0x1d4a11 if mode=='hit' else 0)
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
            # Freeze produced allocation metadata before publication/fill/cache, not original memory.
            metadata={a:get(a) for a in [block,block+4,block+8,block+12,block+16,zone+28,nxt+20]}
            if excess>64:metadata.update({block+11688+off:get(block+11688+off) for off in [0,4,8,16,20]})
            store(0x2c118,block+24);store(sp-36,0x2e437)
            store(sp-40,block+24);store(sp-44,9);store(sp-48,0x3fe85)
            store(sp-52,11664);store(sp-56,0x418fc)
            cursor=block+24;words=2916;heads=0
            while cursor%32:
                store(cursor,0);cursor+=4;words-=1;heads+=1
            store(sp-60,words)
            for _ in range(words):store(cursor,0);cursor+=4
            store(sp-36,0x2e445)
            for off,val in [(40,11664),(44,9),(48,11664),(52,rr[7])]:store(sp-off,val)
            expected=[9,9,1,cache_table+36,(sp-52)&mask,0,36,raw]
            if mode=='miss':
                store(sp-56,0x38d3c);store(sp-60,1);store(sp-56,0x38d41)
                expected[0]=19440;expected[4]=(sp-56)&mask;endpoint=0x39690
            elif mode=='hit':
                store(sp-56,0x38cd3);expected[0]=raw;expected[4]=(sp-56)&mask;endpoint=0x399b0
            else:endpoint=0x38cb4
            actual=[];pcs=[];allocations=[];branches=[];call_seen=[]
            def trace(machine,pc,_n,_d):
                if pc==0x39690:
                    allocations.append(pc)
                    if len(allocations)==2:machine.emu_stop();return
                if pc in [0x399b0,0x38cb4]:machine.emu_stop();return
                if pc==0x38d00:
                    vals=[machine.reg_read(r) for r in regs]
                    require(vals==[9,9,1,11664,(sp-36)&mask,0,11664,rr[7]],'actual caller register seam')
                    actual_return=sum(machine.mem_read((sp-36+j)&mask,1)[0]<<(8*j) for j in range(4))
                    require(actual_return==0x2e445,'actual caller return')
                    require(machine.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==0x40,'caller defined flags')
                    call_seen.append(pc)
                if pc in [0x38d35,0x38cab]:branches.append(pc)
                pcs.append(pc)
            em.hook_add(u.UC_HOOK_CODE,trace)
            em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:actual.append((a,n,v&mask)))
            em.emu_start(0x2e3e0,0,count=10000)
            require(em.reg_read(x.UC_X86_REG_EIP)==endpoint,'wrong actual endpoint')
            require(len(allocations)==(2 if mode=='miss' else 1),'allocation request count')
            require(len(call_seen)==1 and branches==([0x38d35] if mode=='miss' else [0x38cab]),'branch not selected from original cell')
            require([em.reg_read(r) for r in regs]==expected,'all register oracle mismatch')
            require(actual==writes,'ordered write oracle mismatch')
            require(all(bytes(em.mem_read(a,len(buf)))==bytes(buf) for a,buf in memory.items()),'full data memory mismatch')
            require(bytes(em.mem_read(block+24,11664))==bytes(11664),'zero output not preserved')
            require(all(struct.unpack('<I',em.mem_read(a,4))[0]==val for a,val in metadata.items()),'produced allocation metadata changed')
            if mode!='miss':require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==(0x40 if mode=='hit' else 0x81),'signature compare flags')
            require(len(pcs)<=(5331 if mode=='miss' else 5322),'proved step bound exceeded')
            cases.append(dict(alignment=alignment,previous_free=previous_free,excess=excess,wrapping_stack=wrapping,
                              mode=mode,instructions=len(pcs),head_count=heads,word_tail=words%4))
    return dict(cases=len(cases),modes={m:sum(c['mode']==m for c in cases) for m in ['miss','hit','bad_signature']},
      formal_cases=sum(c['mode']!='bad_signature' for c in cases),all_registers=True,ordered_writes=True,full_mapped_data=True,
      output_zero=True,produced_allocation_metadata=True,caller_flags=True,hit_signature_flags=True,miss_final_flags=False,
      head_counts=sorted({c['head_count'] for c in cases}),word_tails=sorted({c['word_tail'] for c in cases}),details=cases,
      scope='Constructed original directory/cache/heap placements. Uninterrupted original entry through full memset, cache CALL/dispatcher; miss stops at the second actual malloc request, hit at tag request. Bad-signature error-entry cases are empirical only. Neither initial cache branch nor heap placement is proved to arise from pinned earlier DOS startup history. No allocator/tag helper completion or filesystem read.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    out=ROOT/'artifacts/e1m1-aim-cache-call';out.mkdir(exist_ok=True)
    (out/'Checked.lean').write_text(certificate())
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(out/'Checked.lean')],cwd=ROOT,capture_output=True,text=True,timeout=300)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout);require(not checked.stderr.strip(),'unexpected stderr')
    native=None
    if args.cross_check:
        native=cross_check();(out/'cross-check.json').write_text(json.dumps(native,indent=2)+'\n')
    elif (out/'cross-check.json').exists(): native=json.loads((out/'cross-check.json').read_text())
    prior=json.loads((ROOT/'artifacts/e1m1-aim-word-aligned/report.json').read_text())
    _,new,profile=cache_data();units=dict(prior['units']);units.update({'cache_'+k:v for k,v in new.items()})
    unique={(int(v['code_offset'],16),len(bytes.fromhex(v['hex']))) for v in units.values()}
    audits=re.findall(r"^'([^']+)'",checked.stdout,re.M)
    report=dict(exe_sha256=profile['exe_sha256'],wad_sha256=prior['wad_sha256'],units=units,unique_ranges=len(unique),
        public_theorems=len(contracts()),audited_declarations=len(audits),unique_audited_declarations=len(set(audits)),cross_check=native,
        scope='Continuous actual original entry to cache dispatcher, selected by the preserved original cache cell. Miss proves full real length CALL/RET and malloc CALL with19440/tag1/owner cache+36 in≤5331steps. Conditional original valid hit proves signature guard and tag CALL in≤5322steps. Complete11664 zero-output and produced first-allocation metadata frames. No second allocation/tag helper return, filesystem read, cache history, gate/side-loop join or initialized startup claim.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: original-state cache CALL/dispatcher and connected real miss/hit helper requests; startup incomplete.')
if __name__=='__main__': main()
