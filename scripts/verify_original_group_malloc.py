#!/usr/bin/env python3
"""Bind counting, allocator entry/first-free path and grouping return to original bytes."""
import argparse,json,re,subprocess
import verify_original_group_selected as selected
ROOT,require,extraction=selected.ROOT,selected.require,selected.extraction
NS='Doom.Verification.ExtractedGroupMalloc.'
NAMES=selected.NAMES+[NS+n for n in ['call_bytes','entry_bytes','count_bytes','program_checked','startup_program_checked','malloc_checked','startup_checked']]
for module,names in [
 ('OriginalGroupMallocEntry',['decoded','byte_mask','byte_mask_normal','call_execution','save_execution','prepare_execution','free_execution','prepared_memory','saved_register','saved_stack','saved_frame','request_e1m1']),
 ('OriginalGroupMalloc',['entry_agrees','selected_agrees','prefix_execution','candidate_memory','candidate_arguments','saved_top','return_address','candidate_free','execution','frame','count_field','inputs']),
 ('OriginalGroupStartup',['count_agrees','malloc_agrees','execution','sector_count','cached_inputs'])]:
 NAMES+=['Doom.Proofs.'+module+'.'+n for n in names]
def certificate(raw):
 s=selected.certificate(raw).replace('import Doom.Proofs.OriginalGroupSelected','import Doom.Proofs.OriginalGroupStartup')
 s+='namespace Doom.Verification.ExtractedGroupMalloc\nopen X86 X86Memory X86Control Doom.Proofs\n'
 for name,key,original in [('call','call','OriginalGroupMallocEntry.callBytes'),('entry','malloc_entry','OriginalGroupMallocEntry.entryBytes'),('count','count','OriginalGroupCount.countBytes')]:
  s+=f'def {name} : List UInt8 := ['+','.join(hex(b) for b in raw[key])+']\n'
  s+=f'theorem {name}_bytes : {name}={original} := by decide +kernel\n'
 s+='''def program : X86Routine.Program := fun pc =>
  if (0x2e639≤pc ∧ pc<0x2e63e) ∨ (0x39690≤pc ∧ pc<0x396f8)
  then OriginalGroupMallocEntry.bytesProgram call entry pc else ExtractedGroupSelected.program pc
theorem program_checked : program=OriginalGroupMalloc.program := by
  unfold program
  rw [call_bytes,entry_bytes,ExtractedGroupSelected.program_checked]; rfl
def startupProgram : X86Routine.Program := fun pc =>
  if 0x2e5ef≤pc ∧ pc<0x2e639 then OriginalGroupCount.bytesProgram count pc else program pc
theorem startup_program_checked : startupProgram=OriginalGroupStartup.program := by
  unfold startupProgram
  rw [count_bytes,program_checked]; rfl
theorem malloc_checked (s : X86Memory.State) (f : Option Flags) (h : OriginalGroupMalloc.Ready s)
    (user : s.regs 3=(0#32)) (tag : s.regs 2=(50#32)) :
    X86Routine.run program [0x2e661,0x2e791] 78 ⟨s,f,0x2e639⟩=some (OriginalGroupMalloc.result s) := by
  rw [program_checked]
  exact OriginalGroupMalloc.execution s f h user tag

theorem startup_checked (es : List OriginalGroupOutput.Line) (s : X86Memory.State) (f : Option Flags)
    (small : es.length<2147483648) (layout : OriginalGroupCountScan.Layout es)
    (inputs : OriginalGroupOutput.Inputs es s.memory)
    (linked : OriginalGroupOutput.Linked es (load32 s.memory 0x2c120))
    (count : (load32 s.memory 0x2c134).toNat=es.length)
    (heap : OriginalGroupMalloc.Ready (OriginalGroupCountScan.final es s).core) :
    X86Routine.run startupProgram [0x2e661,0x2e791] (87+17*es.length) ⟨s,f,0x2e5ef⟩=
      some (OriginalGroupStartup.result es s) := by
  rw [startup_program_checked]
  exact OriginalGroupStartup.execution es s f small layout inputs linked count heap
'''
 return s+'\n'.join('#print axioms '+n for n in NAMES[len(selected.NAMES):])+'\nend Doom.Verification.ExtractedGroupMalloc\n'
def audit(output):
 rest=output.strip()
 for name in NAMES:
  m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
  require(m is not None,'missing audit: '+name)
  axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
  require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
 require(not rest,'unexpected certificate output')

def cross_check(raw):
    """Independent x86 diagnostics; not a proof of heap-search reachability."""
    import random
    import unicorn as uc
    from unicorn import x86_const as x
    import verify_original_noise_topology as topology
    data, _ = topology.pinned_data()
    mask = 2**32-1
    code = 0x100000
    rng = random.Random(0x39731)
    regs = [x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
            x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    cases = 0
    outcomes = dict(rejected=0,split=0,unsplit=0)
    preserved = 0
    # Suitable first free blocks around the split threshold, and wrapping stacks.
    for alignment in range(4):
      for request in [0,1,3,4,2565,2568,2569,0xfffffffc,0xfffffffd,0xffffffff]:
       for wrapping in [False,True]:
        for previous_free,excess in [(p,e) for p in [False,True] for e in [0,64,65]]:
            count=85
            block_request=(((request+3)&mask)&0xfffffffc)+24
            block_request &= mask
            block_size=block_request+excess
            owner=0
            em = uc.Uc(uc.UC_ARCH_X86,uc.UC_MODE_32)
            regions = [(0,0x80000),(0x610000,0x1000),(0x620000,0x3000),
                       (0x630000,0x10000),(0x680000,0x2000),(0xfffff000,0x1000)]
            memory = {}
            for base,size in regions:
                em.mem_map(base,size)
                memory[base] = bytearray(size)
            em.mem_map(code,0x40000)
            for name,offset in [('call',0x2e639),('malloc_entry',0x39690),('select_split',0x396f8),('allocation',0x39731),('entry',0x2e63e),('clear',0x241c0)]:
                em.mem_write(code+offset,raw[name])
            def byte_at(address):
                address &= mask
                for base,buf in memory.items():
                    if base<=address<base+len(buf): return buf,address-base
                raise ValueError('unmapped expected address '+hex(address))
            def write(address,value):
                for i in range(4):
                    buf,j = byte_at(address+i);buf[j]=(value>>(8*i))&255
            def read(address):
                return sum(byte_at(address+i)[0][byte_at(address+i)[1]]<<(8*i) for i in range(4))
            rover=0x620000+alignment;previous=0x621000+alignment
            block=previous if previous_free else rover
            caller_sp = (8 if wrapping else 0x680800)+alignment
            sp=(caller_sp-20)&mask
            initial = [rng.getrandbits(32) for _ in regs]
            initial[0]=request;initial[2]=50;initial[3]=0;initial[4]=caller_sp
            write(0x74fe0,0x610000)
            write(0x61001c,rover);write(rover+20,previous);write(previous+20,0x622000)
            write(previous+4,0 if previous_free else 2)
            write(block,block_size);write(block+4,owner);write(block+16,0x622100)
            write(0x2c148,0x630000);write(0x2c14c,count)
            write(0x2c120,0x632000);write(0x2c134,475)
            fields = []
            for i,row in enumerate(data['rows']):
                address=0x630000+96*i+78;write(address,len(row));fields.append((address,len(row)))
            # Both cached sector-pointer fields of every pinned linedef.
            for i,line in enumerate(data['lines']):
                for offset,key in [(46,4),(50,5)]:
                    value=0 if key==5 and line[3]==65535 else 0x630000+96*line[key]
                    address=0x632000+62*i+offset;write(address,value);fields.append((address,value))
            for base,buf in memory.items():em.mem_write(base,bytes(buf))
            for reg,value in zip(regs,initial):em.reg_write(reg,value)
            em.reg_write(x.UC_X86_REG_EFLAGS,0x202)
            expected = initial.copy(); writes=[]
            def store(address,value):
                writes.append((address&mask,4,value&mask));write(address,value)
            # Execute the actual CALL and prologue in the independent model.
            store(caller_sp-4,code+0x2e63e)
            for offset,reg in [(8,1),(12,6),(16,7),(20,5)]:store(caller_sp-offset,initial[reg])
            expected[4]=sp;expected[5]=initial[2];expected[7]=initial[3]
            selected_rover=read(read(0x74fe0)+28)
            selected_previous=read(selected_rover+20)
            previous_owner=read(selected_previous+4)
            expected[0]=selected_previous;expected[1]=block_request
            expected[3]=selected_previous if previous_owner==0 else selected_rover
            expected[2]=expected[3];expected[6]=read(expected[3]+20)
            require(expected[2]!=expected[6] and read(expected[2]+4)==0,'first-free diagnostic precondition')
            expected[2]=read(expected[2]+16)
            signed=lambda v: v if v<0x80000000 else v-2**32
            def cmp_flags(a,b):
                v=(a-b)&mask
                return (0x40 if v==0 else 0)|(v>>24&0x80)|(1 if a<b else 0)|(0x800 if ((a^b)&(a^v)&0x80000000) else 0)
            accepted=owner==0 and signed(block_request)<=signed(block_size)
            split=False
            if owner==0:expected[0]=block_size
            if accepted:
                extra=(block_size-block_request)&mask
                expected[2]=extra
                split=signed(extra)>64
                if split:
                    remainder=(block+block_request)&mask
                    expected[0]=remainder
                    store(remainder+4,0);store(remainder+8,0);store(remainder,extra)
                    store(remainder+20,block)
                    expected[2]=read(block+16)
                    store(remainder+16,expected[2]);store(expected[2]+20,remainder)
                    store(block+16,remainder);store(block,block_request)
                store(block+4,2)
                zone=read(0x74fe0);next_block=read(block+16)
                store(block+8,50);store(zone+28,next_block);store(block+12,0x1d4a11)
                expected[2]=zone;expected[0]=(block+24)&mask
                for i,reg in enumerate([5,7,6,1]):expected[reg]=read(sp+4*i)
                require(read(sp+16)==code+0x2e63e,'diagnostic saved-return overlap')
                caller_sp=(sp+20)&mask;expected[4]=caller_sp
                expected[5]=read(0x2c148);expected[6]=expected[0];expected[0]=0;expected[2]=read(0x2c14c)
                store(caller_sp+16,0)
                positive=0<expected[2]<0x80000000
                if positive:
                    expected[0]=caller_sp
                    store(caller_sp-4,code+0x2e661);store(caller_sp-8,expected[2])
                    store(caller_sp+12,0x80000000);store(caller_sp+8,0x7fffffff)
                    store(caller_sp,read(caller_sp+12));store(caller_sp+4,read(caller_sp+8))
                    expected[2]=read(caller_sp-8)
            outcomes['split' if split else 'unsplit' if accepted else 'rejected']+=1
            actual_writes=[];pcs=[]
            em.hook_add(uc.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_u: actual_writes.append((a,n,v&mask)))
            em.hook_add(uc.UC_HOOK_CODE,lambda _e,a,_n,_u: pcs.append(a-code))
            stop=0x2e661 if accepted else 0x396bd
            em.emu_start(code+0x2e639,code+stop,count=85)
            require(em.reg_read(x.UC_X86_REG_EIP)==code+stop,'wrong exit')
            require(len(pcs)==(53 if split else 43)+(25 if previous_free else 24),'wrong instruction count')
            require([em.reg_read(r) for r in regs]==expected,'register mismatch')
            flags=0 if accepted else cmp_flags(owner,0) if owner else cmp_flags(initial[1],block_size)
            require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==flags,'modeled flag mismatch')
            require(actual_writes==writes,'ordered write mismatch')
            for base,buf in memory.items():require(bytes(em.mem_read(base,len(buf)))==bytes(buf),'memory mismatch')
            for address,value in fields:require(read(address)==value,'count/pointer changed')
            preserved+=len(fields);cases+=1
    return dict(cases=cases,outcomes=outcomes,preserved_count_and_pointer_words=preserved,
                comparisons=['registers','modeled flags','ordered writes','mapped data memory','exit','instruction count'],
                scope='Actual CALL through prologue, first-free traversal, split and both returns. Both predecessor choices, rounding/wrap boundaries and split threshold; no general search/purge or heap-reachability claim.')

def extracted():
 profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
 binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
 spec=json.loads((ROOT/'tests/reference/original-group-malloc.json').read_text())
 raw=extraction.extract(binary,profile,spec);raw['malloc_entry']=raw.pop('entry')
 for name in ['original-group-handoff','original-group-split','original-group-count']:
  raw.update(extraction.extract(binary,profile,json.loads((ROOT/f'tests/reference/{name}.json').read_text())))
 return raw,profile,spec
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
 raw,profile,spec=extracted()
 out=ROOT/'artifacts/original-group-malloc';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
 with (out/'build.log').open('w') as log:
  subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalGroupStartup'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
 path=out/'Checked.lean';path.write_text(certificate(raw))
 r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True,timeout=90)
 if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
 audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
 native=cross_check(raw) if args.cross_check else None
 (out/'report.json').write_text(json.dumps(dict(exe_sha256=profile['exe_sha256'],audited_declarations=len(NAMES),axioms=r.stdout.splitlines(),cross_check=native,scope=spec['scope']),indent=2)+'\n')
 print(r.stdout,end='');print('PASS: actual allocator CALL/prologue/first-free allocation through grouping entry, composed with counting.')
if __name__=='__main__':main()
