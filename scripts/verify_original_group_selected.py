#!/usr/bin/env python3
"""Certify original candidate acceptance, block splitting and joined grouping entry."""
import argparse,json,re,subprocess
import verify_original_group_handoff as handoff
ROOT,require,extraction=handoff.ROOT,handoff.require,handoff.extraction
NS='Doom.Verification.ExtractedGroupSelected.'
NAMES=handoff.NAMES+[NS+n for n in ['split_bytes','program_checked','selected_checked']]
for module,names in [
 ('OriginalGroupSplit',['decoded','candidate_execution','execution','frame','registers','result_pc','byte_partition','no_split_memory','split_memory']),
 ('OriginalGroupSelected',['split_agrees','handoff_agrees','picked_candidate','selected_execution','allocated_registers','allocated_frame','execution','frame','inputs','count_field'])]:
 NAMES+=['Doom.Proofs.'+module+'.'+n for n in names]
def certificate(raw):
 s=handoff.certificate(raw).replace('import Doom.Proofs.OriginalGroupHandoff','import Doom.Proofs.OriginalGroupSelected')
 s+='namespace Doom.Verification.ExtractedGroupSelected\nopen X86 X86Memory X86Control Doom.Proofs\n'
 s+='def split : List UInt8 := ['+','.join(hex(b) for b in raw['select_split'])+']\n'
 s+='''theorem split_bytes : split=OriginalGroupSplit.splitBytes := by decide +kernel
def program : X86Routine.Program := fun pc =>
  if 0x396f8≤pc ∧ pc<0x39731 then OriginalGroupSplit.bytesProgram split pc
  else ExtractedGroupHandoff.program pc
theorem program_checked : program=OriginalGroupSelected.program := by
  unfold program
  rw [split_bytes,ExtractedGroupHandoff.program_checked]; rfl
theorem selected_checked (s : X86Memory.State) (f : Option Flags)
    (free : load32 s.memory (s.regs 3+(4#32))=(0#32))
    (fits : (s.regs 1).toInt≤(OriginalGroupSplit.candidateSize s).toInt)
    (user : s.regs 7=(0#32)) (tag : s.regs 5=(50#32))
    (safe : OriginalGroupSelected.ReturnSafe s)
    (ret : load32 s.memory (s.regs 4+16)=0x2e63e) :
    X86Routine.run program [0x2e661,0x2e791] 53 ⟨s,f,0x396f8⟩=
      some (OriginalGroupSelected.result s) := by
  rw [program_checked]
  exact OriginalGroupSelected.execution s f free fits user tag safe ret
'''
 return s+'\n'.join('#print axioms '+n for n in NAMES[len(handoff.NAMES):])+'\nend Doom.Verification.ExtractedGroupSelected\n'
def audit(output):
 rest=output.strip()
 for name in NAMES:
  m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
  require(m is not None,'missing audit: '+name)
  axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
  require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms))
  rest=rest[m.end():].strip()
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
    # Candidate sizes around the split threshold, occupied candidates, and wrapping stacks.
    for alignment in range(4):
      for block_size in [2591,2592,2655,2656,2657,4096,0x80000000]:
       for wrapping in [False,True]:
        for owner in [0,2]:
            count=85
            em = uc.Uc(uc.UC_ARCH_X86,uc.UC_MODE_32)
            regions = [(0,0x80000),(0x610000,0x1000),(0x620000,0x1000),
                       (0x630000,0x10000),(0x680000,0x2000),(0xfffff000,0x1000)]
            memory = {}
            for base,size in regions:
                em.mem_map(base,size)
                memory[base] = bytearray(size)
            em.mem_map(code,0x40000)
            for name,offset in [('select_split',0x396f8),('allocation',0x39731),('entry',0x2e63e),('clear',0x241c0)]:
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
            block = 0x620000+alignment
            sp = (0xffffffec if wrapping else 0x680800)+alignment
            initial = [rng.getrandbits(32) for _ in regs]
            initial[1]=2592;initial[3]=block;initial[4]=sp;initial[5]=50;initial[7]=0
            write(0x74fe0,0x610000)
            write(block,block_size);write(block+4,owner);write(block+16,0x620f00)
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
            for i in range(4): write(sp+4*i,rng.getrandbits(32))
            write(sp+16,code+0x2e63e)
            for base,buf in memory.items():em.mem_write(base,bytes(buf))
            for reg,value in zip(regs,initial):em.reg_write(reg,value)
            em.reg_write(x.UC_X86_REG_EFLAGS,0x202)
            expected = initial.copy(); writes=[]
            def store(address,value):
                writes.append((address&mask,4,value&mask));write(address,value)
            signed=lambda v: v if v<0x80000000 else v-2**32
            def cmp_flags(a,b):
                v=(a-b)&mask
                return (0x40 if v==0 else 0)|(v>>24&0x80)|(1 if a<b else 0)|(0x800 if ((a^b)&(a^v)&0x80000000) else 0)
            accepted=owner==0 and signed(initial[1])<=signed(block_size)
            split=False
            if owner==0:expected[0]=block_size
            if accepted:
                extra=(block_size-initial[1])&mask
                expected[2]=extra
                split=signed(extra)>64
                if split:
                    remainder=(block+initial[1])&mask
                    expected[0]=remainder
                    store(remainder+4,0);store(remainder+8,0);store(remainder,extra)
                    store(remainder+20,block)
                    expected[2]=read(block+16)
                    store(remainder+16,expected[2]);store(expected[2]+20,remainder)
                    store(block+16,remainder);store(block,initial[1])
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
            em.emu_start(code+0x396f8,code+stop,count=60)
            require(em.reg_read(x.UC_X86_REG_EIP)==code+stop,'wrong exit')
            require(len(pcs)==((53 if split else 43) if accepted else (2 if owner else 5)),'wrong instruction count')
            require([em.reg_read(r) for r in regs]==expected,'register mismatch')
            flags=0 if accepted else cmp_flags(owner,0) if owner else cmp_flags(initial[1],block_size)
            require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==flags,'modeled flag mismatch')
            require(actual_writes==writes,'ordered write mismatch')
            for base,buf in memory.items():require(bytes(em.mem_read(base,len(buf)))==bytes(buf),'memory mismatch')
            for address,value in fields:require(read(address)==value,'count/pointer changed')
            preserved+=len(fields);cases+=1
    return dict(cases=cases,outcomes=outcomes,preserved_count_and_pointer_words=preserved,
                comparisons=['registers','modeled flags','ordered writes','mapped data memory','exit','instruction count'],
                scope='Candidate gate including rejection, split/no-split and joined actual returns; 85 counts and 950 cached pointers preserved in every case. No search-loop reachability claim.')

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
 profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
 binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
 spec=json.loads((ROOT/'tests/reference/original-group-split.json').read_text())
 raw=extraction.extract(binary,profile,spec)
 raw.update(extraction.extract(binary,profile,json.loads((ROOT/'tests/reference/original-group-handoff.json').read_text())))
 out=ROOT/'artifacts/original-group-selected';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
 with (out/'build.log').open('w') as log:
  subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalGroupSelected'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
 path=out/'Checked.lean';path.write_text(certificate(raw))
 r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True,timeout=90)
 if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
 audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
 native=cross_check(raw) if args.cross_check else None
 (out/'report.json').write_text(json.dumps(dict(exe_sha256=profile['exe_sha256'],audited_declarations=len(NAMES),axioms=r.stdout.splitlines(),cross_check=native,scope=spec['scope']),indent=2)+'\n')
 print(r.stdout,end='');print('PASS: candidate acceptance, exact split/no-split and joined allocator return/grouping entry.')
if __name__=='__main__':main()
