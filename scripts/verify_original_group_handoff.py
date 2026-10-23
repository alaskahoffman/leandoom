#!/usr/bin/env python3
"""Certify selected-block allocation tail and the actual grouping-entry helper."""
import argparse
import json
import re
import subprocess
import verify_original_inline_thrust as extraction

ROOT, require = extraction.ROOT, extraction.require
NS = 'Doom.Verification.ExtractedGroupHandoff.'
NAMES = [NS+n for n in ['allocation_bytes','entry_bytes','clear_bytes','program_checked','handoff_checked']]
for module, names in [
    ('OriginalGroupAllocation', ['decoded','execution','frame','returned_frame','returned_registers','return_pc','from_initial']),
    ('OriginalGroupEntry', ['decoded','clear_execution','execution','frame','registers','positive_pc','box_ready']),
    ('OriginalGroupHandoff', ['allocation_agrees','entry_agrees','execution','frame','registers','positive_pc','inputs','count_field'])]:
    NAMES += ['Doom.Proofs.'+module+'.'+n for n in names]


def certificate(raw):
    source = '''import Doom.Proofs.OriginalGroupHandoff
namespace Doom.Verification.ExtractedGroupHandoff
open X86 X86Memory X86Control Doom.Proofs
'''
    for key, original in [('allocation','OriginalGroupAllocation.allocationBytes'),
                          ('entry','OriginalGroupEntry.entryBytes'),('clear','OriginalGroupEntry.clearBytes')]:
        source += f'def {key} : List UInt8 := ['+','.join(hex(b) for b in raw[key])+']\n'
        source += f'theorem {key}_bytes : {key}={original} := by decide +kernel\n'
    source += '''def program : X86Routine.Program := fun pc =>
  if 0x39731≤pc ∧ pc<0x39776 then OriginalGroupAllocation.bytesProgram allocation pc
  else OriginalGroupEntry.bytesProgram entry clear pc
theorem program_checked : program=OriginalGroupHandoff.program := by
  unfold program
  rw [allocation_bytes,entry_bytes,clear_bytes]; rfl
/-- Premises are at the selected-block boundary, before metadata writes. -/
theorem handoff_checked (s : X86Memory.State) (f : Option Flags)
    (user : s.regs 7=(0#32)) (tag : s.regs 5=(50#32))
    (safe : OriginalGroupAllocation.SafeWord (s.regs 4+16) s)
    (ret : load32 s.memory (s.regs 4+16)=0x2e63e) :
    X86Routine.run program [0x2e661,0x2e791] 34 ⟨s,f,0x39731⟩=
      some (OriginalGroupHandoff.result s) := by
  rw [program_checked]
  exact OriginalGroupHandoff.execution s f user tag safe ret
'''
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedGroupHandoff\n'


def audit(output):
    rest = output.strip()
    for name in NAMES:
        match = re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing axiom audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext','Quot.sound','Classical.choice'}, 'unexpected proof axioms: '+str(axioms))
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


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
    preserved = 0
    # Positive, zero and signed-negative sector counts; unaligned and wrapping stacks.
    for alignment in range(4):
      for count in [0,1,85,0x80000000,0xffffffff]:
       for wrapping in [False,True]:
        for alias in [False,True]:
            em = uc.Uc(uc.UC_ARCH_X86,uc.UC_MODE_32)
            regions = [(0,0x80000),(0x610000,0x1000),(0x620000,0x1000),
                       (0x630000,0x10000),(0x680000,0x2000),(0xfffff000,0x1000)]
            memory = {}
            for base,size in regions:
                em.mem_map(base,size)
                memory[base] = bytearray(size)
            em.mem_map(code,0x40000)
            for name,offset in [('allocation',0x39731),('entry',0x2e63e),('clear',0x241c0)]:
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
            block = 0x74fdc if alias else 0x620000+alignment
            sp = (0xffffffec if wrapping else 0x680800)+alignment
            initial = [rng.getrandbits(32) for _ in regs]
            initial[3]=block;initial[4]=sp;initial[5]=50;initial[7]=0
            write(0x74fe0,0x610000)
            write(block+16,0x620100)
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
            actual_writes=[];pcs=[]
            em.hook_add(uc.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_u: actual_writes.append((a,n,v&mask)))
            em.hook_add(uc.UC_HOOK_CODE,lambda _e,a,_n,_u: pcs.append(a-code))
            stop=0x2e661 if positive else 0x2e791
            em.emu_start(code+0x39731,code+stop,count=40)
            require(em.reg_read(x.UC_X86_REG_EIP)==code+stop,'wrong exit')
            require(len(pcs)==(34 if positive else 23),'wrong instruction count')
            require([em.reg_read(r) for r in regs]==expected,'register mismatch')
            flags=(0x40 if count==0 else 0)|(0x80 if count&0x80000000 else 0)
            require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==flags,'modeled flag mismatch')
            require(actual_writes==writes,'ordered write mismatch')
            for base,buf in memory.items():require(bytes(em.mem_read(base,len(buf)))==bytes(buf),'memory mismatch')
            for address,value in fields:require(read(address)==value,'count/pointer changed')
            preserved+=len(fields);cases+=1
    return dict(cases=cases,preserved_count_and_pointer_words=preserved,
                comparisons=['registers','modeled flags','ordered writes','mapped data memory','exit','instruction count'],
                scope='Selected-block tail through both actual RETs; all cases preserve 85 counts and 950 cached pointers. No heap-search reachability claim.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cross-check', action='store_true')
    args = parser.parse_args()
    profile = json.loads((ROOT/'tests/reference/original-mul.json').read_text())
    sw = json.loads((ROOT/'tests/reference/shareware.json').read_text())
    spec = json.loads((ROOT/'tests/reference/original-group-handoff.json').read_text())
    binary = extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip', sw, profile)
    raw = extraction.extract(binary, profile, spec)
    out = ROOT/'artifacts/original-group-handoff'; out.mkdir(parents=True, exist_ok=True)
    (out/'report.json').unlink(missing_ok=True)
    with (out/'build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalGroupHandoff'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    path = out/'Checked.lean'; path.write_text(certificate(raw))
    result = subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True,timeout=90)
    if result.returncode:
        print(result.stdout); print(result.stderr); result.check_returncode()
    audit(result.stdout); require(not result.stderr.strip(), 'unexpected stderr')
    native = cross_check(raw) if args.cross_check else None
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=profile['exe_sha256'],
        audited_declarations=len(NAMES),axioms=result.stdout.splitlines(),cross_check=native,
        scope=spec['scope']),indent=2)+'\n')
    print(result.stdout,end='')
    print('PASS: selected-block allocator return and grouping entry, with preserved counts/pointers under explicit separation.')

if __name__ == '__main__':
    main()
