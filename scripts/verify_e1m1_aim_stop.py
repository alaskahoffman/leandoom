#!/usr/bin/env python3
"""Certify original aim tag/wall guards, false return, and traversal stop."""
import argparse,json,re,subprocess
import verify_e1m1_query_callback as previous
import verify_original_inline_thrust as extraction
ROOT,require=previous.ROOT,previous.require
pinned_data=previous.pinned_data
GROUPS={'OriginalAimGuard':['decoded','entry_execution','line_execution','stop_execution'],
 'E1M1AimSource':['live','first_wall','blocked_query'],
 'E1M1AimWall':['saved_memory','saved_frame','saved_byte','return_safe','entry_record','returned_fields','execution'],
 'E1M1AimStop':['contains_prior','contains_guard','execution','from_ready','correspondence']}

def extracted():
    spec,profile,raw=previous.extracted()
    part=json.loads((ROOT/'tests/reference/original-aim-guard.json').read_text())
    share=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
    require(not(set(part['units'])&set(spec['units'])),'duplicate aim range')
    raw.update(extraction.extract(binary,profile,part))
    return dict(units={**spec['units'],**part['units']}),profile,raw

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimStop\n'+previous.certificate(data,raw)
    source+='''
namespace Doom.Verification.ExtractedAimStop
set_option backward.isDefEq.respectTransparency false
open Doom Doom.Proofs X86 X86Memory X86Control
open E1M1AimWall (Safe)
open E1M1AimStop (result)
'''
    for name,unit,const in [('head','aimGuard','guardCode'),('tail','aimStop','stopCode')]:
        source+=f'def {name} : List UInt8 := ['+','.join(hex(b) for b in raw[unit])+']\n'
        source+=f'theorem {name}_checked : {name}=OriginalAimGuard.{const} := by decide\n'
    source+='''def guard := OriginalAimGuard.bytesProgram head tail
theorem guard_checked : guard=OriginalAimGuard.program := by
  simp only [guard,head_checked,tail_checked,OriginalAimGuard.program]
def linked : X86Routine.Program := fun pc =>
  match ExtractedQueryDispatch.linked pc with
  | some op => some op
  | none => guard pc
theorem linked_checked : linked=E1M1AimStop.program := by
  unfold linked E1M1AimStop.program
  rw [ExtractedQueryDispatch.program_checked, guard_checked]
  rfl
'''
    text=(ROOT/'Doom/Proofs/E1M1AimStop.lean').read_text();a=text.index('theorem execution ')
    decl=text[a:text.index(' := by',a)].replace('theorem execution','theorem execution_checked',1).replace('FloorCaller.cm program','FloorCaller.cm linked')
    source+=decl+' := by\n  rw [linked_checked]\n  exact E1M1AimStop.execution s hit pointer entry returnWord record isLine tagSafe pointerSafe flagsSafe oneSided\n'
    source+='\n'.join('#print axioms '+n for n in ['head_checked','tail_checked','guard_checked','linked_checked','execution_checked'])+'\nend Doom.Verification.ExtractedAimStop\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedAimStop.head_checked'"
    require(marker in output,'missing aim stop audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedAimStop.'+n for n in ['head_checked','tail_checked','guard_checked','linked_checked','execution_checked']]
    names+=['Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]
    for full in names:
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw,count=384):
    import random,struct,unicorn as u
    from unicorn import x86_const as x
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
    for base,size in [(0,0x40000),(0x100000,0x40000),(0x600000,0x1000),(0x700000,0x1000),(0xfffff000,0x1000)]:em.mem_map(base,size)
    for name,pc in [('aimGuard',0x2b760),('aimStop',0x2b8d2),('interceptGate',0x2c85e)]:em.mem_write(0x100000+pc,raw[name])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    rng=random.Random(0x2b760);writes=[];steps=[];mask=0xffffffff
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda *a:writes.append((a[2],a[3],a[4])))
    stop_at=[None]
    def on_code(machine,address,size,data):
        if address==stop_at[0]:machine.emu_stop()
        else:steps.append(address)
    em.hook_add(u.UC_HOOK_CODE,on_code)
    pack=lambda v:struct.pack('<I',v)
    groups=dict(thing=0,one_sided_stop=0,two_sided_continue=0,wrapping_stack=0)
    for case in range(count):
        mode=case%3;sp=[0x700800,0,4,8,16,0xfffffff0][(case//3)%6]
        before=[rng.getrandbits(32) for _ in regs];before[0]=0x600100;before[4]=sp
        tag=0 if mode==0 else [1,0xffffffff][case%2]
        flags=rng.randrange(256)&~4
        if mode==2:flags|=4
        record=struct.pack('<III',rng.getrandbits(32),tag,0x600200)
        em.mem_write(0x600100,record);em.mem_write(0x600210,bytes([flags]))
        em.mem_write(sp,pack(0x12c86d));cursor=0x2ba20+12*(case%129);em.mem_write(0x2c028,pack(cursor))
        for reg,val in zip(regs,before):em.reg_write(reg,val)
        em.reg_write(x.UC_X86_REG_EFLAGS,2);writes.clear();steps.clear()
        end=0x12b81a if mode==0 else 0x12b77f if mode==2 else 0x12c86d
        stop_at[0]=end
        em.emu_start(0x12b760,end,count=25)
        expected=list(before);expected[2]=before[0];expected[4]=(sp-24)&mask
        if mode:expected[1]=0x600200
        if mode==1:expected=list(before);expected[0]=0;expected[4]=(sp+4)&mask
        require(em.reg_read(x.UC_X86_REG_EIP)==end,f'callback exit mismatch case={case} mode={mode} sp={sp:#x}: got={em.reg_read(x.UC_X86_REG_EIP):#x} expected={end:#x} steps={steps}')
        require([em.reg_read(r) for r in regs]==expected,'callback registers mismatch')
        require(len(steps)==[9,20,12][mode],'callback instruction count mismatch')
        expected_flags=0x44 if mode in (0,1) else 0
        require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c5==expected_flags,'callback modeled flags mismatch')
        expected_writes=[((sp-4*(i+1))&mask,4,before[r]) for i,r in enumerate([3,1,2,6,7,5])]
        require(writes==expected_writes,'callback stack writes mismatch')
        require(bytes(em.mem_read(sp,4))==pack(0x12c86d),'return word changed')
        require(bytes(em.mem_read(0x600100,12))==record,'record changed')
        if mode==1:
            stop_at[0]=0x12c88c
            em.emu_start(end,0x12c88c,count=5);expected[1]=cursor
            require(em.reg_read(x.UC_X86_REG_EIP)==0x12c88c,'parent stop exit mismatch')
            require([em.reg_read(r) for r in regs]==expected,'parent stop registers mismatch')
            require(len(steps)==24 and writes==expected_writes,'parent stop steps/writes mismatch')
            require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c5==0x44,'parent stop modeled flags mismatch')
        groups[['thing','one_sided_stop','two_sided_continue'][mode]]+=1
        groups['wrapping_stack']+=sp<24
    require(all(groups.values()),'missing guard coverage')
    return dict(cases=count,groups=groups,callbacks_or_stubs=False,
                scope='Actual callback entry through type/line guard or full one-sided return and traversal stop; no open-portal or actor body execution.')

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();require(mp['exe_sha256']==profile['exe_sha256'],'profile mismatch')
    out=ROOT/'artifacts/e1m1-aim-stop';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimStop'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Authentic aim callback tag/line guard; full one-sided wall false return and parent traversal stop. '
      'Live source extraction and first-wall result checked. Joined to prior reached callback records and return word, '
      'with map flag encoding, ordered first-hit relation and prologue separation explicit. '
      'Open-portal clipping, actors, repeated selection, full query/caller return and reachable-state discharge remain open. '
      'No runtime, decoder or instruction-semantics change.')
    if args.cross_check:report['cross_check']=cross_check(raw)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: original aim wall guard, real return and traversal stop; live source and strict axiom audit.')
if __name__=='__main__':main()
