#!/usr/bin/env python3
"""Check DOS aiming's real opening call, helper, return and signed height gate."""
import argparse,json,re,subprocess
import verify_e1m1_aim_stop as previous
import verify_original_inline_thrust as extraction
ROOT,require=previous.ROOT,previous.require
pinned_data=previous.pinned_data
GROUPS={
 'OriginalAimOpening':['decoded','call_execution','gate_execution'],
 'E1M1OpeningHeights':['saved_frame','saved_half','heights'],
 'E1M1AimOpening':['contains_call','contains_helper','contains_guard','helper_return','execution','decision','from_callback','height_decision'],
 'E1M1AimPortalSource':['first_closed','blocked_query','signed_bounds','closed_correspondence']}

def extracted():
    spec,profile,raw=previous.extracted()
    part=json.loads((ROOT/'tests/reference/original-aim-opening.json').read_text())
    opening=json.loads((ROOT/'tests/reference/original-noise-opening.json').read_text())['units']['opening']
    part['units']['opening']=opening
    share=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
    require(not(set(part['units'])&set(spec['units'])),'duplicate opening range')
    raw.update(extraction.extract(binary,profile,part))
    return dict(units={**spec['units'],**part['units']}),profile,raw

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimPortalSource\n'+previous.certificate(data,raw)
    source+='''
namespace Doom.Verification.ExtractedAimOpening
set_option backward.isDefEq.respectTransparency false
open Doom Doom.Proofs X86 X86Memory X86Control
open E1M1AimOpening (result CallerSafe)
'''
    for name,unit,const in [('call','aimOpening','OriginalAimOpening.code'),('helper','opening','NoiseOpening.openingBytes')]:
        source+=f'def {name} : List UInt8 := ['+','.join(hex(b) for b in raw[unit])+']\n'
        source+=f'theorem {name}_checked : {name}={const} := by decide\n'
    source+='''def helperProgram : X86Routine.Program := fun pc =>
  if 0x2c340≤pc ∧ pc<0x2c3aa then NoiseOpening.bytesProgram helper NoiseOpening.neighborBytes pc
  else E1M1NoiseTraversal.program pc
theorem helper_checked : helperProgram=E1M1NoiseOpening.program := by
  unfold helperProgram E1M1NoiseOpening.program NoiseOpening.program
  rw [helper_checked]
def linked : X86Routine.Program := fun pc =>
  match OriginalAimOpening.bytesProgram call pc with
  | some op => some op
  | none => match OriginalAimGuard.program pc with
    | some op => some op
    | none => helperProgram pc
theorem linked_checked : linked=E1M1AimOpening.program := by
  unfold linked E1M1AimOpening.program OriginalAimOpening.program
  rw [call_checked, helper_checked]
'''
    # Give the byte equality and program equality distinct names.
    source=source.replace('theorem helper_checked : helperProgram','theorem helper_program_checked : helperProgram')
    source=source.replace('rw [call_checked, helper_checked]','rw [call_checked, helper_program_checked]\n  rfl')
    text=(ROOT/'Doom/Proofs/E1M1AimOpening.lean').read_text();a=text.index('theorem from_callback ')
    decl=text[a:text.index(' := by',a)].replace('theorem from_callback','theorem execution_checked',1).replace('FloorCaller.cm program','FloorCaller.cm linked')
    source+=decl+' := by\n  rw [linked_checked]\n  exact E1M1AimOpening.from_callback s f hit pointer record isLine tagSafe pointerSafe flagsSafe two helperSafe\n'
    names=['call_checked','helper_checked','helper_program_checked','linked_checked','execution_checked']
    source+='\n'.join('#print axioms '+n for n in names)+'\nend Doom.Verification.ExtractedAimOpening\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedAimOpening.call_checked'"
    require(marker in output,'missing aim opening audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedAimOpening.'+n for n in ['call_checked','helper_checked','helper_program_checked','linked_checked','execution_checked']]
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
    for name,pc in [('aimGuard',0x2b760),('aimOpening',0x2b77f),('opening',0x2c340)]:em.mem_write(0x100000+pc,raw[name])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    rng=random.Random(0x2b77f);mask=0xffffffff;writes=[];steps=[];stop=[None]
    signed=lambda v:v if v<2**31 else v-2**32
    pack=lambda v:struct.pack('<I',v&mask)
    def code(machine,address,size,data):
        if address==stop[0]:machine.emu_stop()
        else:steps.append(address)
    em.hook_add(u.UC_HOOK_CODE,code)
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda *a:writes.append((a[2],a[3],a[4])))
    groups=dict(closed=0,open=0,equal_bounds=0,negative_heights=0,wrapping_stack=0,subtraction_disagrees=0)
    edges=[0,1,0x7fffffff,0x80000000,0xffffffff,0x10000,0xffff0000]
    for case in range(count):
        sp=[0x700800,0,4,16,32,0xfffffff0][case%6]
        before=[rng.getrandbits(32) for _ in regs];before[0]=0x600100;before[4]=sp
        ff,fc,bf,bc=[rng.choice(edges) if case%2 else rng.getrandbits(32) for _ in range(4)]
        if case%8==0:ff=fc=bf=bc=edges[(case//8)%len(edges)]
        bottom=max(ff,bf,key=signed);top=min(fc,bc,key=signed);low=min(ff,bf,key=signed)
        closed=signed(bottom)>=signed(top);end=0x12b8d2 if closed else 0x12b797
        record=struct.pack('<III',rng.getrandbits(32),1,0x600200)
        em.mem_write(0x600100,record);em.mem_write(0x600210,bytes([rng.randrange(256)|4]))
        em.mem_write(0x600218,struct.pack('<H',case%32768));em.mem_write(0x60022e,pack(0x600300));em.mem_write(0x600232,pack(0x600400))
        for addr,value in [(0x600300,ff),(0x600304,fc),(0x600400,bf),(0x600404,bc),(sp,0x12c86d)]:em.mem_write(addr,pack(value))
        for reg,val in zip(regs,before):em.reg_write(reg,val)
        em.reg_write(x.UC_X86_REG_EFLAGS,2);writes.clear();steps.clear();stop[0]=end
        em.emu_start(0x12b760,end,count=49)
        expected=list(before);expected[0]=bottom;expected[1]=0x600200;expected[2]=0x600100;expected[4]=(sp-24)&mask
        require(em.reg_read(x.UC_X86_REG_EIP)==end,'opening exit mismatch')
        require([em.reg_read(r) for r in regs]==expected,'opening registers mismatch')
        require(len(steps)<=48,'opening bound mismatch')
        diff=(bottom-top)&mask;overflow=((bottom^top)&(bottom^diff)&0x80000000)!=0
        flags=(int(bottom<top)|((diff&255).bit_count()%2==0)*4|int(diff==0)*64|int(diff>>31)*128|int(overflow)*2048)
        require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c5==flags,'opening flags mismatch')
        expected_writes=[((sp-4*(i+1))&mask,4,before[r]) for i,r in enumerate([3,1,2,6,7,5])]
        expected_writes+=[((sp-28)&mask,4,0x12b786)]
        expected_writes += [((sp-off)&mask,4,value) for off,value in [(32,before[3]),(36,0x600200),(40,0x600100),(44,before[6])]]
        expected_writes += [(0x2c034,4,top),(0x2c030,4,bottom),(0x2c02c,4,low),(0x2c038,4,(top-bottom)&mask)]
        require(writes==expected_writes,'opening writes mismatch')
        for addr,value in [(0x2c034,top),(0x2c030,bottom),(0x2c02c,low),(0x2c038,(top-bottom)&mask),((sp-28)&mask,0x12b786),(sp,0x12c86d)]:
            require(bytes(em.mem_read(addr,4))==pack(value),'opening globals/return mismatch')
        require(bytes(em.mem_read(0x600100,12))==record,'hit record changed')
        groups['closed' if closed else 'open']+=1;groups['equal_bounds']+=bottom==top
        groups['negative_heights']+=any(signed(v)<0 for v in [ff,fc,bf,bc]);groups['wrapping_stack']+=sp<44
        groups['subtraction_disagrees']+=closed!=(signed((top-bottom)&mask)<=0)
    require(all(groups.values()),'missing opening coverage')
    return dict(cases=count,groups=groups,callbacks_or_stubs=False,scope='Actual two-sided callback prologue, CALL, full opening helper, RET and signed opening gate; stops before clipping or callback epilogue.')

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();require(mp['exe_sha256']==profile['exe_sha256'],'profile mismatch')
    out=ROOT/'artifacts/e1m1-aim-opening';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimPortalSource'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Actual two-sided callback through opening helper and signed branch, with static stack protection. '
      'Signed min/max heights derived from helper-entry memory; closed first-line result connected to live Lean aiming. '
      'Map representations at helper entry and ordered first hit remain explicit. Opening-gate to callback/query return, '
      'portal slope clipping, actors, repeated selection and reachable-state discharge remain open. No runtime or semantics changes.')
    if args.cross_check:report['cross_check']=cross_check(raw)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: original aim opening call/helper/return/gate; signed bounds and closed live source; strict axiom audit.')
if __name__=='__main__':main()
