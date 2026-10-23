#!/usr/bin/env python3
"""Certify callback-entry map transport and the original aim distance product."""
import argparse,json,re,subprocess
import verify_e1m1_aim_opening as previous
import verify_original_inline_thrust as extraction
ROOT,require=previous.ROOT,previous.require
pinned_data=previous.pinned_data
GROUPS={
 'E1M1AimOpeningFrame':['stack','line_argument','frame','half_frame','transport','helper_safe','decision','opening_frame','output_frame','output_regs'],
 'E1M1AimMapped':['execution','closed_correspondence'],
 'OriginalAimDistance':['decoded','execution','arithmetic'],
 'E1M1AimDistance':['contains_distance','contains_opening','operands','execution']}

def extracted():
    spec,profile,raw=previous.extracted()
    part=json.loads((ROOT/'tests/reference/original-aim-distance.json').read_text())
    share=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
    require(not(set(part['units'])&set(spec['units'])),'duplicate distance range')
    raw.update(extraction.extract(binary,profile,part))
    return dict(units={**spec['units'],**part['units']}),profile,raw

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimDistance\n'+previous.certificate(data,raw)
    source+='''
namespace Doom.Verification.ExtractedAimDistance
set_option backward.isDefEq.respectTransparency false
open Doom Doom.Proofs X86 X86Memory X86Control Collision
open E1M1AimDistance (result ReadSafe)
'''
    source+='def code : List UInt8 := ['+','.join(hex(b) for b in raw['aimDistance'])+']\n'
    source+='''theorem code_checked : code=OriginalAimDistance.code := by decide
def linked : X86Routine.Program := fun pc =>
  match OriginalAimDistance.bytesProgram code pc with
  | some op => some op
  | none => ExtractedAimOpening.linked pc
theorem linked_checked : linked=E1M1AimDistance.program := by
  unfold linked E1M1AimDistance.program OriginalAimDistance.program
  rw [code_checked,ExtractedAimOpening.linked_checked]
  rfl
'''
    text=(ROOT/'Doom/Proofs/E1M1AimDistance.lean').read_text();a=text.index('theorem execution ')
    decl=text[a:text.index(' := by',a)].replace('theorem execution','theorem execution_checked',1).replace('FloorCaller.cm program','FloorCaller.cm linked')
    source+=decl+' := by\n  rw [linked_checked]\n  exact E1M1AimDistance.execution s f hit line front back ff fc bf bc distance h reads range pass\n'
    source+='\n'.join('#print axioms '+n for n in ['code_checked','linked_checked','execution_checked'])+'\nend Doom.Verification.ExtractedAimDistance\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedAimDistance.code_checked'"
    require(marker in output,'missing aim distance audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedAimDistance.'+n for n in ['code_checked','linked_checked','execution_checked']]
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
    opening=previous.cross_check(raw,count)
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
    for base,size in [(0,0x40000),(0x100000,0x40000),(0x600000,0x1000),(0x700000,0x1000),(0xfffff000,0x1000)]:em.mem_map(base,size)
    for name,pc in [('aimGuard',0x2b760),('aimOpening',0x2b77f),('opening',0x2c340),('aimDistance',0x2b797)]:em.mem_write(0x100000+pc,raw[name])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    rng=random.Random(0x2b797);mask=0xffffffff;writes=[];steps=[]
    signed=lambda v:v if v<2**31 else v-2**32
    pack=lambda v:struct.pack('<I',v&mask)
    def code(machine,address,size,data):
        if address==0x12b7a6:machine.emu_stop()
        else:steps.append(address)
    em.hook_add(u.UC_HOOK_CODE,code)
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda *a:writes.append((a[2],a[3],a[4])))
    groups=dict(negative_product=0,overflowing_result=0,zero_operand=0,wrapping_stack=0)
    edges=[0,1,0x7fffffff,0x80000000,0xffffffff,0x10000,0xffff0000]
    for case in range(count):
        sp=[0x700800,0,4,16,32,0xfffffff0][case%6]
        before=[rng.getrandbits(32) for _ in regs];before[0]=0x600100;before[4]=sp
        levels=sorted(rng.sample(range(-2147483648,2147483648),4))
        ff,bf=levels[:2];fc,bc=levels[2:]
        if case%2:ff,bf=bf,ff
        if case%4<2:fc,bc=bc,fc
        bottom=max(ff,bf)&mask;top=min(fc,bc)&mask;low=min(ff,bf)&mask
        distance,frac=[rng.choice(edges) if case%2 else rng.getrandbits(32) for _ in range(2)]
        if case%16==0:distance=0
        value=(signed(distance)*signed(frac))//65536
        record=struct.pack('<III',frac,1,0x600200)
        em.mem_write(0x600100,record);em.mem_write(0x600210,bytes([rng.randrange(256)|4]))
        em.mem_write(0x600218,struct.pack('<H',case%32768));em.mem_write(0x60022e,pack(0x600300));em.mem_write(0x600232,pack(0x600400))
        for addr,v in [(0x600300,ff),(0x600304,fc),(0x600400,bf),(0x600404,bc),(0x2b9b8,distance),(sp,0x12c86d)]:em.mem_write(addr,pack(v))
        for reg,v in zip(regs,before):em.reg_write(reg,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2);writes.clear();steps.clear()
        em.emu_start(0x12b760,0x12b7a6,count=54)
        expected=list(before);expected[0]=expected[2]=value&mask;expected[1]=0x600200;expected[3]=frac;expected[4]=(sp-24)&mask
        require(em.reg_read(x.UC_X86_REG_EIP)==0x12b7a6,'distance exit mismatch')
        require([em.reg_read(r) for r in regs]==expected,'distance registers mismatch')
        require(len(steps)<=53 and steps[-5:]==[0x12b797,0x12b79c,0x12b79e,0x12b7a0,0x12b7a4],'distance instruction path mismatch')
        expected_writes=[((sp-4*(i+1))&mask,4,before[r]) for i,r in enumerate([3,1,2,6,7,5])]
        expected_writes+=[((sp-28)&mask,4,0x12b786)]
        expected_writes += [((sp-off)&mask,4,v) for off,v in [(32,before[3]),(36,0x600200),(40,0x600100),(44,before[6])]]
        expected_writes += [(0x2c034,4,top),(0x2c030,4,bottom),(0x2c02c,4,low),(0x2c038,4,(top-bottom)&mask)]
        require(writes==expected_writes,'distance path writes mismatch')
        require(bytes(em.mem_read(0x600100,12))==record,'record changed')
        require(bytes(em.mem_read(0x2b9b8,4))==pack(distance),'range changed')
        require(bytes(em.mem_read(sp,4))==pack(0x12c86d),'caller return changed')
        groups['negative_product']+=value<0;groups['overflowing_result']+=not(-2**31<=value<2**31)
        groups['zero_operand']+=distance==0 or frac==0;groups['wrapping_stack']+=sp<44
    require(all(groups.values()),'missing distance coverage')
    return dict(cases=count+opening['cases'],opening=opening,distance=dict(cases=count,groups=groups),
      callbacks_or_stubs=False,scope='Original callback through opening helper/gate, then five distance instructions for open passages. No slope division/clipping or callback/query return.')

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();require(mp['exe_sha256']==profile['exe_sha256'],'profile mismatch')
    out=ROOT/'artifacts/e1m1-aim-distance';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimDistance'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Map image transported from callback entry through saves/CALL; helper read protection derived; closed live-source result joined from callback entry. '
      'Open passage executes through the real distance multiplication with operands derived from entry memory. '
      'Initial callback representations, source ordered-hit relation and static separation remain explicit. '
      'Floor/ceiling slope division/clipping, callback/query returns, actors, repeated selection and reachable-state discharge remain open. No runtime or semantics changes.')
    if args.cross_check:report['cross_check']=cross_check(raw)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: callback-entry map transport, closed correspondence and original distance product; strict axiom audit.')
if __name__=='__main__':main()
