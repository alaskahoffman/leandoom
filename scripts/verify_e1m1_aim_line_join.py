#!/usr/bin/env python3
"""Authenticate the open-line source iteration and original traversal resumption."""
import argparse,json,re,subprocess
import verify_e1m1_aim_window as previous
ROOT,require=previous.ROOT,previous.require
pinned_data=previous.pinned_data
extracted=previous.extracted
GROUPS={
 'E1M1AimIteration':['live','fixed_bne','visit_line','next_line'],
 'E1M1AimResume':['contains_window','contains_gate','execution'],
 'E1M1AimLineJoin':['bits_eq','floor_word','ceiling_word','bottom_word','top_word','correspondence']}

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimLineJoin\n'+previous.certificate(data,raw)
    source+='\nnamespace Doom.Verification.ExtractedAimLineJoin\nset_option backward.isDefEq.respectTransparency false\nopen Doom Doom.Proofs X86 X86Memory X86Control BlockSummary Collision E1M1AimIteration\n'
    source+='def gateCode : List UInt8 := ['+','.join(hex(b) for b in raw['interceptGate'])+']\n'
    source+='theorem gate_checked : gateCode=OriginalInterceptGate.code := by decide\ndef linked : X86Routine.Program := fun pc =>\n  match ExtractedAimWindow.linked pc with\n  | some op => some op\n  | none => OriginalInterceptGate.bytesProgram gateCode pc\ntheorem linked_checked : linked=E1M1AimResume.program := by\n  unfold linked E1M1AimResume.program OriginalInterceptGate.program\n  rw [gate_checked,ExtractedAimWindow.linked_checked]\n  rfl\n'
    text=(ROOT/'Doom/Proofs/E1M1AimLineJoin.lean').read_text();a=text.index('theorem correspondence ')
    decl=text[a:text.index(' := by',a)].replace('theorem correspondence','theorem correspondence_checked',1).replace('FloorCaller.cm E1M1AimResume.program','FloorCaller.cm linked')
    source+=decl+' := by\n  rw [linked_checked]\n  exact E1M1AimLineJoin.correspondence s f scene shooter thing path distance i rest lower upper floorSlope ceilingSlope history hit back line frontPtr backPtr h distanceReads floorReads reads clip range eye bottom top selectedPointer selected two backSector pass floorOk ceilingOk returnSafe returnWord markSafe\n'
    source+='\n'.join('#print axioms '+n for n in ['gate_checked','linked_checked','correspondence_checked'])+'\nend Doom.Verification.ExtractedAimLineJoin\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedAimLineJoin.gate_checked'"
    require(marker in output,'missing aim line-join audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedAimLineJoin.'+n for n in ['gate_checked','linked_checked','correspondence_checked']]
    names+=['Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]
    for full in names:
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')


def cross_check(raw,count=384):
    """Run authentic callback + parent branch; no helper/callback replacement."""
    import random,struct,unicorn as u
    from unicorn import x86_const as x
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
    for base,size in [(0,0x40000),(0x100000,0x40000),(0x600000,0x1000),(0x700000,0x1000),(0xfffff000,0x1000)]:em.mem_map(base,size)
    for name,pc in [('aimGuard',0x2b760),('aimOpening',0x2b77f),('opening',0x2c340),('aimDistance',0x2b797),('aimFloor',0x2b7a6),('division',0x1d180),('aimCeiling',0x2b7d1),('aimWindow',0x2b800),('aimContinue',0x2b89d),('interceptGate',0x2c85e)]:em.mem_write(0x100000+pc,raw[name])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    rng=random.Random(0x2c879);mask=0xffffffff;steps=[];writes=[]
    pack=lambda v:struct.pack('<I',v&mask)
    signed=lambda v:((v+2**31)&mask)-2**31
    def div(a,b):
        guard=(signed(abs(a))>>14)<signed(abs(b))
        if not guard:return 0x7fffffff if (a<0)==(b<0) else -0x80000000
        return (abs(a*65536)//abs(b))*(-1 if (a<0)!=(b<0) else 1)
    def hook(machine,address,size,data):
        if address in (0x12c83a,0x12c88c):machine.emu_stop()
        else:steps.append(address)
    em.hook_add(u.UC_HOOK_CODE,hook)
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda *a:writes.append((a[2],a[3],a[4])))
    groups=dict(continued=0,stopped=0,equal_window=0,both_clips=0,equal_heights=0,wrapping_stack=0)
    for case in range(count):
        sp=[0x700800,0,4,16,32,0xfffffff0][case%6]
        before=[rng.getrandbits(32) for _ in regs];before[0]=before[3]=0x600100;before[4]=sp
        ff,bf,fc,bc=sorted(rng.sample(range(-2**31+1,2**31-1),4))
        if case%2:ff,bf=bf,ff
        if case%3:fc,bc=bc,fc
        if case%5==0:bf=ff
        if case%6==0:bc=fc
        distance=rng.randrange(1,0x7fffffff)*(-1 if case%2 else 1);z=signed(rng.getrandbits(32))
        lo=signed(rng.getrandbits(32));hi=signed(rng.getrandbits(32))
        floor=div(signed(max(ff,bf)-z),distance);ceil=div(signed(min(fc,bc)-z),distance)
        if case%7==0:lo=hi=floor
        low=lo if ff==bf else max(lo,floor);high=hi if fc==bc else min(hi,ceil)
        go=low<high;cursor=rng.getrandbits(32)
        em.mem_write(0x600100,struct.pack('<III',65536,1,0x600200));em.mem_write(0x600210,b'\x04');em.mem_write(0x600218,b'\x00\x00')
        for addr,val in [(0x60022e,0x600300),(0x600232,0x600400),(0x600300,ff),(0x600304,fc),(0x600400,bf),(0x600404,bc),(0x2b9b8,distance),(0x2b9a8,z),(0x2c1e4,lo),(0x2c1e8,hi),(sp,0x12c86d),(0x2c028,cursor)]:em.mem_write(addr,pack(val))
        for reg,val in zip(regs,before):em.reg_write(reg,val)
        em.reg_write(x.UC_X86_REG_EFLAGS,2);steps.clear();writes.clear()
        em.emu_start(0x12b760,0x12c88d,count=145)
        require(em.reg_read(x.UC_X86_REG_EIP)==(0x12c83a if go else 0x12c88c),'wrong traversal continuation')
        require(len(steps)<=144,'instruction bound')
        expected=list(before);expected[0]=int(go);expected[1]=cursor;expected[4]=(sp+4)&mask
        require([em.reg_read(r) for r in regs]==expected,'wrong parent registers')
        for addr,val in [(0x2c1e4,low),(0x2c1e8,high),(0x600100,0x7fffffff if go else 65536),(0x2c028,cursor)]:require(bytes(em.mem_read(addr,4))==pack(val),'wrong carried memory')
        marks=[w for w in writes if w[0]==0x600100]
        require(marks==([(0x600100,4,0x7fffffff)] if go else []),'wrong consumed-hit write')
        require(0x12c86d in steps and steps[-1]==(0x12c885 if go else 0x12c877),'missing real caller branch')
        groups['continued']+=go;groups['stopped']+=not go;groups['equal_window']+=low==high
        groups['both_clips']+=ff!=bf and fc!=bc;groups['equal_heights']+=ff==bf and fc==bc;groups['wrapping_stack']+=sp<44
    require(all(groups.values()),'missing continuation coverage')
    return dict(cases=count,groups=groups,callbacks_or_stubs=False,scope='Real callback entry through caller stop or mark-and-repeat branch; all registers, slope globals, selected fraction and cursor checked.')

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();require(mp['exe_sha256']==profile['exe_sha256'],'profile mismatch')
    out=ROOT/'artifacts/e1m1-aim-line-join';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimLineJoin'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Open two-sided line hit: original callback and enclosing stop/mark/repeat branch, matched to an arbitrary live source loop iteration and its carried bounds/history. '
      'Actual source extraction is proved, entry representation/separation and conditional division success remain explicit. '
      'Actor hits, full repeated-selection invariant, initialization and reachable-state discharge remain open. No runtime or decoder changes.')
    if args.cross_check:report['cross_check']=cross_check(raw)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: source open-line iteration and original traversal continuation; strict axiom audit.')
if __name__=='__main__':main()
