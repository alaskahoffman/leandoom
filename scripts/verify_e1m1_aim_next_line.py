#!/usr/bin/env python3
"""Authenticate persistent map images and the next mapped-line callback inputs."""
import argparse,json,re,subprocess
import verify_e1m1_aim_history_cycle as previous
ROOT,require=previous.ROOT,previous.require
pinned_data=previous.pinned_data
extracted=previous.extracted
GROUPS={
 'E1M1AimMapFrame':['stable_word','region','word','byte','half','image','opening_safe','floor_safe','map_safe'],
 'E1M1AimNextLine':['clip_globals','clip_safe','distance_reads','entry']}
IMAGE_ARGS='s out marked line front back ff fc bf bc frame pointer bounded safe before'
ENTRY_ARGS='s initial hits marked seen visits resolve target out distance j history selection bounded safe querySafe frame pointer markBound front back ff fc bf bc mapRegion mapImage isLine two globals'


def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimNextLine\n'+previous.certificate(data,raw)
    source+='\nnamespace Doom.Verification.ExtractedAimNextLine\nset_option backward.isDefEq.respectTransparency false\nopen Doom Doom.Proofs X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory E1M1InterceptMinimum\nopen E1M1AimNextSelection (head)\nopen E1M1MinimumScan (address)\nopen E1M1AimRepeatProgram (program ReadFrame)\nopen E1M1OrderedTraversal (appended)\nopen E1M1OrderedVisit (walk)\nopen E1M1InterceptMark (consume)\nopen E1M1HistoryDispatch (Selection)\nopen E1M1AimHistoryCycle (Frame Next)\nopen E1M1AimCycleInvariant (Layout QuerySafe)\nopen E1M1AimMapFrame (StableWord Region)\nopen E1M1AimNextLine (ClipGlobalsSafe)\n'
    for module,name,checked,args in [('E1M1AimMapFrame','image','image_checked',IMAGE_ARGS),('E1M1AimNextLine','entry','entry_checked',ENTRY_ARGS)]:
        text=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=text.index('theorem '+name+' ')
        decl=text[a:text.index(' := by',a)].replace('theorem '+name,'theorem '+checked,1)
        source+=decl+' := '+module+'.'+name+' '+args+'\n'
    source+='\n'.join('#print axioms '+n for n in ['image_checked','entry_checked'])+'\nend Doom.Verification.ExtractedAimNextLine\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedAimNextLine.image_checked'"
    require(marker in output,'missing next-line audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedAimNextLine.'+n for n in ['image_checked','entry_checked']]
    names+=['Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]
    for full in names:
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')


def cross_check(raw,count=384):
    """Complete original traversals with different portal heights per hit.

    Extend the previous cycle diagnostic with whole-map byte snapshots.
    Compare every reached callback and final exit to a signed fixed-point
    selection/clipping model; never stub a callback or reset between hits.
    """
    import random,struct,unicorn as u
    from unicorn import x86_const as x
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
    for base,size in [(0,0x40000),(0x100000,0x40000),(0x600000,0x10000),
                      (0x700000,0x1000),(0xfffff000,0x1000)]:
        em.mem_map(base,size)
    units=[('aimGuard',0x2b760),('aimOpening',0x2b77f),('opening',0x2c340),
           ('aimDistance',0x2b797),('aimFloor',0x2b7a6),('division',0x1d180),
           ('aimCeiling',0x2b7d1),('aimWindow',0x2b800),('aimContinue',0x2b89d),
           ('interceptSetup',0x2c810),('interceptMinimum',0x2c841),('interceptGate',0x2c85e)]
    for name,pc in units:em.mem_write(0x100000+pc,raw[name])
    rng=random.Random(0xc11f510);mask=0xffffffff;calls=[];steps=[]
    pack=lambda v:struct.pack('<I',v&mask)
    def word(a):return struct.unpack('<I',bytes(em.mem_read(a&mask,4)))[0]
    def signed(v):return (v&mask)-(1<<32) if v&0x80000000 else v&mask
    def encoded(rows):return b''.join(struct.pack('<III',*(v&mask for v in row)) for row in rows)
    def hook(machine,address,size,data):
        if address in (0x12c887,0x12c88c):machine.emu_stop();return
        steps.append(address)
        if address!=0x12b760:return
        require(bytes(em.mem_read(0x600000,128*n))==map_snapshot,'map bytes changed before next callback')
        require(len(calls)<len(expected),'unexpected extra callback')
        j,remaining,lo,hi,prior=expected[len(calls)]
        require(machine.reg_read(x.UC_X86_REG_EAX)==0x2ba20+12*j and
                machine.reg_read(x.UC_X86_REG_EBX)==0x2ba20+12*j,'wrong selected argument aliases')
        require(machine.reg_read(x.UC_X86_REG_ESI)==remaining,'wrong source-history budget')
        require(machine.reg_read(x.UC_X86_REG_ESP)==(sp-4)&mask,'callback stack did not repeat')
        require(word(sp-4)==0x12c86d and word(sp)==0x12b760,'return word or callback slot lost')
        require(word(0x2c1e4)==lo&mask and word(0x2c1e8)==hi&mask,'clipped window not carried')
        require(word(0x2b9b8)==distance and word(0x2b9a8)==z,'query words changed at next callback')
        require(word(0x2c028)==0x2ba20+12*n,'saved cursor changed')
        if n:require(bytes(em.mem_read(0x2ba20,12*n))==encoded(prior),'record history not carried')
        require(machine.reg_read(x.UC_X86_REG_EDI)==65536,'maximum distance changed')
        calls.append(j)
    em.hook_add(u.UC_HOOK_CODE,hook)
    groups=dict(empty=0,exhausted=0,range_rejected=0,callback_stopped=0,full_buffer=0,
                tied_fractions=0,wrapping_stack=0,lower_changed=0,upper_changed=0,
                multiple_callbacks=0,multiple_changed_windows=0)
    total=0
    for case in range(count):
        n=[0,1,2,4,8,16,127,128][case%8]
        sp=[0x700800,0,4,16,32,0xfffffff0][(case//8)%6]
        distance=rng.randrange(32,129)*65536;z=32*65536
        fractions=[rng.choice([8192,32768,65536,65537,2147483647]) for _ in range(n)]
        if case%5==0:fractions=[65536]*n
        if case%7==0:fractions=[2147483647]*n
        records=[];heights=[]
        for j,fraction in enumerate(fractions):
            line=0x600000+128*j;front=line+64;back=line+80
            ff=0;fc=128*65536
            bf=rng.choice([0,0,16,32,48])*65536;bc=rng.choice([64,96,128])*65536
            if case%6==0:bf=ff;bc=fc
            heights.append((ff,fc,bf,bc));records.append([fraction,1,line])
            em.mem_write(line,bytes((case+17*j+off*13)&255 for off in range(128)))
            em.mem_write(line+16,bytes([((case+j)*73)&255|4]))
            em.mem_write(line+24,struct.pack('<H',(case*257+j*37)%65535))
            for addr,val in [(line+46,front),(line+50,back),(front,ff),(front+4,fc),(back,bf),(back+4,bc)]:
                em.mem_write(addr,pack(val))
        lo,hi=(-65536,65536) if case%11 else (100,100)
        initial_lo,initial_hi=lo,hi
        remaining=n;model=[r[:] for r in records];expected=[];changed_windows=0
        while True:
            old=remaining;remaining=(remaining-1)&mask
            if old==0:destination=0x12c887;groups['exhausted']+=1;break
            best=min(signed(r[0]) for r in model)
            if best>65536:destination=0x12c887;groups['range_rejected']+=1;break
            j=next(i for i,r in enumerate(model) if signed(r[0])==best)
            expected.append((j,remaining,lo,hi,[r[:] for r in model]))
            ff,fc,bf,bc=heights[j]
            product=signed((distance*best)>>16)
            require(product!=0,'invalid diagnostic division fixture')
            def slope(height):
                numerator=(height-z)*65536
                answer=(abs(numerator)//abs(product))*(-1 if (numerator<0)!=(product<0) else 1)
                require(-(1<<31)<=answer<(1<<31),'diagnostic division overflow')
                return answer
            low=lo if bf==ff else max(lo,slope(max(ff,bf)))
            high=hi if fc==bc else min(hi,slope(min(fc,bc)))
            groups['lower_changed']+=low!=lo;groups['upper_changed']+=high!=hi
            changed_windows+=low!=lo or high!=hi
            lo,hi=low,high
            if lo>=hi:destination=0x12c88c;groups['callback_stopped']+=1;break
            model[j][0]=0x7fffffff
        map_snapshot=bytes(em.mem_read(0x600000,128*n)) if n else b''
        if n:em.mem_write(0x2ba20,encoded(records))
        for addr,val in [(sp,0x12b760),(0x2c028,0x2ba20+12*n),(0x2b9b8,distance),
                         (0x2b9a8,z),(0x2c1e4,initial_lo),(0x2c1e8,initial_hi)]:
            em.mem_write(addr,pack(val))
        regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
              x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
        initial=[rng.getrandbits(32) for _ in regs]
        initial[1]=0x2ba20+12*n;initial[4]=sp;initial[6]=n;initial[7]=65536
        for reg,val in zip(regs,initial):em.reg_write(reg,val)
        em.reg_write(x.UC_X86_REG_EFLAGS,2);calls.clear();steps.clear()
        em.emu_start(0x12c83a,0x12c88d,count=4+(n+1)*(157+7*n))
        if n:require(bytes(em.mem_read(0x600000,128*n))==map_snapshot,'map bytes changed at final exit')
        require(calls==[entry[0] for entry in expected],'incorrect complete callback sequence')
        require(len(calls)==len(set(calls)),'consumed hit repeated')
        require(em.reg_read(x.UC_X86_REG_EIP)==destination,'wrong final branch')
        require(em.reg_read(x.UC_X86_REG_ESI)==remaining,'wrong final counter')
        require(em.reg_read(x.UC_X86_REG_ESP)==sp,'parent stack not restored')
        require(em.reg_read(x.UC_X86_REG_EDI)==65536 and em.reg_read(x.UC_X86_REG_EBP)==initial[5],
                'preserved registers changed')
        if n:require(bytes(em.mem_read(0x2ba20,12*n))==encoded(model),'wrong final record image')
        for addr,val in [(sp,0x12b760),(0x2c028,0x2ba20+12*n),(0x2b9b8,distance),
                         (0x2b9a8,z),(0x2c1e4,lo),(0x2c1e8,hi)]:
            require(word(addr)==val&mask,'final frame or clipped window mismatch')
        groups['empty']+=n==0;groups['full_buffer']+=n==128;groups['wrapping_stack']+=sp<44
        groups['tied_fractions']+=len(set(fractions))<len(fractions)
        groups['multiple_callbacks']+=len(calls)>1
        groups['multiple_changed_windows']+=changed_windows>1
        total+=len(calls)
    require(all(groups.values()),'missing cycle coverage')
    return dict(cases=count,callbacks=total,groups=groups,callbacks_or_stubs=False,map_bytes_per_record=128,
        scope='Extension of the previous uninterrupted traversal diagnostic: varied nonzero side indices, flag bytes, poisoned padding and exact whole-map byte snapshots at every callback and final exit. Callback order, query words, clipping and final exits remain checked. Diagnostic coverage, not a universal proof.')

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();require(mp['exe_sha256']==profile['exe_sha256'],'profile mismatch')
    out=ROOT/'artifacts/e1m1-aim-next-line';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimNextLine'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Persistent map-region protection carries sector pointers/heights, halfword side indices and flag bytes through the complete clipping/selection cycle. '
      'The reached next line has derived mapped Inputs, fraction/range read protection and ceiling-clip separation, with reusable static map/global protection. '
      'Universal catalog/loop composition, all-hit aim suffix alignment, other callback branches and reachable-state contract discharge remain open. No runtime or decoder changes.')
    if args.cross_check:report['cross_check']=cross_check(raw)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: map persistence and actual next-line inputs; strict axiom audit.')
if __name__=='__main__':main()
