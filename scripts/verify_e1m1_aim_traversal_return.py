#!/usr/bin/env python3
"""Authenticate the real intercept return and parent cleanup (ending before RET 8)."""
import argparse,json,re,subprocess
import verify_e1m1_aim_ordered_memory as previous
import verify_original_inline_thrust as extraction
ROOT,require=previous.ROOT,previous.require
pinned_data=previous.pinned_data
HEADER=previous.HEADER
GROUPS={
 'OriginalTraversalReturn':['decoded','stop_execution','exhausted_execution','cleanup_execution','return_layout','cleanup_layout'],
 'E1M1AimTraversalReturn':['contains_return','contains_loop','memory','word','execution','chosen','layout','saved_registers','caller_address','append']}
CONTRACTS=[('OriginalTraversalReturn','stop_execution','stop_checked','s f'),
 ('OriginalTraversalReturn','exhausted_execution','exhausted_checked','s f'),
 ('OriginalTraversalReturn','cleanup_execution','cleanup_checked','s f'),
 ('E1M1AimTraversalReturn','execution','execution_checked','s exit safe address'),
 ('E1M1AimTraversalReturn','chosen','chosen_checked','initial resolve s answer exit nonnull'),
 ('E1M1AimTraversalReturn','saved_registers','registers_checked','s safe'),
 ('E1M1AimTraversalReturn','caller_address','caller_checked','s safe address'),
 ('E1M1AimTraversalReturn','append','append_checked','start finish steps run exit safe address')]

def extracted():
    spec,profile,raw=previous.extracted()
    part=json.loads((ROOT/'tests/reference/original-traversal-return.json').read_text())
    share=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
    require(not(set(part['units'])&set(spec['units'])),'duplicate return range')
    raw.update(extraction.extract(binary,profile,part))
    return dict(units={**spec['units'],**part['units']}),profile,raw

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:source.index(' := by',a)]
    for word in ['program','listed','input','result']:
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+module+'.'+word,decl)
    for word in ['returned','cleaned','stored']:
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.OriginalTraversalReturn.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimTraversalReturn\n'+previous.certificate(data,raw)
    source+='\nnamespace Doom.Verification.ExtractedAimTraversalReturn\n'+HEADER
    for label,key in [('intercept','interceptReturn'),('path','pathCleanup')]:
        source+='def '+label+' : List UInt8 := ['+','.join(hex(b) for b in raw[key])+']\n'
        source+='theorem '+label+'_checked : '+label+'=OriginalTraversalReturn.'+label+'Code := by decide\n'
    source+='def returns := OriginalTraversalReturn.bytesProgram intercept path\n'
    source+='theorem returns_checked : returns=OriginalTraversalReturn.program := by unfold returns; rw [intercept_checked,path_checked]; rfl\n'
    source+='def linked : X86Routine.Program := fun pc => match returns pc with | some op => some op | none => Doom.Verification.ExtractedAimOrderedMemory.linked pc\n'
    source+='theorem linked_checked : linked=E1M1AimTraversalReturn.program := by unfold linked; rw [returns_checked,Doom.Verification.ExtractedAimOrderedMemory.linked_checked]; rfl\n'
    for module,name,checked,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+checked,1)
        decl=decl.replace('Doom.Proofs.OriginalTraversalReturn.program','returns').replace('Doom.Proofs.E1M1AimTraversalReturn.program','linked')
        source+='namespace '+module+'\n'+decl+' := by\n  '
        if 'returns []' in decl:source+='rw [returns_checked]\n  '
        if 'linked []' in decl:source+='rw [linked_checked]\n  '
        source+='exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='\n'.join('#print axioms '+n for n in ['intercept_checked','path_checked','returns_checked','linked_checked'])+'\n'
    source+='\n'.join('#print axioms '+m+'.'+checked for m,_,checked,_ in CONTRACTS)+'\nend Doom.Verification.ExtractedAimTraversalReturn\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedAimTraversalReturn.intercept_checked'"
    require(marker in output,'missing traversal return audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedAimTraversalReturn.'+n for n in ['intercept_checked','path_checked','returns_checked','linked_checked']]
    names+=['Doom.Verification.ExtractedAimTraversalReturn.'+m+'.'+checked for m,_,checked,_ in CONTRACTS]
    names+=['Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]
    for full in names:
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw):
    import random,struct,unicorn as u
    from unicorn import x86_const as x
    CODE,MASK=0x100000,0xffffffff
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);em.mem_map(CODE,0x40000)
    for key,address in [('interceptReturn',0x2c887),('pathCleanup',0x2cb0b)]:em.mem_write(CODE+address,raw[key])
    bases=[0,0x2b000,0x2c000,0x600000,0xfffff000]
    for a in bases:em.mem_map(a,4096)
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    rng=random.Random(0x2c887);writes=[];visits=[]
    em.hook_add(u.UC_HOOK_CODE,lambda _e,a,_n,_d:visits.append(a-CODE))
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&MASK)))
    stacks=[0x600800,0x600801,0xffffffa0,0xffffffd0,0x2c020]
    for case in range(256):
        pages={a:bytearray(rng.randbytes(4096)) for a in bases}
        def put(a,v):
            for i,b in enumerate(struct.pack('<I',v&MASK)):
                z=(a+i)&MASK;pages[z&~4095][z&4095]=b
        def get(a):
            return sum(pages[((a+i)&MASK)&~4095][(a+i)&4095]<<(8*i) for i in range(4))
        rr=[rng.getrandbits(32) for _ in regs];sp=stacks[case%len(stacks)];rr[4]=sp
        exhausted=case%2==0
        if not exhausted and case%4==1:rr[0]=0
        put(sp+20,CODE+0x2cb0b)
        for a,page in pages.items():em.mem_write(a,bytes(page))
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2)
        writes.clear();visits.clear()
        expected=list(rr);expected[0]=1 if exhausted else rr[0]
        put(0x2c028,rr[1])
        for reg,off in [(1,12),(3,16),(5,72),(7,76),(6,80)]:expected[reg]=get(sp+off)
        expected[4]=(sp+84)&MASK
        em.emu_start(CODE+(0x2c887 if exhausted else 0x2c88c),CODE+0x2cb11,count=13)
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+0x2cb11,'wrong return destination')
        require(len(visits)==(12 if exhausted else 11),'wrong instruction count')
        require([em.reg_read(r) for r in regs]==expected,'wrong restored registers')
        require(writes==[(0x2c028,4,rr[1])],'unexpected writes')
        for a,page in pages.items():require(bytes(em.mem_read(a,4096))==bytes(page),'memory mismatch')
    return dict(cases=256,checks='all general registers, all mapped data bytes, exact cursor write, return PC and instruction counts; exhausted and stopped paths; aligned, unaligned, wrapping and cursor-overlap stacks',flags='ADD flags abstracted as unknown in existing Lean semantics',ret8_executed=False)

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();require(mp['exe_sha256']==profile['exe_sha256'],'profile mismatch')
    out=ROOT/'artifacts/e1m1-aim-traversal-return';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimTraversalReturn'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Real P_TraverseIntercepts return on both exits and parent P_PathTraverse cleanup, joined to existing loop prefixes under an explicit endpoint saved-return-address/separation premise. Exact cursor store, stack adjustment, restored registers, and aim target/slope preservation. Ends at 0x2cb11 before RET 8. Saved stack preservation through the whole loop and complete P_AimLineAttack remain open. No runtime, decoder or instruction-semantics changes.',
      cross_check=cross_check(raw) if args.cross_check else None)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: authenticated traversal return/cleanup, strict axiom audit.'+(f" {report['cross_check']['cases']} emulator cases." if args.cross_check else ''))
if __name__=='__main__':main()
