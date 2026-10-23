#!/usr/bin/env python3
"""Authenticate RET 8 and the continuous return chain to the aiming caller."""
import argparse,json,re,subprocess
import verify_e1m1_aim_traversal_return as previous
import verify_original_inline_thrust as extraction
ROOT,require=previous.ROOT,previous.require
pinned_data=previous.pinned_data
HEADER=previous.HEADER
GROUPS={
 'Doom.Verification.X86ReturnCleanup':['prior_execution','zero_cleanup','layout','lift','Prefix.transfer','Prefix.trans'],
 'Doom.Proofs.OriginalPathReturn':['decoded','execution','layout'],
 'Doom.Proofs.E1M1AimCompletedReturn':['contains_aim','contains_traversal','contains_ret8','contains_legacy','parent_layout','execution','memory','value','layout','saved_caller','append']}
CONTRACTS=[('Doom.Verification.X86ReturnCleanup','zero_cleanup','zero_checked','cm s'),
 ('Doom.Verification.X86ReturnCleanup','layout','instruction_checked','bytes s'),
 ('Doom.Proofs.OriginalPathReturn','execution','ret8_checked','cm s f'),
 ('Doom.Proofs.OriginalPathReturn','layout','ret8_layout_checked','s f'),
 ('Doom.Proofs.E1M1AimCompletedReturn','parent_layout','parent_checked','s safe address'),
 ('Doom.Proofs.E1M1AimCompletedReturn','execution','execution_checked','s exit safe20 address20 safe84 address84'),
 ('Doom.Proofs.E1M1AimCompletedReturn','value','value_checked','initial resolve s answer exit nonnull'),
 ('Doom.Proofs.E1M1AimCompletedReturn','saved_caller','saved_checked','s safe'),
 ('Doom.Proofs.E1M1AimCompletedReturn','append','append_checked','start finish steps run exit safe20 address20 safe84 address84')]

def extracted():
    spec,profile,raw=previous.extracted()
    part=json.loads((ROOT/'tests/reference/original-aim-completed-return.json').read_text())
    share=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
    require(not(set(part['units'])&set(spec['units'])),'duplicate return range')
    raw.update(extraction.extract(binary,profile,part))
    return dict(units={**spec['units'],**part['units']}),profile,raw

def declaration(module,name):
    source=(ROOT/(module.replace('.','/')+'.lean')).read_text();a=source.index('theorem '+name+' ')
    decl=source[a:source.index(' := by',a)]
    words=['returned','execute'] if module=='Doom.Verification.X86ReturnCleanup' else ['program','result','parent']
    for word in words:decl=re.sub(r'(?<![.\w])'+word+r'\b',module+'.'+word,decl)
    return decl

BASE_NAMES=['path_bytes_checked','aim_bytes_checked','ray_bytes_checked','ret_program_checked','aim_program_checked','legacy_checked','linked_checked']
def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimCompletedReturn\n'+previous.certificate(data,raw)
    source+='\nnamespace Doom.Verification.ExtractedAimCompletedReturn\n'+HEADER
    for label,key,definition in [('path','pathRet8','OriginalPathReturn.code'),('aim','aimReturn','OriginalAimQuery.retBytes'),('ray','ray','OriginalAimQuery.rayBytes')]:
        source+='def '+label+' : List UInt8 := ['+','.join(hex(b) for b in raw[key])+']\n'
        source+='theorem '+label+'_bytes_checked : '+label+'='+definition+' := by decide\n'
    source+='def retProgram := OriginalPathReturn.bytesProgram path\n'
    source+='theorem ret_program_checked : retProgram=OriginalPathReturn.program := by unfold retProgram; rw [path_bytes_checked]; rfl\n'
    source+='def aimProgram := OriginalAimQuery.bytesProgram ray aim\n'
    source+='theorem aim_program_checked : aimProgram=OriginalAimQuery.program := by unfold aimProgram; rw [ray_bytes_checked,aim_bytes_checked]; rfl\n'
    source+='def legacy : X86Routine.Program := fun pc => match aimProgram pc with | some op => some op | none => Doom.Verification.ExtractedAimTraversalReturn.linked pc\n'
    source+='theorem legacy_checked : legacy=E1M1AimCompletedReturn.legacy := by unfold legacy; rw [aim_program_checked,Doom.Verification.ExtractedAimTraversalReturn.linked_checked]; rfl\n'
    source+='def linked : X86ReturnCleanup.Program := fun pc => match retProgram pc with | some op => some op | none => X86ReturnCleanup.embed legacy pc\n'
    source+='theorem linked_checked : linked=E1M1AimCompletedReturn.program := by unfold linked; rw [ret_program_checked,legacy_checked]; rfl\n'
    for module,name,checked,args in CONTRACTS:
        short=module.split('.')[-1]
        decl=declaration(module,name).replace('theorem '+name,'theorem '+checked,1)
        decl=decl.replace('Doom.Proofs.OriginalPathReturn.program','retProgram').replace('Doom.Proofs.E1M1AimCompletedReturn.program','linked')
        source+='namespace '+short+'\n'+decl+' := by\n  '
        if 'retProgram []' in decl:source+='rw [ret_program_checked]\n  '
        if 'linked []' in decl:source+='rw [linked_checked]\n  '
        source+='exact '+module+'.'+name+' '+args+'\nend '+short+'\n'
    source+='\n'.join('#print axioms '+n for n in BASE_NAMES)+'\n'
    source+='\n'.join('#print axioms '+m.split('.')[-1]+'.'+checked for m,_,checked,_ in CONTRACTS)+'\nend Doom.Verification.ExtractedAimCompletedReturn\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms '+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedAimCompletedReturn.path_bytes_checked'"
    require(marker in output,'missing completed return audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedAimCompletedReturn.'+n for n in BASE_NAMES]
    names+=['Doom.Verification.ExtractedAimCompletedReturn.'+m.split('.')[-1]+'.'+checked for m,_,checked,_ in CONTRACTS]
    names+=[m+'.'+n for m,group in GROUPS.items() for n in group]
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
    for key,address in [('interceptReturn',0x2c887),('pathCleanup',0x2cb0b),('pathRet8',0x2cb11),('aimReturn',0x2bbff)]:em.mem_write(CODE+address,raw[key])
    bases=[0,0x2b000,0x2c000,0x600000,0xfffff000]
    for a in bases:em.mem_map(a,4096)
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    rng=random.Random(0x2cb11);writes=[];visits=[]
    em.hook_add(u.UC_HOOK_CODE,lambda _e,a,_n,_d:visits.append(a-CODE))
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&MASK)))
    stacks=[0x600800,0x600801,0xffffffa0,0xffffffd0,0x2c020]
    def start(rr,flags=2):
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,flags);writes.clear();visits.clear()
    for case in range(256):
        pages={a:bytearray(rng.randbytes(4096)) for a in bases}
        def put(a,v):
            for i,b in enumerate(struct.pack('<I',v&MASK)):
                z=(a+i)&MASK;pages[z&~4095][z&4095]=b
        def get(a):return sum(pages[((a+i)&MASK)&~4095][(a+i)&4095]<<(8*i) for i in range(4))
        rr=[rng.getrandbits(32) for _ in regs];sp=stacks[case%len(stacks)];rr[4]=sp
        exhausted=case%2==0
        if not exhausted:rr[0]=0
        target=0 if case%4<2 else 0x600100
        slope=0 if case%8>=6 else rng.getrandbits(32)
        put(0x2b9f8,target);put(0x2b9b4,slope)
        put(sp+20,CODE+0x2cb0b);put(sp+84,CODE+0x2bbff);put(sp+112,CODE+0x30000)
        for a,page in pages.items():em.mem_write(a,bytes(page))
        start(rr);expected=list(rr);expected[0]=slope if target else 0
        put(0x2c028,rr[1])
        for reg,off in [(1,108),(3,16),(5,96),(7,100),(6,104)]:expected[reg]=get(sp+off)
        expected[4]=(sp+116)&MASK
        em.emu_start(CODE+(0x2c887 if exhausted else 0x2c88c),CODE+0x30000,count=22)
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+0x30000,'wrong caller destination')
        require(len(visits)==(21 if exhausted else 20),'wrong complete instruction count')
        require([em.reg_read(r) for r in regs]==expected,'wrong final caller registers/slope')
        require(writes==[(0x2c028,4,rr[1])],'unexpected writes')
        for a,page in pages.items():require(bytes(em.mem_read(a,4096))==bytes(page),'memory mismatch')
    # Independently check unsigned immediates, flags and a return-address load
    # crossing 0xffffffff. These generated encodings test the new semantics;
    # only c2 08 00 is claimed to come from the pinned DOS executable.
    for case in range(128):
        imm=[0,8,0x7fff,1,0x1234][case%5];sp=[0x600800,0x600801,0xfffffffe][case%3]
        rr=[rng.getrandbits(32) for _ in regs];rr[4]=sp
        for i,b in enumerate(struct.pack('<I',CODE+0x30000)):em.mem_write((sp+i)&MASK,bytes([b]))
        location=CODE+0x31000+case*8
        em.mem_write(location,b'\xc2'+struct.pack('<H',imm))
        flags=2|(rng.getrandbits(12)&0x8d5);start(rr,flags)
        expected=list(rr);expected[4]=(sp+4+imm)&MASK
        before={a:bytes(em.mem_read(a,4096)) for a in bases}
        em.emu_start(location,CODE+0x30000,count=1)
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+0x30000,'wrong RET imm16 destination')
        require([em.reg_read(r) for r in regs]==expected,f'RET imm16 unsigned cleanup mismatch in case {case}: got {[em.reg_read(r) for r in regs]}, expected {expected}')
        require(em.reg_read(x.UC_X86_REG_EFLAGS)==flags,'RET imm16 flags changed')
        require(not writes and len(visits)==1,'RET imm16 side effects')
        for a,page in before.items():require(bytes(em.mem_read(a,4096))==page,'RET imm16 memory changed')
    # The installed Unicorn/QEMU backend sign-extends high-bit RET immediates.
    # Record this separately: these are diagnostics, not successful conformance
    # checks. Keep the formal model's architecturally unsigned immediate.
    diagnostics=[]
    for case,imm in enumerate([0x8000,0xffff]):
        sp=0x600800;location=CODE+0x32000+case*8
        em.mem_write(sp,struct.pack('<I',CODE+0x30000))
        em.mem_write(location,b'\xc2'+struct.pack('<H',imm))
        rr=[0]*8;rr[4]=sp;start(rr)
        em.emu_start(location,CODE+0x30000,count=1)
        actual=em.reg_read(x.UC_X86_REG_ESP);expected=(sp+4+imm)&MASK
        signed=(sp+4+imm-65536)&MASK
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+0x30000,'diagnostic return destination')
        require(actual in [expected,signed],'unrecognized high-immediate discrepancy')
        diagnostics.append(dict(immediate=imm,expected_esp=expected,observed_esp=actual,
          conforms=actual==expected,known_signed_adjustment=actual==signed))
    return dict(chain_cases=256,instruction_cases=128,cases=384,ret8_executed=True,
      emulator_version=u.__version__,high_immediate_diagnostics=diagnostics,
      diagnostic_source='https://mail-archive.com/qemu-devel@nongnu.org/msg1234957.html',
      limitation='High-bit RET immediates are not counted as passing emulator conformance cases. The unsigned formal model is retained; the installed emulator may sign-extend them. Pinned Doom RET 8 is unaffected.',

      checks='complete return chain: all general registers, all mapped data bytes, cursor write, caller PC and instruction counts; null target with stale slope and non-null zero slope; aligned, unaligned and wrapping stacks; isolated RET imm16 in 0..0x7fff, exact flag preservation and wrapping return-address load; high-bit immediates recorded separately as emulator diagnostics',
      flags='Full-chain ADD flags retain existing unknown abstraction; isolated RET imm16 flags checked exactly')

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();require(mp['exe_sha256']==profile['exe_sha256'],'profile mismatch')
    out=ROOT/'artifacts/e1m1-aim-completed-return';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimCompletedReturn'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Opt-in RET imm16 semantics preserving all old instruction executions, pinned RET 8 bytes, and a continuous 20/21 instruction return chain from both ordered-loop exits through P_PathTraverse to the aiming caller. Final EAX matches the source slope under the existing exit relation and non-null resolver premise. Saved return addresses and stack separation are endpoint assumptions, not yet established through the loop. Full aiming/reachable-state equivalence remains open. Earlier Doom sources and the old decoder/interpreter are unchanged.',
      cross_check=cross_check(raw) if args.cross_check else None)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: authenticated RET 8 and complete aim return chain; strict axiom audit.'+(f" {report['cross_check']['cases']} emulator cases." if args.cross_check else ''))
if __name__=='__main__':main()
