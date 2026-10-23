#!/usr/bin/env python3
"""Authenticated word-fill loops; complete startup suffix for 32-byte destinations.
The 4-byte-only alignment heads and nonzero word tails remain OPEN.
"""
import argparse,json,random,re,subprocess,sys
sys.setrecursionlimit(max(sys.getrecursionlimit(),10000))
import verify_e1m1_aim_side_memset as previous
ROOT,require=previous.ROOT,previous.require
MODULE='E1M1AimWordFill'
NS='Doom.Verification.ExtractedAimWordFill'
INFRA=['Prefix.trans','Prefix.transfer','lift_prefix']
HEADER='open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary E1M1AimWordFill\n'
def contracts():
    return re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{MODULE}.lean').read_text(),re.M)
def names():
    return [NS+'.'+k+'_checked' for k in ['words','program']]+[
      n for k in contracts() for n in [NS+'.'+k+'_checked','Doom.Proofs.'+MODULE+'.'+k]]+[
      'Doom.Verification.X86WordFillRoutine.'+k for k in INFRA]
def certificate():
    bs,_,_=previous.fill_data()
    source='import Doom.Proofs.E1M1AimWordFill\n'+previous.certificate()
    imports=list(dict.fromkeys(re.findall(r'^import .+$',source,re.M)))
    source='\n'.join(imports)+'\n'+re.sub(r'^import .+\n','',source,flags=re.M)
    source+='\nnamespace '+NS+'\n'+HEADER
    source+='def words : List UInt8 := ['+','.join(hex(b) for b in bs['fill_words'])+']\n'
    source+='theorem words_checked : words=E1M1AimWordFill.wordsBytes := by decide +kernel\n'
    source+='def program : X86WordFillRoutine.Program := fun pc =>\n  if 0x41917≤pc ∧ pc<0x41983 then X86WordFillRoutine.decodeAt words (pc-0x41917)\n  else X86WordFillRoutine.liftProgram Doom.Verification.ExtractedAimSideMemset.program pc\ntheorem program_checked : program=E1M1AimWordFill.program := by\n  unfold program\n  rw [words_checked,Doom.Verification.ExtractedAimSideMemset.program_checked]; rfl\n'
    for name in contracts():
        decl,args=previous.previous.previous.contract(MODULE,name)
        decl=re.sub(r'(?<![\w.])Knowledge\b','Doom.Verification.X86WordFillRoutine.Knowledge',decl)
        decl=decl.replace('theorem '+name,'theorem '+name+'_checked',1)
        changed=decl.replace('Doom.Proofs.E1M1AimWordFill.program',NS+'.program')
        source+=changed+' := by\n'
        if changed!=decl:source+='  simp only ['+NS+'.program_checked]\n'
        source+='  exact Doom.Proofs.'+MODULE+'.'+name+' '+args+'\n'
    source+='end '+NS+'\n'
    return source+'\n'.join('#print axioms '+n for n in names())+'\n'
def audit(output):
    marker="'"+names()[0]+"'";require(marker in output,'missing word fill audit')
    inherited,rest=output.split(marker,1);previous.audit(inherited);rest=(marker+rest).strip()
    for full in names():
        m=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+full)
        require({a.strip() for a in (m[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')
def flag_cross_check():
    import unicorn as u
    from unicorn import x86_const as x
    bs,_,_=previous.fill_data();words=bs['fill_words']
    dec=words[0x41924-0x41917:0x41925-0x41917]
    shr=words[0x41928-0x41917:0x4192b-0x41917]
    require(dec==b'\x49' and shr==b'\xc1\xe9\x02','authenticated opcodes changed')
    rng=random.Random(0x41928)
    values=[0,1,2,3,4,5,7,8,2916,729,728,1<<31,(1<<31)-1,0xffffffff]+[rng.getrandbits(32) for _ in range(32)]
    checks=[]
    for instruction,code in [('dec',dec),('shr2',shr)]:
      for value in values:
       for bits in range(16):
        flags=2|((bits&1)<<0)|(((bits>>1)&1)<<6)|(((bits>>2)&1)<<7)|(((bits>>3)&1)<<11)
        em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);em.mem_map(0x1000,0x1000);em.mem_write(0x1000,code)
        em.reg_write(x.UC_X86_REG_ECX,value);em.reg_write(x.UC_X86_REG_EFLAGS,flags)
        em.emu_start(0x1000,0x1000+len(code),count=1)
        result=((value-1)&0xffffffff) if instruction=='dec' else value>>2
        actual=em.reg_read(x.UC_X86_REG_EFLAGS)
        require(em.reg_read(x.UC_X86_REG_ECX)==result,'register result')
        require(bool(actual&(1<<6))==(result==0),'defined ZF')
        if instruction=='dec':
            require((actual&1)==(flags&1),'DEC must preserve CF')
            require(bool(actual&(1<<7))==bool(result&(1<<31)),'DEC SF')
            require(bool(actual&(1<<11))==(value==1<<31),'DEC OF')
        # OF after SHR2 is expressly NOT compared or fixed. SF/CF are conservatively forgotten.
        checks.append((instruction,value,bits))
    return dict(cases=len(checks),dec_cases=sum(c[0]=='dec' for c in checks),shr2_cases=sum(c[0]=='shr2' for c in checks),
      undefined_OF_assigned=False,shr2_projected_flags=['ZF'],dec_flags=['ZF','SF','OF','preserved CF'])
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    out=ROOT/'artifacts/e1m1-aim-word-fill';out.mkdir(exist_ok=True)
    (out/'Checked.lean').write_text(certificate())
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.'+MODULE],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(out/'Checked.lean')],cwd=ROOT,capture_output=True,text=True,timeout=300)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout);require(not checked.stderr.strip(),'unexpected stderr')
    native=None
    if args.cross_check:
        native=dict(full_memset=previous.cross_check(),partial_flags=flag_cross_check())
        native['formal_32byte_destination_cases']=sum((c['alignment']+24)%32==0 for c in native['full_memset']['details'])
        native['full_memset']['scope']+=' The new word-fill theorem covers only the 32-byte-aligned subset, universally, under its static stack separations.'
        (out/'cross-check.json').write_text(json.dumps(native,indent=2)+'\n')
    elif (out/'cross-check.json').exists():native=json.loads((out/'cross-check.json').read_text())
    prior=json.loads((ROOT/'artifacts/e1m1-aim-side-memset/report.json').read_text())
    units=dict(prior['units']);_,new,_=previous.fill_data();units['fill_words']=new['fill_words']
    unique={(int(v['code_offset'],16),len(bytes.fromhex(v['hex']))) for v in units.values()}
    audits=re.findall(r"^'([^']+)'",checked.stdout,re.M)
    report=dict(exe_sha256=prior['exe_sha256'],wad_sha256=prior['wad_sha256'],units=units,unique_ranges=len(unique),
      public_theorems=len(contracts())+len(INFRA),audited_declarations=len(audits),unique_audited_declarations=len(set(audits)),cross_check=native,
      scope='Universal symbolic 16/32-byte group loops, exact count/cursor and byte zeroing, actual saved-word derivation and all three RETs. Continuous original entry0x2e3e0 to0x2e437 in at most5240 instructions for explicitly32-byte-aligned destinations. All11664 output bytes zero. Static initial heap/catalog/stack/output separations remain assumptions. Four-byte-only alignment heads and nonzero word tails NOT completed; no cache/read/gate or initialized-startup theorem.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: complete32-byte-aligned memset/returns; four-byte-only cases remain open.')
if __name__=='__main__':main()
