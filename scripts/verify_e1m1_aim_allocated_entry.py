#!/usr/bin/env python3
"""Certify range-based aiming entry guards against the inherited DOS/map certificate."""
import argparse,json,re,subprocess
import verify_e1m1_aim_original_inputs as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER+'\nopen Doom.Proofs.E1M1NoiseAllocation (Region)\n'
GROUPS={'E1M1AimRegions': ['stack_word', 'writes_contained', 'safe_reads', 'field', 'kept'], 'E1M1AimStaticRegions': ['table_word', 'sample_words', 'map_word', 'line_stamp', 'map_covered', 'stamps_covered', 'geometry_covered', 'tables_safe'], 'E1M1AimAllocatedEntry': ['setup_safe', 'angle_safe', 'inputs', 'fresh']}
CONTRACTS=[('E1M1AimRegions', 'stack_word', 'stack s reserve n low high'), ('E1M1AimRegions', 'writes_contained', 'stack s reserve'), ('E1M1AimRegions', 'safe_reads', 'stack s addresses reserve covered'), ('E1M1AimRegions', 'field', 'base bytes offset bound fits'), ('E1M1AimRegions', 'kept', 'stack s f addresses reserve covered'), ('E1M1AimStaticRegions', 'table_word', 'i'), ('E1M1AimStaticRegions', 'sample_words', 'angle'), ('E1M1AimStaticRegions', 'map_word', 'base bound i hi'), ('E1M1AimStaticRegions', 'line_stamp', 'lines bound j hj'), ('E1M1AimStaticRegions', 'map_covered', 'stack base lines who words placement size'), ('E1M1AimStaticRegions', 'stamps_covered', 'stack base lines who count placement size'), ('E1M1AimStaticRegions', 'geometry_covered', 'stack base lines s angle placement'), ('E1M1AimStaticRegions', 'tables_safe', 'stack s reserve separate'), ('E1M1AimAllocatedEntry', 'setup_safe', 'q stack s angle reserve placement words lines'), ('E1M1AimAllocatedEntry', 'angle_safe', 'stack s base lines reserve placement'), ('E1M1AimAllocatedEntry', 'inputs', 'q stack s f thing angle reserve placement words before tables value'), ('E1M1AimAllocatedEntry', 'fresh', 'stack s f base lines epoch reserve placement before')]
NAMESPACE='Doom.Verification.ExtractedAimAllocatedEntry'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'Region':'E1M1NoiseAllocation','StackReserve':'E1M1AimRegions','Covered':'E1M1AimRegions',
      'globals':'E1M1AimStaticRegions','blockmap':'E1M1AimStaticRegions','linedefs':'E1M1AimStaticRegions',
      'Layout':'E1M1AimStaticRegions','layout':'E1M1AimControllerInputs'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimAllocatedEntry\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    source+='''
/-- The word count used by the guard is checked against the pinned WAD extraction. -/
theorem pinned_map_checked (stack : Region) (base lines who : Word)
    (placement : E1M1AimStaticRegions.Layout stack base lines who) :
    E1M1AimRegions.Covered stack
      (E1M1AimRetryData.mapReads base Doom.Verification.ExtractedPathMap.words) := by
  exact E1M1AimStaticRegions.map_covered stack base lines who _ placement
    Doom.Verification.ExtractedPathMap.shape_checked.1
'''
    for module,name,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+name+'_checked',1)
        source+='namespace '+module+'\n'+decl+' := by\n  '
        source+='exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='#print axioms pinned_map_checked\n'
    source+='\n'.join('#print axioms '+m+'.'+n+'_checked' for m,n,_ in CONTRACTS)+'\nend '+NAMESPACE+'\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'"+NAMESPACE+".pinned_map_checked'"
    require(marker in output,'missing query selection audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=[NAMESPACE+'.pinned_map_checked']
    names+=[NAMESPACE+'.'+m+'.'+n+'_checked' for m,n,_ in CONTRACTS]
    names+=['Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]
    for full in names:
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')


def main():
    argparse.ArgumentParser(description=__doc__).parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();require(mp['exe_sha256']==profile['exe_sha256'],'profile mismatch')
    out=ROOT/'artifacts/e1m1-aim-allocated-entry';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimAllocatedEntry'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Prologue guards for setup geometry, 3461 blockmap halfwords, all 475 linedef stamps, the shooter angle, and all 10240 trig table entries follow from scalar nonwrapping region bounds and separation from a stack with twenty bytes of reserve. These guards feed the actual first-query setup transport, table transport, register realization and arbitrary-epoch freshness preservation. The blockmap protection envelope deliberately includes two bytes beyond its 6922-byte payload because the prior transport uses four-byte windows. This is not a DOS startup allocation certificate: region placement and pre-existing memory representations, inner-call guards, arithmetic success, capacity and freshness remain premises. Actor/cell catalogs beyond setup still need their own coverage. The complete outer controller theorem is inherited, unchanged and conditional. No runtime or instruction-semantic changes; emulator evidence inherited, not rerun.',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: pinned-map range guards connected to aiming entry; strict inherited axiom audit.')
if __name__=='__main__':main()
