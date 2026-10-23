#!/usr/bin/env python3
"""Authenticate mixed portal/actor traversal and final actor selection."""
import argparse,json,re,subprocess
import verify_e1m1_aim_actor_catalog as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
GROUPS={'E1M1AimMixedStep':['execution'],
        'E1M1AimMixedPrefix':['next_choice','execution','capacity'],'E1M1AimMixedSelected':['selected']}
STEP_ARGS='scene shooter thing path original distance resolve portals who represented empty query a b j step s f seen visits sp fraction history selection before bottom top catalog nextFraction k chosen within'
PREFIX_ARGS='scene shooter thing path original distance resolve portals who represented empty query a final count sequence origin s seen visits history aligned bottom top catalog fraction j chosen within'
SELECT_ARGS=previous.PREFIX_ARGS
CONTRACTS=[('E1M1AimMixedStep','execution','step_checked',STEP_ARGS),
 ('E1M1AimMixedPrefix','execution','prefix_checked',PREFIX_ARGS),
 ('E1M1AimMixedPrefix','capacity','capacity_checked',PREFIX_ARGS),
 ('E1M1AimMixedSelected','selected','selected_checked',SELECT_ARGS)]

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:source.index(' := by',a)]
    decl=re.sub(r'(?<![.\w])program\b','Doom.Proofs.E1M1AimActorSelect.program',decl)
    owners={'Catalog':'E1M1AimActorCatalog','Entry':'E1M1AimActorCatalog','Inputs':'E1M1AimActorCatalog',
            'Outcome':'E1M1AimActorCycle','dispatch':'E1M1AimActorDispatch','Represents':'E1M1AimSourceCatalog',
            'AlignedNext':'E1M1AimSynchronizedCycle','Position':'E1M1AimPortalPrefix','Sequence':'E1M1AimMixedPrefix','Step':'E1M1AimMixedStep',
            'minimum':'E1M1InterceptMinimum','StableWord':'E1M1AimMapFrame','address':'E1M1MinimumScan'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b',lambda m:'Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimMixedSelected\n'+previous.certificate(data,raw)
    source+='\nnamespace Doom.Verification.ExtractedAimMixedTraversal\n'+HEADER
    source+='def linked := Doom.Verification.ExtractedAimActorSelect.linked\n'
    source+='theorem linked_checked : linked=E1M1AimActorSelect.program := Doom.Verification.ExtractedAimActorSelect.linked_checked\n'
    for module,name,checked,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+checked,1)
        decl=decl.replace('Doom.Proofs.E1M1AimActorSelect.program','linked')
        source+='namespace '+module+'\n'+decl+' := by\n  '+('rw [linked_checked]\n  ' if 'linked []' in decl else '')+'exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='#print axioms linked_checked\n'
    source+='\n'.join('#print axioms '+m+'.'+checked for m,_,checked,_ in CONTRACTS)+'\nend Doom.Verification.ExtractedAimMixedTraversal\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedAimMixedTraversal.linked_checked'"
    require(marker in output,'missing mixed traversal audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedAimMixedTraversal.linked_checked']
    names+=['Doom.Verification.ExtractedAimMixedTraversal.'+m+'.'+checked for m,_,checked,_ in CONTRACTS]
    names+=['Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]
    for full in names:
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')


def main():
    parser=argparse.ArgumentParser();parser.parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();require(mp['exe_sha256']==profile['exe_sha256'],'profile mismatch')
    out=ROOT/'artifacts/e1m1-aim-mixed-traversal';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimMixedSelected'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Any supplied finite source sequence of continuing portals and ignored/top-rejected/bottom-rejected actors '
      'is realized by concatenated authenticated instruction prefixes, ending at an admitted callback. '
      'Both catalogs, source index, history, clipped bounds and portal log are derived at each reached state. '
      'The count is bounded by remaining distinct records. A final successful actor executes through its return and parent stop '
      'with the canonical target and slope. Initial reachable-state premises, terminal no-hit/blocking cases after a mixed prefix, '
      'enclosing returns and whole aiming remain open. No new binary ranges, runtime or instruction-semantics changes. '
      'Emulator evidence is inherited; this milestone proves composition.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: mixed traversal and final selection; strict axiom audit.')
if __name__=='__main__':main()
