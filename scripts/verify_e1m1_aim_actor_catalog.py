#!/usr/bin/env python3
"""Authenticate actor catalog transport and portal-prefix selection."""
import argparse,json,re,subprocess
import verify_e1m1_aim_actor_dispatch as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
GROUPS={'E1M1AimActorCatalog':['entry_preserved','preserved','opening_reads','inputs'],
        'E1M1AimActorCatalogCycle':['execution'],'E1M1AimActorPortalPrefix':['selected']}
PRESERVE_ARGS='s out marked scene shooter initial resolve who frame stack pointer bounded catalog'
INPUT_ARGS='s scene shooter thing initial work seen visits resolve portals distance target sp who fraction j history selection before catalog isThing'
EXEC_ARGS=previous.EXEC_ARGS.replace('shooterSafe flagsSafe shooterWord identity flags topSafe safe z0 ht','catalog').replace(' saveSafe','')
PREFIX_ARGS='scene shooter thing path original distance resolve portals who represented empty query a final count sequence origin s seen visits history aligned bottom top catalog fraction j chosen within isThing different shootable topSlope bottomSlope topOk admitted bottomOk bottomAdmitted'
CONTRACTS=[('E1M1AimActorCatalog','preserved','preserved_checked',PRESERVE_ARGS),
 ('E1M1AimActorCatalog','inputs','inputs_checked',INPUT_ARGS),
 ('E1M1AimActorCatalogCycle','execution','cycle_checked',EXEC_ARGS),
 ('E1M1AimActorPortalPrefix','selected','prefix_checked',PREFIX_ARGS)]

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:source.index(' := by',a)]
    decl=re.sub(r'(?<![.\w])program\b','Doom.Proofs.E1M1AimActorSelect.program',decl)
    owners={'Catalog':'E1M1AimActorCatalog','Entry':'E1M1AimActorCatalog','Inputs':'E1M1AimActorCatalog',
            'Outcome':'E1M1AimActorCycle','dispatch':'E1M1AimActorDispatch','Represents':'E1M1AimSourceCatalog',
            'AlignedNext':'E1M1AimSynchronizedCycle','Position':'E1M1AimPortalPrefix','Sequence':'E1M1AimPortalPrefix',
            'minimum':'E1M1InterceptMinimum','StableWord':'E1M1AimMapFrame','address':'E1M1MinimumScan'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b',lambda m:'Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimActorPortalPrefix\n'+previous.certificate(data,raw)
    source+='\nnamespace Doom.Verification.ExtractedAimActorCatalog\n'+HEADER
    source+='def linked := Doom.Verification.ExtractedAimActorSelect.linked\n'
    source+='theorem linked_checked : linked=E1M1AimActorSelect.program := Doom.Verification.ExtractedAimActorSelect.linked_checked\n'
    for module,name,checked,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+checked,1)
        decl=decl.replace('Doom.Proofs.E1M1AimActorSelect.program','linked')
        source+='namespace '+module+'\n'+decl+' := by\n  '+('rw [linked_checked]\n  ' if 'linked []' in decl else '')+'exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='#print axioms linked_checked\n'
    source+='\n'.join('#print axioms '+m+'.'+checked for m,_,checked,_ in CONTRACTS)+'\nend Doom.Verification.ExtractedAimActorCatalog\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedAimActorCatalog.linked_checked'"
    require(marker in output,'missing actor return audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedAimActorCatalog.linked_checked']
    names+=['Doom.Verification.ExtractedAimActorCatalog.'+m+'.'+checked for m,_,checked,_ in CONTRACTS]
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
    out=ROOT/'artifacts/e1m1-aim-actor-catalog';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimActorPortalPrefix'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='An initial catalog supplies actor pointer identity, shootability, z, height and protected memory facts for any selected actor. '
      'The whole catalog survives a continuing callback frame and is carried by the unified actor cycle. '
      'A proved portal prefix transports the catalog to a selected actor, then executes its real callback return and parent stop with the canonical target/slope result. '
      'Initial catalog establishment, arbitrary mixed iteration, enclosing traversal return and whole aiming remain open. '
      'No new binary ranges, runtime changes or instruction semantics changes. Emulator evidence is inherited; this milestone adds composition proofs.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: actor catalog and portal-prefix selection; strict axiom audit.')
if __name__=='__main__':main()
