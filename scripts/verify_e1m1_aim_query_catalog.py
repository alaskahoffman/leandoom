#!/usr/bin/env python3
"""Certify initial aim-loop entry and query-memory transport for all catalogs."""
import argparse,json,re,subprocess
import verify_e1m1_aim_query_selection as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
GROUPS={
 'E1M1AimInitialBoundary':['boundary'], 'E1M1AimInitialCaller':['execution'],
 'E1M1AimEntryCatalog':['byte','half','actor_entry','actors','walls','portal_entry','portals'],
 'E1M1AimQueryCatalog':['image','live_stack','catalogs','globals']}
CONTRACTS=[
 ('E1M1AimInitialBoundary','boundary','scene shooter thing path original distance resolve portals base s outcome shape empty query persistent'),
 ('E1M1AimInitialCaller','execution','scene shooter thing path original distance resolve portals walls who represented wallMap covered empty query available base s outcome persistent bottom top actors wallCatalog targetSafe null protect shape nonnull first second'),
 ('E1M1AimEntryCatalog','byte','before after P image a safe'),
 ('E1M1AimEntryCatalog','half','before after P image a safe'),
 ('E1M1AimEntryCatalog','actor_entry','s t P image stack pointer actor reads entry'),
 ('E1M1AimEntryCatalog','actors','s t scene shooter initial resolve who P image stack reads catalog'),
 ('E1M1AimEntryCatalog','walls','s t initial resolve solid P image stack reads catalog'),
 ('E1M1AimEntryCatalog','portal_entry','s t hit line p P image stack reads entry'),
 ('E1M1AimEntryCatalog','portals','s t initial resolve catalogue P image stack reads catalog'),
 ('E1M1AimQueryCatalog','image','q s out frame'),
 ('E1M1AimQueryCatalog','live_stack','q s hits resolve out outcome live'),
 ('E1M1AimQueryCatalog','catalogs','q s out scene shooter hits resolve who solid openings outcome live frame actorReads wallReads portalReads actors walls portals'),
 ('E1M1AimQueryCatalog','globals','q s out distance z frame safe range eye bottom top null')]
NAMESPACE='Doom.Verification.ExtractedAimQueryCatalog'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'Image':'E1M1AimEntryCatalog','ActorReads':'E1M1AimEntryCatalog',
      'WallReads':'E1M1AimEntryCatalog','PortalReads':'E1M1AimEntryCatalog',
      'view':'E1M1AimQueryCatalog','Protected':'E1M1AimQueryCatalog',
      'Portal':'E1M1AimCatalog','Persistent':'E1M1AimTraversalInvariant',
      'Represents':'E1M1AimSourceCatalog','Available':'E1M1AimOrderedLoop',
      'Catalog':'E1M1AimActorCatalog','StableWord':'E1M1AimMapFrame','Shape':'E1M1AimStackShape'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimQueryCatalog\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    source+='''
def returnProgram := Doom.Verification.ExtractedAimCompletedReturn.linked
theorem returnProgram_checked : returnProgram=E1M1AimCompletedReturn.program :=
  Doom.Verification.ExtractedAimCompletedReturn.linked_checked
'''
    for module,name,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+name+'_checked',1)
        decl=decl.replace('E1M1AimCompletedReturn.program','returnProgram')
        source+='namespace '+module+'\n'+decl+' := by\n  '
        if 'returnProgram []' in decl:source+='rw [returnProgram_checked]\n  '
        source+='exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='#print axioms returnProgram_checked\n'
    source+='\n'.join('#print axioms '+m+'.'+n+'_checked' for m,n,_ in CONTRACTS)+'\nend '+NAMESPACE+'\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'"+NAMESPACE+".returnProgram_checked'"
    require(marker in output,'missing query selection audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=[NAMESPACE+'.returnProgram_checked']
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
    out=ROOT/'artifacts/e1m1-aim-query-catalog';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimQueryCatalog'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Actual first-scan alternatives enter the exhaustive mixed-hit/return theorem without a previous-callback alignment premise. Generic protected-word transport preserves actor, wall and portal catalogs, including flag bytes and side halfwords. Query-specific wrappers derive live stack equality, carry initial-memory catalogs and five aiming globals using the established query frame. Static read protection, initial catalogs/values, persistent callback layout/slot and saved caller assumptions remain explicit. Full continuous query-through-return linking and reachable-state aiming equivalence remain open. No runtime, byte-range or instruction-semantic changes; emulator evidence inherited, not rerun.',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: initial loop boundary and query catalog transport; strict axiom audit.')
if __name__=='__main__':main()
