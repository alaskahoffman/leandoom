#!/usr/bin/env python3
"""Certify exact stamp history through complete cells and mixed itineraries."""
import argparse,json,re,subprocess
import verify_e1m1_aim_stamp_next_scan as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
GROUPS={'E1M1AimStampCell': ['scan', 'gate'],
 'E1M1AimStampCellTail': ['object_run', 'advance'],
 'E1M1AimStampWalk': ['outside', 'inside_one', 'one', 'execution', 'from_entry']}
CONTRACTS=[('E1M1AimStampCellTail',
  'object_run',
  's sp base lines epoch words w h objects trace cell data nodes r seen pc success stack maps mapLayout payload payloadSafe '
  'contracts x y mapX mapY inMap links selection selectionSafe tracked capacity represented returns epochSafe stampSafe locals'),
 ('E1M1AimStampCellTail',
  'advance',
  's sp base lines epoch words w h objects trace cell data nodes r seen pc success stack maps mapLayout payload payloadSafe '
  'contracts x y mapX mapY inMap links selection selectionSafe tracked capacity represented returns epochSafe stampSafe locals '
  'world dimension ids scene origin image'),
 ('E1M1AimStampCell',
  'scan',
  's sp cursor base lines epoch words w h objects trace cell data nodes r seen pc stack list items ids target returnWord maps '
  'mapLayout payload payloadSafe contracts layout x y mapX mapY inMap links selection selectionSafe tracked capacity represented '
  'size stamps returns epochSafe stampSafe locals world dimension sceneIds scene origin image'),
 ('E1M1AimStampCell',
  'gate',
  's sp base lines epoch words w h objects trace cell data nodes r seen pc stack valid maps mapLayout payload payloadSafe '
  'contracts layout x y mapX mapY selected inMap links selection selectionSafe tracked cursorSafe recordsSafe capacity '
  'represented size stamps returns epochSafe stampSafe locals world dimension sceneIds scene origin image'),
 ('E1M1AimStampWalk', 'outside', 'q s r seen common state pc x y mapX mapY outMap origin image'),
 ('E1M1AimStampWalk', 'inside_one', 'q c s r seen common static state images pc x y room origin stampImage'),
 ('E1M1AimStampWalk', 'one', 'q c s r seen common static state images pc x y room origin image'),
 ('E1M1AimStampWalk', 'execution', 'q cells s r seen common statics state images entry follows room origin image'),
 ('E1M1AimStampWalk', 'from_entry', 'q cells s r seen common statics state images entry follows room')]
NAMESPACE='Doom.Verification.ExtractedAimStampWalk'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'LineData':'E1M1ScanContracts','candidates':'E1M1ScanContracts',
      'Represents':'OriginalLineVisits','stamp':'OriginalLineVisits','markPrefix':'OriginalLineVisits',
      'TailSafe':'E1M1FiringVisitedNext','Context':'E1M1CellWalkInvariant',
      'Cell':'E1M1CellWalkInvariant','Common':'E1M1CellWalkInvariant',
      'Follows':'E1M1CellWalk','grid':'E1M1CellWalk','stopPc':'E1M1CellWalk',
      **dict.fromkeys(['Admitted','Images','cost','instructions','budget','bound','next','visits',
        'history','CellResult','Collection'],'E1M1MixedCellWalk')}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimStampWalk\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    source+='\n'.join([
      'def linked := Doom.Verification.ExtractedAimStampNextScan.linked',
      'theorem linked_checked : linked=E1M1AimProgramLink.program :=',
      '  Doom.Verification.ExtractedAimStampNextScan.linked_checked',
      'def returnProgram := Doom.Verification.ExtractedAimCompletedReturn.linked',
      'theorem returnProgram_checked : returnProgram=E1M1AimCompletedReturn.program :=',
      '  Doom.Verification.ExtractedAimCompletedReturn.linked_checked',
      ''])
    for module,name,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+name+'_checked',1)
        decl=decl.replace('E1M1AimProgramLink.program','linked').replace('E1M1AimCompletedReturn.program','returnProgram')
        source+='namespace '+module+'\n'+decl+' := by\n  '
        if 'linked' in decl:source+='rw [linked_checked]\n  '
        if 'returnProgram' in decl:source+='rw [returnProgram_checked]\n  '
        source+='exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='#print axioms linked_checked\n#print axioms returnProgram_checked\n'
    source+='\n'.join('#print axioms '+m+'.'+n+'_checked' for m,n,_ in CONTRACTS)+'\nend '+NAMESPACE+'\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'"+NAMESPACE+".linked_checked'"
    require(marker in output,'missing query selection audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=[NAMESPACE+'.linked_checked',NAMESPACE+'.returnProgram_checked']
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
    out=ROOT/'artifacts/e1m1-aim-stamp-walk';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimStampWalk'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Exact original stamp values now accompany real in-map and outside-map cell executions, object list traversal, grid advancement and finite mixed itineraries. The entry specialization uses the authenticated combined aim program and derives conditional next-epoch freshness from initial memory words, retaining source collection and state invariants. The supplied itinerary, map/object layout, capacity and initial invariant remain premises. This is not yet connected to whole-query initialization, ordered aiming, return and retry; reachable freshness and full three-probe correspondence remain open. No runtime, decoder, instruction-semantic or binary-range changes; no emulator rerun',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: exact stamp history follows complete cells and mixed itineraries; authenticated-program execution and strict axiom audit.')
if __name__=='__main__':main()
