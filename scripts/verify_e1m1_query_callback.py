#!/usr/bin/env python3
"""Authenticate query-to-callback target, record and return-word correspondence."""
import argparse,json,re,subprocess
import verify_e1m1_query_dispatch as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
GROUPS={
 'E1M1SelectionFrame':['scan','execution'],
 'E1M1CallbackEntry':['cursor_apart','memory','frame','control','records','dispatch','selected_record'],
 'E1M1QueryCallback':['collection','execution','aim_argument','specialize_aim','aim_destination']}

def certificate(data,raw):
    source='import Doom.Proofs.E1M1QueryCallback\n'+previous.certificate(data,raw)
    source+='''
namespace Doom.Verification.ExtractedQueryCallback
set_option backward.isDefEq.respectTransparency false
open Doom Doom.Proofs X86 X86Memory X86Control
open E1M1CellWalkInvariant (Context Cell Common State)
open E1M1MixedCellWalk (inside Admitted budget bound history)
open E1M1GridRoute (sourceRoute)
open E1M1QueryCollection (path Entry)
open E1M1TraversalEntry (Protected)
open E1M1CallbackEntry (Outcome)
open E1M1QueryCallback (CallbackSafe)
'''
    text=(ROOT/'Doom/Proofs/E1M1QueryCallback.lean').read_text();a=text.index('theorem execution ')
    decl=text[a:text.index(' := by',a)].replace('theorem execution','theorem execution_checked',1).replace('FloorCaller.cm program','FloorCaller.cm ExtractedQueryDispatch.linked')
    source+=decl+' := by\n  rw [ExtractedQueryDispatch.program_checked]\n  exact E1M1QueryCallback.execution q pick s f sx sy ex ey entry profile xout yout okX okY common height statics scenes payloads separated callbackSafe room\n'
    source+='#print axioms execution_checked\nend Doom.Verification.ExtractedQueryCallback\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedQueryCallback.execution_checked'"
    require(marker in output,'missing callback audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedQueryCallback.execution_checked']
    names+=['Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]
    for full in names:
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();require(mp['exe_sha256']==profile['exe_sha256'],'profile mismatch')
    out=ROOT/'artifacts/e1m1-query-callback';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1QueryCallback'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Query entry through first dispatch retains the callback target from entry memory, exact selected record, full buffer encoding, callee stack and return word. '
      'The proved aim caller supplies PTR_AimTraverse (0x2b760); specialization identifies its entry or the no-hit exit. '
      'New premises are static argument/return-slot separation, not future states or callback results. '
      'Callback body/clipping, repeated processing, enclosing return/caller composition and reachable-state discharge remain open. '
      'No runtime, decoder or instruction-semantics change; same authenticated byte ranges.')
    if args.cross_check:report['cross_check']=previous.cross_check(raw)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: callback target, records and return word from query entry; strict axiom audit.')
if __name__=='__main__':main()
