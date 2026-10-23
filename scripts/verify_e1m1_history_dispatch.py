#!/usr/bin/env python3
"""Authenticate the repeated-hit entry state and source-history connection."""
import argparse,json,re,subprocess
import verify_e1m1_ordered_history as previous
ROOT,require=previous.ROOT,previous.require
pinned_data=previous.pinned_data
extracted=previous.extracted
GROUPS={
 'E1M1SelectionRegisters':['scan','execution'],
 'E1M1NextCallbackState':['dispatch','callback_slot'],
 'E1M1HistoryDispatch':['execution','source_continue','source_stop']}
ENTRY_ARGS='s f initial work seen visits resolve history bounded counter limit encoded maximum targetSafe cursorSafe recordSafe'
SOURCE_ARGS='initial work priorVisits visits seen resolve target sp out distance j selection history result log visit accept'
cross_check=previous.cross_check


def certificate(data,raw):
    source='import Doom.Proofs.E1M1HistoryDispatch\n'+previous.certificate(data,raw)
    source+='\nnamespace Doom.Verification.ExtractedHistoryDispatch\nset_option backward.isDefEq.respectTransparency false\nopen Doom Doom.Proofs X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory E1M1InterceptMinimum\nopen E1M1AimNextSelection (head)\nopen E1M1MinimumScan (address)\nopen E1M1AimRepeatProgram (program ReadFrame)\nopen E1M1OrderedTraversal (appended)\nopen E1M1OrderedVisit (walk)\nopen E1M1InterceptMark (consume)\nopen E1M1HistoryDispatch (Selection Outcome)\n'
    for module,name,checked,args in [('E1M1HistoryDispatch','execution','entry_checked',ENTRY_ARGS),('E1M1HistoryDispatch','source_continue','source_checked',SOURCE_ARGS)]:
        text=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=text.index('theorem '+name+' ')
        decl=text[a:text.index(' := by',a)].replace('theorem '+name,'theorem '+checked,1)
        source+=decl+' := '+module+'.'+name+' '+args+'\n'
    source+='\n'.join('#print axioms '+n for n in ['entry_checked','source_checked'])+'\nend Doom.Verification.ExtractedHistoryDispatch\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedHistoryDispatch.entry_checked'"
    require(marker in output,'missing history dispatch audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedHistoryDispatch.'+n for n in ['entry_checked','source_checked']]
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
    out=ROOT/'artifacts/e1m1-history-dispatch';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1HistoryDispatch'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Authentic repeat-head, full minimum scan and indirect CALL preserve the remaining counter and provide both selected-record pointers, cursor, return frame and encoded buffer. '
      'Source history derives a fresh original hit and exact remaining budget; source continue/stop use that hit at the correct callback index. '
      'Full callback-loop induction, preservation of next map/global/stack contracts, and precomputed all-hit aim suffix alignment remain open. No runtime or decoder changes.')
    if args.cross_check:report['cross_check']=cross_check(raw)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: repeated callback state and source-history alignment; strict axiom audit.')
if __name__=='__main__':main()
