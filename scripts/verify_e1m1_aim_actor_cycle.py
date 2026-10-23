#!/usr/bin/env python3
"""Check actor skip/scan composition and alignment against authenticated DOS code."""
import json,re,subprocess
import verify_e1m1_aim_actor_skip as previous
ROOT,require=previous.ROOT,previous.require
pinned_data=previous.pinned_data
extracted=previous.extracted
GROUPS={
 'E1M1AimActorSkipCycle':['registers','frame','scan','carried','execution'],
 'E1M1AimActorSkipAligned':['boundary','next_callback','line_boundary','execution']}
SCAN_ARGS='s f initial work seen visits resolve target sp fraction j selection layout bounded history encoded'
EXEC_ARGS='s f scene shooter thing path original distance lower upper log work seen visits resolve target sp who fraction j history selection portals before empty query bottom top isThing shooterSafe flagsSafe shooterWord identity flags ignored'
NEXT_ARGS='s scene shooter thing path result distance work seen visits resolve portals lower upper log out history empty query aligned fraction j chosen within'
CONTRACTS=[('E1M1AimActorSkipCycle','scan','scan_checked',SCAN_ARGS),
 ('E1M1AimActorSkipAligned','line_boundary','reuse_checked',NEXT_ARGS),
 ('E1M1AimActorSkipAligned','execution','cycle_checked',EXEC_ARGS)]
HEADER='''
set_option backward.isDefEq.respectTransparency false
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1HistoryDispatch (Selection)
open E1M1InterceptMark (consume)
open E1M1AimCatalog (Portal)
open E1M1AimTraversalInvariant (Persistent)
open E1M1AimIteration
open E1M1AimHistoryCycle (Frame)
open E1M1AimWall (Safe)
open E1M1MinimumScan (address)
'''

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:source.index(' := by',a)]
    decl=re.sub(r'\bprogram\b','Doom.Proofs.E1M1AimActorSkip.program',decl)
    decl=re.sub(r'\bNext\b','Doom.Proofs.E1M1AimActorSkipCycle.Next',decl)
    decl=re.sub(r'\bAligned\b','Doom.Proofs.E1M1AimActorSkipAligned.Aligned',decl)
    return decl.replace('(result s)','(Doom.Proofs.E1M1AimActorSkip.result s)')

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimActorSkipAligned\n'+previous.certificate(data,raw)
    source+='\nnamespace Doom.Verification.ExtractedAimActorCycle\n'+HEADER
    for module,name,checked,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+checked,1)
        uses_program='Doom.Proofs.E1M1AimActorSkip.program' in decl
        decl=decl.replace('Doom.Proofs.E1M1AimActorSkip.program','Doom.Verification.ExtractedAimActorSkip.linked')
        body=('by\n  rw [Doom.Verification.ExtractedAimActorSkip.linked_checked]\n  exact ' if uses_program else '')
        source+='namespace '+module+'\n'+decl+' := '+body+'Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='\n'.join('#print axioms '+m+'.'+checked for m,_,checked,_ in CONTRACTS)+'\nend Doom.Verification.ExtractedAimActorCycle\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedAimActorCycle.E1M1AimActorSkipCycle.scan_checked'"
    require(marker in output,'missing actor cycle audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedAimActorCycle.'+m+'.'+checked for m,_,checked,_ in CONTRACTS]
    names+=['Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]
    for full in names:
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def main():
    data,mp=pinned_data();spec,profile,raw=extracted();require(mp['exe_sha256']==profile['exe_sha256'],'profile mismatch')
    out=ROOT/'artifacts/e1m1-aim-actor-cycle';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimActorSkipAligned'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Self/nonshootable actor rejection composes with the real parent mark, repeat head, minimum scan and indirect CALL. '
      'The exact exhaustion and beyond-range exits remain distinct; an admitted next callback preserves the portal invariant and aligns with the canonical source suffix. '
      'That admitted boundary reuses existing line/portal proofs without substituting their terminal machine state for the actor state. '
      'Actor pointer/flag representation, read separation and the incoming persistent invariant remain premises. '
      'Eligible actor slopes, clipping, target selection, actor catalogs, mixed iteration, whole aiming and reachable-state premise discharge remain open. '
      'No new code range, decoder, instruction semantics or runtime changes; prior emulator evidence is inherited, not rerun.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: actor skip, next scan and aligned callback; strict axiom audit.')
if __name__=='__main__':main()
