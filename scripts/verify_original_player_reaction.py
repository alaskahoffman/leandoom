#!/usr/bin/env python3
"""Certify the original reaction-time decision, movement call or decrement, and argument reload."""
import argparse
import json
import re
import subprocess
import sys
import verify_original_player_joined as joined

ROOT, require = joined.ROOT, joined.require
NAMES = ['caller_checked','function_checked','callee_checked','execution_checked','observation_checked',
         'Doom.Proofs.PlayerReactionProof.establishes_caller',
         'Doom.Proofs.PlayerReactionProof.skip_nonzero',
         'Doom.Proofs.PlayerReactionProof.timer_result',
         'Doom.Proofs.PlayerReactionProof.caller_load']


def certificate(raw,digest):
    lit=lambda key:'['+', '.join(hex(b) for b in raw[key])+']'
    audits='\n'.join('#print axioms '+n for n in NAMES)
    return f'''-- Original DOOM.EXE SHA-256 {digest}.
import Doom.Proofs.OriginalPlayerReaction
set_option maxRecDepth 32768
namespace Doom.Verification.ExtractedPlayerReaction
open X86Memory X86Control Doom.Proofs Doom.Proofs.PlayerReactionProof
def callerCode : List UInt8 := {lit('playerReactionBytes')}
def functionCode : List UInt8 := {lit('playerFunctionBytes')}
def calleeCode : List UInt8 := {lit('setMobjStateBytes')}
theorem caller_checked : callerCode = callerBytes := by decide
theorem function_checked : functionCode = PlayerFunction.functionBytes := by decide
theorem callee_checked : calleeCode = Doom19.setMobjStateBytes := by decide
theorem execution_checked (s : X86Memory.State) (flags : Option Flags)
    (b : Doom.Motion) (a : Doom.PlayerAnim.State) (c : Doom.Ticcmd) (timer : Int32) (h : Inputs s b a c timer) :
    X86Routine.run (bytesProgram callerCode functionCode calleeCode) [0x333cb]
      124 ⟨s,flags,0x333b1⟩ = some (result s b c) := by
  rw [caller_checked,function_checked,callee_checked]
  exact execution s flags b a c timer h
theorem observation_checked (s : X86Memory.State) (flags : Option Flags)
    (b : Doom.Motion) (a : Doom.PlayerAnim.State) (c : Doom.Ticcmd) (timer : Int32) (h : Inputs s b a c timer) :
    (X86Routine.run (bytesProgram callerCode functionCode calleeCode) [0x333cb]
      124 ⟨s,flags,0x333b1⟩).map (fun t =>
      (t.pc,(load32 t.core.memory (PlayerCaller.object s+(32#32)),load32 t.core.memory (PlayerCaller.object s+(72#32)),
        load32 t.core.memory (PlayerCaller.object s+(76#32))),load32 t.core.memory (PlayerCaller.object s+(100#32)),
        load32 t.core.memory (PlayerCaller.object s+(96#32)),load32 t.core.memory (timerAddress s),t.core.regs 4,t.core.regs 0)) =
      some (0x333cb,
        ((Doom.PlayerReaction.move b timer c).angle.raw.toBitVec,(Doom.PlayerReaction.move b timer c).momx.raw.toBitVec,(Doom.PlayerReaction.move b timer c).momy.raw.toBitVec),
        PlayerAnimation.statePointer (Doom.PlayerReaction.animate a timer c).frame,(Doom.PlayerReaction.animate a timer c).tics.toBitVec,
        (Doom.PlayerReaction.remaining timer).toBitVec,s.regs 4,s.regs 2) := by
  rw [caller_checked,function_checked,callee_checked]
  exact observation s flags b a c timer h
{audits}
end Doom.Verification.ExtractedPlayerReaction
'''



def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedPlayerReaction.'+short
        match=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing axiom audit: '+name)
        axioms={a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Classical.choice','Quot.sound'},'unexpected proof axioms: '+str(axioms))
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-player-reaction.json').read_text())
    profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=joined.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=joined.extraction.extract(binary,profile,spec);run_table=joined.animation.table_data(binary,profile,spec)
    _,sine_table=joined.thrust.extract(binary,profile,json.loads((ROOT/'tests/reference/original-thrust.json').read_text()))
    out=ROOT/'artifacts/original-player-reaction';out.mkdir(parents=True,exist_ok=True)
    source=out/'Extracted.lean';source.write_text(certificate(raw,profile['exe_sha256']))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalPlayerReaction','fidelity-probe'],cwd=ROOT,check=True)
    result=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(result.stdout);print(result.stdout,end='',flush=True)
    report={'exe_sha256':profile['exe_sha256'],'units':spec['units'],'axioms':result.stdout.splitlines(),
            'sine_table':joined.thrust.check_tables(sine_table),'run1_table':run_table.hex(),
            'scope':'Original reaction-time guard and both branches: decrement without movement, or full movement/animation caller sequence. Runtime motion/animation/timer helpers are connected to live player preparation. Height calculation, earlier caller paths and whole-game reachability remain outside.',
            'cross_check':joined.cross_check(raw,sine_table,run_table,spec,whole_function=True,caller_context=True,reaction_context=True) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: original reaction-time gate and both branches match the runtime helpers.')
    if report['cross_check']:print('Independent reaction/caller/function x86 comparisons:',report['cross_check']['cases'])

if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as e:
        print(e.stdout or '',file=sys.stderr);print(e.stderr or '',file=sys.stderr);raise
