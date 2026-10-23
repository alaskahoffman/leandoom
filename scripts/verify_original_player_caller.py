#!/usr/bin/env python3
"""Certify the original P_PlayerThink call to P_MovePlayer and argument reload."""
import argparse
import json
import re
import subprocess
import sys
import verify_original_player_joined as joined

ROOT, require = joined.ROOT, joined.require
NAMES = ['caller_checked','function_checked','callee_checked','execution_checked','observation_checked',
         'Doom.Proofs.PlayerCaller.establishes_function',
         'Doom.Proofs.PlayerCaller.entry_return',
         'Doom.Proofs.PlayerCaller.result_registers',
         'Doom.Proofs.PlayerCaller.result_argument']


def certificate(raw,digest):
    lit=lambda key:'['+', '.join(hex(b) for b in raw[key])+']'
    audits='\n'.join('#print axioms '+n for n in NAMES)
    return f'''-- Original DOOM.EXE SHA-256 {digest}.
import Doom.Proofs.OriginalPlayerCaller
set_option maxRecDepth 32768
namespace Doom.Verification.ExtractedPlayerCaller
open X86Memory X86Control Doom.Proofs Doom.Proofs.PlayerCaller
def callerCode : List UInt8 := {lit('playerCallerBytes')}
def functionCode : List UInt8 := {lit('playerFunctionBytes')}
def calleeCode : List UInt8 := {lit('setMobjStateBytes')}
theorem caller_checked : callerCode = callerBytes := by decide
theorem function_checked : functionCode = PlayerFunction.functionBytes := by decide
theorem callee_checked : calleeCode = Doom19.setMobjStateBytes := by decide
theorem execution_checked (s : X86Memory.State) (flags : Option Flags)
    (b : Doom.Motion) (a : Doom.PlayerAnim.State) (c : Doom.Ticcmd) (h : Inputs s b a c) :
    X86Routine.run (bytesProgram callerCode functionCode calleeCode) [0x333cb]
      120 ⟨s,flags,0x333c2⟩ = some (result s b c) := by
  rw [caller_checked,function_checked,callee_checked]
  exact execution s flags b a c h
theorem observation_checked (s : X86Memory.State) (flags : Option Flags)
    (b : Doom.Motion) (a : Doom.PlayerAnim.State) (c : Doom.Ticcmd) (h : Inputs s b a c) :
    (X86Routine.run (bytesProgram callerCode functionCode calleeCode) [0x333cb]
      120 ⟨s,flags,0x333c2⟩).map (fun t =>
      (t.pc,(load32 t.core.memory (object s+(32#32)),load32 t.core.memory (object s+(72#32)),
        load32 t.core.memory (object s+(76#32))),load32 t.core.memory (object s+(100#32)),
        load32 t.core.memory (object s+(96#32)),PlayerFunction.preservedRegisters t.core,t.core.regs 0)) =
      some (0x333cb,
        ((b.movePlayer c).angle.raw.toBitVec,(b.movePlayer c).momx.raw.toBitVec,(b.movePlayer c).momy.raw.toBitVec),
        PlayerAnimation.statePointer (a.startWalking c).frame,(a.startWalking c).tics.toBitVec,
        PlayerFunction.preservedRegisters s,s.regs 2) := by
  rw [caller_checked,function_checked,callee_checked]
  exact observation s flags b a c h
{audits}
end Doom.Verification.ExtractedPlayerCaller
'''



def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedPlayerCaller.'+short
        match=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing axiom audit: '+name)
        axioms={a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Classical.choice','Quot.sound'},'unexpected proof axioms: '+str(axioms))
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-player-caller.json').read_text())
    profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=joined.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=joined.extraction.extract(binary,profile,spec);run_table=joined.animation.table_data(binary,profile,spec)
    _,sine_table=joined.thrust.extract(binary,profile,json.loads((ROOT/'tests/reference/original-thrust.json').read_text()))
    out=ROOT/'artifacts/original-player-caller';out.mkdir(parents=True,exist_ok=True)
    source=out/'Extracted.lean';source.write_text(certificate(raw,profile['exe_sha256']))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalPlayerCaller','fidelity-probe'],cwd=ROOT,check=True)
    result=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(result.stdout);print(result.stdout,end='',flush=True)
    report={'exe_sha256':profile['exe_sha256'],'units':spec['units'],'axioms':result.stdout.splitlines(),
            'sine_table':joined.thrust.check_tables(sine_table),'run1_table':run_table.hex(),
            'scope':'Actual caller MOV/CALL, complete P_MovePlayer with nested walking call, RET and caller argument reload. Callee entry relation and return address are derived; earlier reaction-time selection, caller reachability, height calculation and full tic remain outside.',
            'cross_check':joined.cross_check(raw,sine_table,run_table,spec,whole_function=True,caller_context=True) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: original caller establishes and executes P_MovePlayer, then reloads its player argument.')
    if report['cross_check']:print('Independent caller/function x86 comparisons:',report['cross_check']['cases'])

if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as e:
        print(e.stdout or '',file=sys.stderr);print(e.stderr or '',file=sys.stderr);raise
