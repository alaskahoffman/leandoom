#!/usr/bin/env python3
"""Certify uninterrupted preparation, secret-sector CALL, handler and return."""
import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path
import verify_original_sector_dispatch as dispatch

ROOT, require = dispatch.ROOT, dispatch.require
UNITS = {
    'reaction': ('playerReactionBytes', 'PlayerReactionProof.callerBytes'),
    'movement': ('playerFunctionBytes', 'PlayerFunction.functionBytes'),
    'setter': ('setMobjStateBytes', 'Doom19.setMobjStateBytes'),
    'heightCaller': ('calcHeightCallerBytes', 'PlayerHeight.Caller.callBytes'),
    'height': ('calcHeightBytes', 'PlayerHeight.code'),
    'caller': ('sectorDispatchBytes', 'SectorCaller.callBytes'),
    'entry': ('sectorEntryBytes', 'SectorEntry.entryBytes'),
    'secret': ('sectorSecretBytes', 'SectorSecret.code'),
    'epilogue': ('sectorReturnBytes', 'SectorEntry.returnBytes'),
    'table': ('sectorTableBytes', 'SectorEntry.tableBytes'),
}
NAMES = [label+'_checked' for label in UNITS] + [
    'runtime_checked', 'Doom.Proofs.SectorJoined.transport',
    'Doom.Proofs.SectorJoined.handler_frame', 'Doom.Proofs.SectorJoined.preparation_ordinary',
    'Doom.Proofs.SectorJoined.execution', 'Doom.Verification.X86CodeMemory.lift_routine',
    'live_runtime_checked', 'Doom.Proofs.SectorRuntime.position',
    'Doom.Proofs.SectorRuntime.prepare', 'Doom.Proofs.SectorRuntime.phase_continuation',
    'Doom.Proofs.SectorRuntime.phase_execution', 'Doom.Proofs.SectorRuntime.phase_frame',
    'Doom.Proofs.SectorRuntime.runtime_observation', 'Doom.Proofs.SectorRuntime.correspondence']


def certificate(raw, digest):
    source = f'''-- Original executable SHA-256 {digest}.
import Doom.Proofs.OriginalSectorRuntime
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
namespace Doom.Verification.ExtractedSectorJoined
open X86Memory X86Control Doom.Proofs SectorJoined
'''
    for label, (unit, definition) in UNITS.items():
        lit = '['+','.join(hex(v) for v in raw[unit])+']'
        source += f'def {label} : List UInt8 := {lit}\ntheorem {label}_checked : {label} = {definition} := by decide\n'
    source += '''theorem runtime_checked (s : X86Memory.State) (flags : Option Flags)
    (body : Doom.Motion) (anim : Doom.PlayerAnim.State) (cmd : Doom.Ticcmd) (timer : Int32)
    (v : Doom.ViewState) (time : Int32) (cached live : Bool) (floor : Doom.Fixed) (n : Int32)
    (h : Inputs s body anim cmd timer v time cached live floor n) :
    (X86CodeMemory.run (SectorEntry.codeMemory table)
      (bytesProgram reaction movement setter heightCaller height caller entry secret epilogue)
      [0x333e5] 256 ⟨s,flags,0x333b1⟩).map (observe s) =
      some (0x333e5,PreparedState.expected body anim cmd timer v time cached live,
        BitVec.ofNat 16 (Doom.LevelSpecials.secret 9 body.z floor n).1,
        (Doom.LevelSpecials.secret 9 body.z floor n).2.toBitVec,s.regs 4,s.regs 2) := by
  rw [''' + ','.join(label+'_checked' for label in UNITS) + ''']
  exact observation s flags body anim cmd timer v time cached live floor n h
'''
    source += '''theorem live_runtime_checked (machine : X86Memory.State) (flags : Option Flags)
    (s : Doom.Simulation) (keys : UInt32) (cmd : Doom.Ticcmd)
    (scene : Doom.Collision.Scene) (actor : Doom.Collision.SolidThing) (index : Nat)
    (sync : (SectorRuntime.inputPlayer s).syncScene s.map = .ok scene)
    (found : scene.things[0]? = some actor) (supported : actor.moveFlags.floating = false)
    (lookup : s.map.sectorAt actor.x actor.y = .ok index) (valid : index < s.map.sectors.size)
    (secretSector : s.map.sectors[index]!.special = 9)
    (h : Inputs machine (actor.motion s.player.body) s.player.animation cmd s.player.reactionTime
      s.player.view s.player.levelTime s.player.cachedOnGround true
      (Doom.Fixed.ofInt s.map.sectors[index]!.floor) s.secrets) :
    (X86CodeMemory.run (SectorEntry.codeMemory table)
      (bytesProgram reaction movement setter heightCaller height caller entry secret epilogue)
      [0x333e5] 256 ⟨machine,flags,0x333b1⟩).map (SectorRuntime.machineOutput machine) =
      SectorRuntime.output index (s.prepareSectorTick keys (some cmd)) := by
  rw [''' + ','.join(label+'_checked' for label in UNITS) + ''']
  exact SectorRuntime.correspondence machine flags s keys cmd scene actor index sync found supported
    lookup valid secretSector h
'''
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedSectorJoined\n'


def audit(output):
    rest = output.strip()
    for short in NAMES:
        name = short if '.' in short else 'Doom.Verification.ExtractedSectorJoined.'+short
        match = re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing axiom audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Classical.choice', 'Quot.sound'}, 'unexpected axioms: '+str(axioms))
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


def secret_probe(commands):
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory)/'commands.txt'
        path.write_text('\n'.join(commands)+'\n')
        result = subprocess.run([str(ROOT/'.lake/build/bin/level-probe'), str(path)], cwd=ROOT,
                                capture_output=True, text=True, check=True)
    require(not result.stderr.strip(), 'unexpected secret probe diagnostics')
    return result.stdout.splitlines()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cross-check', action='store_true')
    args = parser.parse_args()
    spec = json.loads((ROOT/'tests/reference/original-sector-joined.json').read_text())
    profile = json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text())
    sw = json.loads((ROOT/'tests/reference/shareware.json').read_text())
    height = dispatch.height
    binary = height.joined.original.extract(ROOT/sw['local_directory']/'doom19s.zip', sw, profile)
    raw = height.joined.extraction.extract(binary, profile, spec, allowed_objects=(1, 3))
    out = ROOT/'artifacts/original-sector-joined'
    out.mkdir(parents=True, exist_ok=True)
    source = out/'Extracted.lean'
    source.write_text(certificate(raw, profile['exe_sha256']))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.OriginalSectorRuntime', 'fidelity-probe', 'level-probe'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)], cwd=ROOT,
                             capture_output=True, text=True, check=True)
    audit(checked.stdout)
    report = {'exe_sha256': profile['exe_sha256'], 'units': spec['units'], 'axioms': checked.stdout.splitlines(),
              'scope': 'Continuous original-byte execution from 0x333b1 through preparation, sector lookup, CALL, prologue, secret or off-floor handler and RET to 0x333e5. Eleven preparation fields and two secret fields match live helpers; caller ESP and player pointer survive. All memory contracts refer to initial state. The live Simulation.prepareSectorTick observation is also proved for explicit Ticcmd input, successful scene synchronization, a supported player actor, valid initial BSP sector lookup and special 9. Reachability of these premises, other sector types and the remaining tic/game are not proved. The independent native comparison still exercises helper composition; the live wrapper is kernel checked.',
              'cross_check': None}
    if args.cross_check:
        _, table = height.joined.thrust.extract(binary, profile, json.loads((ROOT/'tests/reference/original-thrust.json').read_text()))
        run_table = height.joined.animation.table_data(binary, profile, json.loads((ROOT/'tests/reference/original-player-reaction.json').read_text()))
        report['cross_check'] = dispatch.preparation.cross_check(raw, table, run_table, spec, height.cases(),
            height.joined.thrust.probe, require, sector_handler=True, secret_probe=secret_probe)
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(f'PASS: preparation through secret-handler return and live simulation phase; {len(NAMES)} audited declarations.')
    if args.cross_check:
        print('Independent continuous original-byte/native comparisons:', report['cross_check']['cases'])

if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as error:
        print(error.stdout or '', file=sys.stderr)
        print(error.stderr or '', file=sys.stderr)
        raise
