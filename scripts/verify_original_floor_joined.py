#!/usr/bin/env python3
"""Certify uninterrupted player preparation through the floor-damage decision."""
import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
import verify_original_floor_damage as floor_proof
import verify_original_player_height as height
import verify_original_player_preparation as preparation
import verify_original_sector_joined as sector

ROOT, require = floor_proof.ROOT, floor_proof.require
UNITS = {
    'reaction': ('playerReactionBytes', 'PlayerReactionProof.callerBytes'),
    'movement': ('playerFunctionBytes', 'PlayerFunction.functionBytes'),
    'setter': ('setMobjStateBytes', 'Doom19.setMobjStateBytes'),
    'heightCaller': ('calcHeightCallerBytes', 'PlayerHeight.Caller.callBytes'),
    'height': ('calcHeightBytes', 'PlayerHeight.code'),
    'caller': ('sectorCallerBytes', 'SectorCaller.callBytes'),
    'entry': ('sectorEntryBytes', 'SectorEntry.entryBytes'),
    'cases': ('floorDamageBytes', 'FloorDamage.code'),
    'rng': ('playRandomBytes', 'Doom19.playRandomBytes'),
    'switchTable': ('sectorTableBytes', 'SectorEntry.tableBytes'),
    'randomTable': ('randomTableBytes', 'Doom19.randomTableBytes'),
}
NAMES = [label+'_checked' for label in UNITS] + [
    'joined_checked', 'Doom.Proofs.FloorJoined.transport',
    'Doom.Proofs.FloorJoined.handler_frame', 'Doom.Proofs.FloorJoined.contains_caller',
    'Doom.Proofs.FloorJoined.contains_preparation', 'Doom.Proofs.FloorJoined.preparation_active',
    'Doom.Proofs.FloorJoined.execution', 'Doom.Proofs.FloorJoined.correspondence',
    'live_runtime_checked', 'Doom.Proofs.FloorRuntime.effect_inline',
    'Doom.Proofs.FloorRuntime.lookup_failure', 'Doom.Proofs.FloorRuntime.combat_no_damage',
    'Doom.Proofs.FloorRuntime.ordinary_result', 'Doom.Proofs.FloorRuntime.tick_clock',
    'Doom.Proofs.FloorRuntime.phase_execution', 'Doom.Proofs.FloorRuntime.runtime_observation',
    'Doom.Proofs.FloorRuntime.phase_handoff', 'Doom.Proofs.FloorRuntime.decision_frame',
    'Doom.Proofs.FloorRuntime.correspondence', 'Doom.Simulation.hurtFromFloor_request']


def certificate(raw, digest):
    source=f'''-- Original executable SHA-256 {digest}; extraction/loader checked externally.
import Doom.Proofs.OriginalFloorRuntime
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
namespace Doom.Verification.ExtractedFloorJoined
open X86Memory X86Control Doom.Proofs FloorJoined
'''
    for label,(unit,definition) in UNITS.items():
        literal='['+','.join(hex(b) for b in raw[unit])+']'
        source += f'def {label} : List UInt8 := {literal}\ntheorem {label}_checked : {label} = {definition} := by decide\n'
    source += '''theorem joined_checked (kind : FloorDamage.Kind) (s : X86Memory.State) (flags : Option Flags)
    (body : Doom.Motion) (anim : Doom.PlayerAnim.State) (cmd : Doom.Ticcmd) (timer : Int32)
    (v : Doom.ViewState) (time : Int32) (cached live : Bool) (floor : Doom.Fixed)
    (tick : Nat) (suit : Bool) (random : Doom.DoomRandom)
    (h : Inputs kind s body anim cmd timer v time cached live floor tick suit random) :
    (X86CodeMemory.run (SectorEntry.codeMemory switchTable)
      (bytesProgram reaction movement setter heightCaller height caller entry cases rng)
      FloorDamage.exits 267 ⟨s,flags,0x333b1⟩).map (observe s) =
      let answer := Doom.LevelSpecials.floorDamage kind.special body.z floor suit tick random
      some (PreparedState.expected body anim cmd timer v time cached live,
        (answer.1,BitVec.ofNat 32 answer.2.play.toNat,BitVec.ofNat 32 answer.2.misc.toNat),s.regs 4-(20#32)) := by
  rw ['''+', '.join(label+'_checked' for label in UNITS if label!='randomTable')+''']
  exact correspondence kind s flags body anim cmd timer v time cached live floor tick suit random h
'''
    source += '''theorem live_runtime_checked (kind : FloorDamage.Kind) (machine : X86Memory.State) (flags : Option Flags)
    (s : Doom.Simulation) (keys : UInt32) (cmd : Doom.Ticcmd)
    (scene : Doom.Collision.Scene) (actor : Doom.Collision.SolidThing) (index : Nat)
    (sync : (SectorRuntime.inputPlayer s).syncScene s.map = .ok scene)
    (found : scene.things[0]? = some actor) (supported : actor.moveFlags.floating = false)
    (lookup : s.map.sectorAt actor.x actor.y = .ok index) (valid : index < s.map.sectors.size)
    (special : s.map.sectors[index]!.special = kind.special)
    (h : FloorJoined.Inputs kind machine (actor.motion s.player.body) s.player.animation cmd s.player.reactionTime
      s.player.view s.player.levelTime s.player.cachedOnGround true (Doom.Fixed.ofInt s.map.sectors[index]!.floor)
      (s.ticks-1) (s.inventory.suit > 0) s.rng) :
    (X86CodeMemory.run (SectorEntry.codeMemory switchTable)
      (bytesProgram reaction movement setter heightCaller height caller entry cases rng)
      FloorDamage.exits 267 ⟨machine,flags,0x333b1⟩).map (FloorRuntime.machineOutput machine) =
      FloorRuntime.output (s.prepareSectorTick keys (some cmd)) := by
  rw ['''+', '.join(label+'_checked' for label in UNITS if label!='randomTable')+''']
  exact FloorRuntime.correspondence kind machine flags s keys cmd scene actor index sync found supported lookup valid special h
'''
    return source+'\n'.join('#print axioms '+name for name in NAMES)+'\nend Doom.Verification.ExtractedFloorJoined\n'


def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedFloorJoined.'+short
        match=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing axiom audit: '+name)
        axioms={a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext','Classical.choice','Quot.sound'},'unexpected axioms: '+str(axioms))
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cross-check',action='store_true')
    args=parser.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-floor-joined.json').read_text())
    profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text())
    sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=floor_proof.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=floor_proof.extraction.extract(binary,profile,spec,allowed_objects=(1,3))
    raw['randomTableBytes']=floor_proof.arithmetic.verify_units(binary,profile,
        json.loads((ROOT/'tests/reference/original-arithmetic.json').read_text()))['randomTableBytes']
    out=ROOT/'artifacts/original-floor-joined';out.mkdir(parents=True,exist_ok=True)
    source=out/'Extracted.lean';source.write_text(certificate(raw,profile['exe_sha256']))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalFloorRuntime','fidelity-probe','level-probe'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout)
    report={'exe_sha256':profile['exe_sha256'],'units':spec['units'],'axioms':checked.stdout.splitlines(),
        'scope':'One original-byte run from 0x333b1 through reaction/movement, animation, view height, sector lookup, '
                'CALL/prologue and ordinary floor decision to the damage CALL or skip epilogue. All eleven preparation '
                'fields, requested damage, both RNG indices, damage-call arguments and stack position are proved under '
                'initial encoding and separation contracts. Whole-memory frame composes both phases. '
                'The live preparation and floor-request wrapper are linked under explicit synchronized scene, supported actor and initial map lookup premises. '
                'The combat callback consumes this same request and installs its RNG before damage handling. '
                'Applying nonzero damage, handler return, earlier tick reachability and full tic/game remain outside. Independent comparisons still exercise helper composition.',
        'cross_check':None}
    if args.cross_check:
        _,sines=height.joined.thrust.extract(binary,profile,json.loads((ROOT/'tests/reference/original-thrust.json').read_text()))
        run_table=height.joined.animation.table_data(binary,profile,json.loads((ROOT/'tests/reference/original-player-reaction.json').read_text()))
        report['cross_check']=preparation.cross_check({k:v for k,v in raw.items() if k!='randomTableBytes'},
            sines,run_table,spec,height.cases(),height.joined.thrust.probe,require,
            floor_damage=True,damage_probe=sector.secret_probe,random_table=raw['randomTableBytes'])
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f'PASS: preparation through floor-damage decision; {len(NAMES)} audited declarations.')
    if args.cross_check:print('Independent continuous original-byte/native comparisons:',report['cross_check']['cases'])

if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as error:
        print(error.stdout or '',file=sys.stderr);print(error.stderr or '',file=sys.stderr);raise
