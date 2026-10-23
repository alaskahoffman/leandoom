#!/usr/bin/env python3
"""Check the fixed E1M1 profile and its lethal-floor handoff certificate, offline."""
import argparse
import json
import re
import subprocess
import demo_compare
import verify_original_death_branches as branches

ROOT, require = branches.ROOT, branches.require
PROFILE = ROOT/'tests/reference/e1m1-proof-profile.json'
NAMES = ['Doom.Proofs.E1M1Death.'+name for name in
         ['runtime_profile', 'no_automap', 'player_info', 'player_states', 'floor_death']]
NAMES += ['Doom.Verification.FixedE1M1.floor_checked']


def check_profile(profile, executable, shareware):
    expected = dict(schema='leandoom-e1m1-proof-profile-v1', episode=1, map=1,
                    skill=2, console_player=0, players=[True, False, False, False],
                    netgame=False, deathmatch=False, respawn=False, fast=False,
                    nomonsters=False, automap=False,
                    demo_header_hex='6d020101000000000001000000',
                    exe_sha256=executable['exe_sha256'], wad_sha256=shareware['wad_sha256'])
    for key, value in expected.items():
        require(type(profile.get(key)) is type(value) and profile[key] == value,
                'fixed E1M1 profile mismatch: '+key)
    require(bytes.fromhex(profile['demo_header_hex']) == demo_compare.HEADER,
            'comparison header differs from proof target')


def certificate():
    return '''import Doom.Proofs.E1M1Death
namespace Doom.Verification.FixedE1M1
open Doom.Proofs X86 X86Memory X86Control BlockSummary
-- A checked specialization, retaining the original entry and memory contracts.
theorem floor_checked (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32)
    (sim : Simulation) (map : sim.map.name="E1M1")
    (skill : load32 s.memory (0x2b3e0#32)=2)
    (body : Death.Body) (info : body.info=E1M1Death.playerInfo) (w : Fin 3) (y : Fixed)
    (h : KillDeathBranches.Inputs s v d false 0 body sim.deathWorld w y)
    (dead : (PlayerDamage.apply v d none false false sim.rng).killed=true)
    (stackSafe : Apart (0x12c5c#32) (s.regs 4-(56#32))) :
    ∃ t, X86Routine.run KillDeathBranches.program [0x30ea0] 239 ⟨s,f,pc⟩=some t ∧
      t.pc=0x30ea0 ∧ t.core.regs 0=s.regs 0 ∧
      t.core.regs 2=BitVec.ofNat 32 (Death.deathState
        (PlayerDamage.apply v d none false false sim.rng).state.health E1M1Death.playerInfo) ∧
      (t.core.regs 2=158 ∨ t.core.regs 2=165) ∧
      load32 t.core.memory (0x12c5c#32)=0 ∧
      load32 t.core.memory (s.regs 4-56)=0x2a3f1 := by
  obtain ⟨t,run,pcOut,obj,chosen,states,inactive,_,_,_,_,_,_,ret,_⟩ :=
    E1M1Death.floor_death s f pc site v d sim map skill body info w y h dead stackSafe
  exact ⟨t,run,pcOut,obj,chosen,states,inactive,ret⟩
end Doom.Verification.FixedE1M1
''' + '\n'.join('#print axioms '+name for name in NAMES)+'\n'


def audit(output):
    rest = output.strip()
    for name in NAMES:
        match = re.match(re.escape(f"'{name}'")+
                         r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'},
                'unexpected axioms: '+str(axioms))
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cross-check', action='store_true')
    args = parser.parse_args()
    profile = json.loads(PROFILE.read_text())
    executable = json.loads((ROOT/'tests/reference/original-mul.json').read_text())
    shareware = json.loads((ROOT/'tests/reference/shareware.json').read_text())
    check_profile(profile, executable, shareware)
    out = ROOT/'artifacts/e1m1-death'
    out.mkdir(parents=True, exist_ok=True)
    (out/'report.json').unlink(missing_ok=True)
    binary = branches.extraction.original.extract(
        ROOT/shareware['local_directory']/'doom19s.zip', shareware, executable)
    branches.extraction.original.checked_hash(
        (ROOT/shareware['local_directory']/'doom1.wad').read_bytes(), profile['wad_sha256'], 'DOOM1.WAD')
    spec = json.loads((ROOT/'tests/reference/original-death-branches.json').read_text())
    raw = branches.extraction.extract(binary, executable, spec)
    # Recheck the original-byte certificates for the complete imported chain.
    with (out/'dependencies.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/verify-original-death-branches')], cwd=ROOT,
                       stdout=log, stderr=subprocess.STDOUT, check=True)
        subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.E1M1Death'], cwd=ROOT,
                       stdout=log, stderr=subprocess.STDOUT, check=True)
    source = out/'Checked.lean'
    source.write_text(certificate())
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)],
                             cwd=ROOT, capture_output=True, text=True, check=True)
    audit(checked.stdout)
    require(not checked.stderr.strip(), 'unexpected certificate stderr')
    print(checked.stdout, end='', flush=True)
    report = dict(profile=profile, axioms=checked.stdout.splitlines(),
                  original_byte_dependency_chain_checked=True,
                  scope='Conditional lethal floor CALL to P_SetMobjState entry; all entry contracts remain explicit. Not a whole-game invariant or full death routine proof.',
                  cross_check=branches.cross_check(raw, spec, e1m1_profile=True) if args.cross_check else None)
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: fixed E1M1 lethal-floor handoff, player death states 158/165, automap remains inactive.')
    if report['cross_check']:
        print('Independent x86 death-guard/selector checks:', report['cross_check']['cases'])


if __name__ == '__main__':
    main()
