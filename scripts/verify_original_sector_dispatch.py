#!/usr/bin/env python3
"""Certify preparation through DOS's sector dispatch, stopping before its handler."""
import argparse
import json
import re
import struct
import subprocess
import sys
import verify_original_player_height as height
import verify_original_player_preparation as preparation

ROOT, require = height.ROOT, height.require
EXTRA = ['dispatch_bytes_checked', 'dispatch_checked', 'joined_checked',
         'Doom.Proofs.PlayerPreparation.reaction_player',
         'Doom.Proofs.PlayerPreparation.execution_preserved',
         'Doom.Proofs.SectorDispatch.special_preserved',
         'Doom.Proofs.SectorDispatch.joined_execution']


def certificate(raw, digest):
    source = height.certificate(raw, digest).replace('import Doom.Proofs.OriginalPreparedRuntime',
                                                  'import Doom.Proofs.OriginalSectorDispatch')
    literal = '[' + ','.join(hex(b) for b in raw['sectorDispatchBytes']) + ']'
    return source + f'''
namespace Doom.Verification.ExtractedSectorDispatch
open X86Memory X86Control Doom.Proofs Doom.Verification.ExtractedPlayerHeight
def extractedDispatch : List UInt8 := {literal}
theorem dispatch_bytes_checked : extractedDispatch = SectorDispatch.code := by decide
theorem dispatch_checked (s : X86Memory.State) (flags : Option Flags) :
    X86Routine.run (SectorDispatch.bytesProgram extractedDispatch) [0x333e0,0x333e5] 6
      ⟨s,flags,0x333d0⟩ = some (SectorDispatch.result s) := by
  rw [dispatch_bytes_checked]
  exact SectorDispatch.execution s flags
theorem joined_checked (s : X86Memory.State) (flags : Option Flags)
    (body : Doom.Motion) (anim : Doom.PlayerAnim.State) (cmd : Doom.Ticcmd) (timer : Int32)
    (v : Doom.ViewState) (time : Int32) (cached live : Bool)
    (h : PlayerHeightJoin.Inputs s body anim cmd timer v time cached live) (safe : SectorDispatch.Safe s) :
    (X86Routine.run (SectorDispatch.joinedBytes reactionCode movementCode stateCode extractedCaller extracted extractedDispatch)
      [0x333e0,0x333e5] 231 ⟨s,flags,0x333b1⟩).map
      (SectorDispatch.observe (s.regs 2) (PlayerCaller.object s)) =
      some (SectorDispatch.exitPc (SectorDispatch.special s),
        PreparedState.expected body anim cmd timer v time cached live,s.regs 4,s.regs 2) := by
  rw [reaction_bytes_checked,movement_bytes_checked,state_bytes_checked,caller_bytes_checked,bytes_checked,dispatch_bytes_checked]
  exact SectorDispatch.observation s flags body anim cmd timer v time cached live h safe
''' + '\n'.join('#print axioms ' + name for name in EXTRA) + '\nend Doom.Verification.ExtractedSectorDispatch\n'


def audit(output):
    names = [('Doom.Verification.ExtractedPlayerHeight.' + n if '.' not in n else n) for n in height.NAMES]
    names += [('Doom.Verification.ExtractedSectorDispatch.' + n if '.' not in n else n) for n in EXTRA]
    rest = output.strip()
    for name in names:
        match = re.match(re.escape(f"'{name}'") + r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing axiom audit: ' + name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Classical.choice', 'Quot.sound'}, 'unexpected proof axioms: ' + str(axioms))
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


def exhaustive_guard(code):
    """Every 16-bit sector pattern, with dirty adjacent bytes and unaligned pointers."""
    import unicorn as uc
    from unicorn import x86_const as x
    em = uc.Uc(uc.UC_ARCH_X86, uc.UC_MODE_32)
    base, data = 0x100000, 0x200000
    em.mem_map(base, 4096)
    em.mem_map(data, 4096)
    em.mem_write(base, code)
    def stop(machine, addr, _size, _user):
        if addr in (base + 16, base + 21):
            machine.emu_stop()
    em.hook_add(uc.UC_HOOK_CODE, stop)
    regs = [x.UC_X86_REG_EAX, x.UC_X86_REG_ECX, x.UC_X86_REG_EDX, x.UC_X86_REG_EBX,
            x.UC_X86_REG_ESP, x.UC_X86_REG_EBP, x.UC_X86_REG_ESI, x.UC_X86_REG_EDI]
    for value in range(65536):
        player, obj, sub, sector = [data + off + value % 4 for off in (32, 512, 1024, 1536)]
        em.mem_write(data, b'\xa5' * 4096)
        for addr, val in [(player, obj), (obj + 52, sub), (sub, sector), (sector + 14, 0xA5A50000 | value)]:
            em.mem_write(addr, struct.pack('<I', val))
        before = bytes(em.mem_read(data, 4096))
        initial = [0x12345678 + i for i in range(8)]
        initial[2] = player
        for reg, val in zip(regs, initial):
            em.reg_write(reg, val)
        em.reg_write(x.UC_X86_REG_EFLAGS, 0x8D7)
        em.emu_start(base, 0, count=7)
        require(em.reg_read(x.UC_X86_REG_EIP) == base + (16 if value else 21), f'guard branch {value}')
        require(em.reg_read(regs[0]) == (player if value else sector), f'guard argument {value}')
        require(all(em.reg_read(regs[i]) == initial[i] for i in range(1, 8)), f'guard registers {value}')
        flags = em.reg_read(x.UC_X86_REG_EFLAGS)
        require((bool(flags & 64), bool(flags & 128), bool(flags & 2048)) ==
                (value == 0, bool(value & 0x8000), False), f'16-bit CMP flags {value}')
        require(bytes(em.mem_read(data, 4096)) == before, f'guard writes {value}')
    return {'cases': 65536, 'unaligned_addresses': True, 'dirty_adjacent_bytes': True,
            'checks': ['branch', 'argument', 'all other registers', 'ZF/SF/OF', 'entire data page unchanged']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cross-check', action='store_true')
    args = parser.parse_args()
    spec = json.loads((ROOT/'tests/reference/original-sector-dispatch.json').read_text())
    profile = json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text())
    sw = json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary = height.joined.original.extract(ROOT/sw['local_directory']/'doom19s.zip', sw, profile)
    raw = height.joined.extraction.extract(binary, profile, spec)
    out = ROOT/'artifacts/original-sector-dispatch'
    out.mkdir(parents=True, exist_ok=True)
    source = out/'Extracted.lean'
    source.write_text(certificate(raw, profile['exe_sha256']))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.OriginalSectorDispatch', 'fidelity-probe'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)], cwd=ROOT, capture_output=True, text=True, check=True)
    audit(checked.stdout)
    report = {'exe_sha256': profile['exe_sha256'], 'units': spec['units'], 'axioms': checked.stdout.splitlines(),
              'scope': 'Continuous original-byte preparation plus sector dispatch, with eleven preparation fields, caller ESP/EDX and a memory frame. Initial pointer-chain reads must be disjoint from preparation writes. Nonzero sectors stop BEFORE the special-sector CALL with EAX prepared; no handler effects or whole-tic equivalence are assumed.',
              'cross_check': None}
    if args.cross_check:
        _, table = height.joined.thrust.extract(binary, profile, json.loads((ROOT/'tests/reference/original-thrust.json').read_text()))
        reaction_spec = json.loads((ROOT/'tests/reference/original-player-reaction.json').read_text())
        run_table = height.joined.animation.table_data(binary, profile, reaction_spec)
        report['cross_check'] = {
            'guard': exhaustive_guard(raw['sectorDispatchBytes']),
            'continuous': preparation.cross_check(raw, table, run_table, spec, height.cases(),
                height.joined.thrust.probe, require, sector_dispatch=True)}
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(f'PASS: sector dispatch and continuous preparation; {len(height.NAMES)+len(EXTRA)} audited declarations.')
    if args.cross_check:
        print('PASS: 65,536 sector words and 52,052 continuous original-byte comparisons.')

if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as error:
        print(error.stdout or '', file=sys.stderr)
        print(error.stderr or '', file=sys.stderr)
        raise
