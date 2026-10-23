#!/usr/bin/env python3
"""Check original P_MovePlayer guard bytes and Lean certificates, offline.

Optional Unicorn comparisons test the real branches and compiled movePlayer.
The proof uses flat, data-object-relative memory; DOS loading is not verified.
"""
import argparse
import json
from pathlib import Path
import random
import re
import struct
import subprocess
import sys

import verify_original_mul as original
from verify_original_arithmetic import fixups
from verify_original_thrust import probe

ROOT = original.ROOT
require = original.require
NAMES = ['forward_bytes', 'side_bytes', 'forward_checked', 'side_checked',
         'Doom.Proofs.forward_guard_engine_pc', 'Doom.Proofs.side_guard_engine_pc',
         'Doom.Proofs.cmp32_signed_le', 'Doom.Verification.X86Control.runProgram_sound']


def extract(binary, profile, spec):
    code, offsets, _, _ = original.inspect_image(binary, profile)
    relocations = set(fixups(binary, range((len(code)+4095)//4096)))
    result = {}
    for name, unit in spec['units'].items():
        start = int(unit['code_offset'], 16)
        expected = bytes.fromhex(unit['hex'])
        raw = code[start:start+len(expected)]
        require(raw == expected, name+': original bytes mismatch')
        require(offsets[start] == int(unit['file_offset'], 16), name+': file mapping mismatch')
        actual = {(pos-start, obj, target) for pos, obj, target in relocations
                  if max(start, pos) < min(start+len(raw), pos+4)}
        expected_relocs = {(19 if name == 'forwardGuardBytes' else 9, 3, 0x2cf90)}
        require(actual == expected_relocs, name+': relocation mismatch')
        for pos, _, target in actual:
            require(struct.unpack_from('<I', raw, pos)[0] == target, 'relocation operand mismatch')
        result[name] = raw
    return result


def certificate(units, digest):
    literals = {name: '['+', '.join(hex(b) for b in raw)+']' for name, raw in units.items()}
    audits = '\n'.join('#print axioms '+name for name in NAMES)
    return f'''-- Actual slices of DOOM.EXE SHA-256 {digest}; data-object-relative operands.
import Doom.Proofs.OriginalMoveGuards
namespace Doom.Verification.ExtractedMoveGuards
open X86Memory X86Control Doom.Proofs
def forward : List UInt8 := {literals['forwardGuardBytes']}
def side : List UInt8 := {literals['sideGuardBytes']}
theorem forward_bytes : forward = Doom19.forwardGuardBytes := by decide
theorem side_bytes : side = Doom19.sideGuardBytes := by decide
theorem forward_checked (s : X86Memory.State) (flags : Option Flags) :
    (X86Control.run forward [31, 103] 11 ⟨s, flags, 0⟩).map (fun t => (t.pc, t.core.memory)) =
      some (forwardGuardResult s, store32 s.memory 0x2cf90 (if groundFlag s then 1 else 0)) := by
  rw [forward_bytes]
  exact original_forward_guard s flags
theorem side_checked (s : X86Memory.State) (flags : Option Flags) :
    (X86Control.run side [16, 93] 5 ⟨s, flags, 0⟩).map (fun t => (t.pc, t.core.memory)) =
      some (sideGuardResult s, s.memory) := by
  rw [side_bytes]
  exact original_side_guard s flags
{audits}
end Doom.Verification.ExtractedMoveGuards
'''


def audit(output):
    rest = output.strip()
    for short in NAMES:
        name = short if '.' in short else 'Doom.Verification.ExtractedMoveGuards.'+short
        pattern = re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)'
        match = re.match(pattern, rest)
        require(match is not None, 'missing axiom audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected proof axioms')
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


def cross_check(units):
    import capstone
    import unicorn as uc
    from unicorn import x86_const as x
    rng = random.Random(0x3317a)
    signed32 = lambda v: v if v < 2**31 else v-2**32
    signed8 = lambda v: v if v < 128 else v-256
    edges = [0, 1, 0xffffffff, 0x7fffffff, 0x80000000, 0x80000001, 0x7ffffffe]
    forward_cases = [(z, f, c) for z in edges for f in edges for c in range(256)]
    forward_cases += [(rng.getrandbits(32), rng.getrandbits(32), rng.randrange(256)) for _ in range(10000)]
    side_cases = [(g, c) for g in edges for c in range(256)]
    side_cases += [(rng.getrandbits(32), rng.randrange(256)) for _ in range(10000)]
    commands = [f'move-guards {signed32(z)} {signed32(f)} {signed8(c)} 0' for z, f, c in forward_cases]
    commands += [f'move-guards {0 if g else 1} 0 0 {signed8(c)}' for g, c in side_cases]
    answers = [tuple(map(int, line.split())) for line in probe(commands)]
    em = uc.Uc(uc.UC_ARCH_X86, uc.UC_MODE_32)
    CODE, DATA, GLOBAL = 0x100000, 0x300000, 0x2cf90
    em.mem_map(CODE, 4096); em.mem_map(DATA, 4096); em.mem_map(GLOBAL & ~4095, 4096)
    regs = [x.UC_X86_REG_EAX, x.UC_X86_REG_ECX, x.UC_X86_REG_EDX, x.UC_X86_REG_EBX,
            x.UC_X86_REG_ESP, x.UC_X86_REG_EBP, x.UC_X86_REG_ESI, x.UC_X86_REG_EDI]
    exits = set(); writes = []
    def at_instruction(machine, address, size, user):
        if address in exits: machine.emu_stop()
    em.hook_add(uc.UC_HOOK_CODE, at_instruction)
    em.hook_add(uc.UC_HOOK_MEM_WRITE, lambda _e, _a, address, size, _v, _u: writes.append((address, size)))
    listings = {}
    answer_index = 0
    for name, cases, fuel, offsets in [('forwardGuardBytes', forward_cases, 11, [31, 103]),
                                       ('sideGuardBytes', side_cases, 5, [16, 93])]:
        raw = units[name]
        listing = list(capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_32).disasm(raw, CODE))
        require(len(listing) == fuel and b''.join(bytes(i.bytes) for i in listing) == raw, 'independent decode mismatch')
        listings[name] = [f'{i.address-CODE:#x}: {i.mnemonic} {i.op_str}' for i in listing]
        em.mem_write(CODE, b'\xcc'*4096); em.mem_write(CODE, raw); em.ctl_remove_cache(CODE, CODE+4096)
        exits = {CODE+offset for offset in offsets}
        for i, case in enumerate(cases):
            player, obj = DATA+32+i%4, DATA+256+(i//4)%4
            before = [rng.getrandbits(32) for _ in regs]
            before[1], before[6] = player, player+8
            em.mem_write(player, struct.pack('<I', obj))
            if name == 'forwardGuardBytes':
                z, floor, command = case
                em.mem_write(obj+20, struct.pack('<I', z)); em.mem_write(obj+56, struct.pack('<I', floor))
                em.mem_write(player+8, bytes([command]))
                ground = int(signed32(z) <= signed32(floor))
                em.mem_write(GLOBAL, struct.pack('<I', rng.getrandbits(32)))
                expected_pc = 31 if ground and command else 103
                expected_regs = before.copy()
                expected_regs[0], expected_regs[3] = ground, z
                expected_regs[2] = (before[2] & 0xffffff00) | command
                expected_flags = (int(not command or not ground), 0, 0)
                require(answers[answer_index][:2] == (ground, int(expected_pc == 31)), 'compiled forward update mismatch')
                expected_writes = [(GLOBAL, 4)]
            else:
                ground, command = case
                em.mem_write(player+9, bytes([command])); em.mem_write(GLOBAL, struct.pack('<I', ground))
                expected_pc = 16 if command and ground else 93
                expected_regs = before.copy(); expected_regs[2] = (before[2] & 0xffff00ff) | (command << 8)
                expected_flags = (int(not command or not ground), (ground >> 31) if command else 0, 0)
                require(answers[answer_index][2] == int(expected_pc == 16), 'compiled side update mismatch')
                expected_writes = []
            answer_index += 1
            page_before = em.mem_read(DATA, 4096)
            for reg, value in zip(regs, before): em.reg_write(reg, value)
            em.reg_write(x.UC_X86_REG_EFLAGS, 2 | (rng.getrandbits(12) & 0x8d5))
            writes.clear(); em.emu_start(CODE, 0, count=fuel+1)
            require(em.reg_read(x.UC_X86_REG_EIP) == CODE+expected_pc, 'wrong original branch exit')
            require([em.reg_read(reg) for reg in regs] == expected_regs, 'unexpected register effect')
            require(writes == expected_writes, 'unexpected memory write/order')
            require(em.mem_read(DATA, 4096) == page_before, 'unexpected player/object write')
            require(struct.unpack('<I', em.mem_read(GLOBAL, 4))[0] == ground, 'wrong cached ground value')
            flags = em.reg_read(x.UC_X86_REG_EFLAGS)
            require(((flags >> 6) & 1, (flags >> 7) & 1, (flags >> 11) & 1) == expected_flags, 'ZF/SF/OF mismatch')
    return {'forward_cases': len(forward_cases), 'side_cases': len(side_cases),
            'total': len(forward_cases)+len(side_cases), 'all_command_bytes': True,
            'signed_height_extremes': True, 'arbitrary_cached_ground_words': True,
            'compared': ['branch exits', 'all general registers', 'ZF/SF/OF', 'memory writes', 'compiled Motion.movePlayer'],
            'disassembly': listings}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cross-check', action='store_true')
    args = parser.parse_args()
    spec = json.loads((ROOT/'tests/reference/original-move-guards.json').read_text())
    profile = json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text())
    shareware = json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary = original.extract(ROOT/shareware['local_directory']/'doom19s.zip', shareware, profile)
    units = extract(binary, profile, spec)
    out = ROOT/'artifacts/original-move-guards'; out.mkdir(parents=True, exist_ok=True)
    source = out/'Extracted.lean'; source.write_text(certificate(units, profile['exe_sha256']))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.OriginalMoveGuards', 'fidelity-probe'], cwd=ROOT, check=True)
    result = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)], cwd=ROOT, capture_output=True, text=True, check=True)
    audit(result.stdout); print(result.stdout, end='', flush=True)
    report = {'exe_sha256': profile['exe_sha256'], 'units': spec['units'], 'axioms': result.stdout.splitlines(),
              'scope': 'Ground predicate, forward/side guard exits, and memory effects; flat relative-address model. Inlined thrust bodies, caller invariants, animation, loader, and whole-game equivalence remain unproved.',
              'cross_check': cross_check(units) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: original movement guard decisions match the engine conditions.')
    if report['cross_check']: print(json.dumps(report['cross_check']))


if __name__ == '__main__':
    try: main()
    except subprocess.CalledProcessError as error:
        print(error.stdout or '', file=sys.stderr); print(error.stderr or '', file=sys.stderr); raise
