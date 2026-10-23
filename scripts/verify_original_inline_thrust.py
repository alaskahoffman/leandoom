#!/usr/bin/env python3
"""Certify original inlined forward/side thrust; optionally cross-check with x86.

The formal model is flat and data-object-relative. Loader, flags, faults,
branch composition and full P_MovePlayer are outside this certificate.
"""
import argparse
import json
import random
import re
import struct
import subprocess
import sys

import verify_original_mul as original
from verify_original_arithmetic import fixups
import verify_original_thrust as thrust

ROOT, require = original.ROOT, original.require
NAMES = ['forward_bytes', 'side_bytes', 'forward_checked', 'side_checked',
         'Doom.Proofs.original_forward_thrust_memory', 'Doom.Proofs.original_side_thrust_memory',
         'Doom.Proofs.inline_reuses_thrust', 'Doom.Proofs.command_thrust_exact',
         'Doom.Proofs.inline_thrust_inputs']


def extract(binary, profile, spec, *, allowed_objects=(3,)):
    code, offsets, overlaps, _ = original.inspect_image(binary, profile)
    relocations = set(fixups(binary, range((len(code)+4095)//4096)))
    result = {}
    for name, unit in spec['units'].items():
        start = int(unit['code_offset'], 16)
        raw = code[start:start+len(bytes.fromhex(unit['hex']))]
        require(raw.hex() == unit['hex'], name+': original bytes mismatch')
        require(offsets[start] == int(unit['file_offset'], 16), name+': file mapping mismatch')
        actual = {(p-start, o, t) for p, o, t in relocations
                  if max(start, p) < min(start+len(raw), p+4)}
        expected = {(r['offset'], r['object'], int(r['target'], 16)) for r in unit['relocations']}
        require(actual == expected, name+': relocation mismatch')
        require({(p-start, w) for p, w in overlaps if max(start, p) < min(start+len(raw), p+w)} ==
                {(p, 4) for p, _, _ in expected}, name+': unexpected overlapping relocation')
        for p, o, t in expected:
            require(o in allowed_objects and struct.unpack_from('<I', raw, p)[0] == t, 'relocation object/target mismatch')
        result[name] = raw
    return result


def certificate(units, digest):
    source = f'''-- Original DOOM.EXE SHA-256 {digest}; loader is an external obligation.
import Doom.Proofs.OriginalInlineThrust
namespace Doom.Verification.ExtractedInlineThrust
open X86Memory X86Block Doom.Proofs
'''
    for label, count in [('forward', 23), ('side', 24)]:
        name = label+'ThrustBytes'
        literal = '['+', '.join(hex(b) for b in units[name])+']'
        side = 'true' if label == 'side' else 'false'
        source += f'''def {label} : List UInt8 := {literal}
theorem {label}_bytes : {label} = Doom19.{name} := by decide
theorem {label}_checked (s : State) (body : Motion) (cmd : Int8)
    (h : InlineThrustInputs s body {side} cmd) :
    (X86Block.run {count} {label} s).map (·.memory) =
      some (inlineThrustResult s body {side} cmd) := by
  rw [{label}_bytes]
  exact {label}_thrust_matches_doom19 s body cmd h
'''
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedInlineThrust\n'


def audit(output):
    rest = output.strip()
    for short in NAMES:
        name = short if '.' in short else 'Doom.Verification.ExtractedInlineThrust.'+short
        match = re.match(re.escape(f"'{name}'")+
                         r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing axiom audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected proof axioms')
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


def cross_check(units, table, spec):
    import capstone
    import unicorn as uc
    from unicorn import x86_const as x
    rng = random.Random(0x33199)
    signed = lambda v: v if v < 2**31 else v-2**32
    cmdsigned = lambda v: v if v < 128 else v-256
    edges = [0, 1, 0x3fffffff, 0x40000000, 0x7fffffff, 0x80000000, 0xffffffff]
    cases = [(index*524288+low, rng.randrange(256), rng.getrandbits(32), rng.getrandbits(32))
             for index in range(8192) for low in [0, 524287]]
    cases += [(a, c, rng.getrandbits(32), rng.getrandbits(32)) for a in edges for c in range(256)]
    em = uc.Uc(uc.UC_ARCH_X86, uc.UC_MODE_32)
    CODE, DATA = 0x100000, 0x300000
    em.mem_map(CODE, 4096); em.mem_map(DATA, 4096)
    for base in [0, 0x200000]:
        em.mem_map(base, 0x14000)
        em.mem_write(base+0x5a84, table)
        em.mem_write(base+0x13584, struct.pack('<I', base+0x7a84))
    regs = [x.UC_X86_REG_EAX, x.UC_X86_REG_ECX, x.UC_X86_REG_EDX, x.UC_X86_REG_EBX,
            x.UC_X86_REG_ESP, x.UC_X86_REG_EBP, x.UC_X86_REG_ESI, x.UC_X86_REG_EDI]
    writes = []
    em.hook_add(uc.UC_HOOK_MEM_WRITE, lambda _e, _a, addr, size, _v, _u: writes.append((addr, size)))
    sine = struct.unpack('<10240i', table)
    result = {}
    for side, name in enumerate(['forwardThrustBytes', 'sideThrustBytes']):
        raw, unit = units[name], spec['units'][name]
        listing = list(capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_32).disasm(raw, int(unit['code_offset'], 16)))
        require(len(listing) == unit['instructions'] and b''.join(bytes(i.bytes) for i in listing) == raw,
                'independent decoder mismatch')
        answers = thrust.probe([f'thrust {signed((a-side*0x40000000)&0xffffffff)} {cmdsigned(c)*2048} {signed(mx)} {signed(my)}'
                                for a, c, mx, my in cases])
        for i, ((angle, command, mx, my), answer) in enumerate(zip(cases, answers)):
            base = [0, 0x200000][i%2]
            relocated = bytearray(raw)
            for r in unit['relocations']:
                struct.pack_into('<I', relocated, r['offset'], base+int(r['target'], 16))
            em.mem_write(CODE, bytes(relocated)); em.ctl_remove_cache(CODE, CODE+len(raw))
            player, obj, stack = DATA+64+i%4, DATA+256+(i//4)%4, DATA+512+(i//16)%4
            em.mem_write(player, struct.pack('<I', obj))
            em.mem_write(obj+32, struct.pack('<I', angle))
            em.mem_write(obj+72, struct.pack('<II', mx, my))
            before = bytearray(em.mem_read(DATA, 4096))
            values = [rng.getrandbits(32) for _ in regs]
            values[1], values[4] = player, stack
            values[2] = (values[2] & ~(255 << (side*8))) | (command << (side*8))
            for r, v in zip(regs, values): em.reg_write(r, v)
            em.reg_write(x.UC_X86_REG_EFLAGS, 2 | (rng.getrandbits(12) & 0x8d5))
            writes.clear(); em.emu_start(CODE, CODE+len(raw), count=unit['instructions'])
            require(em.reg_read(x.UC_X86_REG_EIP) == CODE+len(raw), 'block did not finish')
            expected = tuple(int(v)&0xffffffff for v in answer.split())
            require(struct.unpack('<II', em.mem_read(obj+72, 8)) == expected, f'momentum mismatch {name} case {i}')
            index = ((angle-side*0x40000000)&0xffffffff) >> 19
            struct.pack_into('<II', before, obj+72-DATA, *expected)
            struct.pack_into('<I', before, stack-DATA, index*4)
            require(em.mem_read(DATA, 4096) == before, 'unexpected memory effect')
            require(writes == [(stack, 4), (obj+72, 4), (obj+76, 4)], 'incorrect write order')
            move = cmdsigned(command)*2048; product = move*sine[index]
            values[0], values[2], values[3] = (product >> 16)&0xffffffff, (product >> 32)&0xffffffff, sine[index]&0xffffffff
            values[5], values[7] = obj, move&0xffffffff
            require([em.reg_read(r) for r in regs] == values, 'incorrect register effects')
        result[name] = {'cases': len(cases), 'instructions': len(listing),
                        'disassembly': [f'{i.address:#x}: {i.mnemonic} {i.op_str}' for i in listing]}
    return {'units': result, 'total_cases': len(cases)*2, 'fine_angle_bins': 8192,
            'all_signed_commands': True, 'data_bases': [0, 0x200000],
            'unaligned_objects_and_stack': True, 'all_registers_and_write_order_checked': True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cross-check', action='store_true')
    args = parser.parse_args()
    spec = json.loads((ROOT/'tests/reference/original-inline-thrust.json').read_text())
    profile = json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text())
    sw = json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary = original.extract(ROOT/sw['local_directory']/'doom19s.zip', sw, profile)
    units = extract(binary, profile, spec)
    _, table = thrust.extract(binary, profile, json.loads((ROOT/'tests/reference/original-thrust.json').read_text()))
    out = ROOT/'artifacts/original-inline-thrust'; out.mkdir(parents=True, exist_ok=True)
    source = out/'Extracted.lean'; source.write_text(certificate(units, profile['exe_sha256']))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.OriginalInlineThrust', 'fidelity-probe'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)], cwd=ROOT,
                             capture_output=True, text=True, check=True)
    audit(checked.stdout); print(checked.stdout, end='', flush=True)
    report = {'exe_sha256': profile['exe_sha256'], 'units': spec['units'],
              'axioms': checked.stdout.splitlines(), 'tables': thrust.check_tables(table),
              'scope': 'Universal inlined thrust memory correspondence for related inputs, including scratch word; excludes loader, flags, faults, prologue/epilogue, guard composition, and full player update.',
              'cross_check': cross_check(units, table, spec) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: both original inlined thrust bodies match engine thrust for every related input state.')
    if report['cross_check']: print('Independent x86 comparisons:', report['cross_check']['total_cases'])


if __name__ == '__main__':
    try: main()
    except subprocess.CalledProcessError as e:
        print(e.stdout or '', file=sys.stderr); print(e.stderr or '', file=sys.stderr); raise
