#!/usr/bin/env python3
"""Bind the reusable block-summary proof to original DOS P_Thrust bytes.

Offline by default. LE extraction/relocation and initial table identity are
external checks. Optional Unicorn checks are independent empirical evidence.
The theorem uses data-object-relative addresses, not a verified DOS loader.
"""
import argparse
import hashlib
import json
from pathlib import Path
import random
import re
import struct
import subprocess
import sys
import tempfile

import verify_original_mul as original
from verify_original_arithmetic import fixups

ROOT = original.ROOT
require = original.require
NAMES = ['bytes_checked', 'memory_checked', 'momentum_checked',
         'Doom.Proofs.BlockSummary.summarized_correct',
         'Doom.Verification.X86Block.eval_append', 'Doom.Proofs.thrust_selected_tables']


def extract(binary, profile, spec):
    code, offsets, relocations, _ = original.inspect_image(binary, profile)
    start = int(spec['code_offset'], 16)
    expected_bytes = bytes.fromhex(spec['hex'])
    raw = code[start:start+len(expected_bytes)]
    require(raw == expected_bytes, 'thrust bytes mismatch')
    require(offsets[start] == int(spec['file_offset'], 16), 'thrust file mapping mismatch')
    # A fixup spanning a page boundary appears in both pages; deduplicate it.
    actual = {r for r in fixups(binary, range(start//4096, (start+len(raw)-1)//4096+1))
              if max(start, r[0]) < min(start+len(raw), r[0]+4)}
    expected = {(start+r['offset'], r['object'], int(r['target'], 16)) for r in spec['relocations']}
    require(actual == expected, 'thrust relocation identity mismatch')
    require({(r, w) for r, w in relocations if max(start, r) < min(start+len(raw), r+w)} ==
            {(r, 4) for r, _, _ in expected}, 'unexpected overlapping relocation')
    for pos, obj, target in expected:
        require(obj == 3 and struct.unpack_from('<I', code, pos)[0] == target,
                'data operand differs from relocation target')

    le = int(profile['le_offset'], 16)
    u32 = lambda p: struct.unpack_from('<I', binary, p)[0]
    data = struct.unpack_from('<6I', binary, le+u32(le+0x40)+48)
    require(data == (0x85e10, 0x70000, 0x2043, 71, 38, 0), 'unexpected data object')
    page_map = le+u32(le+0x48)
    def read_data(start, size):
        out = bytearray()
        for p in range(start, start+size):
            page = data[3]-1+p//4096
            entry = binary[page_map+4*page:page_map+4*page+4]
            require(len(entry) == 4 and entry[3] == 0, 'unsupported data page')
            physical = int.from_bytes(entry[:3], 'big')
            require(physical > 0, 'invalid physical data page')
            pos = int(profile['data_pages_offset'], 16)+(physical-1)*4096+p%4096
            require(pos < len(binary), 'truncated data page')
            out.append(binary[pos])
        return bytes(out)
    table = read_data(0x5a84, 10240*4)
    table_fixups = fixups(binary, range(70+0x5a84//4096, 70+(0x5a84+len(table)-1)//4096+1))
    require(not any(max(0x5a84, p-70*4096) < min(0x5a84+len(table), p-70*4096+4)
                    for p, _, _ in table_fixups), 'sine table contains a relocation')
    require(read_data(0x13584, 4) == struct.pack('<I', 0x7a84), 'cosine pointer value mismatch')
    pointer_fixups = {r for r in fixups(binary, [70+0x13584//4096])
                      if max(70*4096+0x13584, r[0]) < min(70*4096+0x13588, r[0]+4)}
    require(pointer_fixups == {(70*4096+0x13584, 3, 0x7a84)}, 'cosine pointer relocation mismatch')
    return raw, table


def certificate(raw, digest):
    literal = ', '.join(hex(b) for b in raw)
    audits = '\n'.join(f'#print axioms {n}' for n in NAMES)
    return f'''-- Extracted from DOOM.EXE SHA-256 {digest}.
-- Data-object-relative addresses; DOS loading and table initialization are external obligations.
import Doom.Proofs.OriginalThrust
namespace Doom.Verification.ExtractedThrust
open X86 X86Memory X86Block Doom.Proofs
def code : List UInt8 := [{literal}]
theorem bytes_checked : code = Doom19.playerThrustBytes := by decide
theorem memory_checked (s : State) (body : Motion) (angle : Angle) (move : Fixed)
    (h : ThrustInputs s body angle move) :
    (X86Block.run 17 code s).map (·.memory) = some (thrustResultMemory s body angle move) := by
  rw [bytes_checked]
  exact player_thrust_matches_doom19 s body angle move h
theorem momentum_checked (s : State) (body : Motion) (angle : Angle) (move : Fixed)
    (h : ThrustInputs s body angle move) :
    (X86Block.run 17 code s).map (fun t =>
      (load32 t.memory (load32 s.memory (s.regs eax) + 72),
       load32 t.memory (load32 s.memory (s.regs eax) + 76))) =
      some ((body.thrust angle move).momx.raw.toBitVec,
        (body.thrust angle move).momy.raw.toBitVec) := by
  rw [bytes_checked]
  exact player_thrust_momentum s body angle move h
{audits}
end Doom.Verification.ExtractedThrust
'''


def audit(output):
    rest = output.strip()
    for short in NAMES:
        name = short if '.' in short else 'Doom.Verification.ExtractedThrust.'+short
        pattern = re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)'
        match = re.match(pattern, rest)
        require(match is not None, f'missing axiom audit for {name}')
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Classical.choice', 'Quot.sound'}, f'unexpected proof axioms: {axioms}')
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


def probe(commands):
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory)/'commands.txt'
        path.write_text('\n'.join(commands)+'\n')
        result = subprocess.run([str(ROOT/'.lake/build/bin/fidelity-probe'), str(path)],
                                capture_output=True, text=True, check=True)
    require(not result.stderr.strip(), 'unexpected Lean probe diagnostics')
    answers = result.stdout.splitlines()
    require(len(answers) == len(commands), 'Lean probe count mismatch')
    return answers


def check_tables(table):
    answers = probe([f'sine {i}' for i in range(10240)])
    expected = list(struct.unpack('<10240i', table))
    require(list(map(int, answers)) == expected, 'original/compiled Lean sine table mismatch')
    return {'entries': 10240, 'sha256': hashlib.sha256(table).hexdigest(),
            'comparison': 'original bytes versus compiled Lean Tables.fineSine; empirical initialization check'}


def cross_check(raw, table, spec):
    import capstone
    import unicorn as uc
    from unicorn import x86_const as x
    listing = list(capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_32).disasm(raw, 0x32ff4))
    require(len(listing) == 17 and b''.join(bytes(i.bytes) for i in listing) == raw,
            'independent instruction decoding mismatch')
    rng = random.Random(0x32ff4)
    signed = lambda v: v if v < 2**31 else v-2**32
    edges = [0, 1, 0x7fffffff, 0x80000000, 0xffffffff, 65536, 0xffff0000]
    cases = []
    for index in range(8192):
        for low in [0, 1, 0x7fffe, 0x7ffff]:
            cases.append(((index << 19)+low, rng.getrandbits(32), rng.getrandbits(32), rng.getrandbits(32)))
    cases += [(a, m, mx, my) for a in edges for m in edges for mx in edges for my in edges]
    answers = probe([f'thrust {signed(a)} {signed(m)} {signed(mx)} {signed(my)}' for a, m, mx, my in cases])
    em = uc.Uc(uc.UC_ARCH_X86, uc.UC_MODE_32)
    CODE, DYNAMIC = 0x100000, 0x300000
    em.mem_map(CODE, 4096); em.mem_map(DYNAMIC, 4096)
    for base in [0, 0x200000]:
        em.mem_map(base, 0x14000)
        em.mem_write(base+0x5a84, table)
        em.mem_write(base+0x13584, struct.pack('<I', base+0x7a84))
    registers = [x.UC_X86_REG_EAX, x.UC_X86_REG_ECX, x.UC_X86_REG_EDX, x.UC_X86_REG_EBX,
                 x.UC_X86_REG_ESP, x.UC_X86_REG_EBP, x.UC_X86_REG_ESI, x.UC_X86_REG_EDI]
    writes = []
    em.hook_add(uc.UC_HOOK_MEM_WRITE, lambda _em, _access, addr, size, value, _data: writes.append((addr, size)))
    sines = struct.unpack('<10240i', table)
    for i, ((angle, move, mx, my), answer) in enumerate(zip(cases, answers)):
        base = [0, 0x200000][i % 2]
        relocated = bytearray(raw)
        for relocation in spec['relocations']:
            struct.pack_into('<I', relocated, relocation['offset'], base+int(relocation['target'], 16))
        em.mem_write(CODE, bytes(relocated))
        # Remove translated blocks because this test alternates relocated immediates.
        em.ctl_remove_cache(CODE, CODE+len(raw))
        player, obj = DYNAMIC+64+i%4, DYNAMIC+256+(i//4)%4
        em.mem_write(player, struct.pack('<I', obj))
        em.mem_write(obj+72, struct.pack('<II', mx, my))
        before = bytearray(em.mem_read(DYNAMIC, 4096))
        regs = [rng.getrandbits(32) for _ in registers]
        regs[0], regs[2], regs[3] = player, angle, move
        for reg, value in zip(registers, regs): em.reg_write(reg, value)
        em.reg_write(x.UC_X86_REG_EFLAGS, 2 | (rng.getrandbits(12) & 0x8d5))
        writes.clear()
        em.emu_start(CODE, CODE+len(raw), count=17)
        require(em.reg_read(x.UC_X86_REG_EIP) == CODE+len(raw), 'thrust block did not finish')
        expected = tuple(int(v) & 0xffffffff for v in answer.split())
        require(struct.unpack('<II', em.mem_read(obj+72, 8)) == expected,
                f'thrust mismatch for {angle=}, {move=}, {mx=}, {my=}')
        struct.pack_into('<II', before, obj+72-DYNAMIC, *expected)
        require(em.mem_read(DYNAMIC, 4096) == before, 'unexpected dynamic-memory write')
        require(writes == [(obj+72, 4), (obj+76, 4)], 'unexpected write address/order')
        index = angle >> 19
        product = signed(move)*sines[index]
        regs[0], regs[1], regs[2], regs[3] = (product >> 16) & 0xffffffff, move, (product >> 32) & 0xffffffff, sines[index] & 0xffffffff
        regs[5], regs[6], regs[7] = obj, obj, index*4
        require([em.reg_read(r) for r in registers] == regs, 'unexpected register effect')
    return {'cases': len(cases), 'all_fine_angle_bins': 8192, 'low_bits_per_bin': [0, 1, 524286, 524287],
            'full_width_moves_and_momenta': True, 'data_bases': [0, 0x200000], 'unaligned_objects': True,
            'all_registers_and_write_order_checked': True,
            'disassembly': [f'{i.address:#x}: {i.mnemonic} {i.op_str}' for i in listing]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cross-check', action='store_true')
    args = parser.parse_args()
    spec = json.loads((ROOT/'tests/reference/original-thrust.json').read_text())
    profile = json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text())
    shareware = json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary = original.extract(ROOT/shareware['local_directory']/'doom19s.zip', shareware, profile)
    raw, table = extract(binary, profile, spec)
    out = ROOT/'artifacts/original-thrust'; out.mkdir(parents=True, exist_ok=True)
    source = out/'Extracted.lean'; source.write_text(certificate(raw, profile['exe_sha256']))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.OriginalThrust', 'fidelity-probe'], cwd=ROOT, check=True)
    result = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)],
                            cwd=ROOT, capture_output=True, text=True, check=True)
    audit(result.stdout); print(result.stdout, end='', flush=True)
    report = {'exe_sha256': profile['exe_sha256'], 'code_offset': spec['code_offset'], 'bytes': raw.hex(),
              'instructions': 17, 'relocations': spec['relocations'], 'axioms': result.stdout.splitlines(),
              'tables': check_tables(table),
              'scope': 'Universal body memory/momentum correspondence for related inputs in the flat data-object-relative model; excludes loader, stack wrapper, flags, faults, callers, collision and whole-game equivalence.',
              'cross_check': cross_check(raw, table, spec) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: original thrust body matches Motion.thrust for every related input state.')
    if report['cross_check']: print(json.dumps(report['cross_check']))


if __name__ == '__main__':
    try: main()
    except subprocess.CalledProcessError as error:
        print(error.stdout or '', file=sys.stderr); print(error.stderr or '', file=sys.stderr); raise
