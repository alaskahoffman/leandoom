#!/usr/bin/env python3
"""Certify DOS line-fraction rejection, early stop, ordered insertion and return."""
import argparse
import json
import random
import re
import subprocess
import verify_original_inline_thrust as extraction
ROOT, require = extraction.ROOT, extraction.require
NAMES = ['bytes_checked', 'execution_checked']
PROOFS = ['OriginalLineFinish.' + n for n in [
    'decoded', 'unwind_execution', 'insert_execution', 'stopped_execution',
    'selected_execution', 'rejected_execution', 'execution', 'result_memory',
    'result_value', 'result_sp', 'result_pc', 'written_frame', 'frame', 'returned',
    'written_cursor', 'written_record', 'early_live', 'decision_live',
    'line_intercept_live', 'append_encoded', 'append_live']]
PROOFS += ['E1M1LineFinish.' + n for n in [
    'contains_prior', 'contains_finish', 'continue_execution',
    'line_finish_execution', 'fraction_inputs']]


def certificate(raw):
    source = '''import Doom.Proofs.E1M1LineFinish
set_option maxRecDepth 32768
namespace Doom.Verification.ExtractedLineFinish
open Doom Doom.Proofs X86 X86Memory X86Control
'''
    source += 'def finishCode : List UInt8 := [' + ','.join(hex(b) for b in raw['finish']) + ']\n'
    source += '''theorem bytes_checked : finishCode=OriginalLineFinish.code := by decide
theorem execution_checked (s : X86Memory.State) (f : Option Flags) :
    ∃ n≤23, X86Routine.Prefix (OriginalLineFinish.bytesProgram finishCode) [] n
      ⟨s,f,0x2c6bb⟩ (OriginalLineFinish.result s) := by
  rw [bytes_checked]; exact OriginalLineFinish.execution s f
'''
    return source + '\n'.join('#print axioms ' + n for n in NAMES) + '\n' + '\n'.join(
        '#print axioms Doom.Proofs.' + n for n in PROOFS) + '\nend Doom.Verification.ExtractedLineFinish\n'


def audit(output):
    rest = output.strip()
    for name in ['Doom.Verification.ExtractedLineFinish.' + n for n in NAMES] + ['Doom.Proofs.' + n for n in PROOFS]:
        match = re.match(re.escape(f"'{name}'") + r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing audit: ' + name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axioms')
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected output')


def extracted():
    spec = json.loads((ROOT / 'tests/reference/original-line-finish.json').read_text())
    profile = json.loads((ROOT / 'tests/reference' / spec['exe_profile']).read_text())
    sw = json.loads((ROOT / 'tests/reference/shareware.json').read_text())
    binary = extraction.original.extract(ROOT / sw['local_directory'] / 'doom19s.zip', sw, profile)
    return spec, profile, extraction.extract(binary, profile, spec)


def cross_check(raw):
    import capstone
    import unicorn as u
    from unicorn import x86_const as x
    CODE, HEAP, MASK = 0x100000, 0x600000, 0xffffffff
    code = raw['finish']
    listing = list(capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_32).disasm(code, 0x2c6bb))
    require(b''.join(bytes(i.bytes) for i in listing) == code, 'decoder mismatch')
    em = u.Uc(u.UC_ARCH_X86, u.UC_MODE_32)
    em.mem_map(CODE, 0x50000)
    em.mem_write(CODE + 0x2c6bb, code)
    addresses = [0, 0x2c000, HEAP, 0xfffff000]
    for a in addresses:
        em.mem_map(a, 4096)
    regs = [x.UC_X86_REG_EAX, x.UC_X86_REG_ECX, x.UC_X86_REG_EDX, x.UC_X86_REG_EBX,
            x.UC_X86_REG_ESP, x.UC_X86_REG_EBP, x.UC_X86_REG_ESI, x.UC_X86_REG_EDI]
    writes, visits = [], []
    em.hook_add(u.UC_HOOK_MEM_WRITE, lambda _, access, a, size, value, data: writes.append((a & MASK, size, value & MASK)))
    em.hook_add(u.UC_HOOK_CODE, lambda _, a, size, data: visits.append(a - CODE))
    rng = random.Random(0x2c6bb)
    groups = dict(negative=0, disabled_append=0, far_append=0, two_sided_append=0,
                  early_stop=0, unaligned=0, wrapped_buffer=0, wrapped_stack=0,
                  cursor_alias=0, stack_alias=0)
    signed = lambda v: v if v < 0x80000000 else v - 0x100000000
    for i in range(2048):
        pages = {a: bytearray(rng.randbytes(4096)) for a in addresses}

        def put(a, v):
            for k, b in enumerate((v & MASK).to_bytes(4, 'little')):
                q = (a + k) & MASK
                pages[q & ~4095][q & 4095] = b

        def get(a):
            return sum(pages[((a + k) & MASK) & ~4095][((a + k) & MASK) & 4095] << (8 * k) for k in range(4))

        rr = [rng.getrandbits(32) for _ in regs]
        rr[0] = [0xffffffff, 0x80000000, 0, 1, 65535, 65536, 65537, 0x7fffffff][i % 8]
        sp = [HEAP + 256, HEAP + 259, 0xfffffff1, 0][(i // 8) % 4]
        rr[4], rr[1] = sp, HEAP + 1025
        cur = [HEAP + 2048, HEAP + 2049, 0xfffffffa, 0x2c028, 0x2c023,
               (sp + 16) & MASK][(i // 32) % 6]
        put(0x2c024, 0 if (i // 192) % 2 == 0 else 0x80000000)
        put(0x2c028, cur)
        put(rr[1] + 50, 0 if (i // 384) % 2 == 0 else HEAP + 3000)
        put(sp + 36, CODE + 0x4f000)
        for address, page in pages.items():
            em.mem_write(address, bytes(page))
        for reg, val in zip(regs, rr):
            em.reg_write(reg, val)
        em.reg_write(x.UC_X86_REG_EFLAGS, 0x8c3 if i % 3 == 0 else 2)
        wanted, expected = rr.copy(), []
        active, near, back = get(0x2c024) != 0, signed(rr[0]) < 65536, get(rr[1] + 50)
        if signed(rr[0]) < 0:
            group, count, answer, append = 'negative', 11, 1, False
        elif not active:
            group, count, answer, append = 'disabled_append', 19, 1, True
        elif not near:
            group, count, answer, append = 'far_append', 21, 1, True
        elif back:
            group, count, answer, append = 'two_sided_append', 23, 1, True
        else:
            group, count, answer, append = 'early_stop', 17, 0, False
        groups[group] += 1
        if append:
            for address, value in [(cur + 4, 1), (cur, rr[0]), (cur + 8, rr[1]), (0x2c028, cur + 12)]:
                expected.append((address & MASK, 4, value & MASK))
                put(address, value)
        wanted[0], wanted[4] = answer, (sp + 40) & MASK
        for offset, reg in [(16, 5), (20, 6), (24, 2), (28, 1), (32, 3)]:
            wanted[reg] = get(sp + offset)
        stop = get(sp + 36)
        writes.clear()
        visits.clear()
        em.emu_start(CODE + 0x2c6bb, 0, count=count)
        require(em.reg_read(x.UC_X86_REG_EIP) == stop, f'case {i}: return PC')
        require(len(visits) == count, f'case {i}: instruction count')
        require([em.reg_read(r) for r in regs] == wanted, f'case {i}: registers')
        require(writes == expected, f'case {i}: ordered writes {writes} != {expected}')
        for address, page in pages.items():
            require(em.mem_read(address, 4096) == page, f'case {i}: memory')
        groups['unaligned'] += bool(cur % 4)
        groups['wrapped_buffer'] += append and cur == 0xfffffffa
        groups['wrapped_stack'] += sp in [0, 0xfffffff1]
        groups['cursor_alias'] += append and cur in [0x2c028, 0x2c023]
        groups['stack_alias'] += append and cur == (sp + 16) & MASK
    require(all(groups.values()), 'missing coverage')
    return {'total_cases': 2048, 'groups': groups,
            'checks': 'All eight registers, mapped byte memory, instruction count, return PC; ordered writes. No helper stubs.',
            'scope': 'Local callback suffix only; full firing prefix is a conditional kernel theorem. Final flags not compared. Native tests supplement universal proofs.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cross-check', action='store_true')
    args = parser.parse_args()
    spec, profile, raw = extracted()
    out = ROOT / 'artifacts/original-line-finish'
    out.mkdir(parents=True, exist_ok=True)
    source = out / 'Extracted.lean'
    source.write_text(certificate(raw))
    subprocess.run([str(ROOT / 'scripts/lake'), 'build', 'Doom.Proofs.E1M1LineFinish'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT / 'scripts/lake'), 'env', 'lean', str(source)], cwd=ROOT, capture_output=True, text=True, check=True)
    audit(checked.stdout)
    (out / 'axioms.log').write_text(checked.stdout)
    report = {'exe_sha256': profile['exe_sha256'], 'units': spec['units'], 'axioms': checked.stdout.splitlines(),
              'scope': 'Post-fraction line callback, exact ordered writes and actual return. Array correspondence requires capacity, encoded input and separated memory. Whole traversal/game equivalence remains open.',
              'cross_check': cross_check(raw) if args.cross_check else None}
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print('PASS: original line callback finish; extracted bytes and strict axiom audit.')
    if args.cross_check:
        print('Native callback cases:', report['cross_check']['total_cases'])


if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as error:
        print(error.stdout or '')
        print(error.stderr or '')
        raise
