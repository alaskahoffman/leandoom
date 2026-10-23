#!/usr/bin/env python3
"""Verify the pinned E1M1 death RNG call, countdown adjustment, and clamp."""
import argparse
import json
import random
import re
import struct
import subprocess
import tempfile
from pathlib import Path
import verify_e1m1_death_setter as previous
import verify_original_arithmetic as arithmetic
ROOT, require, extraction = previous.ROOT, previous.require, previous.extraction
NAMES = ['timing_checked', 'rng_checked', 'table_checked', 'timing_execution_checked', 'joined_checked']
NAMES += ['Doom.Proofs.RandomReturn.random_execution']
NAMES += ['Doom.Proofs.DeathTiming.'+n for n in
          ['decoded', 'tail_execution', 'execution', 'original_execution', 'memory_frame',
           'result_tics', 'result_index', 'player_table_facts', 'player_tics', 'live_timing', 'live_correspondence']]
NAMES += ['Doom.Proofs.E1M1DeathTiming.'+n for n in ['contains_previous', 'contains_timing', 'joined_execution']]


def extract(binary, profile, spec):
    raw = extraction.extract(binary, profile, spec)
    data = json.loads((ROOT/'tests/reference/original-arithmetic.json').read_text())
    raw['table'] = arithmetic.verify_units(binary, profile, data)['randomTableBytes']
    return raw


def certificate(raw):
    text = '''import Doom.Proofs.E1M1DeathTiming
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
namespace Doom.Verification.ExtractedDeathTiming
open Doom.Proofs X86 X86Memory X86Control BlockSummary
'''
    for name, definition in [('timing', 'DeathTiming.code'), ('rng', 'Doom19.playRandomBytes'),
                             ('table', 'Doom19.randomTableBytes')]:
        text += f'def {name} : List UInt8 := ['+','.join(hex(b) for b in raw[name])+']\n'
        text += f'theorem {name}_checked : {name}={definition} := by decide\n'
    text += '''theorem timing_execution_checked (s : X86Memory.State) (f : Option Flags) (i : UInt8)
    (h : DeathTiming.Inputs s i) :
    X86Routine.run (DeathTiming.bytesProgram timing rng) [0x2a40d] 15 ⟨s,f,0x2a3f1⟩ =
      some (DeathTiming.result s i) := by
  rw [timing_checked,rng_checked]
  exact DeathTiming.original_execution s f i h
'''
    text += (ROOT/'tests/reference/e1m1-death-timing.lean').read_text()
    text += '\n'.join('#print axioms '+n for n in NAMES)
    return text+'\nend Doom.Verification.ExtractedDeathTiming\n'


def audit(output):
    rest = output.strip()
    for short in NAMES:
        name = short if '.' in short else 'Doom.Verification.ExtractedDeathTiming.'+short
        match = re.match(re.escape(f"'{name}'")+
                         r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axioms: '+str(axioms))
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


def cases():
    # First player death states plus clamp and signed/wrapping subtraction edges.
    return [(tics, seed, (seed*73+19)%256, wrap)
            for tics in [10, 5, 4, 3, 2, 1, 0, -1, -2147483648, -2147483647, 2147483647]
            for seed in range(256) for wrap in [False, True]]


def cross_check(raw):
    import capstone
    import unicorn as uc
    from unicorn import x86_const as x
    corpus = cases()
    with tempfile.TemporaryDirectory() as directory:
        inp, out = Path(directory)/'input', Path(directory)/'output'
        inp.write_text(''.join(f'{tics} {play} {misc}\n' for tics, play, misc, _ in corpus))
        subprocess.run([str(ROOT/'.lake/build/bin/death-probe'), 'death-timing', str(inp), str(out)], check=True)
        answers = [tuple(map(int, line.split())) for line in out.read_text().splitlines()]
    require(len(answers) == len(corpus), 'compiled timing row count')
    em = uc.Uc(uc.UC_ARCH_X86, uc.UC_MODE_32)
    CODE, DATA = 0x100000, 0x600000
    for address, size in [(CODE, 0x40000), (0, 0x30000), (DATA, 0x2000), (0xfffff000, 0x1000)]:
        em.mem_map(address, size)
    listings = {}
    for name, address in [('timing', 0x2a3f1), ('rng', 0x24160)]:
        em.mem_write(CODE+address, raw[name])
        listing = list(capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_32).disasm(raw[name], address))
        require(b''.join(bytes(i.bytes) for i in listing) == raw[name], 'independent decoder mismatch')
        listings[name] = [f'{i.address:#x}: {i.mnemonic} {i.op_str}' for i in listing]
    em.mem_write(0x1261c, raw['table'])
    regs = [x.UC_X86_REG_EAX, x.UC_X86_REG_ECX, x.UC_X86_REG_EDX, x.UC_X86_REG_EBX,
            x.UC_X86_REG_ESP, x.UC_X86_REG_EBP, x.UC_X86_REG_ESI, x.UC_X86_REG_EDI]
    writes, visits = [], []
    em.hook_add(uc.UC_HOOK_MEM_WRITE, lambda _e, _a, a, n, v, _u: writes.append((a, n, v & ((1 << (8*n))-1))))
    def visit(e, a, _n, _u):
        if a == CODE+0x2a40d: e.emu_stop()
        else: visits.append(a-CODE)
    em.hook_add(uc.UC_HOOK_CODE, visit)
    put = lambda a, v: em.mem_write(a & 0xffffffff, struct.pack('<I', v & 0xffffffff))
    pages = list(range(0, 0x30000, 4096))+[DATA, DATA+4096, 0xfffff000]
    rng = random.Random(0x2A3F1)
    clamped = unclamped = 0
    for i, ((tics, seed, misc, wrap), (answer, play_out, misc_out, events)) in enumerate(zip(corpus, answers)):
        obj = DATA+128+seed%4
        sp = 0 if wrap else DATA+4096+128+seed%4
        rr = [rng.getrandbits(32) for _ in regs]
        rr[3], rr[4] = obj, sp
        for reg, val in zip(regs, rr): em.reg_write(reg, val)
        em.reg_write(x.UC_X86_REG_EFLAGS, 2 | (rng.getrandbits(12) & 0x8d5))
        put(obj+96, tics); put(0x12720, seed); put(0x1271c, misc)
        before = {a: bytearray(em.mem_read(a, 4096)) for a in pages}
        writes.clear(); visits.clear()
        em.emu_start(CODE+0x2a3f1, CODE+0x40000, count=16)
        require(em.reg_read(x.UC_X86_REG_EIP) == CODE+0x2a40d, f'exit {i}')
        roll = raw['table'][(seed+1)%256] & 3
        delta = (tics-roll)&0xffffffff
        signed_delta = delta if delta < 2**31 else delta-2**32
        clamp = signed_delta < 1
        clamped += int(clamp); unclamped += int(not clamp)
        require(visits.count(0x24160) == 1 and len(visits) == (15 if clamp else 14), f'RNG call/instruction order {i}')
        require(play_out == (seed+1)%256 and misc_out == misc and events == 1, f'compiled RNG/effects {i}')
        expected = [((sp-4)&0xffffffff, 4, CODE+0x2a3f6), (0x12720, 4, play_out), (obj+96, 4, delta)]
        if clamp: expected.append((obj+96, 4, 1))
        require(writes == expected, f'write order {i}')
        require(struct.unpack('<i', em.mem_read(obj+96, 4))[0] == answer, f'compiled countdown {i}')
        rr[0], rr[5] = roll, delta
        require([em.reg_read(r) for r in regs] == rr, f'all registers {i}')
        diff = (delta-1)&0xffffffff
        flags = (0x40 if diff == 0 else 0) | (0x80 if diff >> 31 else 0) | (0x800 if (delta >> 31) and not (diff >> 31) else 0) | (1 if delta < 1 else 0)
        require(em.reg_read(x.UC_X86_REG_EFLAGS) & 0x8c1 == flags, f'compare flags {i}')
        for a, n, value in writes:
            for byte in range(n):
                at = (a+byte)&0xffffffff
                before[at&~4095][at%4096] = (value >> (8*byte)) & 255
        require(all(em.mem_read(a, 4096) == data for a, data in before.items()), f'memory/misc RNG frame {i}')
    require(clamped and unclamped, 'both clamp branches exercised')
    return dict(cases=len(corpus), player_entry_cases=1024, clamped=clamped, unclamped=unclamped,
                compiled_live_randomizeTics=True, all_rng_indices=True,
                registers_flags_ordered_writes_memory_checked=True, wrapping_and_unaligned_stacks=True,
                disassembly=listings)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cross-check', action='store_true')
    args = parser.parse_args()
    spec = json.loads((ROOT/'tests/reference/original-death-timing.json').read_text())
    exe = json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text())
    sw = json.loads((ROOT/'tests/reference/shareware.json').read_text())
    profile = json.loads(previous.previous.PROFILE.read_text())
    previous.previous.check_profile(profile, exe, sw)
    out = ROOT/'artifacts/e1m1-death-timing'; out.mkdir(parents=True, exist_ok=True)
    (out/'report.json').unlink(missing_ok=True)
    binary = extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip', sw, exe)
    raw = extract(binary, exe, spec)
    with (out/'dependencies.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/verify-e1m1-death-setter')], cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=True)
        subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.E1M1DeathTiming', 'death-probe'], cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=True)
    source = out/'Checked.lean'; source.write_text(certificate(raw))
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)], cwd=ROOT, capture_output=True, text=True, check=True)
    audit(checked.stdout); require(not checked.stderr.strip(), 'unexpected certificate stderr')
    print(checked.stdout, end='', flush=True)
    report = dict(profile=profile, units=spec, axioms=checked.stdout.splitlines(),
                  original_byte_dependency_chain_checked=True,
                  scope='Conditional floor CALL through death-state entry/return and timing RNG/clamp. Stops before item-drop dispatch and P_KillMobj return.',
                  cross_check=cross_check(raw) if args.cross_check else None)
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: E1M1 death timing joined from floor CALL through RNG/clamp (278-instruction bound).')
    if report['cross_check']: print('Independent x86 timing comparisons:', report['cross_check']['cases'])


if __name__ == '__main__': main()
