#!/usr/bin/env python3
"""Certify the pinned original floor lookup through lethal damage and sector RET."""
import argparse
import json
import random
import re
import struct
import subprocess
from pathlib import Path
import verify_e1m1_floor_return as previous
ROOT, require, extraction = previous.ROOT, previous.require, previous.extraction
NAMES = ['a_checked', 'b_checked', 'c_checked', 'd_checked', 'return_checked', 'joined_checked']
NAMES += ['Doom.Verification.X86CodeMemory.'+n for n in
          ['execute_success', 'lift_success', 'run_lift_success']]
NAMES += ['Doom.Proofs.FloorReturn.'+n for n in
          ['decoded', 'execution', 'original_execution', 'Saved.then_frame', 'caller_saved', 'restores']]
NAMES += ['Doom.Proofs.E1M1SectorReturn.'+n for n in ['contains_damage', 'contains_floor', 'joined_execution']]
NAMES += ['Doom.Proofs.E1M1FloorCycle.'+n for n in ['contains_return', 'contains_caller', 'joined_execution']]


def certificate(raw):
    source = '''import Doom.Proofs.E1M1FloorCycle
set_option maxRecDepth 32768
set_option maxHeartbeats 600000
namespace Doom.Verification.ExtractedFloorCycle
open Doom.Proofs X86 X86Memory X86Control BlockSummary
'''
    for name in 'abcd':
        source += 'def '+name+' : List UInt8 := ['+','.join(hex(b) for b in raw[name])+']\n'
        source += f'theorem {name}_checked : {name}=FloorReturn.code := by decide\n'
    source += '''theorem return_checked (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ FloorReturn.sites) (returnPC : load32 s.memory (s.regs 4+16)=0x333e5) :
    X86Routine.run (FloorReturn.bytesProgram a b c d) [0x333e5] 5 ⟨s,f,pc⟩=some (FloorReturn.result s f) := by
  rw [a_checked,b_checked,c_checked,d_checked]
  exact FloorReturn.original_execution s f pc site returnPC
'''
    source += (ROOT/'tests/reference/e1m1-floor-cycle.lean').read_text()
    return source+'\n'+'\n'.join('#print axioms '+name for name in NAMES)+'\nend Doom.Verification.ExtractedFloorCycle\n'


def audit(output):
    rest = output.strip()
    for short in NAMES:
        name = short if '.' in short else 'Doom.Verification.ExtractedFloorCycle.'+short
        match = re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axioms: '+str(axioms))
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


def cross_check(raw):
    """Independent x86 check of the four five-instruction suffixes only."""
    import capstone
    import unicorn as uc
    from unicorn import x86_const as x
    em = uc.Uc(uc.UC_ARCH_X86, uc.UC_MODE_32)
    CODE, DATA, STOP = 0x100000, 0x600000, 0x1333e5
    for address, size in [(CODE, 0x40000), (DATA, 0x2000), (0, 0x1000), (0xfffff000, 0x1000)]:
        em.mem_map(address, size)
    sites = [0x2fb7b, 0x2fba5, 0x2fbd7, 0x2fc39]
    listings = {}
    for name, site in zip('abcd', sites):
        em.mem_write(CODE+site, raw[name])
        ins = list(capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_32).disasm(raw[name], site))
        require(b''.join(bytes(i.bytes) for i in ins) == raw[name], 'disassembly coverage')
        listings[name] = [f'{i.address:#x}: {i.mnemonic} {i.op_str}' for i in ins]
    regs = [x.UC_X86_REG_EAX, x.UC_X86_REG_ECX, x.UC_X86_REG_EDX, x.UC_X86_REG_EBX,
            x.UC_X86_REG_ESP, x.UC_X86_REG_EBP, x.UC_X86_REG_ESI, x.UC_X86_REG_EDI]
    visits, writes = [], []
    def visit(e, a, _n, _u):
        if a == STOP: e.emu_stop()
        else: visits.append(a-CODE)
    em.hook_add(uc.UC_HOOK_CODE, visit)
    em.hook_add(uc.UC_HOOK_MEM_WRITE, lambda _e, _a, a, n, v, _u: writes.append((a,n,v)))
    pages = [DATA, DATA+4096, 0, 0xfffff000]
    def put(a, v):
        for j, byte in enumerate(struct.pack('<I', v)):
            em.mem_write((a+j)&0xffffffff, bytes([byte]))
    rand = random.Random(0x333E5)
    count = 0
    for site in sites:
        for align in range(4):
            for wrap in [False, True]:
                for _ in range(32):
                    sp = (0xfffffff0+align) if wrap else DATA+128+align
                    rr = [rand.getrandbits(32) for _ in regs]; rr[4] = sp
                    words = [rand.getrandbits(32) for _ in range(4)]
                    for j, word in enumerate(words+[STOP]): put(sp+4*j, word)
                    for reg, value in zip(regs, rr): em.reg_write(reg, value)
                    flags = 2|(rand.getrandbits(12)&0x8d5)
                    em.reg_write(x.UC_X86_REG_EFLAGS, flags)
                    before = {p:bytes(em.mem_read(p,4096)) for p in pages}
                    visits.clear(); writes.clear()
                    em.emu_start(CODE+site, CODE+0x40000, count=6)
                    require(em.reg_read(x.UC_X86_REG_EIP) == STOP, f'return address {count}')
                    require(visits == list(range(site,site+5)), f'instruction order {count}')
                    rr[4] = (sp+20)&0xffffffff
                    for r, value in zip([6,2,1,3], words): rr[r] = value
                    require([em.reg_read(r) for r in regs] == rr, f'all registers {count}')
                    require(em.reg_read(x.UC_X86_REG_EFLAGS) == flags, f'flags {count}')
                    require(not writes, f'no writes {count}')
                    require(all(bytes(em.mem_read(p,4096)) == data for p,data in before.items()), f'memory {count}')
                    count += 1
    return dict(cases=count, scope='Four original five-instruction POP/RET suffixes only; not the full 342-instruction path.',
                ordinary_and_wrapping_stacks=True, alignments=4, all_registers=True, flags=True,
                full_mapped_data_memory=True, listings=listings)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cross-check', action='store_true')
    args = parser.parse_args()
    spec = json.loads((ROOT/'tests/reference/original-floor-return.json').read_text())
    exe = json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text())
    sw = json.loads((ROOT/'tests/reference/shareware.json').read_text())
    profile = json.loads((ROOT/'tests/reference/e1m1-proof-profile.json').read_text())
    binary = extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip', sw, exe)
    raw = extraction.extract(binary, exe, spec)
    out = ROOT/'artifacts/e1m1-floor-cycle'; out.mkdir(parents=True, exist_ok=True)
    (out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:
        for script in ['verify-e1m1-floor-return', 'verify-original-floor-joined']:
            subprocess.run([str(ROOT/'scripts'/script)], cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=True)
        subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.E1M1FloorCycle'],
                       cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=True)
    path = out/'Checked.lean'; path.write_text(certificate(raw))
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(path)],
                             cwd=ROOT, capture_output=True, text=True, check=True)
    audit(checked.stdout); require(not checked.stderr.strip(), 'unexpected certificate stderr')
    print(checked.stdout, end='', flush=True)
    report = dict(profile=profile, units=spec, axioms=checked.stdout.splitlines(),
                  original_byte_dependency_chains_checked=True,
                  scope='Conditional continuous 0x333d0 sector lookup through lethal damage and all three returns to 0x333e5, bound 342. '
                        'Saved outer frame is derived from the actual caller. Damage preconditions are pulled back through the exact initial-state floor summary; '
                        'global reachability and invariant preservation remain unproved.',
                  cross_check=cross_check(raw) if args.cross_check else None)
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: floor lookup through lethal damage and sector return (342-instruction bound).')
    if report['cross_check']: print('Independent x86 epilogue comparisons:', report['cross_check']['cases'])


if __name__ == '__main__': main()
