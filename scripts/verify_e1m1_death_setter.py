#!/usr/bin/env python3
"""Check E1M1 player death-state entry through the original setter's RET."""
import argparse
import json
import random
import re
import struct
import subprocess
import tempfile
from pathlib import Path
import verify_e1m1_death as previous
from verify_original_arithmetic import fixups

ROOT, require = previous.ROOT, previous.require
extraction = previous.branches.extraction
NAMES = ['setter_checked', 'normal_checked', 'extreme_checked', 'entry_checked', 'joined_checked']
NAMES += ['Doom.Proofs.DeathSetter.'+n for n in
          ['setter_prologue', 'setter_body', 'setter_epilogue', 'original_execution', 'memory_frame', 'entry_fields']]
NAMES += ['Doom.Proofs.E1M1DeathSetter.'+n for n in
          ['table_decoded', 'live_metadata', 'live_entry', 'live_correspondence', 'contains_previous', 'contains_setter', 'joined_execution']]


def table_data(binary, profile, spec):
    le = int(profile['le_offset'], 16)
    u32 = lambda p: struct.unpack_from('<I', binary, p)[0]
    data = struct.unpack_from('<6I', binary, le+u32(le+0x40)+48)
    require(data == (0x85e10, 0x70000, 0x2043, 71, 38, 0), 'unexpected data object')
    result = {}
    for name, index, fields in [('normal', 158, (28, 7, 10, 0, 159, 0, 0)),
                                ('extreme', 165, (28, 14, 5, 0, 166, 0, 0))]:
        row = spec['states'][name]
        start = int(row['offset'], 16)
        require(row['index'] == index and start == 0x15a28+28*index, 'wrong death-state address')
        raw = bytearray()
        for p in range(start, start+28):
            entry = le+u32(le+0x48)+4*(70+p//4096)
            require(binary[entry+3] == 0, 'unsupported table page')
            physical = int.from_bytes(binary[entry:entry+3], 'big')
            require(physical > 0, 'unmapped table page')
            at = int(profile['data_pages_offset'], 16)+(physical-1)*4096+p%4096
            require(at < len(binary), 'truncated table page')
            raw.append(binary[at])
        require(raw.hex() == row['hex'], 'death-state table mismatch')
        relocs = fixups(binary, range(70+start//4096, 70+(start+27)//4096+1))
        require(not any(max(70*4096+start, p) < min(70*4096+start+28, p+4)
                        for p, _, _ in relocs), 'unexpected death-state table relocation')
        require(struct.unpack('<7I', raw) == fields, 'death-state fields mismatch')
        result[name] = bytes(raw)
    return result


def certificate(raw):
    source = '''import Doom.Proofs.E1M1DeathSetter
namespace Doom.Verification.ExtractedDeathSetter
open Doom.Proofs X86 X86Memory X86Control BlockSummary
'''
    for name, definition in [('setter', 'Doom19.setMobjStateBytes'),
                             ('normal', 'E1M1DeathSetter.stateBytes false'),
                             ('extreme', 'E1M1DeathSetter.stateBytes true')]:
        source += f'def {name} : List UInt8 := ['+','.join(hex(b) for b in raw[name])+']\n'
        source += f'theorem {name}_checked : {name}={definition} := by decide\n'
    source += '''theorem entry_checked (extreme : Bool) (s : X86Memory.State) (f : Option Flags)
    (h : DeathSetter.SetterInputs (E1M1DeathSetter.entry extreme) s) :
    X86Routine.run (PainSetter.bytesProgram setter) [0x2a3f1] 24 ⟨s,f,0x30ea0⟩ =
      some (DeathSetter.setterEnd (E1M1DeathSetter.entry extreme) s) := by
  rw [setter_checked]
  exact DeathSetter.original_execution (E1M1DeathSetter.entry extreme) s f h

theorem joined_checked (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32)
    (sim : Simulation) (map : sim.map.name="E1M1") (skill : load32 s.memory (0x2b3e0#32)=2)
    (body : Death.Body) (info : body.info=E1M1Death.playerInfo) (w : Fin 3) (y : Fixed)
    (h : KillDeathBranches.Inputs s v d false 0 body sim.deathWorld w y)
    (dead : (PlayerDamage.apply v d none false false sim.rng).killed=true)
    (stackSafe : Apart (0x12c5c#32) (s.regs 4-(56#32))) (ins : E1M1DeathSetter.Inputs s) :
    ∃ (extreme : Bool) (t : X86Control.State),
      E1M1DeathSetter.stateId extreme=Death.deathState
        (PlayerDamage.apply v d none false false sim.rng).state.health E1M1Death.playerInfo ∧
      X86Routine.run E1M1DeathSetter.program [0x2a3f1] 263 ⟨s,f,pc⟩=some t ∧
      t.pc=0x2a3f1 ∧ t.core.regs 0=1 ∧ t.core.regs 3=s.regs 0 ∧ t.core.regs 4=s.regs 4-52 ∧
      DeathSetter.observeFields t.core.memory (s.regs 0)=
        ((E1M1DeathSetter.entry extreme).pointer,(E1M1DeathSetter.entry extreme).tics,
         (E1M1DeathSetter.entry extreme).sprite,(E1M1DeathSetter.entry extreme).frame) ∧
      load32 t.core.memory (0x12c5c#32)=0 ∧
      KillBookkeeping.joinedObservation s 0 t=KillBookkeeping.joinedLiveObservation
        (PlayerDamage.apply v d none false false sim.rng) 0 body sim.deathWorld ∧
      load32 t.core.memory (KillBookkeeping.player 0+244)=0x15a28+BitVec.ofNat 32 (Weapon.down w.val)*28 ∧
      load32 t.core.memory (KillBookkeeping.player 0+248)=1 ∧
      load32 t.core.memory (KillBookkeeping.player 0+256)=(Weapon.lowerHeight y true).raw.toBitVec ∧
      PlayerHeight.Frame s.memory t.core.memory
        (E1M1DeathSetter.previousWrites s ++ E1M1DeathSetter.suffixWrites s) := by
  exact E1M1DeathSetter.joined_execution s f pc site v d sim map skill body info w y h dead stackSafe ins
'''
    source += '\n'.join('#print axioms '+n for n in NAMES)
    return source+'\nend Doom.Verification.ExtractedDeathSetter\n'


def audit(output):
    rest = output.strip()
    for short in NAMES:
        name = short if '.' in short else 'Doom.Verification.ExtractedDeathSetter.'+short
        match = re.match(re.escape(f"'{name}'")+
                         r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axioms: '+str(axioms))
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


def cross_check(raw, spec):
    import capstone
    import unicorn as uc
    from unicorn import x86_const as x
    cases = [(state, seed, wrap) for state in [158, 165] for seed in range(256) for wrap in [False, True]]
    with tempfile.TemporaryDirectory() as directory:
        inp, out = Path(directory)/'input', Path(directory)/'output'
        inp.write_text(''.join(f'{state} {seed}\n' for state, seed, _ in cases))
        subprocess.run([str(ROOT/'.lake/build/bin/death-probe'), 'state-entry', str(inp), str(out)], check=True)
        answers = [line.split() for line in out.read_text().splitlines()]
    require(len(answers) == len(cases), 'compiled entry row count')
    listing = list(capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_32).disasm(raw['setter'], 0x30ea0))
    require(b''.join(bytes(i.bytes) for i in listing) == raw['setter'], 'independent decoder mismatch')
    em = uc.Uc(uc.UC_ARCH_X86, uc.UC_MODE_32)
    CODE, DATA = 0x100000, 0x600000
    for addr, size in [(CODE, 0x40000), (0, 0x30000), (DATA, 0x2000), (0xfffff000, 0x1000)]:
        em.mem_map(addr, size)
    em.mem_write(CODE+0x30ea0, raw['setter'])
    for name in ['normal', 'extreme']:
        em.mem_write(int(spec['states'][name]['offset'], 16), raw[name])
    registers = [x.UC_X86_REG_EAX, x.UC_X86_REG_ECX, x.UC_X86_REG_EDX, x.UC_X86_REG_EBX,
                 x.UC_X86_REG_ESP, x.UC_X86_REG_EBP, x.UC_X86_REG_ESI, x.UC_X86_REG_EDI]
    writes, visits = [], []
    em.hook_add(uc.UC_HOOK_MEM_WRITE, lambda _e, _a, a, n, v, _u: writes.append((a, n, v & ((1 << (8*n))-1))))
    def visit(e, a, _n, _u):
        if a == CODE+0x2a3f1:
            e.emu_stop()
        else:
            visits.append(a-CODE)
    em.hook_add(uc.UC_HOOK_CODE, visit)
    put = lambda a, v: em.mem_write(a & 0xffffffff, struct.pack('<I', v & 0xffffffff))
    rng = random.Random(0x30EA0)
    pages = list(range(0, 0x30000, 4096))+[DATA, DATA+4096, 0xfffff000]
    for i, ((state, seed, wrap), answer) in enumerate(zip(cases, answers)):
        sid, tics, sprite, frame, next_state, next_rng, events = answer
        sid, tics, frame, next_state, next_rng, events = map(int, [sid, tics, frame, next_state, next_rng, events])
        require(sid == state and sprite == 'PLAY' and next_rng == seed and events == 1, 'compiled entry effects')
        obj = DATA+128+seed%4
        sp = 0 if wrap else DATA+4096+128+seed%4
        rr = [rng.getrandbits(32) for _ in registers]
        rr[0], rr[2], rr[4] = obj, state, sp
        for reg, val in zip(registers, rr): em.reg_write(reg, val)
        em.reg_write(x.UC_X86_REG_EFLAGS, 2 | (rng.getrandbits(12) & 0x8d5))
        put(sp, CODE+0x2a3f1)
        put(0x12720, seed)
        before = {a: bytearray(em.mem_read(a, 4096)) for a in pages}
        writes.clear(); visits.clear()
        em.emu_start(CODE+0x30ea0, CODE+0x40000, count=25)
        require(em.reg_read(x.UC_X86_REG_EIP) == CODE+0x2a3f1, f'return site {i}')
        require(len(visits) == 24, f'instruction count {i}')
        expected_writes = [((sp-4)&0xffffffff, 4, rr[3]), ((sp-8)&0xffffffff, 4, rr[6]),
                           (obj+100, 4, 0x15a28+sid*28), (obj+96, 4, tics),
                           (obj+36, 4, 28), (obj+40, 4, frame)]
        require(writes == expected_writes, f'write sequence {i}')
        rr[0], rr[2], rr[4] = 1, next_state, (sp+4)&0xffffffff
        require([em.reg_read(reg) for reg in registers] == rr, f'registers {i}')
        require(em.reg_read(x.UC_X86_REG_EFLAGS) & 0x8c1 == 0, f'modeled flags {i}')
        for a, n, val in writes:
            for byte in range(n):
                at = (a+byte)&0xffffffff
                before[at&~4095][at%4096] = (val >> (8*byte)) & 255
        require(all(em.mem_read(a, 4096) == data for a, data in before.items()), f'memory frame/RNG {i}')
    return dict(cases=len(cases), instructions_per_call=24, compiled_live_setState=True,
                all_registers_ordered_writes_memory_and_rng_checked=True,
                unaligned_objects_and_stack=True, wrapping_stack=True,
                disassembly=[f'{i.address:#x}: {i.mnemonic} {i.op_str}' for i in listing])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cross-check', action='store_true')
    args = parser.parse_args()
    spec = json.loads((ROOT/'tests/reference/original-death-setter.json').read_text())
    exe = json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text())
    shareware = json.loads((ROOT/'tests/reference/shareware.json').read_text())
    profile = json.loads(previous.PROFILE.read_text())
    previous.check_profile(profile, exe, shareware)
    out = ROOT/'artifacts/e1m1-death-setter'
    out.mkdir(parents=True, exist_ok=True)
    (out/'report.json').unlink(missing_ok=True)
    binary = extraction.original.extract(ROOT/shareware['local_directory']/'doom19s.zip', shareware, exe)
    raw = extraction.extract(binary, exe, spec) | table_data(binary, exe, spec)
    with (out/'dependencies.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/verify-e1m1-death')], cwd=ROOT,
                       stdout=log, stderr=subprocess.STDOUT, check=True)
        subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.E1M1DeathSetter', 'death-probe'], cwd=ROOT,
                       stdout=log, stderr=subprocess.STDOUT, check=True)
    source = out/'Checked.lean'
    source.write_text(certificate(raw))
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)], cwd=ROOT,
                             capture_output=True, text=True, check=True)
    audit(checked.stdout)
    require(not checked.stderr.strip(), 'unexpected certificate stderr')
    print(checked.stdout, end='', flush=True)
    report = dict(profile=profile, units=spec, axioms=checked.stdout.splitlines(),
                  scope='Conditional floor CALL through death-state entry and RET to P_KillMobj; before randomized death timing.',
                  original_byte_dependency_chain_checked=True,
                  cross_check=cross_check(raw, spec) if args.cross_check else None)
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: E1M1 lethal-floor chain through player death-state entry and original RET (263-instruction bound).')
    if report['cross_check']: print('Independent x86 setter comparisons:', report['cross_check']['cases'])


if __name__ == '__main__': main()
