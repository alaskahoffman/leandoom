#!/usr/bin/env python3
"""Certify continuous pinned lethal-floor CALL through kill and damage RETs."""
import argparse
import json
import random
import re
import struct
import subprocess
import tempfile
from pathlib import Path
import verify_e1m1_death_return as previous
ROOT,require,extraction=previous.ROOT,previous.require,previous.extraction
NAMES=['jump_checked','epilogue_checked','damage_return_checked','joined_checked']
NAMES += ['Doom.Proofs.DeathStack.Saved.then_frame','Doom.Proofs.DeathStack.slots_apart',
          'Doom.Proofs.KillEntry.setup_return','Doom.Proofs.KillEntry.joined_execution_tracked',
          'Doom.Proofs.KillBookkeeping.joined_execution_detailed_tracked',
          'Doom.Proofs.KillWeaponDrop.joined_execution_detailed_tracked',
          'Doom.Proofs.KillDeathBranches.joined_execution_tracked','Doom.Proofs.E1M1Death.floor_death_tracked',
          'Doom.Proofs.E1M1DeathSetter.joined_execution_tracked','Doom.Proofs.E1M1DeathTiming.joined_execution_tracked']
NAMES += ['Doom.Proofs.LethalReturn.'+n for n in ['decoded','execution','original_execution','memory_unchanged']]
NAMES += ['Doom.Proofs.E1M1FloorReturn.'+n for n in ['contains_previous','previous_none','contains_return','contains_damage','joined_execution']]


def certificate(raw):
    source='''import Doom.Proofs.E1M1FloorReturn
set_option maxRecDepth 32768
set_option maxHeartbeats 300000
namespace Doom.Verification.ExtractedFloorReturn
open Doom.Proofs X86 X86Memory X86Control BlockSummary
'''
    for name,definition in [('jump','LethalReturn.jumpBytes'),('epilogue','LethalReturn.epilogueBytes')]:
        source+='def '+name+' : List UInt8 := ['+','.join(hex(b) for b in raw[name])+']\n'
        source+=f'theorem {name}_checked : {name}={definition} := by decide\n'
    source+='''theorem damage_return_checked (s : X86Memory.State) (f : Option Flags)
    (outside : 0x2a74e ≤ (LethalReturn.result s).pc) :
    X86Routine.run (LethalReturn.bytesProgram jump epilogue) [(LethalReturn.result s).pc] 6
      ⟨s,f,0x2a6b1⟩=some (LethalReturn.result s) := by
  rw [jump_checked,epilogue_checked]
  exact LethalReturn.original_execution s f outside
'''
    source+=(ROOT/'tests/reference/e1m1-floor-return.lean').read_text()
    return source+'\n'+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedFloorReturn\n'


def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedFloorReturn.'+short
        match=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+name)
        axioms={a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms))
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')


def cross_check(raw):
    import capstone
    import unicorn as uc
    from unicorn import x86_const as x
    corpus = previous.cases()
    with tempfile.TemporaryDirectory() as directory:
        inp, out = Path(directory)/'input', Path(directory)/'output'
        inp.write_text(''.join(f'{tics} {play} {misc}\n' for tics, play, misc, _, _ in corpus))
        subprocess.run([str(ROOT/'.lake/build/bin/death-probe'), 'death-return', str(inp), str(out)], check=True)
        answers = [tuple(map(int, line.split())) for line in out.read_text().splitlines()]
    require(len(answers) == len(corpus), 'compiled row count')
    em = uc.Uc(uc.UC_ARCH_X86, uc.UC_MODE_32)
    CODE, DATA = 0x100000, 0x600000
    for address, size in [(CODE, 0x40000), (0, 0x30000), (DATA, 0x2000), (0xfffff000, 0x1000)]:
        em.mem_map(address, size)
    listings = {}
    for name, address in [('timing', 0x2a3f1), ('rng', 0x24160), ('dispatch', 0x2a40d), ('jump', 0x2a6b1), ('epilogue', 0x2a747)]:
        em.mem_write(CODE+address, raw[name])
        instructions = list(capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_32).disasm(raw[name], address))
        require(b''.join(bytes(i.bytes) for i in instructions) == raw[name], 'decoder byte coverage')
        listings[name] = [f'{i.address:#x}: {i.mnemonic} {i.op_str}' for i in instructions]
    em.mem_write(0x1261c, raw['table'])
    regs = [x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
            x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes, visits = [], []
    stop = CODE+0x2fb7b
    em.hook_add(uc.UC_HOOK_MEM_WRITE, lambda _e,_a,a,n,v,_u: writes.append((a,n,v&((1<<(8*n))-1))))
    def visit(e, a, _n, _u):
        if a == stop: e.emu_stop()
        else: visits.append(a-CODE)
    em.hook_add(uc.UC_HOOK_CODE, visit)
    def put(a, v):
        for j, byte in enumerate(struct.pack('<I', v&0xffffffff)):
            em.mem_write((a+j)&0xffffffff, bytes([byte]))
    pages = list(range(0,0x30000,4096))+[DATA,DATA+4096,0xfffff000]
    rand = random.Random(0x2A40D)
    for number, ((tics,play,misc,align,wrap), answer) in enumerate(zip(corpus,answers)):
        obj = DATA+128+align
        # Crosses the 32-bit address boundary within the saved-register frame.
        sp = ((0xfffffff0+align)&0xffffffff) if wrap else DATA+4096+128+align
        rr = [rand.getrandbits(32) for _ in regs]; rr[3],rr[4] = obj,sp
        saved = [rand.getrandbits(32) for _ in range(5)]
        for j,val in enumerate(saved+[CODE+0x2a6b1]): put((sp+4*j)&0xffffffff,val)
        outer = [rand.getrandbits(32) for _ in range(3)]
        caller = [0x2fb76,0x2fba0,0x2fbd2][number%3]
        stop = CODE+caller+5
        for j,val in enumerate(outer+[stop]): put((sp+36+4*j)&0xffffffff,val)
        for reg,val in zip(regs,rr): em.reg_write(reg,val)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rand.getrandbits(12)&0x8d5))
        put(obj+88,0);put(obj+96,tics);put(0x12720,play);put(0x1271c,misc)
        before = {a:bytearray(em.mem_read(a,4096)) for a in pages}
        writes.clear();visits.clear()
        em.emu_start(CODE+0x2a3f1,CODE+0x40000,count=33)
        require(em.reg_read(x.UC_X86_REG_EIP)==stop,f'return PC {number}')
        expected_tics=tics-(raw['table'][(play+1)%256]&3)
        require(answer==(expected_tics,(play+1)%256,misc,1),f'compiled helpers {number}')
        expected_writes=[((sp-4)&0xffffffff,4,CODE+0x2a3f6),(0x12720,4,(play+1)%256),(obj+96,4,expected_tics)]
        require(writes==expected_writes,f'no item/epilogue writes {number}')
        require(len(visits)==31 and visits[-17:-6]==[0x2a40d,0x2a410,0x2a413,0x2a425,0x2a428,
                0x2a451,0x2a452,0x2a453,0x2a454,0x2a455,0x2a456],f'player branch/order {number}')
        require(visits[-6:]==[0x2a6b1,0x2a747,0x2a74a,0x2a74b,0x2a74c,0x2a74d],f'damage branch/order {number}')
        rr[0]=0;rr[4]=(sp+52)&0xffffffff
        for reg,val in zip([5,7,6,1,3],saved):rr[reg]=val
        for reg,val in zip([5,7,6],outer):rr[reg]=val
        require([em.reg_read(r) for r in regs]==rr,f'all restored registers {number}')
        added=(sp+36)&0xffffffff;before_add=(sp+24)&0xffffffff
        flags=(0x40 if added==0 else 0)|(0x80 if added>>31 else 0)|(1 if added<before_add else 0)|(0x800 if before_add<2**31 and added>=2**31 else 0)
        require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==flags,f'epilogue ADD flags {number}')
        for a,n,val in writes:
            for j in range(n):
                at=(a+j)&0xffffffff;before[at&~4095][at%4096]=(val>>(8*j))&255
        require(all(em.mem_read(a,4096)==data for a,data in before.items()),f'complete data memory frame {number}')
    return dict(cases=len(corpus),all_rng_indices=True,normal_and_extreme=True,all_three_floor_return_sites=True,
                scope="timing CALL through both returns; not whole-floor native execution",
                unaligned_and_wrapping_saved_frames=True,all_registers_flags_ordered_writes_memory_checked=True,
                compiled_live_timing_and_dropItem=True,disassembly=listings)


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-lethal-return.json').read_text())
    exe=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    profile=json.loads((ROOT/'tests/reference/e1m1-proof-profile.json').read_text())
    previous.previous.previous.previous.check_profile(profile,exe,sw)
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,exe)
    raw=extraction.extract(binary,exe,spec)
    raw.update(extraction.extract(binary,exe,json.loads((ROOT/'tests/reference/original-death-return.json').read_text())))
    raw.update(previous.previous.extract(binary,exe,json.loads((ROOT/'tests/reference/original-death-timing.json').read_text())))
    out=ROOT/'artifacts/e1m1-floor-return';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/verify-e1m1-death-return')],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1FloorReturn','death-probe'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    source=out/'Checked.lean';source.write_text(certificate(raw))
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout);require(not checked.stderr.strip(),'unexpected certificate stderr')
    print(checked.stdout,end='',flush=True)
    report=dict(profile=profile,units=spec,axioms=checked.stdout.splitlines(),original_byte_dependency_chain_checked=True,
                scope='Conditional continuous floor CALL through P_KillMobj RET (289) and P_DamageMobj RET (295). Saved values derived from actual CALL/prologues.',
                cross_check=cross_check(raw) if args.cross_check else None)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: lethal floor CALL through both original returns (295-instruction bound).')
    if report['cross_check']:print('Independent x86 timing-through-both-returns comparisons:',report['cross_check']['cases'])


if __name__=='__main__':main()
