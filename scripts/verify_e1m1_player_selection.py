#!/usr/bin/env python3
"""Certify preparation, lethal floor damage and original weapon selection."""
import argparse
import json
import random
import re
import struct
import subprocess
from pathlib import Path
import verify_e1m1_floor_cycle as previous
ROOT, require, extraction = previous.ROOT, previous.require, previous.extraction
NAMES = ['bytes_checked', 'selection_checked', 'live_checked', 'prepared_checked', 'joined_checked']
NAMES += ['Doom.Proofs.DamageTransport.'+n for n in
          ['entry','health','actor','kill','bookLayout','book','bookJoined','drop','branches','setter','timing','returns','Contract.transport','allWrites_eq']]
NAMES += ['Doom.Proofs.PlayerPreparation.'+n for n in ['reaction_command','execution_command']]
NAMES += ['Doom.Proofs.E1M1PreparedFloor.'+n for n in ['contains_cycle','contains_preparation','boundary_agrees','joined_execution']]
NAMES += ['Doom.Proofs.WeaponSelect.'+n for n in ['decoded','read_loaded','masked','mask_sequence','execution','result_memory','result_register','result_pending','live_pending']]
NAMES += ['Doom.Proofs.E1M1PlayerSelection.'+n for n in ['contains_selection','contains_prepared','append_selection','command_byte','inputs_transport','joined_execution']]


def certificate(raw):
    source = '''import Doom.Proofs.E1M1PlayerSelection
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
namespace Doom.Verification.ExtractedPlayerSelection
open Doom Doom.Proofs X86 X86Memory X86Control BlockSummary
'''
    source += 'def extracted : List UInt8 := ['+','.join(hex(b) for b in raw['selection'])+']\n'
    source += '''theorem bytes_checked : extracted=WeaponSelect.code := by decide
 theorem selection_checked (s : X86Memory.State) (f : Option Flags) (b : BitVec 8) (w : Fin 3)
    (h : WeaponSelect.Inputs s b w) :
    X86Routine.run (WeaponSelect.bytesProgram extracted) [0x33476] 24 ⟨s,f,0x333e5⟩=some (WeaponSelect.result s b w) := by
  rw [bytes_checked]
  exact WeaponSelect.execution s f b w h
 theorem live_checked (s : X86Memory.State) (b : BitVec 8) (w : Fin 3) (c : Weapon.Context)
    (owned : (WeaponSelect.owns s w != 0)=c.player.weapons[w.val])
    (ready : WeaponSelect.current s=BitVec.ofNat 32 c.player.readyWeapon.val)
    (pending : load32 s.memory (s.regs 2+116)=BitVec.ofNat 32 c.player.pendingWeapon.val) :
    load32 (WeaponSelect.result s b w).core.memory (s.regs 2+116)=
      BitVec.ofNat 32 (c.select (if b &&& (4#8)=(0#8) then none else some w.val)).player.pendingWeapon.val := by
  exact WeaponSelect.live_pending s b w c owned ready pending
'''
    source += (ROOT/'tests/reference/e1m1-player-selection.lean').read_text()
    return source+'\n'+'\n'.join('#print axioms '+name for name in NAMES)+'\nend Doom.Verification.ExtractedPlayerSelection\n'


def audit(output):
    rest = output.strip()
    for short in NAMES:
        name = short if '.' in short else 'Doom.Verification.ExtractedPlayerSelection.'+short
        match = re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext','Quot.sound','Classical.choice'}, 'unexpected axioms: '+str(axioms))
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


def cross_check(raw):
    """Independent original x86 selection vs the compiled production helper."""
    import capstone
    import unicorn as uc
    from unicorn import x86_const as x
    em = uc.Uc(uc.UC_ARCH_X86,uc.UC_MODE_32)
    CODE, DATA, STOP = 0x100000, 0x600000, 0x133476
    em.mem_map(CODE,0x40000); em.mem_map(DATA,0x3000); em.mem_map(0x20000,0x10000)
    em.mem_write(CODE+0x333e5,raw['selection'])
    ins = list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(raw['selection'],0x333e5))
    require(b''.join(bytes(i.bytes) for i in ins)==raw['selection'],'instruction coverage')
    regs = [x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
            x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes,visits = [],[]
    em.hook_add(uc.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_u:writes.append((a,n,v)))
    def visit(e,a,_n,_u):
        if a==STOP: e.emu_stop()
        else: visits.append(a-CODE)
    em.hook_add(uc.UC_HOOK_CODE,visit)
    rand=random.Random(0x33476)
    cases,commands=[],[]
    for buttons in range(128):
        choice=(buttons&56)>>3
        if buttons&4 and choice>2: continue
        for align in range(4):
            for mask in range(8):
                for ready in range(3):
                    pending=rand.randrange(10)
                    health=rand.choice([0,1,100]); bullets=rand.choice([0,1,200]); shells=rand.choice([0,1,50])
                    commands.append(f'select {ready} {pending} {mask} {choice if buttons&4 else 9} {health} {bullets} {shells}')
                    cases.append((buttons,choice,align,mask,ready,pending))
    out=ROOT/'artifacts/e1m1-player-selection';out.mkdir(parents=True,exist_ok=True)
    inp=out/'selection-input.txt'; answer=out/'selection-output.txt'
    inp.write_text('\n'.join(commands)+'\n')
    subprocess.run([str(ROOT/'.lake/build/bin/weapon-probe'),str(inp),str(answer)],check=True,cwd=ROOT)
    lines=answer.read_text().splitlines();require(len(lines)==len(cases),'compiled output count')
    visited=set()
    for i,((buttons,choice,align,mask,ready,pending),line) in enumerate(zip(cases,lines)):
        player=DATA+0x100+align; command=DATA+0x1000+align
        rr=[rand.getrandbits(32) for _ in regs];rr[2]=player;rr[3]=command;rr[4]=DATA+0x2000
        memory=bytearray(rand.randbytes(0x3000))
        def put(a,v): struct.pack_into('<I',memory,a-DATA,v)
        for w in range(9): put(player+120+4*w,rand.choice([1,0x80000000,0xffffffff]) if mask&(1<<w) else 0)
        put(player+112,ready);put(player+116,pending);memory[command+7-DATA]=buttons
        em.mem_write(DATA,bytes(memory));em.mem_write(0x2a3bc,b'\0'*4)
        for reg,value in zip(regs,rr): em.reg_write(reg,value)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rand.getrandbits(12)&0x8d5))
        visits.clear();writes.clear()
        em.emu_start(CODE+0x333e5,CODE+0x40000,count=25)
        require(em.reg_read(x.UC_X86_REG_EIP)==STOP,f'exit {i}')
        require(len(visits)<=24,f'bound {i}')
        visited.update(visits)
        change=bool(buttons&4 and mask&(1<<choice) and ready!=choice)
        expected_pending=int(line.split('|')[0].split()[1])
        require(expected_pending==(choice if change else pending),f'compiled helper {i}')
        if change: put(player+116,expected_pending)
        require(bytes(em.mem_read(DATA,len(memory)))==bytes(memory),f'complete data memory {i}')
        require(writes==([(player+116,4,choice)] if change else []),f'ordered writes {i}')
        rr[0]=choice if buttons&4 else ((rr[0]&0xffff00ff)|(buttons<<8))
        require([em.reg_read(r) for r in regs]==rr,f'all registers {i}')
        # Final TEST has ZF=1; no-ownership/same-weapon CMP has ZF=1;
        # a changed weapon finishes CMP choice,6, hence CF=SF=1.
        expected_flags=0x81 if change else 0x40
        require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==expected_flags,f'modeled flags {i}')
    return dict(cases=len(cases),scope='Original 0x333e5..0x33476 selection block only; not the full 591-instruction path.',
                ordinary_buttons=88,alignments=4,all_ownership_masks=True,noncanonical_owned_words=True,
                all_registers=True,modeled_flags=True,ordered_writes=True,full_player_command_memory=True,
                production_helper='Doom.Weapon.Context.select',visited=sorted(visited),
                listing=[f'{i.address:#x}: {i.mnemonic} {i.op_str}' for i in ins])


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-weapon-select.json').read_text())
    exe=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,exe)
    raw=extraction.extract(binary,exe,spec)
    out=ROOT/'artifacts/e1m1-player-selection';out.mkdir(parents=True,exist_ok=True)
    (out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/verify-e1m1-floor-cycle')],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1PlayerSelection','weapon-probe'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    path=out/'Checked.lean';path.write_text(certificate(raw))
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout);require(not checked.stderr.strip(),'unexpected stderr')
    print(checked.stdout,end='',flush=True)
    report=dict(profile=json.loads((ROOT/'tests/reference/e1m1-proof-profile.json').read_text()),units=spec,
                axioms=checked.stdout.splitlines(),original_byte_dependency_chains_checked=True,
                scope='Conditional continuous player preparation through lethal floor damage and weapon selection, 0x333b1 to 0x33476, bound 591. '
                      'Contracts transported from initial state. Global startup/reachability, remaining player/world tic and rendering are still unproved.',
                cross_check=cross_check(raw) if args.cross_check else None)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: preparation, lethal floor cycle and weapon selection (591-instruction bound).')
    if report['cross_check']: print('Independent original x86 selection comparisons:',report['cross_check']['cases'])


if __name__=='__main__': main()
