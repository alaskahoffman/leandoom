#!/usr/bin/env python3
"""Original ordinary-floor damage requests: suit, clock, RNG, and call arguments.

This stops before P_DamageMobj: armor/health/death effects are not certified here.
The joined theorem includes the preceding floor guard and switch, beginning
at the outer sector lookup at 0x333d0, including CALL and prologue pushes.
"""
import argparse
import json
import re
import struct
import subprocess
import sys
import tempfile
from pathlib import Path
import verify_original_mul as original
import verify_original_inline_thrust as extraction
import verify_original_arithmetic as arithmetic

ROOT, require = original.ROOT, original.require
NAMES = ['floor_bytes', 'rng_bytes', 'table_bytes', 'correspondence_checked',
         'Doom.Proofs.FloorDamage.decoded', 'Doom.Proofs.FloorDamage.clock_mask',
         'Doom.Proofs.FloorDamage.random_execution', 'Doom.Proofs.FloorDamage.random_call_finish',
         'Doom.Proofs.FloorDamage.light_execution', 'Doom.Proofs.FloorDamage.heavy_execution',
         'Doom.Proofs.FloorDamage.execution', 'Doom.Proofs.FloorDamage.result_observation',
         'Doom.Proofs.FloorDamage.memory_frame', 'Doom.Proofs.FloorDamage.stack_preserved',
         'Doom.Proofs.FloorDamage.damage_arguments',
         'entry_bytes', 'switch_bytes', 'entry_correspondence_checked',
         'Doom.Proofs.FloorEntry.loaded_index', 'Doom.Proofs.FloorEntry.select',
         'Doom.Proofs.FloorEntry.case_inputs', 'Doom.Proofs.FloorEntry.floor_relation',
         'Doom.Proofs.FloorEntry.execution', 'Doom.Proofs.FloorEntry.correspondence',
         'Doom.Proofs.FloorEntry.damage_arguments', 'Doom.Proofs.FloorEntry.memory_frame',
         'Doom.Proofs.FloorEntry.stack_preserved',
         'caller_bytes', 'caller_correspondence_checked',
         'Doom.Proofs.FloorCaller.table_index_apart',
         'Doom.Proofs.FloorCaller.call_prefix', 'Doom.Proofs.FloorCaller.dispatch_prefix',
         'Doom.Proofs.FloorCaller.lookup_preserved', 'Doom.Proofs.FloorCaller.establishes_inputs',
         'Doom.Proofs.FloorCaller.execution', 'Doom.Proofs.FloorCaller.correspondence',
         'Doom.Proofs.FloorCaller.damage_arguments', 'Doom.Proofs.FloorCaller.memory_frame',
         'Doom.Proofs.FloorCaller.memory_unchanged', 'Doom.Proofs.FloorCaller.stack_position']


def certificate(raw, digest):
    literal = lambda data: '['+','.join(hex(b) for b in data)+']'
    return f'''-- Original executable SHA-256 {digest}; file/loader identity checked externally.
import Doom.Proofs.OriginalFloorCaller
namespace Doom.Verification.ExtractedFloorDamage
open X86Memory X86Control Doom.Proofs.FloorDamage
set_option maxRecDepth 32768
def extractedFloor : List UInt8 := {literal(raw['floorDamageBytes'])}
def extractedRng : List UInt8 := {literal(raw['playRandomBytes'])}
def extractedTable : List UInt8 := {literal(raw['randomTableBytes'])}
theorem floor_bytes : extractedFloor = code := by decide
theorem rng_bytes : extractedRng = Doom19.playRandomBytes := by decide
theorem table_bytes : extractedTable = Doom19.randomTableBytes := by decide
-- Inputs pins the table read as well as the CALL/RET memory conditions.
theorem correspondence_checked (kind : Kind) (s : X86Memory.State) (flags : Option Flags)
    (time : Nat) (suit : Bool) (rng : Doom.DoomRandom) (z floor : Doom.Fixed) (onFloor : z = floor)
    (h : Inputs s time suit rng) :
    (X86Routine.run (bytesProgram extractedFloor extractedRng) exits 18 ⟨s,flags,kind.entry⟩).map observe =
      let answer := Doom.LevelSpecials.floorDamage kind.special z floor suit time rng
      some (answer.1,BitVec.ofNat 32 answer.2.play.toNat,BitVec.ofNat 32 answer.2.misc.toNat) := by
  rw [floor_bytes,rng_bytes]
  exact correspondence kind s flags time suit rng z floor onFloor h
def extractedEntry : List UInt8 := {literal(raw['sectorEntryBytes'])}
def extractedSwitch : List UInt8 := {literal(raw['sectorTableBytes'])}
theorem entry_bytes : extractedEntry = Doom.Proofs.SectorEntry.entryBytes := by decide
theorem switch_bytes : extractedSwitch = Doom.Proofs.SectorEntry.tableBytes := by decide
-- The joined statement assumes no on-floor or intermediate case-entry relation.
theorem entry_correspondence_checked (kind : Kind) (s : X86Memory.State) (flags : Option Flags)
    (z floor : Doom.Fixed) (time : Nat) (suit : Bool) (rng : Doom.DoomRandom)
    (h : Doom.Proofs.FloorEntry.Inputs kind s z floor time suit rng) :
    (X86CodeMemory.run (Doom.Proofs.SectorEntry.codeMemory extractedSwitch)
      (Doom.Proofs.FloorEntry.bytesProgram extractedEntry extractedFloor extractedRng)
      exits 31 ⟨s,flags,0x2fb24⟩).map observe =
      let answer := Doom.LevelSpecials.floorDamage kind.special z floor suit time rng
      some (answer.1,BitVec.ofNat 32 answer.2.play.toNat,BitVec.ofNat 32 answer.2.misc.toNat) := by
  rw [entry_bytes,switch_bytes,floor_bytes,rng_bytes]
  exact Doom.Proofs.FloorEntry.correspondence kind s flags z floor time suit rng h
def extractedCaller : List UInt8 := {literal(raw['sectorCallerBytes'])}
theorem caller_bytes : extractedCaller = Doom.Proofs.SectorCaller.callBytes := by decide
-- Initial fields and separation establish the CALL/prologue and nested RNG contracts.
theorem caller_correspondence_checked (kind : Kind) (s : X86Memory.State) (flags : Option Flags)
    (z floor : Doom.Fixed) (time : Nat) (suit : Bool) (rng : Doom.DoomRandom)
    (h : Doom.Proofs.FloorCaller.Inputs kind s z floor time suit rng) :
    (X86CodeMemory.run (Doom.Proofs.SectorEntry.codeMemory extractedSwitch)
      (Doom.Proofs.FloorCaller.bytesProgram extractedCaller extractedEntry extractedFloor extractedRng)
      exits 42 ⟨s,flags,0x333d0⟩).map observe =
      let answer := Doom.LevelSpecials.floorDamage kind.special z floor suit time rng
      some (answer.1,BitVec.ofNat 32 answer.2.play.toNat,BitVec.ofNat 32 answer.2.misc.toNat) := by
  rw [caller_bytes,entry_bytes,switch_bytes,floor_bytes,rng_bytes]
  exact Doom.Proofs.FloorCaller.correspondence kind s flags z floor time suit rng h
'''+ '\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedFloorDamage\n'


def audit(output):
    rest = output.strip()
    for short in NAMES:
        name = short if '.' in short else 'Doom.Verification.ExtractedFloorDamage.'+short
        match = re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing axiom audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext','Classical.choice','Quot.sound'},'unexpected axioms: '+str(axioms))
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')


def cases():
    # Every seed, floor kind, suit branch and clock residue. Also wide clocks,
    # both sides of floor equality, and non-Boolean nonzero suit counters.
    out = [(special,suit,time,seed,0) for special in [5,7,4,16]
           for suit in [0,1] for time in list(range(32))+[32,33,2**31-1,2**31-32]
           for seed in range(256)]
    out += [(special,suit,time,seed,z) for special in [5,7,4,16]
            for suit in [0,1,2100,-1] for time in [0,1,32]
            for seed in [0,59,77,254,255] for z in [-1,0,1]]
    return out


def cross_check(raw,spec):
    import unicorn as uc
    from unicorn import x86_const as x
    import capstone
    for name in ['sectorCallerBytes','sectorEntryBytes','floorDamageBytes','playRandomBytes']:
        pc=int(spec['units'][name]['code_offset'],16)
        decoded=list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(raw[name],pc))
        require(b''.join(bytes(i.bytes) for i in decoded)==raw[name],'incomplete '+name+' disassembly')
    inputs=cases()
    with tempfile.TemporaryDirectory() as directory:
        path=Path(directory)/'commands'
        path.write_text(''.join(f'damage {z} 0 {special} {suit} {time} {seed}\n'
                               for special,suit,time,seed,z in inputs))
        checked=subprocess.run([str(ROOT/'.lake/build/bin/level-probe'),str(path)],cwd=ROOT,
                               capture_output=True,text=True,check=True)
    require(not checked.stderr.strip(),'native diagnostics')
    answers=[tuple(map(int,line.split())) for line in checked.stdout.splitlines()]
    require(len(answers)==len(inputs),'native result count')
    registers=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
               x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    total=0
    for CODE,DATA in [(0x100000,0x800000),(0x500000,0x1000000)]:
        em=uc.Uc(uc.UC_ARCH_X86,uc.UC_MODE_32)
        em.mem_map(CODE,0x40000);em.mem_map(DATA,0x40000)
        for name,unit in spec['units'].items():
            patched=bytearray(raw[name])
            for relocation in unit['relocations']:
                base=CODE if relocation['object']==1 else DATA
                struct.pack_into('<I',patched,relocation['offset'],base+int(relocation['target'],16))
            em.mem_write(CODE+int(unit['code_offset'],16),bytes(patched))
        em.mem_write(DATA+0x1261c,raw['randomTableBytes'])
        stops={CODE+p for p in [0x2fc39,0x2fb76,0x2fba0,0x2fbd2]}
        calls=[];writes=[]
        def hook_code(e,addr,_size,_data):
            if addr==CODE+0x24160:calls.append(addr)
            if addr in stops:e.emu_stop()
        em.hook_add(uc.UC_HOOK_CODE,hook_code)
        em.hook_add(uc.UC_HOOK_MEM_WRITE,lambda _e,_a,addr,size,value,_u:writes.append((addr,size,value)))
        for case,((special,suit,time,seed,z),(amount,index)) in enumerate(zip(inputs,answers)):
            align=case%4
            player,obj,sub,sector,sp=[DATA+v+align for v in [0x34000,0x35000,0x36000,0x37000,0x38000]]
            for addr,value in [(player,obj),(player+56,suit),(obj+52,sub),(obj+20,z&0xffffffff),
                               (sub,sector),(sector,0),(DATA+0x2cf80,time),(DATA+0x12720,seed),
                               (DATA+0x1271c,173)]:
                em.mem_write(addr,struct.pack('<I',value&0xffffffff))
            em.mem_write(sector+14,struct.pack('<H',special))
            initial=[0xffffffff,0xaaaaaaaa,player,0xbbbbbbbb,sp,0xcccccccc,0xdddddddd,0xeeeeeeee]
            for reg,value in zip(registers,initial):em.reg_write(reg,value)
            em.reg_write(x.UC_X86_REG_EFLAGS,2|(case&0x8d5))
            calls.clear();writes.clear()
            em.emu_start(CODE+0x333d0,0,count=64)
            pc=em.reg_read(x.UC_X86_REG_EIP)
            expectedpc=0x2fc39 if amount==0 else {5:0x2fb76,7:0x2fba0,4:0x2fbd2,16:0x2fbd2}[special]
            require(pc==CODE+expectedpc,f'wrong stop at case {case}')
            require(int.from_bytes(em.mem_read(DATA+0x12720,4),'little')==index,f'RNG mismatch {case}')
            require(int.from_bytes(em.mem_read(DATA+0x1271c,4),'little')==173,f'misc RNG changed {case}')
            draw=special in (4,16) and suit!=0 and z==0
            require(len(calls)==int(draw),f'RNG call count {case}')
            expectedwrites=[(sp-4,4,CODE+0x333e5),(sp-8,4,initial[3]),(sp-12,4,initial[1]),
                            (sp-16,4,player),(sp-20,4,initial[6])]
            if draw:expectedwrites += [(sp-24,4,CODE+0x2fbb5),(DATA+0x12720,4,(seed+1)%256)]
            require(writes==expectedwrites,f'memory write order {case}')
            require(em.reg_read(x.UC_X86_REG_ESP)==sp-20,f'stack mismatch {case}')
            if amount:
                args=[em.reg_read(reg) for reg in registers[:4]]
                require(args==[obj,amount,0,0],f'damage arguments {case}: {args}')
            total+=1
    return {'cases':total,'layouts':2,'alignments':4,'all_256_seeds':True,'all_32_clock_residues':True,
            'checks':['compiled live floorDamage helper','floor equality and switch dispatch',
                      'request amount and all four call arguments','RNG CALL before clock gate',
                      'outer lookup, CALL and four prologue pushes','ordered outer and nested stack/index writes','P_Random return and stack','unchanged misc RNG']}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--cross-check',action='store_true')
    args=parser.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-floor-damage.json').read_text())
    profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text())
    sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec,allowed_objects=(1,3))
    arithmetic_spec=json.loads((ROOT/'tests/reference/original-arithmetic.json').read_text())
    raw['randomTableBytes']=arithmetic.verify_units(binary,profile,arithmetic_spec)['randomTableBytes']
    out=ROOT/'artifacts/original-floor-damage';out.mkdir(parents=True,exist_ok=True)
    source=out/'Extracted.lean';source.write_text(certificate(raw,profile['exe_sha256']))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalFloorCaller','level-probe'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout)
    report={'exe_sha256':profile['exe_sha256'],'units':spec['units'],'axioms':checked.stdout.splitlines(),
            'scope':'Joined ordinary-floor path from 0x333d0 through outer dispatch, CALL/prologue, floor contact and switch dispatch to '
                    'the damage-call boundary or skip, including actual RNG CALL/RET. Initial encoding/memory '
                    'and byte-separation premises only; no assumed intermediate state. Earlier player preparation, damage effects and full tic remain outside.',
            'cross_check':cross_check(raw,spec) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f'PASS: original damaging-floor decision; {len(NAMES)} audited declarations.')
    if args.cross_check:print('Independent original-byte/native comparisons:',report['cross_check']['cases'])

if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as error:
        print(error.stdout or '',file=sys.stderr);print(error.stderr or '',file=sys.stderr);raise
