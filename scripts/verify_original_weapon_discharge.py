#!/usr/bin/env python3
"""Bind discharge proofs to pinned DOS bytes and optionally execute those bytes.

Sound, actor setter, flash setter and autoaim remain real call boundaries. The
proved debit/flash interval begins after the actor setter returns.
"""
import argparse
import json
import random
import re
import struct
import subprocess

import verify_original_inline_thrust as extraction

ROOT, require = extraction.ROOT, extraction.require
NAMES = ['pistol_bytes', 'shotgun_bytes', 'pistol_dispatch', 'shotgun_dispatch',
         'weapon_table', 'machine_checked', 'live_checked']
PROOFS = ['decoded', 'sound_execution', 'pose_execution', 'debit_flash_execution',
          'aim_execution', 'related_address', 'related_flash', 'action_ammo',
          'call_arguments', 'memory_frame', 'live_tick']


def data_tables(binary, profile, spec):
    le = int(profile['le_offset'], 16)
    u32 = lambda p: struct.unpack_from('<I', binary, p)[0]
    require(struct.unpack_from('<6I', binary, le+u32(le+0x40)+48) ==
            (0x85e10, 0x70000, 0x2043, 71, 38, 0), 'unexpected data object')
    result = {}
    for name, row in spec['data'].items():
        start, size = int(row['offset'], 16), len(bytes.fromhex(row['hex']))
        raw = bytearray()
        for a in range(start, start+size):
            at = le+u32(le+0x48)+4*(70+a//4096)
            require(binary[at+3] == 0, 'unsupported data page encoding')
            physical = int.from_bytes(binary[at:at+3], 'big')
            require(physical > 0, 'unmapped data page')
            offset = int(profile['data_pages_offset'], 16)+(physical-1)*4096+a%4096
            require(offset < len(binary), 'truncated data page')
            raw.append(binary[offset])
        require(raw.hex() == row['hex'], name+': data bytes differ')
        relocs = extraction.fixups(binary, range(70+start//4096, 70+(start+size-1)//4096+1))
        actual = {(p-(70*4096+start), o, t) for p, o, t in relocs
                  if max(70*4096+start, p) < min(70*4096+start+size, p+4)}
        expected = {(r['offset'], r['object'], int(r['target'], 16)) for r in row['relocations']}
        require(actual == expected, name+': data relocation mismatch')
        for off, _, target in expected:
            require(struct.unpack_from('<I', raw, off)[0] == target, 'data relocation target mismatch')
        result[name] = bytes(raw)
    return result


def certificate(raw, data, digest):
    s = f'''-- DOOM.EXE SHA-256 {digest}. Loader correctness remains external.
import Doom.Proofs.OriginalWeaponDischarge
namespace Doom.Verification.ExtractedWeaponDischarge
open Doom Doom.Proofs X86 X86Memory X86Control
open OriginalWeaponDischarge
'''
    for name, b in raw.items():
        s += 'def '+name+' : List UInt8 := ['+','.join(hex(v) for v in b)+']\n'
        s += f'theorem {name}_bytes : {name} = {name}Bytes := by decide\n'
    for name, b in data.items():
        s += 'def '+name+'Data : List UInt8 := ['+','.join(hex(v) for v in b)+']\n'
    s += '''def wordAt (b : List UInt8) (n : Nat) : Word :=
  load32 (fun a => b.toArray[a.toNat]!.toBitVec) (BitVec.ofNat 32 n)
theorem pistol_dispatch : wordAt pistolData 12 = BitVec.ofNat 32 (entry .pistol) ∧
    wordAt pistolData 8 = (WeaponActions.duration .pistol).toBitVec := by decide
theorem shotgun_dispatch : wordAt shotgunData 12 = BitVec.ofNat 32 (entry .shotgun) ∧
    wordAt shotgunData 8 = (WeaponActions.duration .shotgun).toBitVec := by decide
theorem weapon_table (gun : Fire.Gun) :
    wordAt weaponsData (24*(weaponNumber gun).toNat) = BitVec.ofNat 32 gun.ammoIndex.val ∧
    wordAt weaponsData (24*(weaponNumber gun).toNat+20) = BitVec.ofNat 32 (WeaponActions.flashFrame gun) := by
  cases gun <;> decide
theorem machine_checked (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run (bytesProgram pistol shotgun) [0x2d040] 12 ⟨s,f,afterPose gun⟩ =
      some (flashCall gun s) := by
  rw [pistol_bytes,shotgun_bytes]; exact debit_flash_execution gun s f
theorem live_checked (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : Inputs gun s c)
    (frame : c.state.weapon.frame = WeaponActions.windup gun)
    (timer : c.state.weapon.tics = 1) :
    ∃ t, X86Routine.run (bytesProgram pistol shotgun) [0x2d040] 12 ⟨s,f,afterPose gun⟩ = some t ∧
      load32 t.core.memory (playerAmmo gun s) = (Weapon.tick c).player.ammo[gun.ammoIndex].toBitVec ∧
      t.core.regs 0 = s.regs 1 ∧ t.core.regs 2 = 1 ∧
      t.core.regs 3 = BitVec.ofNat 32 (Weapon.tick c).state.flash.frame ∧ t.pc = 0x2d040 := by
  rw [pistol_bytes,shotgun_bytes]; exact live_tick gun s f c h frame timer
'''
    s += '\n'.join('#print axioms '+n for n in NAMES)+'\n'
    s += '\n'.join('#print axioms Doom.Proofs.OriginalWeaponDischarge.'+n for n in PROOFS)+'\n'
    return s+'end Doom.Verification.ExtractedWeaponDischarge\n'


def audit(output):
    rest = output.strip()
    names = ['Doom.Verification.ExtractedWeaponDischarge.'+n for n in NAMES]
    names += ['Doom.Proofs.OriginalWeaponDischarge.'+n for n in PROOFS]
    for name in names:
        m = re.match(re.escape(f"'{name}'")+
                     r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(m is not None, 'missing audit: '+name)
        axioms = {a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axioms: '+str(axioms))
        rest = rest[m.end():].strip()
    require(not rest, 'unexpected certificate output')


def cross_check(raw, data, spec):
    import capstone
    import unicorn as u
    from unicorn import x86_const as x
    em = u.Uc(u.UC_ARCH_X86, u.UC_MODE_32)
    CODE, HEAP, MASK = 0x100000, 0x600000, 0xffffffff
    for base, size in [(CODE, 0x40000), (0, 0x14000), (HEAP, 4096), (0xfffff000, 4096)]:
        em.mem_map(base, size)
    for name, b in raw.items():
        em.mem_write(CODE+int(spec['units'][name]['code_offset'], 16), b)
    regs = [x.UC_X86_REG_EAX, x.UC_X86_REG_ECX, x.UC_X86_REG_EDX, x.UC_X86_REG_EBX,
            x.UC_X86_REG_ESP, x.UC_X86_REG_EBP, x.UC_X86_REG_ESI, x.UC_X86_REG_EDI]
    writes, visits, stops = [], [], set()
    em.hook_add(u.UC_HOOK_MEM_WRITE, lambda _e, _a, a, n, v, _d: writes.append((a, n, v & MASK)))
    def visit(e, a, _n, _d):
        if a in stops:
            e.emu_stop()
        else:
            visits.append(a-CODE)
    em.hook_add(u.UC_HOOK_CODE, visit)
    rng = random.Random(0x2d890)
    report = {}
    for gun, name in enumerate(['pistol', 'shotgun']):
        entry = int(spec['units'][name]['code_offset'], 16)
        listing = list(capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_32).disasm(raw[name], entry))
        require(b''.join(bytes(i.bytes) for i in listing) == raw[name], 'independent decoder left bytes')
        pcs = [0x2d890,0x2d8a0,0x2d8ac,0x2d8e5,0x2d8ec] if gun == 0 else [0x2d910,0x2d921,0x2d92d,0x2d966,0x2d96d]
        for segment in range(4):
            for i in range(512):
                pages = {a: bytearray(rng.randbytes(4096)) for a in [0,0x12000,0x13000,HEAP,0xfffff000]}
                def put(a, value):
                    for k, b in enumerate(struct.pack('<I', value & MASK)):
                        z = (a+k) & MASK
                        pages[z & ~4095][z & 4095] = b
                def get(a):
                    return int.from_bytes(bytes(pages[((a+k)&MASK)&~4095][((a+k)&MASK)&4095] for k in range(4)), 'little')
                for k,b in enumerate(data['weapons']):
                    a=0x12d90+k; pages[a & ~4095][a & 4095]=b
                p, obj = HEAP+64+i%4, HEAP+1024+(i//4)%4
                sp = [HEAP+3072+i%4,1,0xfffffffd][i%3]
                ammo = [0,1,0xffffffff,0x80000000,0x7fffffff,rng.getrandbits(32)][i%6]
                put(p,obj); put(p+112,gun+1); put(p+156+4*gun,ammo)
                for a,b in pages.items(): em.mem_write(a,bytes(b))
                rr=[rng.getrandbits(32) for _ in regs];rr[0]=p;rr[4]=sp
                if segment:rr[1]=p
                for r,v in zip(regs,rr): em.reg_write(r,v)
                em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5))
                expected=[]
                def store(a,v):
                    expected.append((a&MASK,4,v&MASK));put(a,v)
                def push(v):
                    rr[4]=(rr[4]-4)&MASK;store(rr[4],v)
                if segment==0:
                    push(rr[3]);push(rr[1])
                    if gun: push(rr[6])
                    rr[1]=rr[0];rr[2]=gun+1;rr[0]=get(rr[0]);push(CODE+pcs[1]);target=0x3f370;count=6+gun
                elif segment==1:
                    rr[2]=155;rr[0]=get(rr[1]);push(CODE+pcs[2]);target=0x30ea0;count=3
                elif segment==2:
                    w=get(rr[1]+112);kind=get(0x12d90+w*24);a=(rr[1]+kind*4+156)&MASK
                    store(a,get(a)-1);w=get(rr[1]+112)
                    rr[3]=get(0x12da4+w*24);rr[2]=1;rr[0]=rr[1];push(CODE+pcs[3]);target=0x2d040;count=12
                else:
                    rr[0]=get(rr[1]);push(CODE+pcs[4]);target=0x2d7c0;count=2
                writes.clear();visits.clear();stops={CODE+target}
                em.emu_start(CODE+pcs[segment],CODE+0x40000,count=20)
                require(em.reg_read(x.UC_X86_REG_EIP)==CODE+target, 'wrong call boundary')
                require(len(visits)==count, 'wrong instruction count')
                require([em.reg_read(r) for r in regs]==rr, 'wrong registers')
                require(writes==expected, 'wrong ordered writes')
                for a,b in pages.items():require(em.mem_read(a,4096)==b,'wrong memory')
            report[name+'_'+['sound','pose','debit_flash','aim'][segment]]={'cases':512,'instructions':count}
    return {'segments':report,'total_cases':4096,'all_registers_memory_and_write_order':True,
            'unaligned_player_and_wrapping_stack':True,'flags':'not compared: arithmetic flags are conservatively forgotten'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cross-check',action='store_true')
    args=parser.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-weapon-discharge.json').read_text())
    profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text())
    sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec)
    data=data_tables(binary,profile,spec)
    out=ROOT/'artifacts/original-weapon-discharge';out.mkdir(parents=True,exist_ok=True)
    source=out/'Extracted.lean';source.write_text(certificate(raw,data,profile['exe_sha256']))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalWeaponDischarge'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout);(out/'axioms.log').write_text(checked.stdout)
    report={'exe_sha256':profile['exe_sha256'],'units':spec['units'],'tables':spec['data'],
            'axioms':checked.stdout.splitlines(),'scope':'Original discharge call-site execution and live tick ammo/flash-request correspondence. Callees, loader, full callback/tic and audio samples remain unproved.',
            'cross_check':cross_check(raw,data,spec) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: pinned original discharge bytes, tables, kernel certificate and axiom audit.')
    if report['cross_check']:print('Independent x86 cases:',report['cross_check']['total_cases'])


if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as e:
        print(e.stdout or '');print(e.stderr or '');raise
