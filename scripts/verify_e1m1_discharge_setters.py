#!/usr/bin/env python3
"""Check the executed pose/debit/flash/light interval against pinned DOS bytes."""
import argparse
import json
import random
import re
import struct
import subprocess

import verify_original_weapon_discharge as previous

ROOT, require, extraction = previous.ROOT, previous.require, previous.extraction
NAMES = ['pistol_bytes', 'shotgun_bytes', 'actor_bytes', 'flash_bytes', 'light_bytes',
         'pose_bytes', 'actor_table', 'flash_tables', 'weapon_table', 'joined_checked']
PROOFS = ['E1M1FlashInstall.'+n for n in ['summary', 'execution', 'memory_frame', 'live_observations']]
PROOFS += ['E1M1DischargeSetters.'+n for n in ['pose_execution', 'transport', 'flash_inputs',
           'setters_execution', 'aim_execution', 'live_actor', 'live_ammo', 'live_flash', 'live_joined']]


def certificate(raw, data, spec):
    s = '''import Doom.Proofs.E1M1DischargeSetters
namespace Doom.Verification.ExtractedDischargeSetters
open Doom Doom.Proofs X86 X86Memory X86Control E1M1DischargeSetters
'''
    targets = {'pistol':'OriginalWeaponDischarge.pistolBytes',
               'shotgun':'OriginalWeaponDischarge.shotgunBytes',
               'actor':'Doom19.setMobjStateBytes', 'flash':'PspriteSetter.code', 'light':'PspriteLight.code 1'}
    for name, b in raw.items():
        s += 'def '+name+' : List UInt8 := ['+','.join(hex(v) for v in b)+']\n'
        s += f'theorem {name}_bytes : {name} = {targets[name]} := by decide\n'
    for name, b in data.items():
        s += 'def '+name+'Data : Array UInt8 := #['+','.join(hex(v) for v in b)+']\n'
    s += 'def tableMemory : Memory := fun a =>\n'
    for name, row in spec['data'].items():
        lo = int(row['offset'], 16)
        s += f'  if {lo} ≤ a.toNat ∧ a.toNat < {lo+len(data[name])} then {name}Data[a.toNat-{lo}]!.toBitVec else\n'
    s += '''  0
theorem pose_bytes : poseData.toList = poseBytes := by decide
theorem actor_table : DeathSetter.Table actorEntry tableMemory := by constructor <;> decide
theorem flash_tables (gun : Fire.Gun) : FlashTables gun tableMemory := by
  cases gun <;> constructor <;> decide
theorem weapon_table (gun : Fire.Gun) :
    load32 tableMemory (OriginalWeaponDischarge.tableOffset (OriginalWeaponDischarge.weaponNumber gun)+0x12d90) = BitVec.ofNat 32 gun.ammoIndex.val ∧
    load32 tableMemory (OriginalWeaponDischarge.tableOffset (OriginalWeaponDischarge.weaponNumber gun)+0x12da4) = BitVec.ofNat 32 (WeaponActions.flashFrame gun) := by
  cases gun <;> decide
theorem joined_checked (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : Inputs gun s c) :
    ∃ n, n≤116 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (flashed gun s) ∧
      Agrees gun s c (flashed gun s) := live_joined gun s f c h
'''
    s += '\n'.join('#print axioms '+n for n in NAMES)+'\n'
    s += '\n'.join('#print axioms Doom.Proofs.'+n for n in PROOFS)+'\n'
    return s+'end Doom.Verification.ExtractedDischargeSetters\n'


def audit(output):
    rest = output.strip()
    names = ['Doom.Verification.ExtractedDischargeSetters.'+n for n in NAMES]
    names += ['Doom.Proofs.'+n for n in PROOFS]
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
    for base, size in [(CODE, 0x40000), (0, 0x18000), (HEAP, 4096), (0xfffff000, 4096)]:
        em.mem_map(base, size)
    for name, b in raw.items():
        at = int(spec['units'][name]['code_offset'], 16)
        listing = list(capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_32).disasm(b, at))
        require(b''.join(bytes(i.bytes) for i in listing) == b, 'independent decoder left bytes')
        em.mem_write(CODE+at, b)
    regs = [x.UC_X86_REG_EAX, x.UC_X86_REG_ECX, x.UC_X86_REG_EDX, x.UC_X86_REG_EBX,
            x.UC_X86_REG_ESP, x.UC_X86_REG_EBP, x.UC_X86_REG_ESI, x.UC_X86_REG_EDI]
    writes, visits = [], []
    em.hook_add(u.UC_HOOK_MEM_WRITE, lambda _e, _a, a, n, v, _d: writes.append((a, n, v & MASK)))
    def visit(e, a, _n, _d):
        if a == CODE+0x2d7c0:
            e.emu_stop()
        else:
            visits.append(a-CODE)
    em.hook_add(u.UC_HOOK_CODE, visit)
    rng = random.Random(0x16b1c)
    report = {}
    for gun, name in enumerate(['pistol', 'shotgun']):
        for i in range(512):
            pages = {a: bytearray(rng.randbytes(4096)) for a in
                     [*range(0,0x18000,4096),HEAP,0xfffff000]}
            def put(a, value):
                for k, b in enumerate(struct.pack('<I', value & MASK)):
                    z = (a+k) & MASK
                    pages[z & ~4095][z & 4095] = b
            for key, bs in data.items():
                bs = bytearray(bs)
                for r in spec['data'][key]['relocations']:
                    require(r['object'] == 1, 'unexpected data relocation object')
                    struct.pack_into('<I', bs, r['offset'], CODE+int(r['target'],16))
                for k, b in enumerate(bs):
                    a = int(spec['data'][key]['offset'],16)+k
                    pages[a & ~4095][a & 4095] = b
            p, obj = HEAP+64+i%4, HEAP+1024+(i//4)%4
            sp = [HEAP+3072+i%4,1,0xfffffffd][i%3]
            ammo = [0,1,0xffffffff,0x80000000,0x7fffffff,8,rng.getrandbits(32)][i%7]
            put(p,obj); put(p+112,gun+1); put(p+156+4*gun,ammo)
            for a,b in pages.items(): em.mem_write(a,bytes(b))
            rr = [rng.getrandbits(32) for _ in regs]; rr[1]=p; rr[4]=sp
            for r,v in zip(regs,rr): em.reg_write(r,v)
            em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5))
            expected = []
            def store(a,v):
                expected.append((a&MASK,4,v&MASK)); put(a,v)
            poseRet,flashRet,aimRet = (0x2d8ac,0x2d8e5,0x2d8ec) if gun==0 else (0x2d92d,0x2d966,0x2d96d)
            ptr,tics = (0x15c04,7) if gun==0 else (0x15d70,4)
            store(sp-4,CODE+poseRet); store(sp-8,rr[3]); store(sp-12,rr[6])
            for off,v in [(100,0x16b1c),(96,6),(36,28),(40,0x8005)]: store(obj+off,v)
            store(p+156+4*gun,ammo-1)
            store(sp-4,CODE+flashRet); store(sp-8,p); store(sp-12,rr[6])
            store(p+260,ptr); store(p+264,tics); store(sp-16,CODE+0x2d095); store(p+232,1)
            store(sp-4,CODE+aimRet)
            rr[0]=obj; rr[2]=tics; rr[3]=p+260; rr[4]=(sp-4)&MASK
            writes.clear(); visits.clear()
            em.emu_start(CODE+(0x2d8a0 if gun==0 else 0x2d921),CODE+0x40000,count=119)
            require(em.reg_read(x.UC_X86_REG_EIP)==CODE+0x2d7c0, 'wrong autoaim boundary')
            require(len(visits)<=118, 'instruction bound exceeded')
            require(visits.count(0x30ea0)==1 and visits.count(0x2d040)==1 and visits.count(0x2db50)==1,
                    'did not execute all three actual callees')
            require([em.reg_read(r) for r in regs]==rr, 'wrong registers')
            require(writes==expected, 'wrong ordered writes')
            for a,b in pages.items(): require(em.mem_read(a,4096)==b, 'wrong memory')
        report[name] = {'cases':512,'instructions':len(visits),'writes':len(writes)}
    return {'guns':report,'total_cases':1024,'callees_stubbed':False,
            'all_registers_memory_and_write_order':True,'unaligned_player_actor_and_wrapping_stack':True,
            'flags':'not compared; formal arithmetic flags are conservatively forgotten'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cross-check',action='store_true')
    args = parser.parse_args()
    spec = json.loads((ROOT/'tests/reference/e1m1-discharge-setters.json').read_text())
    profile = json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text())
    sw = json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary = extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw = extraction.extract(binary,profile,spec)
    data = previous.data_tables(binary,profile,spec)
    out = ROOT/'artifacts/e1m1-discharge-setters'; out.mkdir(parents=True,exist_ok=True)
    source = out/'Extracted.lean'; source.write_text(certificate(raw,data,spec))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1DischargeSetters'],cwd=ROOT,check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout); (out/'axioms.log').write_text(checked.stdout)
    report = {'exe_sha256':profile['exe_sha256'],'units':spec['units'],'tables':spec['data'],
              'axioms':checked.stdout.splitlines(),
              'scope':'Post-sound through actor setter, debit, flash/light setters and return, with production action observations. Entry to autoaim also executed. Sound, autoaim body, pellets/damage, later countdown, loader and full tic remain outside this theorem.',
              'cross_check':cross_check(raw,data,spec) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: pinned bytes/tables and joined execution/production correspondence axiom audit.')
    if report['cross_check']: print('Independent complete-interval x86 cases:',report['cross_check']['total_cases'])


if __name__ == '__main__':
    try: main()
    except subprocess.CalledProcessError as e:
        print(e.stdout or ''); print(e.stderr or ''); raise
