"""Pinned DOS discharge instructions joined to the real weapon tick."""
import copy
import json
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
import verify_original_weapon_discharge as proof


class WeaponDischargeTests(unittest.TestCase):
    lean = runtime.WeaponRuntimeTests.lean
    succeeds = runtime.WeaponRuntimeTests.succeeds
    rejects = runtime.WeaponRuntimeTests.rejects

    def setUp(self):
        self.spec = json.loads((ROOT/'tests/reference/original-weapon-discharge.json').read_text())
        self.raw = {k:bytes.fromhex(v['hex']) for k,v in self.spec['units'].items()}
        self.data = {k:bytes.fromhex(v['hex']) for k,v in self.spec['data'].items()}
        self.source = proof.certificate(self.raw,self.data,'test')

    def test_certificate_and_axioms(self):
        output = self.succeeds(self.source)
        proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'), output.replace('Quot.sound','bad._native.ax_1'),
                    output+'extra', output.replace('live_checked','missing')]:
            with self.assertRaises(ValueError): proof.audit(bad)

    def test_byte_table_and_dispatch_mutations(self):
        for name, offset in [('pistol',48),('shotgun',49),('pistol',12),('shotgun',84),
                             ('pistolData',12),('shotgunData',8),('weaponsData',44)]:
            with self.subTest(name=name,offset=offset):
                raw,data=self.raw.copy(),self.data.copy()
                dest = data if name.endswith('Data') else raw
                key = name.removesuffix('Data')
                b=bytearray(dest[key]);b[offset]^=1;dest[key]=bytes(b)
                self.rejects(proof.certificate(raw,data,'test'))

    def test_live_contract_premises_and_outputs(self):
        # Keep executable bodies opaque so these test public theorem signatures.
        source = self.source.replace('open OriginalWeaponDischarge', '''open OriginalWeaponDischarge
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Weapon.tick flashCall X86Routine.run''')
        self.succeeds(source)
        for old,new in [('(h : Inputs gun s c)','(h : True)'),
                        ('(timer : c.state.weapon.tics = 1)','(timer : True)'),
                        ('(frame : c.state.weapon.frame = WeaponActions.windup gun)','(frame : True)'),
                        ('12 ⟨s,f,afterPose gun⟩','11 ⟨s,f,afterPose gun⟩'),
                        ('t.core.regs 2 = 1','t.core.regs 2 = 0'),
                        ('(Weapon.tick c).player.ammo[gun.ammoIndex].toBitVec','c.player.ammo[gun.ammoIndex].toBitVec')]:
            with self.subTest(change=new):
                self.assertIn(old,source);self.rejects(source.replace(old,new))

    def test_nonvacuous_wrapping_fixture(self):
        source=(ROOT/'tests/reference/original-weapon-discharge.lean').read_text()
        self.succeeds(source)
        for old,new in [('= 0xffffffff','= 0xfffffffe'),('= 0x7fffffff','= 0x80000000'),
                        ('regs 3 = 30','regs 3 = 17'),('= 0x2d966','= 0x2d8e5')]:
            self.assertIn(old,source);self.rejects(source.replace(old,new))

    def test_memory_frame_requires_both_separations(self):
        source = '''import Doom.Proofs.OriginalWeaponDischarge
set_option backward.isDefEq.respectTransparency true
open Doom Doom.Proofs Doom.Verification X86 X86Memory
open OriginalWeaponDischarge BlockSummary
attribute [local irreducible] flashCall load32
example (gun : Fire.Gun) (s : X86Memory.State) (a : Word)
    (debitSafe : Apart a (ammoAddress s)) (stackSafe : Apart a (s.regs 4-4)) :
    load32 (flashCall gun s).core.memory a = load32 s.memory a :=
  memory_frame gun s a debitSafe stackSafe
'''
        self.succeeds(source)
        self.rejects(source.replace('(debitSafe : Apart a (ammoAddress s))', '(debitSafe : True)'))
        self.rejects(source.replace('(stackSafe : Apart a (s.regs 4-4))', '(stackSafe : True)'))

    def test_original_extraction_and_relocations(self):
        profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text())
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
        self.assertEqual(proof.extraction.extract(binary,profile,self.spec),self.raw)
        self.assertEqual(proof.data_tables(binary,profile,self.spec),self.data)
        for part,name,field,value in [('units','pistol','relocations',[]),
                                      ('data','shotgun','relocations',[]),
                                      ('data','weapons','offset','0x12d94')]:
            spec=copy.deepcopy(self.spec);spec[part][name][field]=value
            with self.assertRaises(ValueError):
                if part=='units':proof.extraction.extract(binary,profile,spec)
                else:proof.data_tables(binary,profile,spec)


if __name__ == '__main__':unittest.main()
