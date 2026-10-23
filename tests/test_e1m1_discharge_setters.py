"""Executed original setters, preserved inputs, and live firing-action outputs."""
import copy
import json
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
import verify_e1m1_discharge_setters as proof


class DischargeSettersTests(unittest.TestCase):
    lean = runtime.WeaponRuntimeTests.lean
    succeeds = runtime.WeaponRuntimeTests.succeeds
    rejects = runtime.WeaponRuntimeTests.rejects

    def setUp(self):
        self.spec = json.loads((ROOT/'tests/reference/e1m1-discharge-setters.json').read_text())
        self.raw = {k:bytes.fromhex(v['hex']) for k,v in self.spec['units'].items()}
        self.data = {k:bytes.fromhex(v['hex']) for k,v in self.spec['data'].items()}
        self.source = proof.certificate(self.raw,self.data,self.spec)

    def test_certificate_and_axioms(self):
        output = self.succeeds(self.source)
        proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output.replace('Quot.sound','native.ax'),
                    output+'extra',output.replace('live_joined','missing')]:
            with self.assertRaises(ValueError): proof.audit(bad)

    def test_bytes_and_tables_mutations(self):
        for part,name,offset in [('code','actor',0),('code','flash',0),('code','light',6),
                                 ('data','pose',8),('data','pistolflash',8),
                                 ('data','shotgunflash1',12),('data','shotgunflash1',16)]:
            with self.subTest(name=name,offset=offset):
                raw,data = self.raw.copy(),self.data.copy()
                dest = raw if part=='code' else data
                b=bytearray(dest[name]); b[offset]^=1; dest[name]=bytes(b)
                self.rejects(proof.certificate(raw,data,self.spec))

    def test_joined_contract_and_bounds(self):
        source = self.source.replace('namespace Doom.Verification.ExtractedDischargeSetters', '''
set_option backward.isDefEq.respectTransparency true
namespace Doom.Verification.ExtractedDischargeSetters''')
        source = source.replace('theorem joined_checked', '''attribute [local irreducible]
  E1M1DischargeSetters.flashed E1M1DischargeSetters.Agrees
theorem joined_checked''')
        self.succeeds(source)
        for old,new in [('(h : Inputs gun s c)','(h : True)'),('n≤116','n≤115'),
                        ('⟨s,f,OriginalWeaponDischarge.afterSound gun⟩','⟨s,f,OriginalWeaponDischarge.afterPose gun⟩'),
                        ('Agrees gun s c (flashed gun s)','Agrees gun s c ⟨s,f,0⟩')]:
            self.assertIn(old,source); self.rejects(source.replace(old,new))

    def test_preservation_premises(self):
        source = '''import Doom.Proofs.E1M1DischargeSetters
set_option backward.isDefEq.respectTransparency true
open Doom Doom.Proofs Doom.Verification X86 X86Memory BlockSummary E1M1DischargeSetters
attribute [local irreducible] posed
example (gun : Fire.Gun) (s : X86Memory.State) (c : Weapon.Context)
    (h : OriginalWeaponDischarge.Inputs gun s c)
    (safe : ∀ a, a ∈ debitReads gun s → ∀ b, b ∈ poseWrites gun s → Apart a b) :
    OriginalWeaponDischarge.Inputs gun (posed gun s).core c := transport gun s c h safe
'''
        self.succeeds(source)
        self.rejects(source.replace('(h : OriginalWeaponDischarge.Inputs gun s c)','(h : True)'))
        self.rejects(source.replace('(safe : ∀ a, a ∈ debitReads gun s → ∀ b, b ∈ poseWrites gun s → Apart a b)', '(safe : True)'))

    def test_nonvacuous_joined_fixture(self):
        source = (ROOT/'tests/reference/e1m1-discharge-setters.lean').read_text()
        self.succeeds(source)
        # Wrong post-install duration (using the later same-tic countdown),
        # wrong ammo, or wrong callback return must not certify.
        for old,new in [('=0xffffffff','=0xfffffffe'),('(p+264)=7','(p+264)=6'),
                        ('=0x2d966','=0x2d8e5')]:
            self.assertIn(old,source); self.rejects(source.replace(old,new))

    def test_extraction_and_relocations(self):
        profile = json.loads((ROOT/'tests/reference/original-mul.json').read_text())
        sw = json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary = proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
        self.assertEqual(proof.extraction.extract(binary,profile,self.spec),self.raw)
        self.assertEqual(proof.previous.data_tables(binary,profile,self.spec),self.data)
        for part,name,field,value in [('units','actor','relocations',[]),('units','flash','relocations',[]),
                                      ('data','pistolflash','relocations',[]),('data','pose','offset','0x16b20')]:
            spec=copy.deepcopy(self.spec); spec[part][name][field]=value
            with self.assertRaises(ValueError):
                if part=='units': proof.extraction.extract(binary,profile,spec)
                else: proof.previous.data_tables(binary,profile,spec)


if __name__ == '__main__': unittest.main()
