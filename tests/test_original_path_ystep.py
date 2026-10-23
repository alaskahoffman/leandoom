"""Y-axis division, second crossing and original firing-to-grid correspondence."""
import copy
import json
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_path_ystep as proof

HEADER='''import Doom.Proofs.E1M1PathGridSetup
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
'''

class PathYStepTests(unittest.TestCase):
    lean=runtime.WeaponRuntimeTests.lean
    succeeds=runtime.WeaponRuntimeTests.succeeds
    rejects=runtime.WeaponRuntimeTests.rejects

    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-path-ystep.json').read_text())
        self.raw={k:bytes.fromhex(v['hex']) for k,v in self.spec['units'].items()}
        self.source=proof.certificate(self.raw)

    def test_certificate_and_axioms(self):
        out=self.succeeds(self.source);proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('first_grid_correspondence','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_all_four_byte_ranges_and_execution_contract(self):
        for name,offset in [('ystep',1),('ystep',8),('ystep',30),('ystep',78),
                            ('abs',3),('division',26),('second',9),('second',24)]:
            raw={k:bytearray(v) for k,v in self.raw.items()};raw[name][offset]^=1
            with self.subTest(name=name,offset=offset):self.rejects(proof.certificate(raw))
        source=self.source.replace('namespace Doom.Verification.ExtractedPathYStep',
            'set_option backward.isDefEq.respectTransparency true\nnamespace Doom.Verification.ExtractedPathYStep')
        source=source.replace('theorem execution_checked','attribute [local irreducible] result\ntheorem execution_checked')
        self.succeeds(source)
        for old,new in [('n≤41','n≤40'),('⟨s,comparison s,0x2ca10⟩','⟨s,none,0x2ca10⟩'),
                        ('(safe : Safe s)','(safe : True)'),('[] 10','[] 9')]:self.rejects(source.replace(old,new))

    def test_live_success_and_encoding_required(self):
        source=HEADER+'''open OriginalPathYStep
attribute [local irreducible] result Collision.PathStart.yStep
example (s : X86Memory.State) (p : Collision.PathStart) (out : Int32 × Fixed × Fixed)
    (h : Inputs s p) (ok : p.yStep=.ok out) :
    Safe s ∧ observe s (result s)=liveObserve out := live s p out h ok
'''
        self.succeeds(source)
        for old,new in [('(h : Inputs s p)','(h : True)'),('(ok : p.yStep=.ok out)','(ok : True)'),
                        ('ok : p.yStep=.ok out','ok : p.xStep=.ok out')]:self.rejects(source.replace(old,new))

    def test_direction_saturation_and_second_crossing_fixtures(self):
        source=(ROOT/'tests/reference/original-path-ystep.lean').read_text();self.succeeds(source)
        for old,new in [('(1,⟨65280⟩,⟨32768⟩)','(1,⟨65281⟩,⟨32768⟩)'),
                        ('(-1,⟨256⟩,⟨32768⟩)','(1,⟨256⟩,⟨32768⟩)'),
                        ('else 32767)','else 32768)')]:
            self.assertIn(old,source);self.rejects(source.replace(old,new))

    def test_full_numeric_grid_setup_from_encoded_initialization(self):
        source=(ROOT/'tests/reference/e1m1-path-grid-setup.lean').read_text();self.succeeds(source)
        for old,new in [('(4294902780#32)','(4294902781#32)'),
                        ('(4294902274#32)','(4294902275#32)')]:
            self.assertIn(old,source);self.rejects(source.replace(old,new))

    def test_second_inputs_and_memory_frame_requirements(self):
        source=HEADER+'''open BlockSummary E1M1PathGridSetup
attribute [local irreducible] OriginalPathYStep.result after OriginalPathSecondIntercept.result
example (s : X86Memory.State) (p : Collision.PathStart) (portion stride : Fixed)
    (h : OriginalPathSecondIntercept.Inputs s p portion stride) :
    OriginalPathSecondIntercept.Ready s (OriginalPathSecondIntercept.result s) p portion stride :=
  OriginalPathSecondIntercept.live s p portion stride h
example (s : X86Memory.State) (off : Word) (h : off∈[12,16,20,24,32,40,44]) :
    load32 (after s).core.memory (s.regs 4+off)=load32 s.memory (s.regs 4+off) := after_local s off h
'''
        self.succeeds(source)
        self.rejects(source.replace('(h : OriginalPathSecondIntercept.Inputs s p portion stride)','(h : True)'))
        self.rejects(source.replace('off∈[12,16,20,24,32,40,44]','off∈[12,16,20,24,28,40,44]'))
        self.rejects(source.replace('off∈[12,16,20,24,32,40,44]','off∈[12,16,20,24,36,40,44]'))

    def test_joined_observation_requires_both_arithmetic_successes(self):
        source=HEADER+'''attribute [local irreducible] E1M1PathGridSetup.firstGrid Collision.PathStart.xStep Collision.PathStart.yStep
example (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c)
    (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok xout)
    (okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout) :
    ∃ n, n≤338 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PathGridSetup.program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (E1M1PathGridSetup.firstGrid gun s) ∧
    E1M1PathGridSetup.Ready ((E1M1PathXStep.firstXStep gun s).core.regs 4) (E1M1PathGridSetup.firstGrid gun s)
      (Collision.pathStart ox oy sx sy ex ey) xout yout :=
  E1M1PathGridSetup.first_grid_correspondence gun s f c h ox oy sx sy ex ey geometry xout yout okX okY
'''
        self.succeeds(source)
        for old,new in [('(geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)','(geometry : True)'),
                        ('(okX : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok xout)','(okX : True)'),
                        ('(okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout)','(okY : True)'),
                        ('n≤338','n≤337')]:self.rejects(source.replace(old,new))

    def test_actual_discharge_fixture(self):
        source=(ROOT/'tests/reference/e1m1-discharge-setters.lean').read_text().replace(
            'import Doom.Proofs.E1M1DischargeSetters','import Doom.Proofs.E1M1PathGridSetup')
        source+='''
open DischargeSettersFixture
example (i : Fin 4)
    (sx : OriginalPathXStep.Safe (E1M1PathInit.firstPath (gunOf i) (machine (gunOf i) (ammoOf i))).core)
    (sy : OriginalPathYStep.Safe (E1M1PathIntercept.firstIntercept (gunOf i) (machine (gunOf i) (ammoOf i))).core) :
    ∃ n, n≤338 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PathGridSetup.program [] n
      ⟨machine (gunOf i) (ammoOf i),none,OriginalWeaponDischarge.afterSound (gunOf i)⟩
      (E1M1PathGridSetup.firstGrid (gunOf i) (machine (gunOf i) (ammoOf i))) :=
  E1M1PathGridSetup.first_grid_execution _ _ _ _ (inputs i) sx sy
'''
        self.succeeds(source)
        self.rejects(source.replace('OriginalWeaponDischarge.afterSound (gunOf i)⟩','0x2ca10⟩'))

    def test_original_file_mapping_and_relocations(self):
        extraction=proof.extraction
        profile=json.loads((ROOT/'tests/reference'/self.spec['exe_profile']).read_text())
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
        self.assertEqual(extraction.extract(binary,profile,self.spec),self.raw)
        for name in self.spec['units']:
            bad=copy.deepcopy(self.spec);bad['units'][name]['file_offset']='0x0'
            with self.assertRaises(ValueError):extraction.extract(binary,profile,bad)
            bad=copy.deepcopy(self.spec);bad['units'][name]['relocations']=[{'offset':0,'object':3,'target':'0x0'}]
            with self.assertRaises(ValueError):extraction.extract(binary,profile,bad)

if __name__=='__main__':unittest.main()
