"""Boundaries, aliasing and remaining contracts of actor/opening region proofs."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_map_entry as prior
import verify_e1m1_aim_catalog_entry as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimCatalogEntry\n'+proof.HEADER+'''
set_option maxRecDepth 32768
'''
class AimCatalogEntryTests(unittest.TestCase):
    lean=prior.AimMapEntryTests.lean
    succeeds=prior.AimMapEntryTests.succeeds
    rejects=prior.AimMapEntryTests.rejects
    mutations=prior.AimMapEntryTests.mutations
    def contract(self,module,name):
        args=next(a for m,n,a in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',
                    output.replace('ExtractedAimCatalogEntry.pinned_map_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_actor_flag_transport_requires_full_word_prefix(self):
        self.succeeds(HEADER+'''
example : (E1M1AimObjectRegions.region 4097 108).Contains (4097+104) := by decide
example : ¬(E1M1AimObjectRegions.region 4097 107).Contains (4097+104) := by decide
example : (E1M1AimObjectRegions.region (4294967296-108) 108).Contains (4294967296-4) := by decide
example : ¬(E1M1AimObjectRegions.region (4294967296-107) 108).Contains (4294967296-4) := by decide
''')
    def test_unaligned_line_pointers_and_sector_boundary(self):
        self.succeeds(HEADER+'''
example : (E1M1AimObjectRegions.region 4096 62).Contains (4096+46) := by decide
example : (E1M1AimObjectRegions.region 4096 62).Contains (4096+50) := by decide
example : ¬(E1M1AimObjectRegions.region 4096 53).Contains (4096+50) := by decide
example : (E1M1AimObjectRegions.region 8192 8).Contains (8192+4) := by decide
example : ¬(E1M1AimObjectRegions.region 8192 7).Contains (8192+4) := by decide
''')
    def test_shared_front_and_back_sector_is_allowed(self):
        self.succeeds(HEADER+'''
example (stack : Region) (line sector : Word)
    (l : E1M1AimObjectRegions.Storage stack line 62)
    (h : E1M1AimObjectRegions.Storage stack sector 8) :
    ∀ a∈(line+16)::E1M1OpeningHeights.reads line sector sector,
      E1M1AimObjectRegions.Located stack a :=
  E1M1AimObjectRegions.opening stack line sector sector l h h
''')
    def test_opening_helper_stack_boundary(self):
        self.succeeds(HEADER+'''
def state (sp : Word) : X86Memory.State := ⟨fun _ => sp,fun _ => 0⟩
example : E1M1AimObjectRegions.OpeningReserve ⟨100,116⟩ (state 116) := by
  unfold E1M1AimObjectRegions.OpeningReserve; decide
example : ¬E1M1AimObjectRegions.OpeningReserve ⟨101,116⟩ (state 116) := by
  unfold E1M1AimObjectRegions.OpeningReserve; decide
example : ¬E1M1AimObjectRegions.OpeningReserve ⟨0,16⟩ (state 15) := by
  unfold E1M1AimObjectRegions.OpeningReserve; decide
example (stack : Region) : ¬E1M1AimObjectRegions.Storage stack 0x2c030 8 := by
  intro storage
  exact (by decide : ¬(E1M1AimObjectRegions.region 0x2c030 8).Disjoint
    E1M1AimMapRegions.globalStores) storage.globalsApart
''')
    def test_empty_catalog_requires_no_object_storage(self):
        self.succeeds(HEADER+'''
example (stack : Region) (lookup : Intercept → Word) :
    E1M1AimCatalogRegions.Layout stack #[] lookup (fun _ => none) := by
  constructor <;> simp
example (stack : Region) (lookup : Intercept → Word) :
    ∀ a∈E1M1AimRetryCatalog.reads #[] lookup (fun _ => none),
      E1M1AimObjectRegions.Located stack a := by
  simp [E1M1AimRetryCatalog.reads]
''')
    def test_initial_still_requires_placement_and_later_frames(self):
        self.mutations(self.contract('E1M1AimCatalogEntry','initial'),[
            ('(placement : E1M1AimCatalogRegions.Layout stack hits (Doom.Proofs.E1M1ThingFinish.resolve q.lines q.objects) portals)','(placement : True)'),
            ('E1M1FiringMapState.Safe q.sp q.lines a ∧ E1M1AimEntryFrame.SafeWord (q.sp-112) a','True'),
            ('(other : Doom.Proofs.E1M1AimCatalogEntry.OtherInputs q s scene shooter hits portals walls who)','(other : True)')])
    def test_other_inputs_preserve_exactly_the_remaining_fields(self):
        old=(ROOT/'Doom/Proofs/E1M1AimPreRayCatalog.lean').read_text().split(' : Prop where',1)[1].split('/--',1)[0]
        new=(ROOT/'Doom/Proofs/E1M1AimCatalogEntry.lean').read_text().split(' : Prop where',1)[1].split('/--',1)[0]
        def fields(text):
            return {m[1]:m[0].strip() for m in re.finditer(r'^  (\w+) :.*?(?=^  \w+ :|\Z)',text,re.M|re.S)}
        wanted=fields(old)
        for name in ['portalReads','actorReads','wallReads']:del wanted[name]
        self.assertEqual(fields(new),wanted)
    def test_helper_requires_storage_and_signed_extrema(self):
        self.mutations(self.contract('E1M1AimCatalogEntry','opening_heights'),[
            ('(frontStorage : E1M1AimObjectRegions.Storage stack front 8)','(frontStorage : True)'),
            ('(reserve : E1M1AimObjectRegions.OpeningReserve stack s)','(reserve : True)'),
            ('if bc.toInt≤fc.toInt then bc else fc','if bc.toNat≤fc.toNat then bc else fc'),
            ('(side : load16 s.memory (s.regs 0+24) ≠ 0xffff)','(side : True)')])
    def test_controller_keeps_angle_and_original_memory_contracts(self):
        self.mutations(self.contract('E1M1AimCatalogEntry','controller'),[
            ('(value : load32 s.memory (s.regs 0+32)=angle.raw.toBitVec)','(value : True)'),
            ('(room : stack.lo+124 ≤ (s.regs 4).toNat)','(room : stack.lo+123 ≤ (s.regs 4).toNat)'),
            ('(angleSafe : ∀ b∈OriginalBulletSlope.saveWrites s, Apart (s.regs 0+32) b)','(angleSafe : True)')])
    def test_reached_catalog_requires_geometry(self):
        self.mutations(self.contract('E1M1AimCatalogEntry','remaining'),[
            ('(geometry : E1M1AimGeometry.Inputs s thing angle distance\n      (Fixed.ofInt q.world.grid.origin.x) (Fixed.ofInt q.world.grid.origin.y))','(geometry : True)')])
if __name__=='__main__':unittest.main()
