"""Object catalog guards derived from storage without dropping content or identity."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_helper_entry as prior
import verify_e1m1_aim_object_entry as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimObjectEntry\n'+proof.HEADER+'\nset_option maxRecDepth 32768\n'
class AimObjectEntryTests(unittest.TestCase):
    lean=prior.AimHelperEntryTests.lean
    succeeds=prior.AimHelperEntryTests.succeeds
    rejects=prior.AimHelperEntryTests.rejects
    mutations=prior.AimHelperEntryTests.mutations
    def contract(self,module,name):
        args=next(a for m,n,a in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',
                    output.replace('ExtractedAimObjectEntry.pinned_map_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_concrete_actor_entry_with_actual_zero_contents(self):
        self.succeeds(HEADER+'''
def objectState : X86Memory.State := ⟨fun _ => 972,fun _ => 0⟩
example (thing : SolidThing) : E1M1AimActorCatalog.Entry objectState 0x50000
    {thing with shootable := false,z := ⟨0⟩,height := ⟨0⟩} := by
  apply E1M1AimObjectCatalog.actor ⟨900,1112⟩ 1112 objectState 0x50000
  · exact ⟨by decide,by decide,by decide⟩
  · unfold E1M1AimWalkRegions.Reserve; decide
  · rfl
  · exact ⟨rfl,rfl,rfl⟩
''')
    def test_safe_storage_does_not_imply_matching_values(self):
        self.succeeds(HEADER+'''
example (thing : SolidThing) : ¬E1M1AimObjectCatalog.ActorValues (fun _ => 0) 0x50000
    {thing with shootable := true} := by
  intro h
  have wrong : false=true := h.flags
  contradiction
''')
        self.mutations(self.contract('E1M1AimObjectCatalog','actor'),[
          ('(values : Doom.Proofs.E1M1AimObjectCatalog.ActorValues s.memory pointer thing)','(values : True)')])
    def test_front_back_aliasing_and_unaligned_line_field(self):
        self.succeeds(HEADER+'''
def shared : E1M1AimCatalog.Portal := ⟨0x60000,0x60000,0,0,0,0⟩
example (s : X86Memory.State) (hit : Intercept) (position : s.regs 4=972)
    (values : E1M1AimObjectCatalog.PortalValues s.memory hit 0x50000 shared) :
    E1M1AimMapFrame.StableWord s (0x50000+50) := by
  have entry := E1M1AimObjectCatalog.portal ⟨900,1112⟩ 1112 s hit 0x50000 shared
    ⟨by decide,by decide,by decide⟩ ⟨by decide,by decide,by decide⟩
    ⟨by decide,by decide,by decide⟩ (by unfold E1M1AimWalkRegions.Reserve; decide) position values
  exact entry.2.1 _ (by simp [E1M1OpeningHeights.reads])
''')
    def test_prefix_width_and_wrapping_boundary(self):
        self.succeeds(HEADER+'''
example : E1M1AimObjectRegions.Storage ⟨900,1112⟩ 0xffffff94 108 :=
  ⟨by decide,by decide,by decide⟩
example : ¬E1M1AimObjectRegions.Storage ⟨900,1112⟩ 0xffffff95 108 := by
  intro h
  exact (by decide : ¬(0xffffff95#32).toNat+108≤2^32) h.bound
example : ¬E1M1AimObjectRegions.Storage ⟨900,1112⟩ 0x2c000 108 := by
  intro h
  exact (by decide : ¬(E1M1AimObjectRegions.region 0x2c000 108).Disjoint
    E1M1AimMapRegions.globalStores) h.globalsApart
''')
        self.mutations(self.contract('E1M1AimObjectCatalog','actor'),[
          ('(storage : Doom.Proofs.E1M1AimObjectRegions.Storage stack pointer 108)',
           '(storage : Doom.Proofs.E1M1AimObjectRegions.Storage stack pointer 107)')])
    def test_catalogs_keep_classification_and_shooter_identity(self):
        self.mutations(self.contract('E1M1AimObjectCatalog','actors'),[
          ('lookup hits[i]! = who ↔ hits[i]!.id=shooter','lookup hits[i]! = who → hits[i]!.id=shooter')])
        self.mutations(self.contract('E1M1AimObjectCatalog','walls'),[
          ('(values : ∀ i<hits.size, solid i → Doom.Proofs.E1M1AimObjectCatalog.WallValues s.memory hits[i]! (lookup hits[i]!))','(values : True)')])
    def test_actor_transport_keeps_actual_cycle_contracts(self):
        self.mutations(self.contract('E1M1AimObjectCatalog','actor_preserved'),[
          ('(frame : E1M1AimHistoryCycle.Frame s out)','(frame : True)'),
          ('(sameStack : out.core.regs 4=s.regs 4)','(sameStack : True)'),
          ('(bounded : marked<128)','(bounded : marked<129)')])
    def test_storage_and_stack_position_remain_explicit(self):
        self.mutations(self.contract('E1M1AimObjectCatalog','portal'),[
          ('(frontStorage : Doom.Proofs.E1M1AimObjectRegions.Storage stack p.front 8)','(frontStorage : True)'),
          ('(position : s.regs 4=sp-140)','(position : s.regs 4=sp-136)')])
    def test_residual_data_has_no_embedded_address_guards(self):
        s=(ROOT/'Doom/Proofs/E1M1AimObjectEntry.lean').read_text()
        fields=s.split('structure OtherInputs',1)[1].split('\n\n',1)[0]
        self.assertEqual(re.findall(r'^  (\w+) :',fields,re.M),['portals','shooterReg','actors','walls'])
        self.assertNotRegex(fields,r'\b(StableWord|Apart|Safe|Entry|Catalog|Layout)\b')
        self.assertIn('s.memory',fields)
        for typ in ['ActorValues','PortalValues','WallValues']:
            source=(ROOT/'Doom/Proofs/E1M1AimObjectCatalog.lean').read_text()
            part=source.split(typ+' ',1)[1].split('\n\n',1)[0]
            self.assertNotRegex(part,r'\b(StableWord|Apart|Safe|Storage|Layout)\b')
    def test_entry_joins_retain_contents_and_original_angle(self):
        self.mutations(self.contract('E1M1AimObjectEntry','other'),[
          ('(input : Doom.Proofs.E1M1AimObjectEntry.OtherInputs q s scene shooter hits portals walls who)','(input : True)'),
          ('(placement : E1M1AimCatalogRegions.Layout stack hits (Doom.Proofs.E1M1ThingFinish.resolve q.lines q.objects) portals)','(placement : True)')])
        self.mutations(self.contract('E1M1AimObjectEntry','controller'),[
          ('(value : load32 s.memory (s.regs 0+32)=angle.raw.toBitVec)','(value : True)')])
if __name__=='__main__':unittest.main()
