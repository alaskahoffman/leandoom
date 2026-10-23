"""Initial portal joins and their retained assumptions."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_loaded_scan as prior
import verify_e1m1_aim_initial_portal as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER="import Doom.Proofs.E1M1AimInitialPortal\n"+proof.HEADER+"\nset_option maxRecDepth 32768\n"
FIXTURE="""import Doom.Proofs.E1M1AimInitialPortal
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1NoiseAllocation (Region)
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
namespace InitialPortalFixture
 def stack : Region := ⟨0x80000,0x80010⟩
 def mem : Memory :=
  store32 (store32 (store32 (store32 (store32 (store32 (store32 (store32 (store32 (store32 (store32
    (fun _ => 0) 0x2c134 1) 0x2c138 0x90000) 0x2c118 0x50000)
    0x40000 0x10000) (0x40000+4) 4) (0x40000+10) 0x10000)
    (0x50000+14) 0x60000) (0x50000+32) 0x70000)
    (0x90000+8) 65536) (0x60000+4) 0x800000) (0x70000+4) 0x800000
 def state : X86Memory.State := ⟨fun r => if r=1 then 0x40000 else if r=3 then 0x30000 else if r=4 then 0x80010 else 0,mem⟩
 def sides : Fin 1 → E1M1LineOutput.Sides := fun _ => ⟨0,1,0x60000,0x70000⟩
 def geometry : Fin 1 → E1M1LineSource.Record := fun _ => ⟨0,1,0,0,65536,0⟩
 theorem reserve : E1M1AimLoadedScanRegions.Reserve stack 0x80010 := by unfold E1M1AimLoadedScanRegions.Reserve; decide
 theorem protect (a : Word) (bound : a.toNat+4≤2^32)
    (line : (E1M1AimObjectRegions.region a 4).Disjoint (E1M1AimObjectRegions.region 0x30000 62))
    (saved : (E1M1AimObjectRegions.region a 4).Disjoint stack) :
    E1M1LineFrame.Protected a 0x30000 0x80010 := by
  exact E1M1AimLoadedScanRegions.protected_read (E1M1AimObjectRegions.region a 4) stack a 0x30000 0x80010
    (by simpa only [E1M1AimObjectRegions.region,BitVec.add_zero] using E1M1AimRegions.field a 4 0 bound (by decide)) (by decide) line saved reserve
 theorem loop : E1M1LineScan.Layout 1 0x30000 0x80010 := by
  refine ⟨by decide,?_⟩
  intro i hi
  have zero : i=0 := by omega
  subst i
  exact protect _ (by decide) (by decide) (by decide)
 theorem ready : E1M1LineScan.Ready 1 0x40000 0x30000 0x80010 0 state :=
  ⟨by decide,by decide,by decide,by decide,by decide⟩
 theorem sidesImage : E1M1LineOutput.Image sides 0x40000 0x50000 mem := by
  intro i; have eq := Subsingleton.elim i (0 : Fin 1); subst i
  exact ⟨by decide,by decide,by decide,by decide,by decide⟩
 theorem sidesSafe : E1M1LineOutput.ImageLayout sides 0x40000 0x50000 0x30000 0x80010 := by
  intro i j a ha
  have iz := Subsingleton.elim i (0 : Fin 1); have jz := Subsingleton.elim j (0 : Fin 1); subst i; subst j
  simp [E1M1LineOutput.reads,E1M1LineOutput.sideReads,sides,E1M1LineScan.cursor] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl <;> exact protect _ (by decide) (by decide) (by decide)
 theorem vertices : E1M1LineSource.Image geometry 0x40000 0x90000 mem := by
  intro i; have eq := Subsingleton.elim i (0 : Fin 1); subst i
  exact ⟨by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
 theorem verticesSafe : E1M1LineSource.ImageLayout geometry 0x40000 0x90000 0x30000 0x80010 := by
  intro i j a ha
  have iz := Subsingleton.elim i (0 : Fin 1); have jz := Subsingleton.elim j (0 : Fin 1); subst i; subst j
  simp [E1M1LineSource.reads,geometry,E1M1LineScan.cursor] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact protect _ (by decide) (by decide) (by decide)
 example (hit : Intercept) (kind : hit.isLine=true) :
    X86Routine.run E1M1LineIteration.program [0x2e3c1] 104 ⟨state,none,0x2e29a⟩=
      some (E1M1LineScan.states state none 1) ∧
    (E1M1LineScan.states state none 1).pc=0x2e3c1 ∧
    E1M1AimObjectCatalog.PortalValues (E1M1LineScan.states state none 1).core.memory hit 0x30000
      (E1M1AimInitialPortal.portal (sides 0) 0 0x800000 0 0x800000) := by
  exact E1M1AimInitialPortal.execution_from_image 1 sides geometry 0x40000 0x50000 0x90000 0x30000 0x80010
    stack state none 0 hit 0 0x800000 0 0x800000 loop ready verticesSafe vertices (by intro i; simp [geometry,E1M1LineSource.good])
    sidesSafe sidesImage ⟨by decide,by decide⟩ ⟨by decide,by decide,by decide⟩
    ⟨by decide,by decide,by decide⟩ reserve (by decide)
    (by unfold E1M1AimLoadedPortal.SectorValues; decide) kind (by decide)
 example : load32 mem (0x30000+46)=0 ∧ load16 mem (0x30000+24)=0 ∧ mem (0x30000+16)=0 := by decide
end InitialPortalFixture
"""
class AimInitialPortalTests(unittest.TestCase):
    lean=prior.AimLoadedScanTests.lean
    succeeds=prior.AimLoadedScanTests.succeeds
    rejects=prior.AimLoadedScanTests.rejects
    mutations=prior.AimLoadedScanTests.mutations
    def contract(self,name):
        module='E1M1AimInitialPortal'
        args=next(a for m,n,a in proof.CONTRACTS if n==name)
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_inherited_certificate_and_reused_proofs_strictly_audited(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();scan=proof.previous.scan_data()
        self.assertEqual(len(proof.previous.combined_units(spec['units'],scan[1])),60)
        output=self.succeeds(proof.certificate(data,raw,scan));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',
                    output.replace('ExtractedAimInitialPortal.E1M1AimInitialPortal.source_at_copy_checked','missing'),
                    output.replace("'Doom.Proofs.E1M1LineSource.arithmetic_of_image'", "'missing'")]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_initial_uncached_image_establishes_actual_scan_portal(self):
        self.succeeds(FIXTURE)
    def test_side_image_and_static_separation_are_required(self):
        self.mutations(self.contract('source_at_copy'),[
          ('(image : E1M1LineOutput.Image records raw sideBase s.memory)','(image : True)'),
          ('(separate : E1M1LineOutput.ImageLayout records raw sideBase base sp)','(separate : True)')])
    def test_sector_values_and_storage_are_required(self):
        self.mutations(self.contract('sectors_at_copy'),[
          ('(initial : E1M1AimLoadedPortal.SectorValues s.memory p)','(initial : True)'),
          ('(front : E1M1AimLoadedScanRegions.Sector total base p.front stack)','(front : True)')])
    def test_presence_classification_and_reached_flag_remain_explicit(self):
        self.mutations(self.contract('established'),[
          ('(present : (records i).backIndex≠0xffff)','(present : True)'),
          ('(kind : hit.isLine=true)','(kind : True)'),
          ('(two : (E1M1LineOutput.copyInput (Doom.Proofs.E1M1LineScan.states s f i.val).core).memory (Doom.Proofs.E1M1LineScan.cursor base 62 i.val+16) &&& (4#8)≠0)','(two : True)')])
    def test_arithmetic_comes_from_real_initial_geometry_and_safety(self):
        self.mutations(self.contract('execution_from_image'),[
          ('(vertices : E1M1LineSource.Image geometry raw vertexBase s.memory)','(vertices : True)'),
          ('(good : ∀ j, E1M1LineSource.good (geometry j)=true)','(good : True)'),
          ('(verticesSafe : E1M1LineSource.ImageLayout geometry raw vertexBase base sp)','(verticesSafe : True)')])
    def test_initial_loop_representation_still_required(self):
        self.mutations(self.contract('execution_from_image'),[
          ('(ready : E1M1LineScan.Ready total raw base sp 0 s)','(ready : True)')])
    def test_absent_back_side_identity_is_preserved_without_becoming_portal(self):
        decl=proof.declaration('E1M1AimInitialPortal','source_at_copy').replace('theorem source_at_copy','example',1)
        decl=decl.replace('(image : E1M1LineOutput.Image records raw sideBase s.memory)',
          '(image : E1M1LineOutput.Image records raw sideBase s.memory) (absent : (records i).backIndex=0xffff)')
        decl=decl.replace('source.backIndex=(records i).backIndex','source.backIndex=0xffff')
        self.succeeds(HEADER+decl+''' := by
  obtain ⟨source,index⟩ := E1M1AimInitialPortal.source_at_copy total records raw sideBase base sp s f i loop ready separate image
  exact ⟨source,index.trans absent⟩
''')
    def test_no_reached_side_height_or_arithmetic_hypothesis_reintroduced(self):
        decl=proof.declaration('E1M1AimInitialPortal','execution_from_image')
        self.assertNotIn('E1M1LineScan.Arithmetic',decl)
        self.assertNotIn('E1M1LineLoad.Source',decl)
        self.assertIn('SectorValues s.memory',decl)
        self.assertEqual(decl.count('E1M1LineOutput.copyInput'),1)
        self.assertIn('(two : (E1M1LineOutput.copyInput',decl)
if __name__=='__main__':unittest.main()
