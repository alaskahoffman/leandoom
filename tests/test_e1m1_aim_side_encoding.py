"""Original side writes supply byte-level aiming inputs, with explicit frames."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_encoded_portal as prior
import verify_e1m1_aim_side_encoding as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimSideEncoding\n'+proof.HEADER+'\nset_option backward.isDefEq.respectTransparency false\nset_option maxRecDepth 32768\n'
FIXTURE="""import Doom.Proofs.E1M1AimSideEncoding
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1NoiseAllocation (Region)
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
namespace InitialPortalFixture
 def stack : Region := ⟨0x80000,0x80010⟩
 def originalMem : Memory :=
  store32 (store32 (store32 (store32 (store32 (store32 (store32 (store32 (store32 (store32 (store32
    (fun _ => 0) 0x2c134 1) 0x2c138 0x90000) 0x2c118 0x50000)
    0x40000 0x10000) (0x40000+4) 4) (0x40000+10) 0x10000)
    (0x50000+14) 0x60000) (0x50000+32) 0x60056)
    (0x90000+8) 65536) (0x60000+4) 0x800000) (0x60056+4) 0x800000
 def before : Memory := store32 (store32 (store32 (store32 originalMem
   (0x50000+14) 0) (0x50000+32) 0) 0x2c148 0x60000) (0xa001e+28) 1
 def frontState : X86Memory.State := ⟨fun r => if r=2 then 0x50000 else if r=3 then 0xa0000 else if r=4 then 0xb0000 else 0,before⟩
 def backState : X86Memory.State := ⟨fun r => if r=2 then 0x50012 else if r=3 then 0xa001e else if r=4 then 0xb0000 else 0,
   (OriginalSideLoader.linked frontState).core.memory⟩
 def mem : Memory := (OriginalSideLoader.linked backState).core.memory
 example : load32 before (0x50000+14)=0 ∧ load32 before (0x50000+32)=0 := by decide
 theorem frontInput : E1M1AimSideEncoding.Input frontState 0 0 0x50000 0x60000 := by
   refine ⟨by decide,?_,by decide,?_,by decide⟩
   · unfold E1M1NoiseImage.Realizes; decide
   · unfold Apart; decide
 theorem backInput : E1M1AimSideEncoding.Input backState 1 1 0x50000 0x60000 := by
   refine ⟨by decide,?_,by decide,?_,by decide⟩
   · unfold E1M1NoiseImage.Realizes; decide
   · unfold Apart; decide
 theorem frontKept : E1M1AimSideEncoding.Kept
   (E1M1NoiseImage.word (0x50000+14) 0x60000) (OriginalSideLoader.linked frontState).core.memory mem := by
   exact E1M1AimSideEncoding.link_retains backState _ (by
     unfold OriginalSideLoader.linkPatch E1M1NoiseImage.word
     decide)
 def state : X86Memory.State := ⟨fun r => if r=1 then 0x40000 else if r=3 then 0x30000 else if r=4 then 0x80010 else 0,mem⟩
 def sides : Fin 1 → E1M1LineOutput.Sides := fun _ => ⟨0,1,0x60000,0x60056⟩
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

 def row : E1M1AimEncodedPortal.Row := ⟨geometry 0,4,0,1,0,1,0,0x800000,0,0x800000⟩
 def rows : Fin 1 → E1M1AimEncodedPortal.Row := fun _ => row
 def sectors (n : Nat) : Word := if n=0 then 0x60000 else 0x60056
 theorem encoded : E1M1AimEncodedPortal.Encoded 1 rows 0x40000 0x90000 0x50000 sectors mem := by
   refine ⟨?_,?_,?_,?_,?_⟩
   · unfold E1M1NoiseImage.Realizes; decide
   · intro i; have eq := Subsingleton.elim i (0 : Fin 1); subst i
     unfold E1M1NoiseImage.Realizes; decide
   · intro i; have eq := Subsingleton.elim i (0 : Fin 1); subst i
     unfold E1M1NoiseImage.Realizes; decide
   · intro i; have eq := Subsingleton.elim i (0 : Fin 1); subst i
     have h := (E1M1AimSideEncoding.row_encoding row 0x50000 0x60000 frontState backState none none mem
       frontInput (fun _ => backInput) frontKept (fun _ _ _ => rfl)).2.2
     have patchEq : E1M1AimEncodedPortal.sideBytes row 0x50000 (E1M1AimSideEncoding.sectorAddress 0x60000)=
       E1M1AimEncodedPortal.sideBytes row 0x50000 sectors := by decide
     rw [patchEq] at h
     exact h
   · intro i _; have eq := Subsingleton.elim i (0 : Fin 1); subst i
     unfold E1M1NoiseImage.Realizes; decide
 example (hit : Intercept) (kind : hit.isLine=true) :
    X86Routine.run E1M1LineIteration.program [0x2e3c1] 104 ⟨state,none,0x2e29a⟩=
      some (E1M1LineScan.states state none 1) ∧
    (E1M1LineScan.states state none 1).pc=0x2e3c1 ∧
    E1M1AimObjectCatalog.PortalValues (E1M1LineScan.states state none 1).core.memory hit 0x30000
      (E1M1AimEncodedPortal.portal row sectors) := by
  exact E1M1AimEncodedPortal.execution 1 rows sectors 0x40000 0x50000 0x90000 0x30000 0x80010
    stack state none 0 hit loop ready verticesSafe
    (by intro j; change E1M1LineSource.good ⟨0,1,0,0,65536,0⟩=true; decide)
    sidesSafe encoded (by intro j; change (0#16)≠65535; decide)
    ⟨by decide,by decide⟩ ⟨by decide,by decide,by decide⟩
    ⟨by decide,by decide,by decide⟩ reserve (by decide) kind (by intro j hj; omega) (by decide)
end InitialPortalFixture
"""
class AimSideEncodingTests(unittest.TestCase):
    lean=prior.AimEncodedPortalTests.lean
    succeeds=prior.AimEncodedPortalTests.succeeds
    rejects=prior.AimEncodedPortalTests.rejects
    mutations=prior.AimEncodedPortalTests.mutations
    def contract(self,name):
        module=proof.MODULE
        args=next(a for m,n,a in proof.CONTRACTS if n==name)
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_inherited_certificate_side_bytes_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();scan=proof.evidence.scan_data();side=proof.side_data()
        self.assertEqual(len(proof.combined_units(spec['units'],scan[1],side[1])),62)
        source=proof.certificate(data,raw,scan,side)
        output=self.succeeds(source);proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',
                    output.replace('ExtractedSideLoader.link_checked','missing'),
                    output.replace('ExtractedAimSideEncoding.back_input','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        self.assertEqual(proof.GROUPS[proof.MODULE],re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{proof.MODULE}.lean').read_text(),re.M))
        self.assertIn('0x6b,0xc0,0x56',source)
        self.rejects(source.replace('0x6b,0xc0,0x56','0x6b,0xc0,0x55'))
    def test_actual_two_side_emissions_feed_complete_line_loop(self):
        self.succeeds(FIXTURE)
    def test_word_representation_includes_wrapping_and_unaligned_addresses(self):
        self.succeeds(HEADER+"""
example (m : Memory) (a v : Word) : E1M1NoiseImage.Realizes (E1M1NoiseImage.word a v) (store32 m a v) := by
  exact E1M1AimSideEncoding.word_of_load _ _ _ (load_store m a v)
example (m : Memory) (v : Word) : E1M1NoiseImage.Realizes (E1M1NoiseImage.word 0xffffffff v) (store32 m 0xffffffff v) := by
  exact E1M1AimSideEncoding.word_of_load _ _ _ (load_store m 0xffffffff v)
""")
    def test_absent_back_requires_no_loader_entry(self):
        prefix=FIXTURE.split(' theorem encoded :')[0]
        self.succeeds(prefix+"""
def missing : E1M1AimEncodedPortal.Row := { row with backIndex:=65535,backSector:=999999 }
example : E1M1NoiseImage.Realizes
    (E1M1AimEncodedPortal.sideBytes missing 0x50000 (E1M1AimSideEncoding.sectorAddress 0x60000)) mem := by
  exact (E1M1AimSideEncoding.row_encoding missing 0x50000 0x60000 frontState backState none none mem
    frontInput (fun h => False.elim (h rfl)) frontKept (fun h => False.elim (h rfl))).2.2
end InitialPortalFixture
""")
    def test_shared_side_requires_no_disjointness_between_front_and_back(self):
        prefix=FIXTURE.split(' theorem encoded :')[0]
        self.succeeds(prefix+"""
def shared : E1M1AimEncodedPortal.Row := { row with backIndex:=0,backSector:=0 }
example : E1M1NoiseImage.Realizes
    (E1M1AimEncodedPortal.sideBytes shared 0x50000 (E1M1AimSideEncoding.sectorAddress 0x60000)) mem := by
  exact (E1M1AimSideEncoding.row_encoding shared 0x50000 0x60000 frontState frontState none none mem
    frontInput (fun _ => frontInput) frontKept (fun _ => frontKept)).2.2
end InitialPortalFixture
""")
    def test_stack_write_can_destroy_previously_emitted_pointer(self):
        prefix=FIXTURE.split(' theorem encoded :')[0]
        self.succeeds(prefix+"""
def overlap : X86Memory.State := { backState with regs:=fun r => if r=4 then 0x50000+14 else backState.regs r }
example : ¬ E1M1AimSideEncoding.Kept (E1M1NoiseImage.word (0x50000+14) 0x60000)
    overlap.memory (OriginalSideLoader.linked overlap).core.memory := by
  intro kept
  have h := kept (0x50000+14,0) (by decide)
  change (86#8)=0 at h
  contradiction
end InitialPortalFixture
""")
    def test_input_bounds_and_scratch_separation_are_required(self):
        source=HEADER+"""
example (s : X86Memory.State) (side : BitVec 16) (index : Nat) (sideBase sectorBase : Word)
    (record : s.regs 2=sideBase+side.signExtend 32*18)
    (source : E1M1NoiseImage.Realizes (E1M1NoiseImage.half (s.regs 3+28) (BitVec.ofNat 16 index)) s.memory)
    (sectors : load32 s.memory 0x2c148=sectorBase) (safe : Apart 0x2c148 (s.regs 4)) (valid : index<32768) :
    E1M1AimSideEncoding.Input s side index sideBase sectorBase := by
  exact ⟨record,source,sectors,safe,valid⟩
"""
        self.mutations(source,[('(valid : index<32768)','(valid : True)'),
          ('(safe : Apart 0x2c148 (s.regs 4))','(safe : True)'),
          ('(sectors : load32 s.memory 0x2c148=sectorBase)','(sectors : True)')])
    def test_frames_and_byte_value_premises_cannot_be_dropped(self):
        self.mutations(self.contract('preserved'),[
          ('(kept : Doom.Proofs.E1M1AimSideEncoding.Kept p before after)','(kept : True)'),
          ('(image : Doom.Proofs.E1M1NoiseImage.Realizes p before)','(image : True)')])
        self.mutations(self.contract('link_retains'),[
          ('(outside : ∀ x∈p, ∀ y∈OriginalSideLoader.linkPatch s, y.1≠x.1)','(outside : True)')])
    def test_initializer_join_replaces_only_side_image(self):
        self.succeeds(self.contract('initial_encoding'))
        self.succeeds(self.contract('row_source'))
        decl=proof.declaration(proof.MODULE,'initial_encoding')
        self.assertNotIn('(sides :',decl)
        for premise in ['frontInput','backInput','frontKept','backKept','rawImage','vertices','sectors','globals']:
            self.assertIn(premise,decl)
if __name__=='__main__':unittest.main()
