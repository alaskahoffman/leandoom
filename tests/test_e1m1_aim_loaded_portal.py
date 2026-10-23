"""Loader-established portal image, sentinel/alias boundaries and byte authentication."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_object_entry as prior
import verify_e1m1_aim_loaded_portal as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimLoadedPortal\n'+proof.HEADER+'\nset_option maxRecDepth 32768\n'
FIXTURE='''
open E1M1AimLoadedPortal
-- Raw sides 0/1, side-table pointers and preexisting sector values.
-- Cached line pointers and back index initially remain zero.
def mem : Memory :=
  store32 (store32 (store32 (store32 (store32 (store32 (store32 (fun _ => 0)
    0x2c118 0x50000) (0x40000+10) 0x10000)
    (0x50000+14) 0x60000) (0x50000+32) 0x70000)
    (0x30000+16) 4) (0x60000+4) 0x800000) (0x70000+4) 0x800000
 def state : X86Memory.State := ⟨fun r => if r=1 then 0x40000 else if r=3 then 0x30000 else 0,mem⟩
def p : Portal := ⟨0x60000,0x70000,0,0x800000,0,0x800000⟩
def source : E1M1LineLoad.Source (line 0x30000 p) state := by
  refine ⟨0,1,0x50000,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rfl
  · decide
  · decide
  · decide
  · unfold HalfMemory.Separate; decide
  · decide
  · decide
  · constructor <;> unfold HalfMemory.Separate <;> decide
  · intro _; constructor <;> unfold HalfMemory.Separate <;> decide
  · intro _; constructor <;> unfold HalfMemory.Separate <;> decide
  · unfold Apart; decide
  · intro _; unfold Apart; decide
theorem sectorSafe : SectorSafe 0x30000 p := by
  intro a ha
  simp only [sectorReads,p,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl
  all_goals refine ⟨⟨?_,?_⟩,?_,?_⟩
  all_goals first | (unfold HalfMemory.Separate; decide) | (unfold Apart; decide)
'''
class AimLoadedPortalTests(unittest.TestCase):
    lean=prior.AimObjectEntryTests.lean
    succeeds=prior.AimObjectEntryTests.succeeds
    rejects=prior.AimObjectEntryTests.rejects
    mutations=prior.AimObjectEntryTests.mutations
    def contract(self,name):
        module='E1M1AimLoadedPortal'
        args=next(a for m,n,a in proof.CONTRACTS if n==name)
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,profile,raw=proof.extracted();loader_raw,units,digest=proof.loader_data()
        self.assertEqual(len(spec['units']),51);self.assertEqual(len(units),3);self.assertEqual(digest,profile['exe_sha256'])
        output=self.succeeds(proof.certificate(data,raw,loader_raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',
                    output.replace('ExtractedLineLoad.copy_checked','missing'),
                    output.replace('ExtractedAimLoadedPortal.pinned_map_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_changed_loader_bytes_are_rejected(self):
        raw,_,_=proof.loader_data()
        for name in ['copy','cache','advance']:
            bad={k:bytes(v) for k,v in raw.items()};bad[name]=bytes([bad[name][0]^1])+bad[name][1:]
            self.rejects(proof.loader.certificate(bad))
    def test_raw_source_establishes_previously_missing_portal_fields(self):
        self.succeeds(HEADER+FIXTURE+'''
example : load16 state.memory (0x30000+24)=0 ∧ load32 state.memory (0x30000+46)=0 := by decide
example (hit : Intercept) (kind : hit.isLine=true) :
    E1M1AimObjectCatalog.PortalValues (OriginalLineLoad.result state).core.memory hit 0x30000 p := by
  exact values 0x30000 p state hit source (by decide) sectorSafe
    (by unfold SectorValues; decide) kind (by decide)
example : load16 (OriginalLineLoad.result state).core.memory (0x30000+24)=1 := by
  exact back_index _ state source
''')
    def test_sentinel_back_side_is_not_a_portal(self):
        self.succeeds(HEADER+'''
example (address : Word) (p : E1M1AimCatalog.Portal) (s : X86Memory.State)
    (source : E1M1LineLoad.Source (E1M1AimLoadedPortal.line address p) s)
    (absent : source.backIndex=0xffff) (hit : Intercept) :
    ¬E1M1AimObjectCatalog.PortalValues (OriginalLineLoad.result s).core.memory hit address p := by
  intro value
  have side : load16 (OriginalLineLoad.result s).core.memory (address+24)=0xffff :=
    (E1M1AimLoadedPortal.back_index _ s source).trans absent
  exact value.2.1.side side
''')
    def test_flags_frame_supports_wrapping_line_base(self):
        self.succeeds(HEADER+'''
example (m : Memory) :
    (OriginalLineLoad.result ⟨fun _ => 0xfffffff0,m⟩).core.memory 0=m 0 := by
  simpa using E1M1AimLoadedPortal.flags ⟨fun _ => 0xfffffff0,m⟩
''')
    def test_shared_sectors_and_overlap_rejection(self):
        self.succeeds(HEADER+'''
def same : E1M1AimCatalog.Portal := ⟨0x60000,0x60000,0,0,0,0⟩
example : E1M1AimLoadedPortal.SectorSafe 0x30000 same := by
  intro a ha
  simp only [E1M1AimLoadedPortal.sectorReads,same,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl
  all_goals refine ⟨⟨?_,?_⟩,?_,?_⟩
  all_goals first | (unfold HalfMemory.Separate; decide) | (unfold Apart; decide)
example (address : Word) (p : E1M1AimCatalog.Portal) (overlap : p.front=address+46) :
    ¬E1M1AimLoadedPortal.SectorSafe address p := by
  intro h
  have hit := (h p.front (by simp [E1M1AimLoadedPortal.sectorReads])).2.1
  rw [overlap] at hit
  exact hit 0 0 rfl
''')
    def test_loader_source_and_sector_contents_are_not_inferred(self):
        self.mutations(self.contract('pointers'),[
          ('(source : E1M1LineLoad.Source e s)','(source : True)')])
        self.mutations(self.contract('image'),[
          ('(values : Doom.Proofs.E1M1AimLoadedPortal.SectorValues s.memory p)','(values : True)'),
          ('(present : source.backIndex≠0xffff)','(present : True)')])
    def test_portal_classification_and_flag_are_required(self):
        self.mutations(self.contract('values'),[
          ('(kind : hit.isLine=true)','(kind : True)'),
          ('(two : s.memory (address+16) &&& (4#8)≠0)','(two : True)')])
    def test_transport_keeps_exact_read_frame(self):
        self.mutations(self.contract('transport'),[
          ('(frame : ∀ a∈Doom.Proofs.E1M1AimLoadedPortal.reads address p, load32 after a=load32 before a)','(frame : True)')])
        self.succeeds(HEADER+'''
example (address : Word) (p : E1M1AimCatalog.Portal) :
    (E1M1AimLoadedPortal.reads address p).length=8 := rfl
''')
    def test_catalog_requires_intervening_frame_and_storage(self):
        self.mutations(self.contract('catalog'),[
          ('(frame : ∀ a∈Doom.Proofs.E1M1AimLoadedPortal.reads address p, load32 aim.memory a=load32 (OriginalLineLoad.result s).core.memory a)','(frame : True)'),
          ('(frontStorage : E1M1AimObjectRegions.Storage stack p.front 8)','(frontStorage : True)')])
if __name__=='__main__':unittest.main()
