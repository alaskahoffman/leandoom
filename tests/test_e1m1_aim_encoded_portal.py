"""Pinned map byte encoding and initial portal execution boundary."""
import copy,re,unittest
from unittest import mock
from pathlib import Path
import test_e1m1_aim_raw_portal as prior
import verify_e1m1_aim_encoded_portal as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER="import Doom.Proofs.E1M1AimEncodedPortal\n"+proof.HEADER+"\nset_option maxRecDepth 32768\n"
FIXTURE="""import Doom.Proofs.E1M1AimEncodedPortal
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

 def row : E1M1AimEncodedPortal.Row := ⟨geometry 0,4,0,1,0,1,0,0x800000,0,0x800000⟩
 def rows : Fin 1 → E1M1AimEncodedPortal.Row := fun _ => row
 def sectors (n : Nat) : Word := if n=0 then 0x60000 else 0x70000
 theorem encoded : E1M1AimEncodedPortal.Encoded 1 rows 0x40000 0x90000 0x50000 sectors mem := by
  constructor
  · unfold E1M1NoiseImage.Realizes; decide
  · intro i; have eq := Subsingleton.elim i (0 : Fin 1); subst i
    unfold E1M1NoiseImage.Realizes; decide
  · intro i; have eq := Subsingleton.elim i (0 : Fin 1); subst i
    unfold E1M1NoiseImage.Realizes; decide
  · intro i; have eq := Subsingleton.elim i (0 : Fin 1); subst i
    unfold E1M1NoiseImage.Realizes; decide
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
class AimEncodedPortalTests(unittest.TestCase):
    lean=prior.AimRawPortalTests.lean
    succeeds=prior.AimRawPortalTests.succeeds
    rejects=prior.AimRawPortalTests.rejects
    mutations=prior.AimRawPortalTests.mutations
    def contract(self,name):
        module='E1M1AimEncodedPortal'
        args=next(a for m,n,a in proof.CONTRACTS if n==name)
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_full_certificate_and_pinned_map_audit(self):
        data,_=proof.pinned_data();_,_,raw=proof.extracted();scan=proof.evidence.scan_data()
        rows,meta=proof.pinned_rows(scan);self.assertEqual(len(rows),475);self.assertEqual(meta['sectors'],85)
        output=self.succeeds(proof.certificate(data,raw,scan));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',
                    output.replace('ExtractedAimEncodedPortal.pinned_execution','missing'),
                    output.replace('ExtractedAimEncodedPortal.geometry_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_concrete_byte_encoding_supplies_full_loader_execution(self):
        self.succeeds(FIXTURE)
    def test_corrupt_wad_or_record_provenance_is_rejected(self):
        scan=proof.evidence.scan_data();bad=list(scan);bad[2]=copy.deepcopy(scan[2]);bad[2]['lines'][0][2]^=1
        with self.assertRaises(ValueError):proof.pinned_rows(bad)
        original=Path.read_bytes
        def altered(path):
            data=original(path)
            return bytes([data[0]^1])+data[1:] if path.name=='doom1.wad' else data
        with mock.patch.object(Path,'read_bytes',altered):
            with self.assertRaises(ValueError):proof.pinned_rows(scan)
    def test_changed_geometry_fails_existing_authenticated_delta_link(self):
        rows,_=proof.pinned_rows()
        deltas=[((r[0][4]-r[0][2])&0xffffffff,(r[0][5]-r[0][3])&0xffffffff) for r in rows]
        prefix=HEADER+'\nnamespace Doom.Verification.ExtractedLineIteration\ndef deltas : List (BitVec 32 × BitVec 32) := '+str(deltas).replace(' ','')+'\nend Doom.Verification.ExtractedLineIteration\nnamespace PinnedRowsTest\n'
        def part(rs):return prefix+proof.pinned_certificate(rs).split('theorem pinned_execution',1)[0]+'\nend PinnedRowsTest\n'
        self.succeeds(part(rows))
        bad=copy.deepcopy(rows);bad[0][0][4]^=65536
        self.rejects(part(bad))
    def test_raw_flag_is_little_endian_low_byte(self):
        self.succeeds(HEADER+'''
def r : E1M1AimEncodedPortal.Row := ⟨⟨0,1,0,0,65536,0⟩,0x0104,0,1,0,1,0,0,0,0⟩
def patch := E1M1AimEncodedPortal.rawBytes r 0x40000
example : (E1M1NoiseImage.applyPatch patch (fun _ => 0)) (0x40000+4)=4 := by
  exact E1M1AimEncodedPortal.flag_byte r 0x40000 _
    (E1M1NoiseImage.realizes (by unfold E1M1NoiseImage.Consistent; decide) _)
example : ¬E1M1NoiseImage.Realizes patch (fun _ => 0) := by
  intro h
  have wrong := E1M1AimEncodedPortal.flag_byte r 0x40000 _ h
  change (0#8)=4 at wrong
  contradiction
''')
    def test_absent_back_side_requires_no_back_pointer_bytes(self):
        self.succeeds(HEADER+'''
example (r : E1M1AimEncodedPortal.Row) (base : Word) (sector : Nat → Word)
    (absent : r.backIndex=65535) :
    E1M1AimEncodedPortal.sideBytes r base sector=
      E1M1NoiseImage.word (E1M1NoiseGraph.sideAddress base r.frontIndex) (sector r.frontSector) := by
  simp [E1M1AimEncodedPortal.sideBytes,absent]
''')
    def test_initial_byte_encoding_and_front_presence_are_required(self):
        self.mutations(self.contract('images'),[
          ('(encoded : Doom.Proofs.E1M1AimEncodedPortal.Encoded total rows raw vertexBase sideBase sector m)','(encoded : True)'),
          ('(fronts : ∀ i, (rows i).frontIndex≠65535)','(fronts : True)')])
    def test_back_height_image_and_presence_are_required(self):
        self.mutations(self.contract('sector_values'),[
          ('(present : r.backIndex≠65535)','(present : True)'),
          ('(image : Doom.Proofs.E1M1NoiseImage.Realizes (Doom.Proofs.E1M1AimEncodedPortal.sectorBytes r sector) m)','(image : True)')])
    def test_pinned_specialization_keeps_memory_and_storage_not_finite_obligations(self):
        rows,_=proof.pinned_rows();decl=proof.pinned_certificate(rows).split('theorem pinned_execution',1)[1].split(' := by',1)[0]
        self.assertNotIn('(good :',decl);self.assertNotIn('(fronts :',decl);self.assertNotIn('(present :',decl)
        self.assertIn('(encoded :',decl);self.assertIn('(layout :',decl);self.assertIn('(verticesSafe :',decl)
        self.assertNotIn('copyInput',decl)
if __name__=='__main__':unittest.main()
