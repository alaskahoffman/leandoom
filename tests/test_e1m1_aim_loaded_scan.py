"""Full-loader portal preservation: ordered records, storage and execution boundary."""
import copy,re,unittest
from pathlib import Path
import test_e1m1_aim_loaded_portal as prior
import verify_e1m1_aim_loaded_scan as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimLoadedScan\n'+proof.HEADER+'\nset_option maxRecDepth 32768\n'
FIXTURE='''
open E1M1AimLoadedScanRegions E1M1LineScan
 def stack : Region := ⟨0x80000,0x80010⟩
 theorem layout : E1M1AimLoadedScanRegions.Layout 475 0x30001 stack := ⟨by decide,by decide⟩
 theorem reserve : Reserve stack 0x80010 := by unfold Reserve; decide
 def p : E1M1AimCatalog.Portal := ⟨0x60003,0x60003,0,0x800000,0,0x800000⟩
 theorem sector : Sector 475 0x30001 0x60003 stack := ⟨by decide,by decide,by decide⟩
'''
class AimLoadedScanTests(unittest.TestCase):
    lean=prior.AimLoadedPortalTests.lean
    succeeds=prior.AimLoadedPortalTests.succeeds
    rejects=prior.AimLoadedPortalTests.rejects
    mutations=prior.AimLoadedPortalTests.mutations
    def contract(self,module,name):
        args=next(a for m,n,a in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,profile,raw=proof.extracted();scan=proof.scan_data()
        self.assertEqual(scan[3]['exe_sha256'],profile['exe_sha256'])
        self.assertEqual(len(proof.combined_units(spec['units'],scan[1])),60)
        output=self.succeeds(proof.certificate(data,raw,scan));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',
                    output.replace('ExtractedLineIteration.division_checked','missing'),
                    output.replace('ExtractedLineScan.scan_checked','missing'),
                    output.replace('ExtractedAimLoadedScan.pinned_map_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_changed_newly_joined_loop_bytes_are_rejected(self):
        raw,_,data,_=proof.scan_data()
        for name in ['metadata','slope','vertices','delta','horizontal','vertical']:
            bad={k:bytes(v) for k,v in raw.items()};bad[name]=bytes([bad[name][0]^1])+bad[name][1:]
            self.rejects(proof.scan.certificate(bad,data))
    def test_overlapping_certificate_metadata_must_agree(self):
        spec,_,_=proof.extracted();scan=proof.scan_data()
        units=copy.deepcopy(scan[1]);units['scan_copy']['hex']='00'
        with self.assertRaises(ValueError):proof.combined_units(spec['units'],units)
    def test_unaligned_adjacent_and_last_record_fields(self):
        self.succeeds(HEADER+FIXTURE+'''
example : E1M1LineFrame.Protected (cursor 0x30001 62 0+50) (cursor 0x30001 62 1) 0x80010 :=
  earlier_field 475 0x30001 0x80010 stack 0 1 50 layout reserve (by decide) (by decide) (by decide)
example : E1M1LineFrame.Protected (cursor 0x30001 62 473+50) (cursor 0x30001 62 474) 0x80010 :=
  earlier_field 475 0x30001 0x80010 stack 473 474 50 layout reserve (by decide) (by decide) (by decide)
example : (E1M1AimObjectRegions.region 0x30001 (62*475)).Contains (cursor 0x30001 62 474+58) :=
  record_field 475 0x30001 474 58 layout.bound (by decide) (by decide)
example : (cursor 0x30001 62 474).toNat=0x30001+62*474 :=
  cursor_nat 0x30001 474 (by decide)
''')
    def test_shared_sectors_survive_every_later_record(self):
        self.succeeds(HEADER+FIXTURE+'''
example (i j : Nat) (order : i<j) (inside : j<475) :
    ∀ a∈E1M1AimLoadedPortal.reads (cursor 0x30001 62 i) p,
      E1M1LineFrame.Protected a (cursor 0x30001 62 j) 0x80010 :=
  portal_reads 475 0x30001 0x80010 stack i j p layout sector sector reserve order inside
example : E1M1AimLoadedPortal.SectorSafe (cursor 0x30001 62 474) p :=
  sector_safe 475 0x30001 0x80010 stack 474 p layout sector sector reserve (by decide)
''')
    def test_same_record_and_partial_sector_overlap_are_rejected(self):
        self.succeeds(HEADER+'''
example (base sp : Word) : ¬E1M1LineFrame.Protected (base+46) base sp := by
  intro h
  exact h.words 46 (by simp) 0 0 rfl
example : ¬E1M1AimLoadedScanRegions.Sector 2 0x30001 (0x30001+62-4) ⟨0x80000,0x80010⟩ := by
  intro h
  have nope : ¬(E1M1AimObjectRegions.region (0x30001+62-4) 8).Disjoint
      (E1M1AimObjectRegions.region 0x30001 (62*2)) := by decide
  exact nope h.linesApart
''')
    def test_nonwrapping_and_stack_reserve_bounds(self):
        self.succeeds(HEADER+'''
example : ¬E1M1AimLoadedScanRegions.Layout 2 0xfffffff0 ⟨100,116⟩ := by
  intro h; have bad := h.bound; contradiction
example : ¬E1M1AimLoadedScanRegions.Reserve ⟨0x80000,0x80010⟩ 0x8000f := by
  unfold E1M1AimLoadedScanRegions.Reserve; decide
''')
    def test_protection_requires_order_and_storage(self):
        self.mutations(self.contract('E1M1AimLoadedScanRegions','earlier_field'),[
          ('(order : i<j)','(order : True)'),
          ('(layout : Doom.Proofs.E1M1AimLoadedScanRegions.Layout total base stack)','(layout : True)'),
          ('(reserve : Doom.Proofs.E1M1AimLoadedScanRegions.Reserve stack sp)','(reserve : True)')])
    def test_retained_does_not_invent_initial_values(self):
        self.mutations(self.contract('E1M1AimLoadedScan','retained'),[
          ('(initial : E1M1AimObjectCatalog.PortalValues (Doom.Proofs.E1M1LineScan.states s f (i+1)).core.memory hit (Doom.Proofs.E1M1LineScan.cursor base 62 i) p)','(initial : True)'),
          ('(front : E1M1AimLoadedScanRegions.Sector total base p.front stack)','(front : True)')])
    def test_established_retains_source_contents_and_presence(self):
        self.mutations(self.contract('E1M1AimLoadedScan','established'),[
          ('(present : source.backIndex≠0xffff)','(present : True)'),
          ('(heights : E1M1AimLoadedPortal.SectorValues (E1M1LineOutput.copyInput (Doom.Proofs.E1M1LineScan.states s f i).core).memory p)','(heights : True)'),
          ('(kind : hit.isLine=true)','(kind : True)')])
    def test_execution_retains_arithmetic_and_initial_loop_state(self):
        self.mutations(self.contract('E1M1AimLoadedScan','execution'),[
          ('(arithmetic : E1M1LineScan.Arithmetic total s f)','(arithmetic : True)'),
          ('(ready : E1M1LineScan.Ready total raw base sp 0 s)','(ready : True)')])
    def test_last_record_empty_suffix_uses_same_loaded_state(self):
        self.succeeds(HEADER+FIXTURE+'''
example (s : X86Memory.State) (f : Option Flags) (hit : Intercept) (raw : Word)
    (loop : E1M1LineScan.Layout 475 0x30001 0x80010)
    (ready : Ready 475 raw 0x30001 0x80010 0 s)
    (value : E1M1AimObjectCatalog.PortalValues (states s f 475).core.memory hit (cursor 0x30001 62 474) p) :
    E1M1AimObjectCatalog.PortalValues (states s f 475).core.memory hit (cursor 0x30001 62 474) p :=
  E1M1AimLoadedScan.retained 475 raw 0x30001 0x80010 stack s f 474 hit p loop ready
    layout sector sector reserve (by decide) value
''')
if __name__=='__main__':unittest.main()
