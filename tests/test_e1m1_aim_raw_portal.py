"""Raw flags through metadata, geometry and the initial-image execution join."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_initial_portal as prior
import verify_e1m1_aim_raw_portal as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimRawPortal\n'+proof.HEADER+'\nset_option maxRecDepth 32768\n'
FIXTURE=prior.FIXTURE.replace('import Doom.Proofs.E1M1AimInitialPortal','import Doom.Proofs.E1M1AimRawPortal')
FIXTURE=FIXTURE.replace('E1M1AimInitialPortal.execution_from_image','E1M1AimRawPortal.execution_from_image')
FIXTURE=FIXTURE.replace('kind (by decide)','kind (by intro j hj; omega) (by decide)')
class AimRawPortalTests(unittest.TestCase):
    lean=prior.AimInitialPortalTests.lean
    succeeds=prior.AimInitialPortalTests.succeeds
    rejects=prior.AimInitialPortalTests.rejects
    mutations=prior.AimInitialPortalTests.mutations
    def contract(self,module,name):
        args=next(a for m,n,a in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_inherited_certificate_and_all_new_declarations_audited(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();scan=proof.previous.previous.scan_data()
        self.assertEqual(len(proof.previous.previous.combined_units(spec['units'],scan[1])),60)
        output=self.succeeds(proof.certificate(data,raw,scan));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',
                    output.replace('ExtractedAimRawPortal.E1M1AimLoaderFlags.prepared_frame_checked','missing'),
                    output.replace("'Doom.Proofs.OriginalLineSetup.metadata_fields'", "'missing'")]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_horizontal_execution_uses_only_initial_content(self):
        self.succeeds(FIXTURE)
    def test_vertical_and_diagonal_execution_use_same_join(self):
        for dx in [0,65536]:
            source=FIXTURE.replace(' def mem : Memory :=',' def rawMem : Memory :=')
            source=source.replace(' def state :',' def mem : Memory := store32 rawMem (0x90000+12) 65536\n def state :')
            source=source.replace('(0x90000+8) 65536)',f'(0x90000+8) {dx})')
            source=source.replace('⟨0,1,0,0,65536,0⟩',f'⟨0,1,0,0,{dx},65536⟩')
            source=source.replace('(by intro i; simp [geometry,E1M1LineSource.good])',
              f'(by intro i; change E1M1LineSource.good ⟨0,1,0,0,{dx},65536⟩=true; decide)')
            self.succeeds(source)
    def test_flags_byte_preservation_supports_wrapping_line_address(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (line : s.regs 3=0xfffffff8) (sp : s.regs 4=0x80010) :
    (E1M1LineOutput.copyInput s).memory 8=s.memory (s.regs 1+4) := by
  have h := E1M1AimLoaderFlags.flag_byte s (by
    intro off member
    rw [line,sp]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl <;> unfold Apart <;> decide)
  have dst : s.regs 3+16=(8#32) := by rw [line]; decide
  rw [dst] at h
  exact h
''')
    def test_exact_byte_does_not_infer_two_sided_from_back_presence(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State)
    (stack : ∀ off∈[(4#32),8,12,16], Apart (s.regs 3+16) (s.regs 4-off))
    (solid : s.memory (s.regs 1+4) &&& (4#8)=0) :
    (E1M1LineOutput.copyInput s).memory (s.regs 3+16) &&& (4#8)=0 := by
  rw [E1M1AimLoaderFlags.flag_byte s stack]; exact solid
''')
    def test_post_metadata_frame_requires_real_write_protection(self):
        self.mutations(self.contract('E1M1AimLoaderFlags','copy_frame'),[
          ('(safe : Doom.Proofs.E1M1AimLoaderFlags.Safe s a)','(safe : True)')])
        self.mutations(self.contract('E1M1AimLoaderFlags','flag_byte'),[
          ('(stack : ∀ off∈[(4#32),8,12,16], Apart (s.regs 3+16) (s.regs 4-off))','(stack : True)')])
    def test_raw_flag_read_requires_protection_against_earlier_records(self):
        self.mutations(self.contract('E1M1AimRawPortal','flag_at_copy'),[
          ('(flagSourceSafe : ∀ j, j<i.val → E1M1LineFrame.Protected\n      (Doom.Proofs.E1M1LineScan.cursor raw 14 i.val+4) (Doom.Proofs.E1M1LineScan.cursor base 62 j) sp)','(flagSourceSafe : True)'),
          ('(reserve : E1M1AimLoadedScanRegions.Reserve stack sp)','(reserve : True)')])
    def test_initial_flag_and_back_side_presence_remain_distinct(self):
        self.mutations(self.contract('E1M1AimRawPortal','established'),[
          ('(two : s.memory (Doom.Proofs.E1M1LineScan.cursor raw 14 i.val+4) &&& (4#8)≠0)','(two : True)'),
          ('(present : (records i).backIndex≠0xffff)','(present : True)')])
    def test_join_contains_no_reached_content_or_arithmetic_premise(self):
        decl=proof.declaration('E1M1AimRawPortal','execution_from_image')
        self.assertNotIn('copyInput',decl)
        self.assertNotIn('E1M1LineScan.Arithmetic',decl)
        self.assertNotIn('E1M1LineLoad.Source',decl)
        self.assertIn('SectorValues s.memory',decl)
        self.assertIn('(two : s.memory',decl)
if __name__=='__main__':unittest.main()
