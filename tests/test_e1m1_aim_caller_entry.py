"""Caller-word phase boundaries and derived initial catalog read guards."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_saved_entry as prior
import verify_e1m1_aim_caller_entry as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimCallerEntry\n'+proof.HEADER+'\nset_option maxRecDepth 32768\n'
class AimCallerEntryTests(unittest.TestCase):
    lean=prior.AimSavedEntryTests.lean
    succeeds=prior.AimSavedEntryTests.succeeds
    rejects=prior.AimSavedEntryTests.rejects
    mutations=prior.AimSavedEntryTests.mutations
    def contract(self,module,name):
        args=next(a for m,n,a in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',
                    output.replace('ExtractedAimCallerEntry.pinned_map_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_path_entry_boundary_and_wrapping_translation(self):
        self.succeeds(HEADER+'''
example (sp : Word) : Apart (sp-52) (sp+(-56#32)) :=
  E1M1AimCallerRegions.above sp 52 (-56#32) (by decide) (by decide) (by decide)
example : Apart (0-52 : Word) (0+(-56#32)) :=
  E1M1AimCallerRegions.above 0 52 (-56#32) (by decide) (by decide) (by decide)
example : ¬Apart (1000-53 : Word) (1000-56) := by unfold Apart; decide
example : E1M1AimQueryCaller.callerSlots.map ((1112-136 : Word)+·)=
    [(1112-52#32),1112-40,1112-36,1112-32,1112-28,1112-24] := by decide
''')
    def test_new_path_return_cannot_be_preserved_from_pre_ray_memory(self):
        self.succeeds(HEADER+'''
def query : X86Memory.State := ⟨fun _ => 1088,fun _ => 0⟩
example : ¬E1M1PathMapQuery.Safe query (1112-52) := by
  intro h
  have hit := h.setup (1112-52) (by
    simp [OriginalAimSetup.writes,E1M1PathMapQuery.withStack,query,write])
  exact hit 0 0 rfl
example : (E1M1AimPreRayMemory.layout query).regs 4=1112-52 := by decide
''')
    def test_concrete_path_entry_guard(self):
        self.succeeds(HEADER+'''
def pathState : X86Memory.State := ⟨fun _ => 1060,fun _ => 0⟩
example (q : E1M1CellWalkInvariant.Context) (anchor : q.sp=1112) (lines : q.lines=4096) :
    E1M1AimQueryCatalog.Protected q pathState (q.sp-52) := by
  apply E1M1AimCallerRegions.path_guard ⟨900,1112⟩ q pathState 52
  · simpa only [lines] using (show E1M1AimCallbackRegions.Layout ⟨900,1112⟩ 4096 from
      ⟨by decide,by decide,by decide⟩)
  · simp only [anchor,E1M1AimWalkRegions.Reserve]; decide
  · simp [pathState,anchor]
  · decide
  · decide
''')
    def test_relative_bound_cannot_be_widened(self):
        self.mutations(self.contract('E1M1AimCallerRegions','above'),[
          ('(high : n≤52)','(high : n≤53)'),
          ('off.toNat≤2^32-56','off.toNat≤2^32-55')])
    def test_setup_requires_actual_path_stack_position(self):
        self.mutations(self.contract('E1M1AimCallerRegions','setup'),[
          ('(position : s.regs 4=q.sp-52)','(position : s.regs 4=q.sp-48)'),
          ('(placement : Doom.Proofs.E1M1AimCallbackRegions.Layout stack q.lines)','(placement : True)')])
    def test_caller_memory_transport_keeps_execution_frame(self):
        self.mutations(self.contract('E1M1AimCallerRegions','word'),[
          ('''(frame : ∀ a, E1M1PathMapSetup.Safe s a → E1M1FiringMapState.Safe q.sp q.lines a →
      E1M1AimEntryFrame.SafeWord (q.sp-112) a → load32 out.core.memory a=load32 s.memory a)''',
           '(frame : True)')])
    def test_residual_fields_remove_only_caller_reads(self):
        def fields(module):
            s=(ROOT/f'Doom/Proofs/{module}.lean').read_text().split('structure OtherInputs',1)[1].split('\n\n',1)[0]
            return re.findall(r'^  (\w+) :',s,re.M)
        self.assertEqual(fields('E1M1AimCallerEntry'),[x for x in fields('E1M1AimSavedEntry') if x!='callerReads'])
        self.mutations(self.contract('E1M1AimCallerEntry','other'),[
          ('(position : s.regs 4=q.sp-24)','(position : True)'),
          ('(input : Doom.Proofs.E1M1AimCallerEntry.OtherInputs q s scene shooter hits portals walls who)','(input : True)')])
    def test_outer_and_query_stack_relations_differ_by_twenty_bytes(self):
        self.succeeds(HEADER+'''
def outer : X86Memory.State := ⟨fun _ => 1108,fun _ => 0⟩
example : (E1M1AimControllerInputs.layout outer ⟨0⟩).regs 4=1112-24 := by decide
example : (E1M1AimPreRayMemory.layout (E1M1AimControllerInputs.layout outer ⟨0⟩)).regs 4=1112-52 := by decide
''')
        self.mutations(self.contract('E1M1AimCallerEntry','controller'),[
          ('(position : s.regs 4=q.sp-4)','(position : s.regs 4=q.sp-24)')])
    def test_initial_catalog_and_controller_retain_remaining_contracts(self):
        self.mutations(self.contract('E1M1AimCallerEntry','initial'),[
          ('(callerPlacement : E1M1AimCallbackRegions.Layout stack q.lines)','(callerPlacement : True)')])
        self.mutations(self.contract('E1M1AimCallerEntry','controller'),[
          ('(value : load32 s.memory (s.regs 0+32)=angle.raw.toBitVec)','(value : True)')])
if __name__=='__main__':unittest.main()
