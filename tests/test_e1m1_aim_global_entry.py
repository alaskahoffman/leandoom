"""Phase-specific global guards: deliberate writes, alias rejection and catalog joins."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_caller_entry as prior
import verify_e1m1_aim_global_entry as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimGlobalEntry\n'+proof.HEADER+'\nset_option maxRecDepth 32768\n'
class AimGlobalEntryTests(unittest.TestCase):
    lean=prior.AimCallerEntryTests.lean
    succeeds=prior.AimCallerEntryTests.succeeds
    rejects=prior.AimCallerEntryTests.rejects
    mutations=prior.AimCallerEntryTests.mutations
    def contract(self,module,name):
        args=next(a for m,n,a in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',
                    output.replace('ExtractedAimGlobalEntry.pinned_map_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_clipping_bounds_are_not_continuing_invariants(self):
        self.succeeds(HEADER+'''
example : (0x2c1e4#32)∈E1M1AimGlobalRegions.values ∧
    (0x2c1e8#32)∈E1M1AimGlobalRegions.values ∧
    (0x2c1e4#32)∉E1M1AimGlobalRegions.stable ∧
    (0x2c1e8#32)∉E1M1AimGlobalRegions.stable := by decide
example (s : X86Memory.State) : ¬E1M1AimMapFrame.StableWord s 0x2c1e4 := by
  intro h
  exact h.1.2 _ (by simp [E1M1AimReturnFrame.writes]) 0 0 rfl
example (s : X86Memory.State) : ¬E1M1AimMapFrame.StableWord s 0x2c1e8 := by
  intro h
  exact h.1.2 _ (by simp [E1M1AimReturnFrame.writes]) 0 0 rfl
''')
    def test_target_selection_is_outside_continuing_frame(self):
        self.succeeds(HEADER+'''
example : (0x2b9f8#32)∈E1M1AimGlobalRegions.stable := by decide
example (s : X86Memory.State) : ¬E1M1AimSavedWords.Protect s 0x2b9f8 := by
  intro h
  exact h.2.1 0 0 rfl
''')
    def test_aim_setup_creates_globals_before_preserved_phase(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) : ¬E1M1PathMapQuery.Safe s 0x2b9f8 := by
  intro h
  exact h.setup _ (by simp [OriginalAimSetup.writes]) 0 0 rfl
example (s : X86Memory.State) : ¬E1M1PathMapQuery.Safe s 0x2c1e4 := by
  intro h
  exact h.setup _ (by simp [OriginalAimSetup.writes]) 0 0 rfl
''')
    def test_line_global_separation_is_additional_to_stack_separation(self):
        self.succeeds(HEADER+'''
example : E1M1AimCallbackRegions.Layout ⟨900,1112⟩ (0x2b9ac-54) :=
  ⟨by decide,by decide,by decide⟩
example : ¬(E1M1AimStaticRegions.linedefs (0x2b9ac-54)).Disjoint
    E1M1AimMapRegions.globalStores := by decide
example : ¬Apart (0x2b9ac#32) ((0x2b9ac-54)+54) := by unfold Apart; decide
example : ¬E1M1AimGlobalRegions.Layout ⟨900,1112⟩ (0x2b9ac-54) := by
  intro h
  exact (by decide : ¬(E1M1AimStaticRegions.linedefs (0x2b9ac-54)).Disjoint
    E1M1AimMapRegions.globalStores) h.linesGlobals
''')
    def test_collection_guards_retain_separation_and_reserve(self):
        self.mutations(self.contract('E1M1AimGlobalRegions','collection'),[
          ('(placement : Doom.Proofs.E1M1AimGlobalRegions.Layout stack q.lines)',
           '(placement : E1M1AimCallbackRegions.Layout stack q.lines)'),
          ('(reserve : E1M1AimWalkRegions.Reserve stack q.sp)','(reserve : True)')])
    def test_floor_helper_guard_keeps_phase_and_membership(self):
        self.mutations(self.contract('E1M1AimGlobalRegions','floor_word'),[
          ('(position : s.regs 4=q.sp-164)','(position : s.regs 4=q.sp-140)'),
          ('(member : a∈[(0x2c034#32),0x2b9a8,0x2c1e8])','(member : True)')])
    def test_collection_excludes_cursor_and_covers_final_record(self):
        self.succeeds(HEADER+'''
example : ¬OriginalLineMixedInvariant.ArraySafe 0x2ba20 0x2c028 := by
  intro h
  exact h.2 0 0 rfl
example : Apart (0x2c1e4#32) (0x2ba20+BitVec.ofNat 32 (12*127)+8) :=
  (E1M1AimGlobalRegions.array 0x2c1e4 (by decide)).1 127 (by decide) 8 (by simp)
''')
    def test_residual_fields_remove_exactly_seven_guards(self):
        def fields(module):
            s=(ROOT/f'Doom/Proofs/{module}.lean').read_text().split('structure OtherInputs',1)[1].split('\n\n',1)[0]
            return re.findall(r'^  (\w+) :',s,re.M)
        removed={'query','clip','valueReads','shooterSafe','shooterLater','targetSafe','globalReads'}
        self.assertEqual(fields('E1M1AimGlobalEntry'),[x for x in fields('E1M1AimCallerEntry') if x not in removed])
        self.assertEqual(fields('E1M1AimGlobalEntry'),['layout','portals','shooterReg','actors','walls'])
        self.mutations(self.contract('E1M1AimGlobalEntry','other'),[
          ('(input : Doom.Proofs.E1M1AimGlobalEntry.OtherInputs q s scene shooter hits portals walls who)','(input : True)')])
    def test_initial_and_controller_retain_placement_and_angle_value(self):
        self.mutations(self.contract('E1M1AimGlobalEntry','initial'),[
          ('(globalPlacement : E1M1AimGlobalRegions.Layout stack q.lines)','(globalPlacement : True)')])
        self.mutations(self.contract('E1M1AimGlobalEntry','controller'),[
          ('(value : load32 s.memory (s.regs 0+32)=angle.raw.toBitVec)','(value : True)'),
          ('(position : s.regs 4=q.sp-4)','(position : s.regs 4=q.sp-24)')])
if __name__=='__main__':unittest.main()
