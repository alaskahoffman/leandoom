"""Guard the whole catalog and the actual callback-cycle invariant."""
import re
import unittest
from pathlib import Path
import test_e1m1_aim_next_line as prior
import verify_e1m1_aim_traversal_invariant as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='''import Doom.Proofs.E1M1AimTraversalInvariant
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1MinimumScan (address)
open E1M1SelectionHistory (History)
open E1M1HistoryDispatch (Selection)
open E1M1InterceptMark (consume)
open E1M1AimHistoryCycle (Frame)
open E1M1AimCycleInvariant (Layout QuerySafe)
open E1M1AimNextLine (ClipGlobalsSafe)
open E1M1AimCatalog (Portal Catalog Entry)
open E1M1AimTraversalInvariant (Persistent)
attribute [local irreducible] load32 store32
'''
class AimTraversalInvariantTests(unittest.TestCase):
    lean=prior.AimNextLineTests.lean
    succeeds=prior.AimNextLineTests.succeeds
    rejects=prior.AimNextLineTests.rejects
    mutations=prior.AimNextLineTests.mutations
    def contract(self,module,name,args):
        source=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        start=re.search(r'^theorem '+name+r'(?: | :)',source,re.M).start()
        decl=source[start:source.index(' := by',start)]
        decl=re.sub(r'\bprogram\b','E1M1AimRepeatProgram.program',decl)
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'
    def test_certificate_and_complete_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),42)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimTraversalInvariant.execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for m,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+)(?: | :)',(ROOT/f'Doom/Proofs/{m}.lean').read_text(),re.M))
    def test_catalog_preserves_all_entries_under_real_frame(self):
        self.mutations(self.contract('E1M1AimCatalog','preserved',
            's out marked initial resolve portals frame stack pointer bounded catalog'),[
            ('(frame : Frame s out)','(frame : True)'),
            ('(stack : out.core.regs 4=s.regs 4)','(stack : True)'),
            ('(catalog : Catalog s initial resolve portals)','(catalog : True)'),
            ('Catalog out.core initial resolve portals','Catalog out.core initial resolve (fun i => portals (i+1))')])
    def test_partial_catalog_does_not_classify_arbitrary_hits(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (initial : Array Intercept) (resolve : Intercept → Word) :
    Catalog s initial resolve (fun _ => none) := by
  intro i inside p listed
  cases listed
''')
        self.mutations(self.contract('E1M1AimCatalog','inputs',
            's initial work seen visits resolve portals target sp fraction j p history selection catalog listed layout query globals'),[
            ('(listed : portals j=some p)','(listed : True)'),
            ('(listed : portals j=some p)','(listed : portals (j+1)=some p)'),
            ('(selection : Selection initial work seen resolve target sp s fraction j)','(selection : True)')])
    def test_persistent_state_requires_actual_cycle_and_mark(self):
        self.mutations(self.contract('E1M1AimTraversalInvariant','preserved',proof.PRESERVE_ARGS),[
            ('(frame : Frame s out)','(frame : True)'),
            ('(pointer : s.regs 3=address marked)','(pointer : True)'),
            ('(inside : marked<initial.size)','(inside : True)'),
            ('Persistent out.core initial (consume work marked) resolve portals distance z','Persistent out.core initial (consume work marked) resolve portals z distance')])
    def test_carried_callback_has_exact_original_aim_address(self):
        self.mutations(self.contract('E1M1AimTraversalInvariant','carried',
            's initial work marked seen visits resolve portals distance z out history before frame pointer inside done'),[
            ('(before : Persistent s initial work resolve portals distance z)','(before : True)'),
            ('(history : History initial (consume work marked) seen visits)','(history : True)'),
            ('Next s initial (consume work marked) seen resolve portals distance z out','Next s initial work seen resolve portals distance z out')])
    def test_cycle_rebuilds_invariant_and_preserves_changed_window(self):
        self.mutations(self.contract('E1M1AimTraversalInvariant','execution',proof.CYCLE_ARGS),[
            ('(before : Persistent s initial work resolve portals distance z)','(before : True)'),
            ('(listed : portals j=some p)','(listed : True)'),
            ('load32 out.core.memory (0x2c1e4#32)=(if p.bf=p.ff then lower.raw else max lower.raw floorSlope.raw).toBitVec','load32 out.core.memory (0x2c1e4#32)=lower.raw.toBitVec'),
            ('load32 out.core.memory (0x2c1e8#32)=(if p.fc=p.bc then upper.raw else min upper.raw ceilingSlope.raw).toBitVec','load32 out.core.memory (0x2c1e8#32)=upper.raw.toBitVec')])
    def test_cycle_keeps_history_advance_and_stop_distinct(self):
        self.mutations(self.contract('E1M1AimTraversalInvariant','execution',proof.CYCLE_ARGS),[
            ('History initial (consume work j) (j::seen) (visits.push work[j]!)','History initial work (j::seen) (visits.push work[j]!)'),
            ('out.pc=0x2c88c','out.pc=0x2c887'),
            ('⟨s,f,0x2b760⟩ out','⟨s,f,0x2c83a⟩ out')])
    def test_invariant_carries_callback_slot_and_resolver_stability(self):
        source=HEADER+'''
example (s : X86Memory.State) (initial work : Array Intercept)
    (resolve : Intercept → Word) (portals : Nat → Option Portal) (distance z : Fixed)
    (h : Persistent s initial work resolve portals distance z) (i : Nat) (inside : i<initial.size) :
    load32 s.memory (s.regs 4+4)=0x2b760 ∧
    Apart (s.regs 4+4) (address i) ∧
    resolve {initial[i]! with frac := ⟨2147483647⟩}=resolve initial[i]! :=
  ⟨h.callback,h.slotMarks i inside,h.resolver i inside⟩
'''
        self.mutations(source,[
            ('load32 s.memory (s.regs 4+4)=0x2b760','load32 s.memory (s.regs 4)=0x2b760'),
            ('(inside : i<initial.size)','(inside : True)')])
if __name__=='__main__':unittest.main()
