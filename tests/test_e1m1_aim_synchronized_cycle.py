"""Guard source/catalog arithmetic and the synchronized original callback cycle."""
import re
import unittest
from pathlib import Path
import test_e1m1_aim_path_bridge as prior
import verify_e1m1_aim_synchronized_cycle as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='''import Doom.Proofs.E1M1AimSynchronizedCycle
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1HistoryDispatch (Selection)
open E1M1InterceptMark (consume)
open E1M1AimCatalog (Portal)
open E1M1AimTraversalInvariant (Persistent Next)
open E1M1AimSourceCatalog (Represents front back)
open E1M1AimIteration
open E1M1AimHistoryCycle (Frame)
open E1M1AimRepeatProgram (program)
open E1M1AimSynchronizedCycle (AlignedNext)
attribute [local irreducible] load32 store32 SolidThing.shootHeight
'''
class AimSynchronizedCycleTests(unittest.TestCase):
    lean=prior.AimPathBridgeTests.lean
    succeeds=prior.AimPathBridgeTests.succeeds
    rejects=prior.AimPathBridgeTests.rejects
    mutations=prior.AimPathBridgeTests.mutations
    def contract(self,module,name,args):
        text=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        start=re.search(r'^theorem '+name+r' ',text,re.M).start()
        decl=text[start:text.index(' := by',start)]
        decl=re.sub(r'\bprogram\b','E1M1AimRepeatProgram.program',decl)
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'
    def test_certificate_and_complete_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),42)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimSynchronizedCycle.execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for m,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{m}.lean').read_text(),re.M))
    def test_partial_scene_catalog_and_selected_original_record(self):
        self.succeeds(HEADER+'''
example (scene : Scene) (initial : Array Intercept) :
    Represents scene initial (fun _ => none) := by
  intro i inside p listed
  cases listed
''')
        self.mutations(self.contract('E1M1AimSourceCatalog','entry',
            'scene initial work seen resolve portals target sp s fraction j p selection represented listed'),[
            ('(represented : Represents scene initial portals)','(represented : True)'),
            ('(listed : portals j=some p)','(listed : portals (j+1)=some p)'),
            ('scene.lines[work[j]!.id]!.back=some (back p)','scene.lines[work[j]!.id]!.back=some (front p)')])
    def test_source_arithmetic_retains_signed_window_and_division_guards(self):
        self.mutations(self.contract('E1M1AimSourceCatalog','arithmetic',
            'p distance z hit lower upper floorSlope ceilingSlope pass floorOk ceilingOk'),[
            ('(pass : max (front p).floor.raw (back p).floor.raw <\n      min (front p).ceiling.raw (back p).ceiling.raw)','(pass : True)'),
            ('(p.bf≠p.ff → checkedPathDiv','(p.bf=p.ff → checkedPathDiv'),
            ('(bottomAfter (front p) (back p) lower floorSlope).raw','lower.raw'),
            ('(topAfter (front p) (back p) upper ceilingSlope).raw','upper.raw')])
    def test_canonical_suffix_index_and_remaining_length(self):
        self.mutations(self.contract('E1M1AimSynchronizedCycle','indices','i size inside'),[
            ('(inside : i<size)','(inside : True)'),
            ("i::List.range' (i+1) (size-(i+1))","i::List.range' (i+1) (size-i)"),
            ("i::List.range' (i+1)","i::List.range' i")])
    def test_boundary_derives_source_finish_or_next_alignment(self):
        self.mutations(self.contract('E1M1AimSynchronizedCycle','boundary',
            's scene shooter thing path result distance work seen visits resolve portals lower upper log out history empty run next'),[
            ('(history : History result.collected work seen visits)','(history : True)'),
            ('(empty : result.visited=#[])','(empty : True)'),
            ('(next : Next s result.collected work seen resolve portals distance thing.shootHeight out)','(next : True)')])
    def test_admitted_next_hit_reuses_actual_persistent_callback(self):
        self.mutations(self.contract('E1M1AimSynchronizedCycle','next_callback',proof.NEXT_ARGS),[
            ('(within : ¬fraction>65536)','(within : True)'),
            ('(chosen : E1M1InterceptMinimum.minimum work=.ok (fraction,some j))','(chosen : True)'),
            ('Selection result.collected work seen resolve 0x2b760 (s.regs 4+4) out fraction j','Selection result.collected work seen resolve 0x2b760 (s.regs 4) out fraction j'),
            ('Persistent out.core result.collected work resolve portals distance thing.shootHeight','Persistent out.core result.collected work resolve portals thing.shootHeight distance')])
    def test_cycle_requires_source_catalog_and_real_precomputed_path(self):
        self.mutations(self.contract('E1M1AimSynchronizedCycle','execution',proof.CYCLE_ARGS),[
            ('(represented : Represents scene result.collected portals)','(represented : True)'),
            ('(query : E1M1QuerySource.visitHits result (fun _ _ => true)=.ok path)','(query : True)'),
            ('(before : Persistent s result.collected work resolve portals distance thing.shootHeight)','(before : True)'),
            ('(listed : portals j=some p)','(listed : True)')])
    def test_cycle_synchronizes_bounds_history_stop_and_source_suffix(self):
        self.mutations(self.contract('E1M1AimSynchronizedCycle','execution',proof.CYCLE_ARGS),[
            ('load32 out.core.memory (0x2c1e4#32)=lo.raw.toBitVec','load32 out.core.memory (0x2c1e4#32)=lower.raw.toBitVec'),
            ('History result.collected (consume work j) (j::seen)','History result.collected work (j::seen)'),
            ("List.range' (seen.length+1) (path.visited.size-(seen.length+1))","List.range' seen.length (path.visited.size-seen.length)"),
            ('E1M1AimSource.stopped path (seen.length+1)','E1M1AimSource.stopped path seen.length'),
            ('out.pc=0x2c88c','out.pc=0x2c887')])
if __name__=='__main__':unittest.main()
