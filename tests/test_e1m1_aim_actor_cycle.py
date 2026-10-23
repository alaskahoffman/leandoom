"""Guard actor skip/scan continuity, exact source progress and reusable boundaries."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_actor_skip as prior
import verify_e1m1_aim_actor_cycle as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimActorSkipAligned\n'+proof.HEADER+'\nattribute [local irreducible] load32 store32 E1M1AimActorSkip.result\n'
class AimActorCycleTests(unittest.TestCase):
    lean=prior.AimActorSkipTests.lean
    succeeds=prior.AimActorSkipTests.succeeds
    rejects=prior.AimActorSkipTests.rejects
    mutations=prior.AimActorSkipTests.mutations
    def contract(self,module,name,args):
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'
    def test_certificate_and_complete_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),43)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimActorSkipCycle.scan','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_scan_inputs_come_from_actual_return_and_cursor(self):
        self.mutations(self.contract('E1M1AimActorSkipCycle','registers','s safe'),[
            ('(safe : Safe (s.regs 4) 0x2c028)','(safe : True)'),
            ('load32 s.memory 0x2c028','load32 s.memory 0x2c02c'),
            ('core.regs 4=s.regs 4+4','core.regs 4=s.regs 4'),
            ('(s.regs 3) 0x7fffffff','(s.regs 0) 0x7fffffff'),
            ('.pc=0x2c83a','.pc=0x2c88c')])
    def test_actor_frame_requires_both_prologue_and_mark_separation(self):
        self.mutations(self.contract('E1M1AimActorSkipCycle','frame','s a safe mark'),[
            ('(safe : Safe (s.regs 4) a)','(safe : True)'),
            ('(mark : Apart a (s.regs 3))','(mark : True)')])
    def test_scan_requires_consumed_image_history_and_layout(self):
        self.mutations(self.contract('E1M1AimActorSkipCycle','scan',proof.SCAN_ARGS),[
            ('(selection : Selection initial work seen resolve target sp ⟨s,f,0x2b760⟩ fraction j)','(selection : True)'),
            ('(layout : E1M1AimCycleInvariant.Layout s work)','(layout : True)'),
            ('(bounded : initial.size≤128)','(bounded : True)'),
            ('(history : History initial (consume work j) (j::seen) (visits.push work[j]!))','(history : True)'),
            ('(encoded : OriginalLineFinish.Encodes (Doom.Proofs.E1M1AimActorSkip.result s).core.memory 0x2ba20 resolve (consume work j))','(encoded : True)'),
            ('n≤13+7*work.size','n≤12+7*work.size')])
    def test_carried_invariant_is_derived_for_actual_next_callback(self):
        self.mutations(self.contract('E1M1AimActorSkipCycle','carried',
            's initial work marked seen visits resolve portals distance z out history before keep pointer inside done'),[
            ('(keep : Frame s out)','(keep : True)'),
            ('(pointer : s.regs 3=address marked)','(pointer : True)'),
            ('(before : Persistent s initial work resolve portals distance z)','(before : True)'),
            ('(inside : marked<initial.size)','(inside : True)'),
            ('Doom.Proofs.E1M1AimActorSkipCycle.Next s initial (consume work marked) seen resolve portals distance z out',
             'Doom.Proofs.E1M1AimActorSkipCycle.Next s initial work seen resolve portals distance z out')])
    def test_complete_cycle_does_not_assume_away_actor_representation(self):
        self.mutations(self.contract('E1M1AimActorSkipCycle','execution',proof.EXEC_ARGS),[
            ('(before : Persistent s original.collected work resolve portals distance thing.shootHeight)','(before : True)'),
            ('(identity : resolve original.collected[j]! = who ↔ (work[j]!).id=shooter)','(identity : True)'),
            ('(flags : (s.memory (resolve original.collected[j]!+104) &&& (4#8) != 0)=scene.things[work[j]!.id]!.shootable)','(flags : True)'),
            ('(ignored : (work[j]!).id=shooter ∨ scene.things[work[j]!.id]!.shootable=false)','(ignored : True)'),
            ('n≤41+7*work.size','n≤40+7*work.size')])
    def test_alignment_preserves_bounds_history_and_exact_source_suffix(self):
        self.mutations(self.contract('E1M1AimActorSkipAligned','execution',proof.EXEC_ARGS),[
            ('History original.collected (consume work j) (j::seen) (visits.push work[j]!)',
             'History original.collected work seen visits'),
            ('resolve portals lower upper log out','resolve portals upper lower log out'),
            ('load32 out.core.memory (0x2c1e4#32)=lower.raw.toBitVec',
             'load32 out.core.memory (0x2c1e4#32)=upper.raw.toBitVec'),
            ("List.range' (seen.length+1) (path.visited.size-(seen.length+1))",
             "List.range' (seen.length+2) (path.visited.size-(seen.length+2))")])
    def test_existing_line_boundary_requires_admitted_successor(self):
        source=self.contract('E1M1AimActorSkipAligned','line_boundary',proof.NEXT_ARGS)
        self.mutations(source,[
            ('(chosen : E1M1InterceptMinimum.minimum work=.ok (fraction,some j))','(chosen : True)'),
            ('(within : ¬fraction>65536)','(within : True)'),
            ('(aligned : Doom.Proofs.E1M1AimActorSkipAligned.Aligned s scene shooter thing path result distance work seen resolve portals lower upper log out)',
             '(aligned : True)')])
if __name__=='__main__':unittest.main()
