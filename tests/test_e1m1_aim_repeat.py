"""Guard the continuous program seam, window frame and live continuation."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_next_selection as prior
import verify_e1m1_aim_repeat as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='''import Doom.Proofs.E1M1AimRepeatSource
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary Collision E1M1AimIteration
open E1M1MinimumScan (address)
open E1M1AimRepeatProgram (program ReadFrame)
attribute [local irreducible] load32 store32
'''
ARGS='s f hit line front back ff fc bf bc distance z lower upper floorSlope ceilingSlope h distanceReads floorReads reads clip range eye bottom top pass floorOk ceilingOk returnSafe returnWord markSafe hits resolve j inside bounded image safe pointer stable cursorSafe cursor maximum targetSafe recordSafe boundsSafe slotSafe slotMark'
class AimRepeatTests(unittest.TestCase):
    lean=prior.AimNextSelectionTests.lean
    succeeds=prior.AimNextSelectionTests.succeeds
    rejects=prior.AimNextSelectionTests.rejects
    mutations=prior.AimNextSelectionTests.mutations
    def contract(self,module,name,args):
        s=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=re.search(r'^theorem '+name+r'(?: | :)',s,re.M).start()
        decl=s[a:s.index(' := by',a)]
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'
    def test_certificate_checks_common_program_and_complete_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),42)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out+'extra',out.replace('AimRepeatSource.correspondence','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for m,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+)(?: | :)',(ROOT/f'Doom/Proofs/{m}.lean').read_text(),re.M))
        changed=dict(raw);b=bytearray(raw['interceptHandoff']);self.assertEqual(b[9],0xe8);b[9]=0xe9;changed['interceptHandoff']=bytes(b)
        self.rejects(proof.certificate(data,changed))
    def test_join_needs_return_site_and_preserves_changed_bounds(self):
        self.mutations(self.contract('E1M1AimRepeat','execution',ARGS),[
            ('(returnWord : load32 s.memory (s.regs 4)=0x2c86d)','(returnWord : True)'),
            ('(boundsSafe : Apart (0x2c1e4#32) (s.regs 4) ∧ Apart (0x2c1e8#32) (s.regs 4))','(boundsSafe : True)'),
            ('load32 out.core.memory (0x2c1e4#32)=(if bf=ff then lower.raw else max lower.raw floorSlope.raw).toBitVec','load32 out.core.memory (0x2c1e4#32)=lower.raw.toBitVec'),
            ('load32 out.core.memory (0x2c1e8#32)=(if fc=bc then upper.raw else min upper.raw ceilingSlope.raw).toBitVec','load32 out.core.memory (0x2c1e8#32)=upper.raw.toBitVec')])
    def test_callback_stop_and_repeat_keep_exact_machine_seam(self):
        self.mutations(self.contract('E1M1AimRepeat','execution',ARGS),[
            ('out.pc=0x2c88c','out.pc=0x2c887'),
            ('⟨s,f,0x2b760⟩ out','⟨s,f,0x2c83a⟩ out'),
            ('E1M1CallbackEntry.Outcome (E1M1InterceptMark.consume hits j)','E1M1CallbackEntry.Outcome hits'),
            ('(load32 s.memory (s.regs 4+4)) (s.regs 4+4) out','(load32 s.memory (s.regs 4)) (s.regs 4+4) out')])
    def test_next_search_frame_requires_store_separation(self):
        self.mutations(self.contract('E1M1AimRepeatProgram','repeat_selection','s f hits resolve bounded nonempty limit encoded maximum targetSafe recordSafe'),[
            ('(limit : s.regs 1=address hits.size)','(limit : True)'),
            ('(encoded : OriginalLineFinish.Encodes s.memory 0x2ba20 resolve hits)','(encoded : True)'),
            ('⟨s,f,0x2c83a⟩ out','⟨s,f,0x2c841⟩ out')])
    def test_source_join_carries_portals_window_and_matching_hit(self):
        self.mutations(self.contract('E1M1AimRepeatSource','correspondence',proof.SOURCE_ARGS),[
            ('(listedHit : hits[j]! = hit)','(listedHit : True)'),
            ('(selectedPointer : s.regs 3=s.regs 0)','(selectedPointer : True)'),
            ('(history.push (portal scene.lines[hit.id]!.front back distance hit))','history'),
            ('E1M1AimSource.stopped path (i+1)','E1M1AimSource.stopped path i')])
    def test_read_frame_does_not_promise_preservation_at_a_written_word(self):
        source=HEADER+'''
example (s : X86Memory.State) (out : X86Control.State) (a : Word)
    (h : ReadFrame s out) (cursor : Apart a 0x2c028) (stack : Apart a (s.regs 4-4)) :
    load32 out.core.memory a=load32 s.memory a := h a cursor stack
'''
        self.mutations(source,[('(cursor : Apart a 0x2c028)','(cursor : True)'),('(stack : Apart a (s.regs 4-4))','(stack : True)')])
if __name__=='__main__':unittest.main()
