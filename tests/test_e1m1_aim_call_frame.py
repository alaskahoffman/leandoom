"""Regress continuous memory preservation across aim entry, hits, return and retry."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_retry_query as prior
import verify_e1m1_aim_call_frame as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimCallFrame\n'+proof.HEADER+'''
set_option maxRecDepth 32768
attribute [local irreducible] load32 store32 SolidThing.shootHeight BitVec.add
'''
class AimCallFrameTests(unittest.TestCase):
    lean=prior.AimRetryQueryTests.lean
    succeeds=prior.AimRetryQueryTests.succeeds
    rejects=prior.AimRetryQueryTests.rejects
    mutations=prior.AimRetryQueryTests.mutations
    def contract(self,module,name):
        args=next(args for m,n,args in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimCallFrame.retry','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_caller_requires_live_callback_and_terminal_return_protection(self):
        self.mutations(self.contract('E1M1AimCallerFrame','execution'),[
            ('(watchedSafe : s.pc=0x2b760 → ∀ addr∈watched, E1M1AimSavedWords.Protect s.core addr)',
             '(watchedSafe : True)'),
            ('(watchedCursor : ∀ addr∈watched, Apart addr 0x2c028)',
             '(watchedCursor : s.pc=0x2b760 → ∀ addr∈watched, Apart addr 0x2c028)')])
    def test_collection_and_callback_guards_both_required(self):
        self.mutations(self.contract('E1M1AimQueryFrame','execution'),[
            ('(watchedRead : ∀ addr∈watched, Doom.Proofs.E1M1AimQueryCatalog.Protected q s addr)',
             '(watchedRead : True)'),
            ('(watchedSafe : ∀ addr∈watched, E1M1AimSavedWords.Protect (Doom.Proofs.E1M1AimQueryCatalog.view q s) addr)',
             '(watchedSafe : True)')])
    def test_complete_call_needs_protection_during_setup_and_later(self):
        self.mutations(self.contract('E1M1AimCallFrame','execution'),[
            ('E1M1AimPreRayMemory.Read q s addr','E1M1AimPreRayMemory.Later q s addr'),
            ('E1M1AimPreRayMemory.Read q s addr','E1M1PathMapQuery.Safe s addr'),
            ('(watchedSafe : ∀ addr∈watched, E1M1AimSavedWords.Protect (E1M1AimQueryCatalog.view q s) addr)',
             '(watchedSafe : True)')])
    def test_frame_cannot_claim_unwatched_words(self):
        for module in ['E1M1AimCallerFrame','E1M1AimQueryFrame','E1M1AimCallFrame']:
            self.mutations(self.contract(module,'execution'),[
                ('(∀ addr∈watched, load32 out.core.memory addr=',
                 '(∀ addr, load32 out.core.memory addr=')])
    def test_retry_needs_both_writes_excluded_and_actual_source_miss(self):
        self.mutations(self.contract('E1M1AimCallFrame','retry'),[
            ('Apart addr 0x2c0c0 ∧ Apart addr (s.regs 4)','Apart addr 0x2c0c0'),
            ('Apart addr 0x2c0c0 ∧ Apart addr (s.regs 4)','Apart addr (s.regs 4)'),
            ('(answer.target=none →','(answer.slope.raw=0 →')])
    def test_continuous_frame_starts_before_setup_and_ends_after_retry(self):
        source=self.contract('E1M1AimCallFrame','retry')
        args=source.split(' :\n    let g :=')[0]
        for absent in ['(out :','(kept :','(frame :','(miss :','traversal s']:
            self.assertNotIn(absent,args)
        self.assertIn('load32 (E1M1BulletAim.nextQuery second out.core).core.memory addr=',source)
        self.assertIn('load32 s.memory addr',source)
        self.mutations(source,[
            ('(n+(4+(if second then 4 else 5)))','(n+(4+(if second then 5 else 4)))'),
            ('(controller : s.regs 6=s.regs 0 ∧ s.regs 1=angle.raw.toBitVec)','(controller : True)')])
if __name__=='__main__':unittest.main()
