"""Callback entry must use the original target and intact records/return frame."""
import re,unittest
from pathlib import Path
import test_e1m1_query_dispatch as prior
import verify_e1m1_query_callback as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER=prior.HEADER.replace('import Doom.Proofs.E1M1QueryDispatch','import Doom.Proofs.E1M1QueryCallback')+'''
open E1M1CallbackEntry (Outcome Ready)
open E1M1QueryCallback (CallbackSafe)
open OriginalInterceptGate (called saved)
'''

class QueryCallbackTests(unittest.TestCase):
    lean=prior.QueryDispatchTests.lean
    succeeds=prior.QueryDispatchTests.succeeds
    rejects=prior.QueryDispatchTests.rejects
    mutations=prior.QueryDispatchTests.mutations

    def contract(self,module,name,args):
        s=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        a=re.search(r'^theorem '+name+r'(?: | :)',s,re.M).start()
        decl=s[a:s.index(' := by',a)]
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'

    def test_certificate_bytes_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),33)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('QueryCallback.execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for m,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+)(?: | :)',(ROOT/f'Doom/Proofs/{m}.lean').read_text(),re.M))
        altered=dict(raw);b=bytearray(raw['interceptGate']);self.assertEqual(b[13],0x14)
        b[13]=0x10;altered['interceptGate']=bytes(b)
        self.rejects(proof.certificate(data,altered))

    def test_dispatch_requires_real_records_and_slot_separation(self):
        args='s hits resolve bounded limit encoded maximum pc targetSafe recordSafe'
        self.mutations(self.contract('E1M1CallbackEntry','dispatch',args),[
            ('(encoded : OriginalLineFinish.Encodes s.core.memory 0x2ba20 resolve hits)','(encoded : True)'),
            ('(targetSafe : Apart (s.core.regs 4) 0x2c028)','(targetSafe : True)'),
            ('(s.core.regs 4-4))','(s.core.regs 4-8))'),
            ('Outcome hits resolve (load32 s.core.memory (s.core.regs 4))','Outcome hits resolve 0x2b760')])

    def test_final_stores_require_both_separations(self):
        self.mutations(self.contract('E1M1CallbackEntry','frame','s f a cursor stack'),[
            ('(cursor : Apart a 0x2c028)','(cursor : True)'),
            ('(stack : Apart a (s.regs 4-4))','(stack : True)')])
        self.mutations(self.contract('E1M1CallbackEntry','control','s f safe'),[
            ('(safe : Apart (s.regs 4) 0x2c028)','(safe : True)'),
            ('=0x2c86d','=0x2cb0b')])

    def test_whole_query_preserves_entry_target_and_full_records(self):
        args='q pick s f sx sy ex ey entry profile xout yout okX okY common height statics scenes payloads separated callbackSafe room'
        self.mutations(self.contract('E1M1QueryCallback','execution',args),[
            ('(callbackSafe : CallbackSafe q s)','(callbackSafe : True)'),
            ('(load32 s.memory (q.sp-44))','(load32 s.memory (q.sp-40))'),
            ('(q.sp-136) out','(q.sp-132) out')])
        self.mutations(self.contract('E1M1CallbackEntry','selected_record','hits resolve target sp out ready'),[
            ('(ready : Ready hits resolve target sp out)','(ready : True)'),
            ('(out.core.regs 0) hits[j]','(out.core.regs 0+4) hits[j]')])

    def test_aim_identity_comes_from_initial_argument(self):
        self.mutations(self.contract('E1M1QueryCallback','aim_argument','s separated'),[
            ('(separated : OriginalAimSetup.Separated s)','(separated : True)'),
            ('=0x2b760','=0x2b761')])
        self.mutations(self.contract('E1M1QueryCallback','specialize_aim','q s hits resolve out stack argument outcome'),[
            ('(argument : load32 s.memory (s.regs 4+8)=0x2b760)','(argument : True)'),
            ('(stack : s.regs 4=q.sp-52)','(stack : True)')])

    def test_actual_aliasing_counterexamples_and_intact_record(self):
        self.succeeds(HEADER+'''
open OriginalInterceptGate (called saved)
def machine (sp : Word) : X86Memory.State :=
  ⟨fun r => if r=4 then sp else if r=1 then 0x12345678 else if r=3 then 0x2ba20 else 0,
    store32 (store32 (fun _ => 0) sp 0x2b760) 0x2ba20 42⟩
def out (sp : Word) := called (saved (machine sp)) none
example : (out 0x40000).pc=0x2b760 ∧ (out 0x40000).core.regs 0=0x2ba20 ∧
    load32 (out 0x40000).core.memory 0x2ba20=42 ∧
    load32 (out 0x40000).core.memory 0x3fffc=0x2c86d := by decide +kernel
-- If the callback slot aliases the cursor, the gate really changes its target.
example : (out 0x2c028).pc=0x12345678 := by decide +kernel
-- If the return push overlaps a record, its fraction really is overwritten.
example : load32 (out 0x2ba24).core.memory 0x2ba20=0x2c86d := by decide +kernel
''')

if __name__=='__main__':unittest.main()
