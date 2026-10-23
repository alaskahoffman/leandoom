"""Original collection-to-selector call and count must stay tied to real memory."""
import re,unittest
from pathlib import Path
import test_e1m1_intercept_gate as prior
import verify_e1m1_traversal_entry as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='''import Doom.Proofs.E1M1TraversalEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1CellWalkInvariant (Context Cell Common State)
open E1M1MixedCellWalk (inside Admitted budget bound history)
open E1M1GridRoute (sourceRoute)
open E1M1QueryCollection (path Entry)
open OriginalInterceptSetup
attribute [local irreducible] load32 store32
'''
class TraversalEntryTests(unittest.TestCase):
    lean=prior.InterceptGateTests.lean
    succeeds=prior.InterceptGateTests.succeeds
    rejects=prior.InterceptGateTests.rejects
    mutations=prior.InterceptGateTests.mutations

    def contract(self,module,name,args):
        s=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=re.search(r'^theorem '+name+r'(?: | :)',s,re.M).start()
        decl=s[a:s.index(' := by',a)]
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'

    def test_certificate_and_original_bytes(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),33)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('TraversalEntry.execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for m,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+)(?: | :)',(ROOT/f'Doom/Proofs/{m}.lean').read_text(),re.M))
        for unit,index,value in [('interceptSetup',44,0x46),('interceptHandoff',3,64)]:
            b=bytearray(raw[unit]);self.assertNotEqual(b[index],value);b[index]=value
            changed=dict(raw);changed[unit]=bytes(b);self.rejects(proof.certificate(data,changed))

    def test_count_requires_real_cursor_and_bound(self):
        self.mutations(self.contract('OriginalInterceptSetup','count_execution','s f n bound limit'),[
            ('(bound : n≤128)','(bound : True)'),
            ('(limit : s.regs 1=E1M1MinimumScan.address n)','(limit : True)'),
            ('(ready s n)','(ready s (n+1))'),
            ('⟨s,f,0x2c822⟩','⟨s,f,0x2c83a⟩')])

    def test_setup_requires_static_cursor_separation(self):
        self.mutations(self.contract('E1M1InterceptSetup','execution','s f n bound limit safe'),[
            ('(safe : Safe (s.regs 4) 0x2c028)','(safe : True)'),
            ('(limit : load32 s.memory 0x2c028=E1M1MinimumScan.address n)','(limit : True)'),
            ('[] 23','[] 22'),
            ('⟨s,f,0x2cafd⟩','⟨s,f,0x2cb06⟩')])

    def test_frame_protects_all_six_slots(self):
        self.mutations(self.contract('E1M1InterceptSetup','frame','s a safe'),[
            ('(safe : Safe (s.regs 4) a)','(safe : True)'),
            ('load32 s.memory a','load32 s.memory (a+4)')])
        s=(ROOT/'Doom/Proofs/E1M1InterceptSetup.lean').read_text()
        s=s[:s.index('theorem cursor_read')]+ '\nend Doom.Proofs.E1M1InterceptSetup\n'
        s=s.replace('namespace Doom.Proofs.E1M1InterceptSetup','namespace Doom.Proofs.ScratchSetup').replace('end Doom.Proofs.E1M1InterceptSetup','end Doom.Proofs.ScratchSetup')
        self.mutations(s,[('[(4#32),8,12,16,20,24]','[(4#32),8,12,16,20]')])

    def test_collection_bridge_requires_actual_invariant_and_exit(self):
        self.mutations(self.contract('E1M1TraversalEntry','from_collection','q s r seen state pc separated'),[
            ('(state : State q s r seen)','(state : True)'),
            ('(pc : s.pc=0x2cafd)','(pc : True)'),
            ('(separated : Protected q)','(separated : True)'),
            ('if r.collected.size=0 then 0x2c887 else 0x2c841','if r.collected.size=0 then 0x2c841 else 0x2c887')])

    def test_whole_query_connection_requires_entry_and_protection(self):
        args='q pick s f sx sy ex ey entry profile xout yout okX okY common height statics scenes payloads separated room'
        self.mutations(self.contract('E1M1TraversalEntry','execution',args),[
            ('(entry : Entry q s sx sy ex ey)','(entry : True)'),
            ('(separated : Protected q)','(separated : True)'),
            ('⟨s,f,0x2c8a0⟩','⟨s,f,0x2cafd⟩')])

    def test_zero_count_wrap_and_capacity(self):
        self.succeeds(HEADER+'''
def blank : X86Memory.State := ⟨fun _ => 0,fun _ => 0⟩
example : (ready blank 0).pc=0x2c887 ∧ (ready blank 0).core.regs 6=0xffffffff := by decide +kernel
example : (ready blank 1).pc=0x2c841 ∧ (ready blank 1).core.regs 6=0 := by decide +kernel
example : (ready blank 128).pc=0x2c841 ∧ (ready blank 128).core.regs 6=127 := by decide +kernel
example : X86Routine.decode [0x4e,0x85,0xc0]=some (.addImmediate 6 (-1),[0x85,0xc0]) := by decide +kernel
example (s : X86Memory.State) (f : Option Flags) :
    X86Routine.execute (.addImmediate 6 (-1)) ⟨s,f,0x2c83d⟩=some ⟨put s 6 (s.regs 6-1),none,0x2c83d⟩ := by
  simp [X86Routine.execute,BitVec.sub_eq_add_neg]
''')
if __name__=='__main__':unittest.main()
