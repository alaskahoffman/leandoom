"""Callback inputs must derive from initialized trace and original line memory."""
import re
import unittest
from pathlib import Path
import test_e1m1_firing_next_suffix as prior
import verify_e1m1_firing_next_geometry as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER=prior.HEADER.replace('import Doom.Proofs.E1M1FiringNextSuffix','import Doom.Proofs.E1M1FiringNextGeometry')
HEADER+='open E1M1ScanMemory (LineWords lineReads)\nopen E1M1ScanGeometry (linePointer)\nopen E1M1ScanContracts (candidate)\nopen E1M1NextCallbackReady (Ready)\n'
COMMON=prior.prior.previous.ARGS
FRAME=prior.prior.FULL+prior.prior.REST
NEXT=prior.prior.NEXT+' nextData nextInput traceSafe activeSafe'

class FiringNextGeometryTests(unittest.TestCase):
    lean=prior.FiringNextSuffixTests.lean
    succeeds=prior.FiringNextSuffixTests.succeeds
    rejects=prior.FiringNextSuffixTests.rejects
    mutations=prior.FiringNextSuffixTests.mutations

    def contract(self,module,name,args,section=False):
        return prior.FiringNextSuffixTests.contract(self,module,name,args,section).replace(prior.HEADER,HEADER,1)

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),29)
        self.assertEqual(len(data['cells']),828)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('FiringNextGeometry.execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_line_transport_requires_all_original_reads(self):
        self.mutations(self.contract('E1M1NextCallbackMemory','line_words','m n line p v w encoded keep'),[
            ('(encoded : LineWords m line p v w)','(encoded : True)'),
            ('(keep : ∀ a∈lineReads p v w, load32 n a=load32 m a)','(keep : True)'),
            ('LineWords n line p v w :=','LineWords n line p w v :=')])

    def test_callback_is_written_by_the_real_prologue(self):
        self.mutations(self.contract('E1M1NextCallbackMemory','caller_callback','s'),[
            ('s.regs 4-(12#32)','s.regs 4-(8#32)'),
            ('=(0x2c5f0#32)','=(0x2cab1#32)')])
        self.mutations(self.contract('E1M1NextCallbackMemory','callback_word',FRAME,True),[
            ('s.regs 4-(124#32)','s.regs 4-(120#32)')])

    def test_firing_data_requires_setup_and_full_lifetime_separation(self):
        self.mutations(self.contract('E1M1NextCallbackMemory','firing_frame',FRAME+' a setup safe',True),[
            ('(setup : E1M1PathMapFiring.Safe gun s a)','(setup : True)'),
            ('(safe : E1M1FiringMapState.Safe (s.regs 4) lines a)','(safe : True)')])

    def test_initialized_frame_is_not_old_firing_memory(self):
        self.mutations(self.contract('E1M1NextCallbackMemory','initialized_frame',FRAME+' a safe',True),[
            ('load32 (firstScan gun s).core.memory a','load32 s.memory a'),
            ('(safe : E1M1FiringMapState.Safe (s.regs 4) lines a)','(safe : True)')])
        self.mutations(self.contract('E1M1NextCallbackMemory','active',FRAME+' safe',True),[
            ('core.memory 0x2c024=0','core.memory 0x2c024=4')])

    def test_callback_branches_require_the_matching_side_decision(self):
        self.mutations(self.contract('E1M1NextCallbackReady','rejection','s lines trace c data ready i same'),[
            ('(ready : Ready s lines trace c data)','(ready : True)'),
            (').crosses=false',').crosses=true')])
        self.mutations(self.contract('E1M1NextCallbackReady','crossing','s lines trace c data ready i crosses'),[
            ('(ready : Ready s lines trace c data)','(ready : True)'),
            (').crosses=true',').crosses=false')])

    def test_joined_readiness_is_for_exact_suffix_and_trace(self):
        self.mutations(self.contract('E1M1FiringNextGeometry','execution',NEXT,True),[
            ('(nextInput : E1M1NextCallbackReady.Data gun s lines (path thing angle ox oy).trace\n      (E1M1DuplicateSuffix.tailCell nextCell) nextData)','(nextInput : True)'),
            ('(activeSafe : E1M1FiringMapState.Safe (s.regs 4) lines (0x2c024#32))','(activeSafe : True)'),
            ('Ready out.core lines (path thing angle ox oy).trace (E1M1DuplicateSuffix.tailCell nextCell) nextData',
             'Ready out.core lines (path thing angle ox oy).trace nextCell nextData'),
            ('steps≤467+281*c.ids.length+230*nodes.length','steps≤466+281*c.ids.length+230*nodes.length')])

    def test_new_inputs_do_not_assume_reached_callback_results(self):
        data=(ROOT/'Doom/Proofs/E1M1NextCallbackReady.lean').read_text().split('structure Data',1)[1].split('/-- Callback templates',1)[0]
        for reached in ['Ready','Prefix','OriginalLineCrossing.Inputs','OriginalLineReject.Inputs',
                        'E1M1FiringNextScan.result','E1M1FiringNextSuffix.result']:
            self.assertNotIn(reached,data)
        self.assertIn('LineWords s.memory',data)
        self.assertIn('Collision.interceptVector trace',data)

if __name__=='__main__':unittest.main()
