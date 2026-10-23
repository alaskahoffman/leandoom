"""Pre-helper preservation, live append and actual crossing-list return contracts."""
import copy
import json
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_line_tail as proof
HEADER='''import Doom.Proofs.E1M1LineTail
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
'''

class LineTailTests(unittest.TestCase):
    lean=runtime.WeaponRuntimeTests.lean
    succeeds=runtime.WeaponRuntimeTests.succeeds

    def rejects(self,source):
        result=self.lean(source)
        self.assertNotEqual(result.returncode,0)
        self.assertIn('error:',result.stdout)
        for bad in ['maximum','timeout','object file','unknown module prefix']:
            self.assertNotIn(bad,result.stdout.lower())

    def setUp(self):
        self.spec,self.profile,self.raw=proof.extracted()
        self.source=proof.certificate(self.raw)

    def declaration(self,module,name,args):
        text=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        decl=text[text.index('theorem '+name):].split(' :=',1)[0]
        return HEADER+'open '+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+name+' '+args+'\n'

    def mutations(self,source,pairs):
        self.succeeds(source)
        for old,new in pairs:
            self.assertIn(old,source)
            with self.subTest(old=old):self.rejects(source.replace(old,new))

    def test_certificate_and_strict_axiom_audit(self):
        out=self.succeeds(self.source);proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('live_append','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_bytes_and_execution_contract(self):
        for key in self.raw:
            raw=copy.deepcopy(self.raw);code=bytearray(raw[key]);code[-1]^=1;raw[key]=code
            with self.subTest(key=key):self.rejects(proof.certificate(raw))
        self.mutations(self.source,[('n≤108','n≤107'),('⟨s,f,0x2c691⟩','⟨s,f,0x2c692⟩'),
            ('OriginalLineTail.Layout s','True')])

    def test_pre_helper_frame_and_seen_require_protection(self):
        self.mutations(self.declaration('OriginalLineTail','frame','s a cursor safe'),
            [('Protected s a','True'),('StackSafe s (0x2c028#32)','True')])
        self.mutations(self.declaration('OriginalLineTail','preserves_seen','s p cursor safe'),
            [('Protected s a','True')])

    def test_live_append_requires_initial_encoding_capacity_and_safety(self):
        source=self.declaration('OriginalLineTail','live_append',
            's trace line frac flags p v base h r id resolve cursorSafe nonnegative clear capacity encoded atEnd pointer newSafe oldSafe')
        self.mutations(source,[('r.collected.size<128','r.collected.size≤128'),
            ('OriginalLineFinish.Encodes s.memory base resolve r.collected','True'),
            ('Protected s (base+BitVec.ofNat 32 (12*i)+off)','True'),
            ('resolve ⟨frac,true,id⟩=p','True'),('¬frac.raw<0','True')])

    def test_crossing_suffix_and_join_require_initial_window(self):
        args='s f trace line frac flags p v list h layout ret saved savedSafe keepGoing count window windowSafe last lastSafe'
        self.mutations(self.declaration('OriginalLineTail','through_sentinel',args),
            [('steps≤115+10*count','steps≤114+10*count'),('Protected s (list+BitVec.ofNat 32 (2*(count+1)))','True'),
             ('OriginalLineResume.SeenAt s.memory (list+BitVec.ofNat 32 (2*(i+1)))','True')])
        args='gun s f c h ox oy sx sy ex ey geometry layout xout yout okX okY atCrossing trace line frac flags p v list inputs tailLayout ret saved savedSafe keepGoing count window windowSafe last lastSafe'
        self.mutations(self.declaration('E1M1LineTail','crossing_list_return_execution',args),
            [('steps≤656+10*count','steps≤655+10*count'),('(boundary gun s).pc=0x2c691','True')])

    def test_numeric_and_nonvacuous_fixtures(self):
        source=(ROOT/'tests/reference/original-line-tail.lean').read_text()
        self.mutations(source,[('regs 2=(0x600303#32)','regs 2=(0x600305#32)'),
            ('=(0x60080d#32)','=(0x600819#32)'),('=(32768#32)','=(32769#32)')])

    def test_original_mapping_and_relocations(self):
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,self.profile)
        self.assertEqual(proof.extraction.extract(binary,self.profile,self.spec),self.raw)
        for key in self.spec['units']:
            bad=copy.deepcopy(self.spec);bad['units'][key]['file_offset']='0x0'
            with self.assertRaises(ValueError):proof.extraction.extract(binary,self.profile,bad)
        bad=copy.deepcopy(self.spec);bad['units']['setup']['relocations']=[]
        with self.assertRaises(ValueError):proof.extraction.extract(binary,self.profile,bad)

if __name__=='__main__':unittest.main()
