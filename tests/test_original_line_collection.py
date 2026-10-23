"""Ordered original-memory collection and conservative remaining capacity."""
import copy
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_line_collection as proof
HEADER='''import Doom.Proofs.OriginalLineCollection
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
'''

class LineCollectionTests(unittest.TestCase):
    lean=runtime.WeaponRuntimeTests.lean
    succeeds=runtime.WeaponRuntimeTests.succeeds

    def rejects(self,source):
        out=self.lean(source)
        self.assertNotEqual(out.returncode,0)
        self.assertIn('error:',out.stdout)
        for bad in ['maximum','timeout','object file','unknown module prefix']:
            self.assertNotIn(bad,out.stdout.lower())

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
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),out+'extra',out.replace('slots_apart','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_bytes_and_execution_contract(self):
        for key in ['cell','entry','finish','setup']:
            raw=copy.deepcopy(self.raw);code=bytearray(raw[key]);code[-1]^=1;raw[key]=code
            with self.subTest(key=key):self.rejects(proof.certificate(raw))
        self.mutations(self.source,[('steps≤281','steps≤280'),('s.regs 2+(2#32)','s.regs 2+(4#32)')])

    def test_dispatch_transports_existing_records(self):
        self.mutations(self.declaration('OriginalLineDispatchAppend','entry_encodes','s base resolve hits encoded safe'),[
            ('OriginalLineFinish.Encodes s.memory base resolve hits','True'),
            ('OriginalLineDispatch.Safe s (base+BitVec.ofNat 32 (12*i)+off)','True')])
        self.mutations(self.declaration('OriginalLineDispatchAppend','live_append',
            's trace line frac flags p v w h r id base resolve nonnegative clear capacity encoded atEnd pointer newSafe oldDispatch oldSafe'),[
            ('(capacity : r.collected.size<128)','(capacity : True)'),
            ('(nonnegative : ¬frac.raw<0)','(nonnegative : True)'),
            ('(clear : (flags &&& 4 != 0 && frac.raw<65536 && line.back.isNone)=false)','(clear : True)'),
            ('(atEnd : OriginalLineFinish.cursor s=base+BitVec.ofNat 32 (12*r.collected.size))','(atEnd : True)')])

    def test_slot_separation_and_capacity_need_their_bounds(self):
        self.mutations(self.declaration('OriginalLineCollection','slots_apart','base i j hi hj ne a b ha hb'),[
            ('(hi : i<128)','(hi : True)'),('(ne : i≠j)','(ne : True)'),('(ha : a∈[(0#32),4,8])','(ha : True)')])
        self.mutations(self.declaration('OriginalLineCollection','capacity','s base resolve hits reserve h'),[
            ('Tracks s base resolve hits (reserve+1)','Tracks s base resolve hits reserve')])

    def test_append_preserves_exact_order_and_consumes_one_reserve(self):
        self.mutations(self.declaration('OriginalLineCollection','append',
            's trace line frac flags p v w ready r id base resolve reserve tracked layout nonnegative clear pointer'),[
            ('(layout : Layout s base)','(layout : True)'),
            ('(r.collected.push ⟨frac,true,id⟩) reserve','r.collected reserve'),
            ('(pointer : resolve ⟨frac,true,id⟩=p)','(pointer : True)')])

    def test_nonappend_visits_preserve_records_and_cursor(self):
        self.mutations(self.declaration('OriginalLineCollection','preserve','s t base resolve hits reserve h cursor memory'),[
            ('OriginalLineFinish.cursor t=OriginalLineFinish.cursor s','True'),
            ('load32 t.memory (slot base i off)=load32 s.memory (slot base i off)','True')])
        self.mutations(self.declaration('OriginalLineCollection','duplicate','s base resolve hits reserve h last seen'),[
            ('OriginalLineCell.already (OriginalLineCell.header s).core','True')])
        self.mutations(self.declaration('OriginalLineCollection','rejected','s trace line p v w ready base resolve hits reserve h layout cursor'),[
            ('OriginalLineDispatch.Safe s (0x2c028#32)','True'),('(layout : Layout s base)','(layout : True)')])

    def test_nonempty_append_then_duplicate_in_both_geometry_branches(self):
        source=(ROOT/'tests/reference/original-line-collection.lean').read_text()
        self.mutations(source,[('=(123#32)','=(124#32)'),('=(0x700818#32)','=(0x70080c#32)')])

    def test_original_mapping_and_relocations(self):
        import json
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,self.profile)
        self.assertEqual(proof.extraction.extract(binary,self.profile,self.spec),self.raw)
        bad=copy.deepcopy(self.spec);bad['units']['finish']['relocations']=[]
        with self.assertRaises(ValueError):proof.extraction.extract(binary,self.profile,bad)

if __name__=='__main__':unittest.main()
