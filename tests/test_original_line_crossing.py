"""Callback-entry contracts across both side tests, scratch writes and live append."""
import copy
import json
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_line_crossing as proof
HEADER='''import Doom.Proofs.E1M1LineCrossing
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
'''
CONTEXT='''open OriginalLineCrossing
variable (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
  (p v w : Word) (h : Inputs s trace line p v w)
include h
'''
DATA='''variable (frac : Fixed) (flags : Nat) (data : TailData s trace line frac flags p v)
include data
'''

class LineCrossingTests(unittest.TestCase):
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

    def declaration(self,name,args,data=False):
        text=(ROOT/'Doom/Proofs/OriginalLineCrossing.lean').read_text()
        decl=text[text.index('theorem '+name):].split(' :=',1)[0]
        return HEADER+CONTEXT+(DATA if data else '')+decl.replace('theorem '+name,'example',1)+' :=\n  '+name+' '+args+'\n'

    def mutations(self,source,pairs):
        self.succeeds(source)
        for old,new in pairs:
            self.assertIn(old,source)
            with self.subTest(old=old):self.rejects(source.replace(old,new))

    def test_certificate_and_strict_axiom_audit(self):
        out=self.succeeds(self.source);proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('saved_cursor','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_bytes_and_entry_execution_contract(self):
        for key in self.raw:
            raw=copy.deepcopy(self.raw);code=bytearray(raw[key]);code[-1]^=1;raw[key]=code
            with self.subTest(key=key):self.rejects(proof.certificate(raw))
        self.mutations(self.source,[('n≤270','n≤269'),('⟨s,f,0x2c5f0⟩','⟨s,f,0x2c5f1⟩'),
            ('OriginalLineCrossing.Inputs s trace line p v w','True'),
            ('OriginalLineCrossing.TailData s trace line frac flags p v','True')])

    def test_memory_and_geometry_transport_require_separation(self):
        self.mutations(self.declaration('frame','s trace line p v w h a cursor safe'),
            [('Protected s a','True')])
        self.mutations(self.declaration('fraction_inputs','s trace line p v w h safe'),
            [('ScratchSafe s a','True')])

    def test_saved_cursor_comes_from_prologue_and_continuation_is_exact(self):
        self.mutations(self.declaration('saved_cursor','s trace line p v w h'),
            [('load32 (tested s).core.memory (s.regs 4-(12#32))=s.regs 2','load32 (tested s).core.memory (s.regs 4-(12#32))=s.regs 3')])
        self.mutations(self.declaration('continued','s trace line p v w h frac flags data savedSafe keepGoing',True),
            [('s.regs 2+(2#32)','s.regs 2+(4#32)'),('s.regs 4+(4#32)','s.regs 4+(8#32)'),
             ('OriginalLineTail.RecordSafe s (s.regs 4-(12#32))','True')])

    def test_live_append_uses_entry_memory_and_capacity(self):
        self.mutations(self.declaration('live_append','s trace line p v w h frac flags data r id base resolve nonnegative clear capacity encoded atEnd pointer newSafe oldSafe',True),
            [('r.collected.size<128','r.collected.size≤128'),
             ('OriginalLineFinish.Encodes s.memory base resolve r.collected','True'),
             ('Protected s (base+BitVec.ofNat 32 (12*i)+off)','True')])

    def test_firing_join_starts_before_crossing_tests(self):
        text=(ROOT/'Doom/Proofs/E1M1LineCrossing.lean').read_text()
        decl=text[text.index('theorem callback_execution'):].split(' :=',1)[0]
        source=HEADER+'open E1M1LineCrossing\n'+decl.replace('theorem callback_execution','example',1)+''' :=
  callback_execution gun s f c h ox oy sx sy ex ey geometry layout xout yout okX okY entry trace line p v w inputs frac flags data
'''
        self.mutations(source,[('steps≤649','steps≤648'),('(boundary gun s).pc=0x2c5f0','True')])

    def test_both_branch_fixtures_and_nonvacuous_inputs(self):
        source=(ROOT/'tests/reference/original-line-crossing.lean').read_text()
        self.mutations(source,[('regs 2=(24#32)','regs 2=(26#32)'),
            ('=(0x60080c#32)','=(0x600818#32)'),('=(43690#32)','=(43691#32)')])

    def test_original_mapping_and_relocations(self):
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,self.profile)
        self.assertEqual(proof.extraction.extract(binary,self.profile,self.spec),self.raw)
        for key in self.spec['units']:
            bad=copy.deepcopy(self.spec);bad['units'][key]['file_offset']='0x0'
            with self.assertRaises(ValueError):proof.extraction.extract(binary,self.profile,bad)
        bad=copy.deepcopy(self.spec);bad['units']['entry']['relocations']=[]
        with self.assertRaises(ValueError):proof.extraction.extract(binary,self.profile,bad)

if __name__=='__main__':unittest.main()
