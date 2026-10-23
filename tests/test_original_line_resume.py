"""Real callback resumption, initial-memory duplicate windows and sentinel RET."""
import copy
import json
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_line_resume as proof
HEADER='''import Doom.Proofs.E1M1LineResume
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
'''

class LineResumeTests(unittest.TestCase):
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

    def test_certificate_and_strict_axiom_audit(self):
        out=self.succeeds(self.source);proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('through_sentinel','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_bytes_and_execution_contract(self):
        for key,index in [('finish',94),('cell',55),('cell',57),('cell',60),('cell',67),
                          ('lineEntry',0),('lineReturn',1),('lineReturn',7),('lineReturn',9)]:
            raw=copy.deepcopy(self.raw);code=bytearray(raw[key]);code[index]^=1;raw[key]=code
            with self.subTest(key=key,index=index):self.rejects(proof.certificate(raw))
        for old,new in [('n≤5','n≤4'),('⟨s,f,0x2c578⟩','⟨s,f,0x2c57a⟩')]:
            self.rejects(self.source.replace(old,new))

    def test_initial_memory_window_supplies_all_duplicate_conditions(self):
        source=HEADER+'''open OriginalLineResume
attribute [local irreducible] Duplicates SeenAt
example (n : Nat) (s : X86Control.State)
    (window : ∀ i<n, SeenAt s.core.memory (s.core.regs 2+BitVec.ofNat 32 (2*i))) :
    Duplicates n s := duplicates_from_memory n s window
'''
        self.succeeds(source)
        self.rejects(source.replace('SeenAt s.core.memory (s.core.regs 2+BitVec.ofNat 32 (2*i))','True'))
        self.rejects(source.replace('BitVec.ofNat 32 (2*i)','BitVec.ofNat 32 i'))

    def test_duplicate_loop_and_sentinel_require_their_contracts(self):
        source=HEADER+'''open OriginalLineResume
attribute [local irreducible] skipMany
example (n : Nat) (s : X86Control.State) (atHeader : s.pc=0x2c57f)
    (window : ∀ i<n, SeenAt s.core.memory (s.core.regs 2+BitVec.ofNat 32 (2*i)))
    (last : load16 s.core.memory (s.core.regs 2+BitVec.ofNat 32 (2*n))=(0xffff#16)) :
    ∃ steps≤10*n+7, X86Routine.Prefix program [] steps s
      (OriginalLineBounds.returned (OriginalLineCell.header (skipMany n s).core).core) :=
  through_sentinel n s atHeader window last
'''
        self.succeeds(source)
        for old,new in [('steps≤10*n+7','steps≤10*n+6'),('s.pc=0x2c57f','True'),
                        ('SeenAt s.core.memory (s.core.regs 2+BitVec.ofNat 32 (2*i))','True'),
                        ('=(0xffff#16)', '=(0xfffe#16)')]:
            self.rejects(source.replace(old,new))

    def test_callback_cursor_and_return_require_separation(self):
        source=HEADER+'''open OriginalLineResume
attribute [local irreducible] result OriginalLineFinish.result
example (s : X86Memory.State) (list : Word)
    (ret : load32 s.memory (s.regs 4+(36#32))=(0x2c578#32))
    (saved : load32 s.memory (s.regs 4+(24#32))=list)
    (safe : ∀ a∈[s.regs 4+(24#32),s.regs 4+(36#32)],
      ∀ w∈[OriginalLineFinish.cursor s,OriginalLineFinish.cursor s+(4#32),OriginalLineFinish.cursor s+(8#32),(0x2c028#32)], Apart a w)
    (keepGoing : ¬(¬(s.regs 0).toInt<0 ∧ OriginalLineFinish.early s)) :
    (OriginalLineFinish.result s).pc=0x2c578 ∧
    (result (OriginalLineFinish.result s).core).pc=0x2c57f ∧
    (result (OriginalLineFinish.result s).core).core.regs 2=list+(2#32) :=
  finish_continue s list ret saved safe keepGoing
'''
        self.succeeds(source)
        for old,new in [('Apart a w','True'),('list+(2#32)','list+(4#32)'),
                        ('load32 s.memory (s.regs 4+(36#32))=(0x2c578#32)','True'),
                        ('¬(¬(s.regs 0).toInt<0 ∧ OriginalLineFinish.early s)','True')]:
            self.rejects(source.replace(old,new))

    def test_numeric_and_nonvacuous_window_fixtures(self):
        source=(ROOT/'tests/reference/original-line-resume.lean').read_text();self.succeeds(source)
        for old,new in [('regs 2=(3#32)','regs 2=(5#32)'),('steps≤37','steps≤36'),
                        ('regs 7=(777#32)','regs 7=(0#32)'),('regs 4=(0xfffffe29#32)','regs 4=(0xfffffe2d#32)'),
                        ('(0x600474,99)','(0x600474,98)')]:
            self.assertIn(old,source);self.rejects(source.replace(old,new,1))

    def test_firing_prefix_joins_finite_list_return(self):
        # Copy only the declaration, replacing its proof by the established theorem.
        text=(ROOT/'Doom/Proofs/E1M1LineResume.lean').read_text()
        declaration=text[text.index('theorem line_list_return_execution'):]
        declaration=declaration[:declaration.index(' := by')]
        source=HEADER+'open E1M1LineResume\n'+declaration.replace('theorem line_list_return_execution','example',1)+''' :=
  line_list_return_execution gun s f c h ox oy sx sy ex ey geometry layout xout yout okX okY safe count atHeader window last
'''
        self.succeeds(source)
        for old,new in [('steps≤656+10*count','steps≤655+10*count'),
                        ('(resumed gun s).pc=0x2c57f','True'),
                        ('E1M1LineFraction.Ready (E1M1LineSecondPoint.lineTest gun s)','True')]:
            self.rejects(source.replace(old,new))

    def test_original_mapping_and_relocations(self):
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,self.profile)
        self.assertEqual(proof.extraction.extract(binary,self.profile,self.spec),self.raw)
        for key in self.spec['units']:
            bad=copy.deepcopy(self.spec);bad['units'][key]['file_offset']='0x0'
            with self.assertRaises(ValueError):proof.extraction.extract(binary,self.profile,bad)
        bad=copy.deepcopy(self.spec);bad['units']['cell']['relocations']=[]
        with self.assertRaises(ValueError):proof.extraction.extract(binary,self.profile,bad)

if __name__=='__main__':unittest.main()
