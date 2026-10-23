"""Original comparator byte folding, preservation, and isolated semantics."""
import copy,json,re,unittest
from pathlib import Path
import test_e1m1_aim_texture_table as prior
import verify_e1m1_aim_texture_fold as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.OriginalTextureFold\n'+proof.HEADER+'\nset_option backward.isDefEq.respectTransparency false\nset_option maxRecDepth 32768\nset_option maxHeartbeats 1600000\nopen X86ByteRoutine OriginalTextureFold\n'
class AimTextureFoldTests(unittest.TestCase):
    lean=prior.AimTextureTableTests.lean
    succeeds=prior.AimTextureTableTests.succeeds
    rejects=prior.AimTextureTableTests.rejects
    mutations=prior.AimTextureTableTests.mutations
    def test_certificate_strict_audit_and_authenticated_byte_mutation(self):
        data,_=proof.pinned_data();_,_,raw=proof.extracted()
        source=proof.certificate(data,raw);output=self.succeeds(source);proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('ExtractedAimTextureFold.fold_checked','missing'),output.replace('X86ByteRoutine.run_lift','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        self.rejects(source.replace('0x80,0xf9,0x41,0x72','0x80,0xf9,0x42,0x72'))
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
        self.assertEqual([n for n,_ in proof.SEMANTICS],re.findall(r'^theorem (\w+) ',(ROOT/'Doom/Verification/X86ByteRoutine.lean').read_text(),re.M))
    def test_ascii_boundaries_and_idempotence(self):
        self.succeeds(HEADER+'''
example : [0,64,65,90,91,127,128,255].map (fun n => (lower (BitVec.ofNat 8 n)).toNat) =
    [0,64,97,122,91,127,128,255] := by decide +kernel
example (b : BitVec 8) : lower (lower b)=lower b := lower_idempotent b
example (b : BitVec 8) : lower b=(if 65≤b.toNat ∧ b.toNat≤90 then b+32 else b) := lowercase_spec b
''')
    def test_byte_decoder_forms_and_unsupported_forms(self):
        self.succeeds(HEADER+'''
example : X86ByteRoutine.decode [0x80,0xfd,0x41]=some (.compareImmediate 5 65,[]) ∧
    X86ByteRoutine.decode [0x80,0xc5,0x20]=some (.addImmediate 5 32,[]) ∧
    X86ByteRoutine.decode [0x38,0xe9]=some (.compareBytes 1 5,[]) ∧
    X86ByteRoutine.decode [0x77,0x03]=some (.base (.jumpAbove 3),[]) := by decide
example : X86ByteRoutine.decode [0x80,0xf9]=none ∧
    X86ByteRoutine.decode [0x38]=none := by decide
example : X86Routine.decode [0x80,0xc5,0x20]=none := by decide
''')
    def test_old_executions_embed_for_arbitrary_program_state_and_fuel(self):
        self.succeeds(HEADER+'''
example (p : X86Routine.Program) (exits : List Nat) (n : Nat) (s : X86Control.State) :
    X86ByteRoutine.run (liftProgram p) exits n s=X86Routine.run p exits n s := run_lift p exits n s
''')
    def test_real_blocks_and_both_bytes_preserved(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (f : Option Flags) :
    X86ByteRoutine.run OriginalTextureFold.program [0x419a6] 5 ⟨s,f,0x41999⟩=some (clResult s) := cl_execution s f
example (s : X86Memory.State) (f : Option Flags) :
    X86ByteRoutine.run OriginalTextureFold.program [0x419b3] 5 ⟨s,f,0x419a6⟩=some (chResult s) := ch_execution s f
example (s : X86Memory.State) :
    readByte (chResult (clResult s).core).core.regs 1=lower (readByte s.regs 1) ∧
    readByte (chResult (clResult s).core).core.regs 5=lower (readByte s.regs 5) := pair_values s
example (s : X86Memory.State) : (folded (folded s 1) 5).memory=s.memory := by rw [fold_memory,fold_memory]
''')
    def test_flags_include_unsigned_carry_and_signed_overflow(self):
        self.succeeds(HEADER+'''
example : (X86ByteRoutine.compare8 0 255).carry=some true ∧
    (X86ByteRoutine.compare8 128 1).overflow=true ∧
    (add8 255 1).carry=some true ∧ (add8 255 1).zero=true ∧
    (add8 127 1).overflow=true ∧ (add8 127 1).sign=true := by decide
''')
    def test_extraction_rejects_wrong_mapping_and_instructions(self):
        e=proof.extraction_support.extraction
        spec=json.loads((ROOT/'tests/reference/original-texture-fold.json').read_text());profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=e.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
        for field,value in [('file_offset','0x839ae'),('hex','90'+spec['units']['fold']['hex'][2:])]:
            bad=copy.deepcopy(spec);bad['units']['fold'][field]=value
            with self.assertRaises(ValueError):e.extract(binary,profile,bad)
if __name__=='__main__':unittest.main()
