"""Saved caller frame through the one-image side loop and cleanup."""
import sys, unittest
sys.setrecursionlimit(max(sys.getrecursionlimit(),10000))
import test_e1m1_aim_side_loop as prior
ROOT=prior.ROOT
HEADER='import Doom.Proofs.E1M1AimSideStack\nopen Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary E1M1AimTextureCatalog E1M1AimPinnedCatalog E1M1AimSideLoop E1M1AimSideStack\n'
class AimSideCleanupTests(unittest.TestCase):
    lean=prior.AimSideLoopTests.lean
    succeeds=prior.AimSideLoopTests.succeeds
    rejects=prior.AimSideLoopTests.rejects
    def test_saved_upper_stack_from_one_image(self):
        self.assertTrue((ROOT/'Doom/Proofs/E1M1AimSideStack.lean').exists(),'upper-stack loop frame missing')
        text=HEADER+'''
example (l : LayoutData) (layout : Layout l) (s : X86Memory.State)
    (f : Option Flags) (initial : Incoming l s) (upper : UpperStack l layout)
    (off : Nat) (low : 4≤off) (high : off+4≤36) :
    load32 (states s f 648).core.memory (l.sp+BitVec.ofNat 32 off)=
      load32 s.memory (l.sp+BitVec.ofNat 32 off) :=
  upper_preserved l layout s f initial upper off low high
'''
        self.succeeds(text)
        self.rejects(text.replace('(upper : UpperStack l layout)','(upper : True)'))
    def test_real_owned_free_and_caller_return(self):
        self.assertTrue((ROOT/'Doom/Proofs/OriginalSideCleanup.lean').exists(),'real cleanup execution missing')
        self.succeeds('''import Doom.Proofs.OriginalSideCleanup
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary OriginalSideCleanup
example (s : X86Memory.State) (f : Option Flags) (h : Ready s) :
    ∃ k≤40, X86Routine.Prefix program [] k ⟨s,f,0x2e4dd⟩ (result s) :=
  execution s f h
''')
    def test_loop_cleanup_from_initial_owned_image(self):
        self.assertTrue((ROOT/'Doom/Proofs/E1M1AimSideCleanup.lean').exists(),'initial-image loop/cleanup composition missing')
        self.succeeds('''import Doom.Proofs.E1M1AimSideCleanup
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1AimSideLoop E1M1AimSideStack E1M1AimSideCleanup
example (l : LayoutData) (layout : Layout l) (h : Heap l) (s : X86Memory.State)
    (f : Option Flags) (initial : Incoming l s) (upper : UpperStack l layout)
    (placement : Placement l layout h) (image : Image l h s.memory)
    (raw : load32 s.memory (l.sp+4)=l.raw) :
    ∃ k≤648*(3*(202*2147483647+30)+36)+40,
      X86ByteRoutine.Prefix program [] k ⟨s,f,0x2e46a⟩
        (OriginalSideCleanup.result (states s f 648).core) :=
  execution l layout h s f initial upper placement image raw
''')
    def test_return_observations_and_output_frame(self):
        self.succeeds('''import Doom.Proofs.E1M1AimSideCleanup
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1AimSideLoop E1M1AimSideStack E1M1AimSideCleanup
example (l : LayoutData) (layout : Layout l) (h : Heap l) (s : X86Memory.State)
    (f : Option Flags) (initial : Incoming l s) (upper : UpperStack l layout)
    (placement : Placement l layout h) (image : Image l h s.memory)
    (raw : load32 s.memory (l.sp+4)=l.raw) :
    let t := OriginalSideCleanup.result (states s f 648).core
    Outputs l 648 t.core.memory ∧ t.pc=(load32 s.memory (l.sp+32)).toNat ∧
      t.core.regs 4=l.sp+36 ∧
      (∀ r off, (r,off)∈savedRegisters → t.core.regs r=load32 s.memory (l.sp+off)) :=
  observations l layout h s f initial upper placement image raw
''')
    def test_authenticated_cleanup_certificate(self):
        self.assertTrue((ROOT/'scripts/verify_e1m1_aim_side_cleanup.py').exists(),'cleanup byte certificate missing')
        import verify_e1m1_aim_side_cleanup as proof
        data,_,raw=proof.inputs()
        source=proof.certificate(data,raw)
        output=self.succeeds(source);proof.audit(output)
        for bad in [output+'extra',output.replace('Quot.sound','sorryAx'),output.replace('observations_checked','absent')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for old,new in [('0x8b,0x44,0x24,0x4,0xe8','0x8b,0x44,0x24,0x8,0xe8'),
                        ('0x81,0x7a,0xc,0x11,0x4a','0x81,0x7a,0xc,0x12,0x4a')]:
            self.assertIn(old,source);self.rejects(source.replace(old,new,1))
        import copy
        units=proof.cleanup_data()[1]
        for field,value in [('file_offset','0x704f2'),('code_offset','0x2e4de')]:
            bad=copy.deepcopy(units);bad['cleanup'][field]=value
            with self.assertRaises(ValueError):proof.cleanup_data({'units':bad})
        bad=copy.deepcopy(units);bad['free']['relocations'][0]['object']=1
        with self.assertRaises(ValueError):proof.cleanup_data({'units':bad})
    def test_independent_owned_cleanup_and_connected_loop(self):
        import verify_e1m1_aim_side_cleanup as proof
        self.assertTrue(hasattr(proof,'cross_check'),'independent cleanup oracle missing')
        import subprocess,os,json
        run=subprocess.run([str(ROOT/'.tools/x86-check/bin/python'),'-c',
          'import verify_e1m1_aim_side_cleanup as p,json; print(json.dumps(p.cross_check()))'],
          cwd=ROOT,env={**os.environ,'PYTHONPATH':'scripts'},capture_output=True,text=True,timeout=300)
        self.assertEqual(run.returncode,0,run.stdout+run.stderr)
        result=json.loads(run.stdout)
        self.assertEqual(result['loop']['sides'],648)
        self.assertEqual(result['loop']['cleanup_instructions'],33)
        self.assertEqual(result['local']['cases'],128)
        self.assertTrue(result['loop']['ordered_cleanup_writes'])
        self.assertTrue(result['local']['all_registers'])
    def test_required_incoming_guards(self):
        import verify_e1m1_aim_side_cleanup as p
        decl,args=p.contract('E1M1AimSideCleanup','execution')
        source='import Doom.Proofs.E1M1AimSideCleanup\n'+p.HEADER+decl.replace('theorem execution','example',1)+' := by\n  exact E1M1AimSideCleanup.execution '+args+'\n'
        self.succeeds(source)
        for guard in ['(upper : UpperStack l layout)',
          '(placement : Doom.Proofs.E1M1AimSideCleanup.Placement l layout h)',
          '(image : Doom.Proofs.E1M1AimSideCleanup.Image l h s.memory)',
          '(raw : load32 s.memory (l.sp+4)=l.raw)']:
            self.assertIn(guard,source)
            self.rejects(source.replace(guard,guard.split(':')[0]+': True)'))
    def test_initial_cache_owner_cell_survives_loop(self):
        self.succeeds('''import Doom.Proofs.E1M1AimSideCleanup
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1AimSideLoop E1M1AimSideStack E1M1AimSideCleanup
example (l : LayoutData) (layout : Layout l) (h : Heap l) (s : X86Memory.State)
    (f : Option Flags) (initial : Incoming l s) (placement : Placement l layout h)
    (image : Image l h s.memory) :
    load32 (states s f 648).core.memory h.user=l.raw :=
  cache_owned l layout h s f initial placement image
''')
if __name__=='__main__':unittest.main()
