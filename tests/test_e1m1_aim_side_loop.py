"""One incoming side image; no per-iteration invariant premise."""
import sys, unittest
sys.setrecursionlimit(max(sys.getrecursionlimit(),10000))
import test_e1m1_aim_texture_catalog as prior
ROOT=prior.ROOT
HEADER='import Doom.Proofs.E1M1AimSideLoop\nopen Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary E1M1AimTextureCatalog E1M1AimPinnedCatalog E1M1AimSideLoop\n'
class AimSideLoopTests(unittest.TestCase):
    lean=prior.AimTextureCatalogTests.lean
    succeeds=prior.AimTextureCatalogTests.succeeds
    rejects=prior.AimTextureCatalogTests.rejects
    def test_body_register_progress(self):
        self.assertTrue((ROOT/'Doom/Proofs/E1M1AimSideLoop.lean').exists(),'side-loop module missing')
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (table : Word) (pointer : Nat → Word)
    (row : Fin 648) (ready : BodyReady s table pointer row) :
    (body s).core.regs 3=s.regs 3+30 ∧
    (body s).core.regs 2=s.regs 2+18 ∧
    (body s).core.regs 5=s.regs 5+1 ∧
    (body s).core.regs 4=s.regs 4 ∧
    (body s).core.regs 1=s.regs 1+30 ∧
    (body s).core.regs 7=s.regs 7+30 ∧
    (body s).core.regs 6=s.regs 6+30 := body_progress s table pointer row ready
''')
    def test_full_loop_from_one_image(self):
        self.succeeds(HEADER+'''
example (l : LayoutData) (placement : Layout l) (s : X86Memory.State)
    (f : Option Flags) (initial : Incoming l s) :
    (∃ k≤648*(3*(202*2147483647+30)+36),
      X86ByteRoutine.Prefix E1M1AimSideLookup.iterationProgram [] k
        ⟨s,f,0x2e46a⟩ (states s f 648)) ∧
    (states s f 648).pc=0x2e4dd ∧
    Outputs l 648 (states s f 648).core.memory ∧
    (∀ p, Persistent l p → load32 (states s f 648).core.memory p=load32 s.memory p) :=
  execution l placement s f initial
''')
    def test_pinned_raw_sector_image(self):
        self.assertTrue((ROOT/'Doom/Proofs/E1M1AimPinnedSides.lean').exists(),'authenticated raw-side specialization missing')
        self.succeeds('import Doom.Proofs.E1M1AimPinnedSides\n'+HEADER+'''
open E1M1AimPinnedSides
example (l : LayoutData) (placement : Storage (pinned l)) (s : X86Memory.State)
    (f : Option Flags) (initial : PinnedIncoming l s) :
    (∃ k≤648*(3*(202*2147483647+30)+36),
      X86ByteRoutine.Prefix E1M1AimSideLookup.iterationProgram [] k
        ⟨s,f,0x2e46a⟩ (states s f 648)) ∧
    (states s f 648).pc=0x2e4dd ∧
    Outputs (pinned l) 648 (states s f 648).core.memory ∧
    (∀ p, Persistent (pinned l) p → load32 (states s f 648).core.memory p=load32 s.memory p) :=
  pinned_execution l placement s f initial
''')
    def test_cumulative_certificate_and_negative_guards(self):
        import verify_e1m1_aim_side_loop as proof
        data,_=proof.previous.previous.previous.previous.previous.previous.pinned_data()
        _,_,raw=proof.previous.previous.previous.previous.previous.previous.extracted()
        source=proof.certificate(data,raw)
        output=self.succeeds(source);proof.audit(output)
        for bad in [output+'extra',output.replace('Quot.sound','sorryAx'),output.replace('pinned_execution_checked','absent')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for old,new in [('0xe8,0xcd,0x62,0x0,0x0','0xe8,0xcc,0x62,0x0,0x0'),
                        ('def sectorIndices : List (Fin 85) := [\n  40,','def sectorIndices : List (Fin 85) := [\n  41,')]:
            self.assertIn(old,source);self.rejects(source.replace(old,new,1))
        for module,name,guard in [
            ('E1M1AimSideLoop','execution','(placement : Doom.Proofs.E1M1AimSideLoop.Layout l)'),
            ('E1M1AimSideLoop','execution','(initial : Doom.Proofs.E1M1AimSideLoop.Incoming l s)'),
            ('E1M1AimPinnedSides','pinned_execution','(initial : Doom.Proofs.E1M1AimPinnedSides.PinnedIncoming l s)')]:
            decl,args=proof.contract(module,name)
            text='import Doom.Proofs.E1M1AimPinnedSides\n'+HEADER+'open E1M1AimPinnedSides\n'+decl.replace('theorem '+name,'example',1)+' := by\n  exact Doom.Proofs.'+module+'.'+name+' '+args+'\n'
            self.succeeds(text);self.assertIn(guard,text)
            self.rejects(text.replace(guard,guard.split(':')[0]+': True)'))
    def test_all_earlier_words_preserved(self):
        self.succeeds(HEADER+'''
example (l : LayoutData) (layout : Layout l) (s : X86Memory.State)
    (f : Option Flags) (initial : Incoming l s) (j start count off : Nat)
    (earlier : j<start) (bound : start+count≤648) (fits : off+4≤18) :
    load32 (states s f (start+count)).core.memory (cursor l.output 18 j+BitVec.ofNat 32 off)=
      load32 (states s f start).core.memory (cursor l.output 18 j+BitVec.ofNat 32 off) :=
  earlier_words l layout s f initial j start count off earlier bound fits
''')
    def test_extractor_mapping_mutation_rejected(self):
        import verify_e1m1_aim_side_loop as proof
        from unittest.mock import patch
        unpack=proof.struct.unpack_from
        def bad(fmt,buffer,offset=0):
            result=unpack(fmt,buffer,offset)
            if fmt=='<II8s' and result[2].rstrip(b'\0')==b'SIDEDEFS':
                return result[0]+1,result[1],result[2]
            return result
        with patch.object(proof.struct,'unpack_from',side_effect=bad):
            with self.assertRaises(ValueError):proof.sector_data()
    def test_independent_matching_loop_image(self):
        import verify_e1m1_aim_side_loop as proof
        self.assertTrue(hasattr(proof,'cross_check_loop'),'independent loop header invariant checker missing')
        import subprocess,os,json
        run=subprocess.run([str(ROOT/'.tools/x86-check/bin/python'),'-c','import verify_e1m1_aim_side_loop as p,json; print(json.dumps(p.cross_check_loop()))'],cwd=ROOT,env={**os.environ,'PYTHONPATH':'scripts'},capture_output=True,text=True,timeout=300)
        self.assertEqual(run.returncode,0,run.stdout+run.stderr)
        report=json.loads(run.stdout)
        self.assertEqual(report['sides'],648);self.assertEqual(report['exact_return_ids'],1944)
        self.assertTrue(report['exact_registers_at_every_header'])
        self.assertTrue(report['published_side_global_preserved'])
        self.assertTrue(report['all_inputs_at_every_header'])
    def test_constructed_regional_storage(self):
        self.succeeds('import Doom.Proofs.E1M1AimPinnedSides\n'+HEADER+'''
open E1M1AimPinnedSides
example : Nonempty (Storage (pinned constructed)) := constructed_storage
''')
if __name__=='__main__':unittest.main()
