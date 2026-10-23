"""Stable catalog: actual post-CALL/PUSH comparisons and first matches."""
import sys, unittest
sys.setrecursionlimit(max(sys.getrecursionlimit(),10000))
import test_e1m1_aim_texture_lookup as prior
ROOT=prior.ROOT
HEADER='import Doom.Proofs.E1M1AimTextureCatalog\nopen Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary E1M1AimTextureCatalog\n'
class AimTextureCatalogTests(unittest.TestCase):
    lean=prior.AimTextureLookupTests.lean
    succeeds=prior.AimTextureLookupTests.succeeds
    rejects=prior.AimTextureLookupTests.rejects
    def test_actual_search_first_match(self):
        self.assertTrue((ROOT/'Doom/Proofs/E1M1AimTextureCatalog.lean').exists(),'stable catalog first-match implementation missing')
        self.succeeds(HEADER+'''
example (c : Catalog) (s : X86Memory.State) (f : Option Flags) (n i j : Nat)
    (image : Image c s.memory) (safe : SearchSafe c (s.regs 4))
    (regs : Cursor c s i) (first : FirstMatch c j)
    (before : i≤j) (fuel : j-i<n) :
    (OriginalTextureSearch.search n s f).core.regs 0=BitVec.ofNat 32 j :=
  search_first_match c s f n i j image safe regs first before fuel
''')
    def test_named_and_dash_wrapper_results(self):
        self.succeeds(HEADER+'''
example (c : Catalog) (s : X86Memory.State) (f : Option Flags) (j : Nat)
    (image : Image c s.memory) (safe : WrapperSafe c (s.regs 4))
    (query : s.regs 0=c.query) (resolved : Resolved c j) :
    (E1M1AimTextureLookup.wrapped s f).pc=(load32 s.memory (s.regs 4)).toNat ∧
      (E1M1AimTextureLookup.wrapped s f).core.regs 0=BitVec.ofNat 32 j :=
  wrapper_result c s f j image safe query resolved
''')
    def test_side_success_is_derived(self):
        self.succeeds(HEADER+'''
example (a b c : Catalog) (s : X86Memory.State) (f : Option Flags) (x y z : Nat)
    (input : SideInput a b c s x y z) : E1M1AimSideLookup.Returned s f :=
  side_returned a b c s f x y z input
''')
    def test_authenticated_pinned_names(self):
        self.assertTrue((ROOT/'Doom/Proofs/E1M1AimPinnedCatalog.lean').exists(),'pinned Lean catalog missing')
        self.succeeds('import Doom.Proofs.E1M1AimPinnedCatalog\n'+HEADER+'''
open E1M1AimPinnedCatalog
example (table query : Word) (pointer : Nat → Word) (q : Fin 33) :
    Resolved (catalog table pointer query q) (textureID q) := pinned_resolved table query pointer q
''')
    def test_body_entry_and_all_protected_words(self):
        self.succeeds(HEADER+'''
example (a b c : Catalog) (s : X86Memory.State) (x y z : Nat)
    (catalog : BodyCatalog a b c s x y z) (addresses : List Word)
    (safe : ∀ p∈addresses, BodySafe s p) :
    ∀ p∈addresses, load32 (body s).core.memory p=load32 s.memory p :=
  body_words a b c s x y z catalog addresses safe
''')
    def test_body_count_branch_is_derived(self):
        self.succeeds(HEADER+'''
example (a b c : Catalog) (s : X86Memory.State) (x y z i total : Nat)
    (catalog : BodyCatalog a b c s x y z) (countSafe : BodySafe s 0x2c11c)
    (index : (s.regs 5).toNat=i) (count : (load32 s.memory 0x2c11c).toNat=total)
    (small : total<2147483648) (inside : i<total) :
    (body s).pc=(if i+1<total then 0x2e46a else 0x2e4dd) ∧
      ((body s).core.regs 5).toNat=i+1 :=
  body_bounded a b c s x y z catalog countSafe i total index count small inside
''')
    def test_cumulative_certificate_and_negative_guards(self):
        import verify_e1m1_aim_texture_catalog as proof
        self.assertTrue(hasattr(proof,'certificate'),'stable catalog certificate missing')
        data,_=proof.previous.previous.previous.previous.previous.pinned_data()
        _,_,raw=proof.previous.previous.previous.previous.previous.extracted()
        source=proof.certificate(data,raw)
        self.assertEqual(proof.pinned_source(),(ROOT/'Doom/Proofs/E1M1AimPinnedCatalog.lean').read_text())
        output=self.succeeds(source); proof.audit(output)
        field_prefix='def fieldNames : List (Fin 33) := [\n  '
        first=source.split(field_prefix,1)[1].split(',',1)[0]
        mutated=source.replace(field_prefix+first+',',field_prefix+str((int(first)+1)%33)+',',1)
        self.assertNotEqual(mutated,source); self.rejects(mutated)
        for bad in [output+'extra',output.replace('Quot.sound','sorryAx'),output.replace('body_bounded_checked','absent')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        self.rejects(source.replace('0xe8,0xcd,0x62,0x0,0x0','0xe8,0xcc,0x62,0x0,0x0'))
        self.rejects(source.replace('def queryBytes : List (List (BitVec 8) × Nat) := [\n  ([45,0,0,0,0,0,0,0],0)', 'def queryBytes : List (List (BitVec 8) × Nat) := [\n  ([46,0,0,0,0,0,0,0],0)'))
        for module,name,guard in [
            ('E1M1AimTextureCatalog','search_first_match','(safe : Doom.Proofs.E1M1AimTextureCatalog.SearchSafe c (s.regs 4))'),
            ('E1M1AimTextureCatalog','side_returned','(input : Doom.Proofs.E1M1AimTextureCatalog.SideInput a b c s x y z)'),
            ('E1M1AimTextureCatalog','body_frame','(safe : Doom.Proofs.E1M1AimTextureCatalog.BodySafe s p)')]:
            decl,args=proof.contract(module,name)
            text=HEADER+decl.replace('theorem '+name,'example',1)+' := by\n  exact Doom.Proofs.'+module+'.'+name+' '+args+'\n'
            self.succeeds(text); self.assertIn(guard,text)
            self.rejects(text.replace(guard,guard.split(':')[0]+': True)'))
    def test_pinned_full_body_has_no_success_premise(self):
        self.succeeds('import Doom.Proofs.E1M1AimPinnedCatalog\n'+HEADER+'''
open E1M1AimPinnedCatalog
example (s : X86Memory.State) (f : Option Flags) (table : Word) (pointer : Nat → Word)
    (row : Fin 648) (ready : BodyReady s table pointer row)
    (side : BitVec 16) (index : Nat) (sideBase sectorBase : Word)
    (input : E1M1AimSideEncoding.Input s side index sideBase sectorBase)
    (sourceSafe : BodySafe s (s.regs 3+28)) (sectorSafe : BodySafe s 0x2c148) :
    (∃ k≤3*(202*2147483647+30)+36,
      X86ByteRoutine.Prefix E1M1AimSideLookup.iterationProgram [] k ⟨s,f,0x2e46a⟩ (body s)) ∧
    E1M1NoiseImage.Realizes
      (E1M1NoiseImage.word (E1M1NoiseGraph.sideAddress sideBase side) (E1M1AimSideEncoding.sectorAddress sectorBase index))
      (body s).core.memory :=
  pinned_body s f table pointer row ready side index sideBase sectorBase input sourceSafe sectorSafe
''')
    def test_independent_full_pinned_side_loop(self):
        import verify_e1m1_aim_texture_catalog as proof
        self.assertTrue(hasattr(proof,'cross_check_pinned_loop'),'pinned full-loop CPU checker missing')
        import subprocess,os,json
        run=subprocess.run([str(ROOT/'.tools/x86-check/bin/python'),'-c','import verify_e1m1_aim_texture_catalog as p,json; print(json.dumps(p.cross_check_pinned_loop()))'],cwd=ROOT,env={**os.environ,'PYTHONPATH':'scripts'},capture_output=True,text=True,timeout=300)
        self.assertEqual(run.returncode,0,run.stdout+run.stderr)
        report=json.loads(run.stdout)
        self.assertEqual(report['sides'],648);self.assertEqual(report['exact_return_ids'],1944)
        self.assertTrue(report['all_prior_records_at_every_header'])
        self.assertTrue(report['source_catalog_globals_preserved'])
if __name__=='__main__':unittest.main()
