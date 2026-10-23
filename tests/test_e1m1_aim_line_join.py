"""Guard the source continuation, authentic parent branch and joined contracts."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_window as prior
import verify_e1m1_aim_line_join as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='''import Doom.Proofs.E1M1AimLineJoin
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary Collision E1M1AimIteration E1M1AimSource
attribute [local irreducible] load32 store32
'''
SOURCE_ARGS='scene shooter thing path distance i rest lower upper floorSlope ceilingSlope history hit back selected isLine two backSector pass floorOk ceilingOk'
MACHINE_ARGS='s f hit line front back ff fc bf bc distance z lower upper floorSlope ceilingSlope h distanceReads floorReads reads clip range eye bottom top pass floorOk ceilingOk returnSafe returnWord markSafe'
JOIN_ARGS='s f scene shooter thing path distance i rest lower upper floorSlope ceilingSlope history hit back line frontPtr backPtr h distanceReads floorReads reads clip range eye bottom top selectedPointer selected two backSector pass floorOk ceilingOk returnSafe returnWord markSafe'
class AimLineJoinTests(unittest.TestCase):
    lean=prior.AimWindowTests.lean
    succeeds=prior.AimWindowTests.succeeds
    rejects=prior.AimWindowTests.rejects
    mutations=prior.AimWindowTests.mutations
    def contract(self,module,name,args):
        s=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=re.search(r'^theorem '+name+r'(?: | :)',s,re.M).start()
        decl=s[a:s.index(' := by',a)]
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'
    def test_certificate_authenticates_parent_and_audits_all_new_theorems(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),42)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out+'extra',out.replace('AimLineJoin.correspondence','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for m,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+)(?: | :)',(ROOT/f'Doom/Proofs/{m}.lean').read_text(),re.M))
        changed=dict(raw);b=bytearray(raw['interceptGate']);self.assertEqual(b[17],0x75);b[17]=0x74;changed['interceptGate']=bytes(b)
        self.rejects(proof.certificate(data,changed))
    def test_source_extraction_uses_all_hits_and_initial_bounds(self):
        self.mutations(self.contract('E1M1AimIteration','live','scene shooter thing path distance'),[
            ("List.range' 0 path.visited.size","List.range' 1 path.visited.size"),
            ('aimBottomSlope aimTopSlope #[]','aimTopSlope aimBottomSlope #[]')])
    def test_source_iteration_carries_updated_window_and_history(self):
        self.mutations(self.contract('E1M1AimIteration','next_line',SOURCE_ARGS),[
            ('(selected : path.visited[i]! = hit)','(selected : True)'),
            ('(bottomAfter scene.lines[hit.id]!.front back lower floorSlope)\n          (topAfter','lower\n          (topAfter'),
            ('(history.push (portal scene.lines[hit.id]!.front back distance hit))','history'),
            ('stopped path (i+1)','stopped path i'),
            ('floor.raw <\n      min','floor.raw ≤\n      min')])
    def test_parent_requires_return_site_and_mark_separation(self):
        self.mutations(self.contract('E1M1AimResume','execution',MACHINE_ARGS),[
            ('(returnWord : load32 s.memory (s.regs 4)=0x2c86d)','(returnWord : True)'),
            ('(markSafe : Apart (0x2c1e4#32) (s.regs 3) ∧ Apart (0x2c1e8#32) (s.regs 3))','(markSafe : True)'),
            ('then 0x2c83a else 0x2c88c','then 0x2c88c else 0x2c83a'),
            ('load32 (result s).core.memory (s.regs 3)=0x7fffffff','load32 (result s).core.memory (s.regs 3)=0')])
    def test_join_requires_matching_path_map_and_source_division(self):
        self.mutations(self.contract('E1M1AimLineJoin','correspondence',JOIN_ARGS),[
            ('(selected : path.visited[i]! = hit)','(selected : True)'),
            ('(backSector : scene.lines[hit.id]!.back=some back)','(backSector : True)'),
            ('(E1M1AimResume.result s).pc=0x2c83a then','(E1M1AimResume.result s).pc=0x2c88c then'),
            ('(distance*hit.frac)=.ok floorSlope','(distance*hit.frac)=.ok ceilingSlope')])
    def test_word_bridge_uses_correct_signed_bounds(self):
        self.mutations(self.contract('E1M1AimLineJoin','floor_word','a b'),[('=max a.raw b.raw','=min a.raw b.raw')])
        self.mutations(self.contract('E1M1AimLineJoin','ceiling_word','a b'),[('=min a.raw b.raw','=max a.raw b.raw')])
if __name__=='__main__':unittest.main()
