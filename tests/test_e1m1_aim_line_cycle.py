"""Guard exhaustive covered-line dispatch without assuming its branch outcome."""
import re
import unittest
from pathlib import Path
import test_e1m1_aim_blocking_prefix as prior
import verify_e1m1_aim_line_cycle as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER=prior.HEADER.replace('import Doom.Proofs.E1M1AimBlockingPrefix','import Doom.Proofs.E1M1AimLineCycle')+'\nopen E1M1InterceptMark (consume)\nopen E1M1AimLineDispatch (dispatch)\nopen E1M1AimLineCoverage (Coverage)\n'
class AimLineCycleTests(unittest.TestCase):
    lean=prior.AimBlockingPrefixTests.lean
    succeeds=prior.AimBlockingPrefixTests.succeeds
    rejects=prior.AimBlockingPrefixTests.rejects
    mutations=prior.AimBlockingPrefixTests.mutations
    def contract(self,module,name,args):
        text=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        start=re.search(r'^theorem '+name+r' ',text,re.M).start()
        decl=text[start:text.index(' := by',start)]
        decl=re.sub(r'\bprogram\b','E1M1AimRepeatProgram.program',decl)
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'
    def test_certificate_and_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),42)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimLineCycle.execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for m,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{m}.lean').read_text(),re.M))
    def test_selected_coverage_requires_original_identity_and_line_kind(self):
        self.mutations(self.contract('E1M1AimLineCoverage','selected',proof.SELECT_ARGS),[
            ('(selection : Selection initial work seen resolve target sp s fraction j)','(selection : True)'),
            ('(covered : Coverage initial walls portals)','(covered : True)'),
            ('(isLine : (work[j]!).isLine=true)','(isLine : True)')])
    def test_labels_are_exclusive_only_under_shared_representation(self):
        self.mutations(self.contract('E1M1AimLineCoverage','exclusive',proof.EXCLUSIVE_ARGS),[
            ('(wallMap : E1M1AimWallCatalog.Represents scene initial walls)','(wallMap : True)'),
            ('(portalMap : E1M1AimSourceCatalog.Represents scene initial portals)','(portalMap : True)'),
            ('(wall : walls j)','(wall : True)'),
            ('(listed : portals j=some p)','(listed : True)')])
    def test_dispatch_requires_coverage_catalogs_and_successful_guarded_divisions(self):
        source=self.contract('E1M1AimLineCycle','execution',proof.EXEC_ARGS)
        div=source[source.index('    (divisions :'):source.index(' :\n    ∃ n',source.index('    (divisions :'))]
        self.mutations(source,[
            ('(covered : Coverage result.collected walls portals)','(covered : True)'),
            ('(catalog : E1M1AimWallCatalog.Catalog s result.collected resolve walls)','(catalog : True)'),
            ('(wallMap : E1M1AimWallCatalog.Represents scene result.collected walls)','(wallMap : True)'),
            ('(represented : Represents scene result.collected portals)','(represented : True)'),
            (div,'    (divisions : True)')])
    def test_stop_outcome_uses_derived_bounds_and_exact_visit(self):
        self.mutations(self.contract('E1M1AimLineCycle','execution',proof.EXEC_ARGS),[
            ('out.pc=0x2c88c','out.pc=0x2c887'),
            ('E1M1AimSource.stopped path (seen.length+1)','E1M1AimSource.stopped path seen.length'),
            ('load32 out.core.memory (0x2c1e4#32)=lo.raw.toBitVec','load32 out.core.memory (0x2c1e4#32)=lower.raw.toBitVec'),
            ('load32 out.core.memory (0x2c1e8#32)=hi.raw.toBitVec','load32 out.core.memory (0x2c1e8#32)=upper.raw.toBitVec')])
    def test_continue_outcome_advances_history_and_preserves_next_catalog(self):
        self.mutations(self.contract('E1M1AimLineCycle','execution',proof.EXEC_ARGS),[
            ('History result.collected (consume work j) (j::seen) (visits.push work[j]!)','History result.collected work seen visits'),
            ('log.push entry','log'),
            ("List.range' (seen.length+1) (path.visited.size-(seen.length+1))","List.range' seen.length (path.visited.size-seen.length)"),
            ('out nextFraction k → E1M1AimWallCatalog.Catalog out.core result.collected resolve walls','out nextFraction k → E1M1AimWallCatalog.Catalog out.core result.collected resolve (fun _ => True)')])
    def test_classifier_wall_closed_open_and_missing_back_boundaries(self):
        source=HEADER+'''
open E1M1AimLineDispatch (Decision)
def sample (two : Bool) (ff fc : Int32) (back : Option Heights) : Scene :=
  { grid:=default, lines:=#[{(default : Line) with twoSided:=two, front:=⟨⟨ff⟩,⟨fc⟩⟩, back:=back}], links:=#[] }
def hit : Intercept := ⟨⟨32768⟩,true,0⟩
def observe : Option Decision → Option (Int32 × Int32 × Bool)
  | none => none
  | some (.stop lo hi) => some (lo.raw,hi.raw,false)
  | some (.next lo hi _) => some (lo.raw,hi.raw,true)
def check (scene : Scene) (fs cs : Int32) := observe (dispatch scene hit ⟨65536⟩ ⟨-10⟩ ⟨10⟩ ⟨fs⟩ ⟨cs⟩)
-- Wall flags take priority over a missing back sector.
example : check (sample false 0 128 none) 999 (-999)=some (-10,10,false) := by decide
-- An invalid two-sided record remains unsupported.
example : check (sample true 0 128 none) 999 (-999)=none := by decide
-- Equality closes the sector before either slope is used.
example : check (sample true 0 64 (some ⟨⟨64⟩,⟨128⟩⟩)) 999 (-999)=some (-10,10,false) := by decide
-- Open sector, but the clipped window is exactly closed.
example : check (sample true 0 128 (some ⟨⟨64⟩,⟨128⟩⟩)) 10 999=some (10,10,false) := by decide
-- The same portal leaves a nonempty window at a lower floor slope.
example : check (sample true 0 128 (some ⟨⟨64⟩,⟨128⟩⟩)) 0 999=some (0,10,true) := by decide
-- Ceiling clipping can close the window too.
example : check (sample true 0 128 (some ⟨⟨0⟩,⟨64⟩⟩)) 999 (-10)=some (-10,-10,false) := by decide
-- Opening comparisons are signed, including negative map heights.
example : check (sample true (-128) (-64) (some ⟨⟨-96⟩,⟨-32⟩⟩)) 0 20=some (0,10,true) := by decide
'''
        self.mutations(source,[
            ('some (10,10,false)','some (10,10,true)'),
            ('999 (-999)=none','999 (-999)=some (-10,10,false)'),
            ('some (0,10,true)','some (0,10,false)')])
if __name__=='__main__':unittest.main()
