"""The live outer traversal must retain the checked scan and all surrounding control."""
import re
import unittest
from pathlib import Path
import test_e1m1_line_source as prior
import verify_e1m1_traversal_source as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER=prior.HEADER.replace('import Doom.Proofs.E1M1LineSourceScan','import Doom.Proofs.E1M1TraversalLineJoin')
HEADER+='open Collision\nopen E1M1TraversalSource\n'
FIXTURE=prior.FIXTURE.replace('import Doom.Proofs.E1M1LineSourceScan','import Doom.Proofs.E1M1TraversalLineJoin')
FIXTURE+='open E1M1TraversalSource\n'

class TraversalSourceTests(unittest.TestCase):
    lean=prior.LineSourceTests.lean
    succeeds=prior.LineSourceTests.succeeds
    rejects=prior.LineSourceTests.rejects
    mutations=prior.LineSourceTests.mutations

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),29);self.assertEqual(len(data['cells']),828)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('TraversalSource.live','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+)(?: | :)',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_unconditional_live_equality_keeps_the_aiming_flags(self):
        source=HEADER+'''attribute [local irreducible] Scene.pathTraverse withLines
example (scene : Scene) (sx sy ex ey : Fixed) (visit : Intercept → Nat → Bool) :
  scene.pathTraverse sx sy ex ey 3 visit = withLines scene sx sy ex ey aimingScan 3 visit :=
  live_aiming scene sx sy ex ey visit
'''
        self.mutations(source,[('pathTraverse sx sy ex ey 3 visit','pathTraverse sx sy ex ey 7 visit'),
                               ('aimingScan 3 visit','aimingScan 1 visit')])

    def outer_contract(self):
        s=(ROOT/'Doom/Proofs/E1M1TraversalSource.lean').read_text()
        a=s.index('def withLines ');b=s.index('/-- At aiming flags',a)
        return HEADER+'attribute [local irreducible] ForIn.forIn Bind.bind Array.append Array.push\nnamespace Scratch\n'+s[a:b]+'end Scratch\n'

    def test_live_connection_rejects_grid_and_raw_list_drift(self):
        self.mutations(self.outer_contract(),[
            ('for _ in [:64] do','for _ in [:63] do'),
            ('(#[0] ++ ids)','ids'),
            ('blocks.push (true, mapx, mapy)','blocks.push (false, mapx, mapy)')])

    def test_live_connection_rejects_tie_order_and_visitor_drift(self):
        self.mutations(self.outer_contract(),[
            ('work[i]!.frac.raw < distance','work[i]!.frac.raw ≤ distance'),
            ('if !visit hit (result.visited.size - 1)','if visit hit (result.visited.size - 1)')])

    def test_dos_join_still_requires_memory_and_capacity_contracts(self):
        s=(ROOT/'Doom/Proofs/E1M1TraversalLineJoin.lean').read_text()
        a=s.index('section Scan');b=s.index(' := by',s.index('theorem execution'))
        decl=s[a:b].replace('theorem execution','example',1)
        source=HEADER+'namespace E1M1TraversalLineJoin\n'+decl+' := E1M1TraversalLineJoin.execution '+prior.SCAN+'\nend Scan\nend E1M1TraversalLineJoin\n'
        self.mutations(source,[
            ('(represented : Represents s.memory lines epoch seen)','(represented : True)'),
            ('(tracked : OriginalLineCollection.Tracks s 0x2ba20 (E1M1ThingFinish.resolve lines objects) r.collected c.ids.length)','(tracked : True)'),
            ('(none,out.2,markPrefix (candidates trace lines c.ids data) c.ids.length 0 seen)','(none,out.2,seen)')])

    def test_early_out_is_preserved_for_other_flags(self):
        self.succeeds(FIXTURE+'''
example : (lineFlow 7 trace #[wall 1048576] #[0] #[false] r).toOption.map
    (fun out => (out.1.map (fun stop => stop.completed),out.2.1.collected.size,out.2.2.toList)) =
    some (some false,0,[true]) := by decide +kernel
example : (lineFlow 3 trace #[wall 1048576] #[0] #[false] r).toOption.map
    (fun out => (out.1.isNone,out.2.1.collected.size,out.2.2.toList)) =
    some (true,1,[true]) := by decide +kernel
''')

    def test_aiming_adapter_preserves_errors_and_duplicate_validation(self):
        self.succeeds(FIXTURE+'''
example : aimingScan trace #[] #[0] #[true] r =
    .error "path: invalid linedef" := by rfl
example : aimingScan trace #[] #[32768] #[] r =
    .error "path: signed linedef index is unverified" := by rfl
example : (aimingScan trace #[wall 1048576] #[0,0] #[false] r).toOption.map
    (fun out => (out.1.isNone,out.2.1.collected.size,out.2.2.toList)) =
    some (true,1,[true]) := by decide +kernel
''')

if __name__=='__main__':unittest.main()
