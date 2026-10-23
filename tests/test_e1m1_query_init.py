"""Query setup must derive clean loop state without weakening entry contracts."""
import re
import unittest
from pathlib import Path
import test_e1m1_live_walk as prior
import verify_e1m1_query_init as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER=prior.HEADER.replace('import Doom.Proofs.E1M1LiveWalk','import Doom.Proofs.E1M1QuerySource').replace('open E1M1CellWalk (Follows grid stopPc)','open E1M1CellWalk (Follows stopPc)')+'''
open E1M1PathMapSetup (grid StackSafe)
open Doom.Collision
'''
FIXTURE=prior.FIXTURE.replace('import Doom.Proofs.E1M1LiveWalk','import Doom.Proofs.E1M1QuerySource')+'''
open E1M1QuerySource
'''

class QueryInitTests(unittest.TestCase):
    lean=prior.LiveWalkTests.lean
    succeeds=prior.LiveWalkTests.succeeds
    rejects=prior.LiveWalkTests.rejects
    mutations=prior.LiveWalkTests.mutations

    def contract(self,module,name,args):
        s=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        a=re.search(r'^theorem '+name+r'(?: | :)',s,re.M).start()
        decl=re.split(r' :=(?: by)?(?:\n| rfl)',s[a:],maxsplit=1)[0]
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'

    def extraction(self):
        s=(ROOT/'Doom/Proofs/E1M1QuerySource.lean').read_text().split('/-- Successful preparation')[0]
        return s.replace('namespace Doom.Proofs.E1M1QuerySource','namespace Doom.Proofs.ScratchQuery')+'\nend Doom.Proofs.ScratchQuery\n'

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),29);self.assertEqual(len(data['cells']),828)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('QueryInit.numeric','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+)(?: | :)',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_source_preparation_rejects_history_axis_and_budget_drift(self):
        self.mutations(self.extraction(),[
            ('Array.replicate scene.lines.size false','Array.replicate scene.lines.size true'),
            ('E1M1FiringGridState.initial p xout yout','E1M1FiringGridState.initial p yout xout'),
            ('scene start.trace 64','scene start.trace 63')])

    def test_source_preparation_rejects_error_and_hit_order_drift(self):
        self.mutations(self.extraction(),[
            ('path: unsupported BLOCKMAP profile','path: invalid profile'),
            ('work[i]!.frac.raw < distance','work[i]!.frac.raw ≤ distance')])

    def test_numeric_join_requires_both_calculations(self):
        self.mutations(self.contract('E1M1QueryInit','numeric','s ox oy sx sy ex ey geometry xout yout okX okY'),[
            ('(okX : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok xout)','(okX : True)'),
            ('(okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout)','(okY : True)'),
            ('(grid s).pc=0x2ca7f','(grid s).pc=0x2cafd')])

    def test_empty_buffer_requires_cursor_separation(self):
        source=self.contract('E1M1QueryInit','empty_collection','s ox oy sx sy ex ey geometry safe resolve')
        source=source.replace('open E1M1CellWalk (Follows grid stopPc)','open E1M1CellWalk (Follows stopPc)')
        self.mutations(source,[('(safe : StackSafe (s.regs 4-60) 0x2c028)','(safe : True)'),
                              ('resolve #[] 0','resolve #[] 129')])

    def test_visit_join_requires_next_epoch_freshness_and_memory_separation(self):
        source=self.contract('E1M1QueryInit','initial_visits','s ox oy sx sy ex ey geometry lines count epochSafe stampSafe fresh')
        source=source.replace('open E1M1CellWalk (Follows grid stopPc)','open E1M1CellWalk (Follows stopPc)')
        self.mutations(source,[
            ('(epochSafe : StackSafe (s.regs 4-60) 0x13580)','(epochSafe : True)'),
            ('(stampSafe : ∀ j<count, E1M1PathMapSetup.Safe s (OriginalLineVisits.stamp lines j))','(stampSafe : True)'),
            ('(fresh : ∀ j<count, load32 s.memory (OriginalLineVisits.stamp lines j)≠load32 s.memory 0x13580+1)',
             '(fresh : ∀ j<count, load32 s.memory (OriginalLineVisits.stamp lines j)≠load32 s.memory 0x13580)')])

    def test_preparation_produces_zero_count_empty_hits_and_fresh_history(self):
        self.succeeds(FIXTURE+'''
example : (prepare world (Fixed.ofInt 0) (Fixed.ofInt 0) (Fixed.ofInt 32) (Fixed.ofInt 16)).toOption.map
    (fun s => ([s.grid.count.toNat,s.result.collected.size,s.result.visited.size,s.result.blocks.size],s.seen.toList)) =
    some ([0,0,0,0],[false]) := by decide +kernel
example : (prepare world (Fixed.ofInt 0) (Fixed.ofInt 0) (Fixed.ofInt 32) (Fixed.ofInt 16)).toOption.map
    (fun s => (s.trace.x.raw.toInt,s.trace.y.raw.toInt)) = some (65536,65536) := by decide +kernel
''')

    def test_unsupported_profile_fails_before_collection(self):
        self.succeeds(FIXTURE+'''
def errorOf {α : Type} (v : Except String α) : Option String :=
  match v with | .error e => some e | .ok _ => none
example : errorOf (prepare {world with grid:={world.grid with width:=0}}
    (Fixed.ofInt 0) (Fixed.ofInt 0) (Fixed.ofInt 32) (Fixed.ofInt 16)) =
    some "path: unsupported BLOCKMAP profile" := by decide +kernel
''')

if __name__=='__main__':unittest.main()
