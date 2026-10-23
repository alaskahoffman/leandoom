"""The next scan must retain mixed hits and require a real suffix capacity budget."""
import re
import unittest
from pathlib import Path
import test_e1m1_firing_next_geometry as prior
import verify_e1m1_firing_next_lines as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER=prior.HEADER.replace('import Doom.Proofs.E1M1FiringNextGeometry','import Doom.Proofs.E1M1FiringNextLines')
HEADER+='open E1M1ScanContracts (candidates)\nopen OriginalLineVisits (markPrefix)\n'
CURSOR=prior.FRAME+' locals globalsSafe imageSafe x y mapX mapY nextCell inMap valid selectedCell'
SCAN='s sp cursor lines objects trace c data stack list items ids ready layout'
NEXT=prior.NEXT+' nextLayout budget'

class FiringNextLinesTests(unittest.TestCase):
    lean=prior.FiringNextGeometryTests.lean
    succeeds=prior.FiringNextGeometryTests.succeeds
    rejects=prior.FiringNextGeometryTests.rejects
    mutations=prior.FiringNextGeometryTests.mutations

    def contract(self,module,name,args,section=False):
        if module!='E1M1NextLineScan' or not section:
            return prior.FiringNextGeometryTests.contract(self,module,name,args,section).replace(prior.HEADER,HEADER,1)
        source=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        start=source.index('theorem '+name+' ')
        earlier=source[source.index('section Scan'):start]
        context=''.join(re.findall(r'^variable .*?(?=^include)',earlier,re.M|re.S))
        context+='\n'.join(re.findall(r'^include .+$',earlier,re.M))+'\n'
        decl=re.split(r' :=(?: by)?(?:\n| rfl)',source[start:],maxsplit=1)[0]
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+context+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),29)
        self.assertEqual(len(data['cells']),828)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('FiringNextLines.execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_suffix_cursor_comes_from_selected_map_offset(self):
        self.mutations(self.contract('E1M1NextCursor','tail_address','base offset'),[
            ('(2*(offset+1))','(2*offset)')])
        self.mutations(self.contract('E1M1NextCursor','firing_cursor',CURSOR,True),[
            ('(2*nextCell.offset)','(2*(nextCell.offset+1))'),
            ('(selectedCell : words[4+Collision.pathCellIndex x y w]?=some nextCell.offset)','(selectedCell : True)'),
            ('(mapX : (E1M1PathAdvance.step (initial (path thing angle ox oy) xout yout)).mapX=x.toBitVec)','(mapX : True)')])

    def test_tail_id_bounds_require_valid_map_data(self):
        self.mutations(self.contract('E1M1NextCursor','tail_ids','c words valid i'),[
            ('(valid : c.Valid words)','(valid : True)'),
            ('ids[i.val]<475','ids[i.val]<474')])

    def test_scan_requires_readiness_and_unchanged_list(self):
        self.mutations(self.contract('E1M1NextLineScan','execution',SCAN+' stamps f r tracked epoch seen size represented',True),[
            ('(ready : Ready s lines trace c data)','(ready : True)'),
            ('(items : E1M1PathMapLookup.ScanWords s lines c)','(items : True)'),
            ('(list : s.regs 2=cursor)','(list : True)'),
            ('(layout : E1M1ScanContracts.Layout sp cursor lines c.ids.length (candidates trace lines c.ids data))','(layout : True)')])

    def test_scan_requires_mixed_collection_capacity_and_history(self):
        self.mutations(self.contract('E1M1NextLineScan','execution',SCAN+' stamps f r tracked epoch seen size represented',True),[
            ('r.collected c.ids.length)','r.collected 0)'),
            ('(represented : Represents s.memory lines epoch seen)','(represented : True)'),
            ('(size : seen.size=475)','(size : True)'),
            ('(markPrefix (candidates trace lines c.ids data) c.ids.length 0 seen)','seen')])

    def test_existing_hits_are_not_replaced_by_new_hits(self):
        self.mutations(self.contract('E1M1NextLineScan','run_prefix','cs k i s r'),[
            ('r.collected.toList++added','added++r.collected.toList')])
        self.mutations(self.contract('E1M1NextLineScan','execution',SCAN+' stamps f r tracked epoch seen size represented',True),[
            ('out.2.collected 0','out.2.collected 1'),
            ('steps≤281*c.ids.length+7','steps≤281*c.ids.length+6')])

    def test_continuous_firing_needs_two_cell_budget_and_static_layout(self):
        self.mutations(self.contract('E1M1FiringNextLines','execution',NEXT,True),[
            ('(budget : c.ids.length+nodes.length+nextCell.ids.tail.length≤128)','(budget : c.ids.length+nodes.length≤128)'),
            ('(base+BitVec.ofNat 32 (2*(nextCell.offset+1)))','(base+BitVec.ofNat 32 (2*nextCell.offset))'),
            ('steps≤474+281*(c.ids.length+nextCell.ids.tail.length)+230*nodes.length','steps≤473+281*(c.ids.length+nextCell.ids.tail.length)+230*nodes.length'),
            ('out.2.collected.toList=after.collected.toList++added','out.2.collected.toList=added++after.collected.toList')])

if __name__=='__main__':unittest.main()
