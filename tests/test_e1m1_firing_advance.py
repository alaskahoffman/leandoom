"""Pinned cell-step bytes, semantic boundaries and continuous first-cell prefix."""
import copy
import json
import re
import unittest
from pathlib import Path
import test_e1m1_firing_things as previous
import verify_e1m1_firing_advance as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER=previous.HEADER.replace('import Doom.Proofs.E1M1FiringThings','import Doom.Proofs.E1M1FiringAdvance')
HEADER+='open E1M1ThingList (Layout Image head run)\nopen E1M1ThingVisit (result)\n'
FULL=previous.ARGS+previous.HEAD+previous.DATA

class FiringAdvanceTests(unittest.TestCase):
    lean=previous.FiringThingsTests.lean
    succeeds=previous.FiringThingsTests.succeeds
    rejects=previous.FiringThingsTests.rejects
    mutations=previous.FiringThingsTests.mutations

    def contract(self,module,name,args,section=False):
        source=previous.FiringThingsTests.contract(self,module,name,args,section)
        return source.replace(previous.HEADER,HEADER,1)

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),29)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),out+'extra',out.replace('counter_limit','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^(?:@\[local simp\] )?theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_byte_mapping_and_relocations_fail_closed(self):
        data,_=proof.pinned_data();_,profile,raw=proof.extracted()
        bad=dict(raw);changed=bytearray(raw['gridAdvance']);changed[5]=5;bad['gridAdvance']=bytes(changed)
        self.rejects(proof.certificate(data,bad))
        share=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
        spec=json.loads((ROOT/'tests/reference/original-path-advance.json').read_text())
        for key,value in [('hex',bytes(changed).hex()),('file_offset','0x6eaca'),
                          ('relocations',[dict(offset=0,object=3,target='0x2c028')])]:
            mutated=copy.deepcopy(spec);mutated['units']['gridAdvance'][key]=value
            with self.assertRaises(ValueError):proof.extraction.extract(binary,profile,mutated)

    def test_exact_execution_bound_and_numeric_observation(self):
        self.mutations(self.contract('OriginalPathAdvance','execution','s f'),[
            ('∃ n≤19','∃ n≤18'),('⟨s,f,0x2cab5⟩','⟨s,f,0x2cabf⟩')])
        self.mutations(self.contract('E1M1PathAdvance','result_observe','s'),[
            ('=step (observe s)','=observe s'),('=nextPc (observe s)','=0x2ca7f')])

    def test_production_signed_axis_and_legal_counter_limit(self):
        self.mutations(self.contract('E1M1PathAdvance','production_axis',
            'mapx mapy xi yi mapxstep mapystep xstep ystep endx endy count'),[
            ('mapxstep.toBitVec,mapystep.toBitVec','mapystep.toBitVec,mapxstep.toBitVec')])
        self.mutations(self.contract('E1M1PathAdvance','counter_limit','n bound'),[
            ('↔ n+1<64','↔ n+1≤64')])
        # Explicit fragment boundary: this theorem does not verify the outer loop.
        source=(ROOT/'Doom/Path.lean').read_text()
        self.assertIn('''    if mapx == xt2 && mapy == yt2 then break
    if yi.raw >>> 16 == mapy then
      yi := yi + ystep; mapx := mapx + mapxstep
    else if xi.raw >>> 16 == mapx then
      xi := xi + xstep; mapy := mapy + mapystep''',source)

    def test_whole_list_read_preservation_needs_separation(self):
        self.mutations(self.contract('E1M1ThingListFrame','traversal_frame',
            's trace resolve nodes ret layout image cursor pc r tracked capacity a safe'),[
            ('(safe : E1M1ThingVisit.ReadSafe (s.core.regs 4) a)','(safe : True)'),
            ('(capacity : r.collected.size+nodes.length≤128)','(capacity : r.collected.size≤128)')])

    def test_firing_prefix_includes_advancement_without_claiming_initial_numeric_state(self):
        self.mutations(self.contract('E1M1FiringAdvance','execution',FULL+' room world dimension ids scene f',True),[
            ('steps≤427+','steps≤426+'),
            ('out.core.regs 4=s.regs 4-(112#32)','out.core.regs 4=s.regs 4-(116#32)'),
            ('out.pc=E1M1PathAdvance.nextPc (E1M1PathAdvance.observe before.core)','out.pc=0x2ca7f')])

    def test_endpoint_priority_negative_wrap_stall_and_final_iteration(self):
        source=(ROOT/'tests/reference/original-path-advance.lean').read_text()
        self.succeeds(source)
        self.rejects(source.replace('=(4,4,0x30000,0x58000)','=(3,3,0x20000,0x40000)'))

if __name__=='__main__':unittest.main()
