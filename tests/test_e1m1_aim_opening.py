"""Opening correspondence must retain real CALL/RET, signed bounds and images."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_stop as prior
import verify_e1m1_aim_opening as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='''import Doom.Proofs.E1M1AimPortalSource
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1AimSource (afterPath attackPath stopped)
attribute [local irreducible] load32 store32
'''
class AimOpeningTests(unittest.TestCase):
    lean=prior.AimStopTests.lean
    succeeds=prior.AimStopTests.succeeds
    rejects=prior.AimStopTests.rejects
    mutations=prior.AimStopTests.mutations
    def contract(self,module,name,args):
        s=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=re.search(r'^theorem '+name+r'(?: | :)',s,re.M).start()
        decl=s[a:s.index(' := by',a)]
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'

    def test_certificate_bytes_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),37)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimOpening.from_callback','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for m,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+)(?: | :)',(ROOT/f'Doom/Proofs/{m}.lean').read_text(),re.M))
        for unit,index,value in [('aimOpening',3,0xbb),('aimOpening',18,0x8e),('opening',33,0x7c)]:
            changed=dict(raw);b=bytearray(raw[unit]);self.assertNotEqual(b[index],value);b[index]=value
            changed[unit]=bytes(b);self.rejects(proof.certificate(data,changed))

    def test_helper_return_needs_global_stack_separation(self):
        self.mutations(self.contract('E1M1AimOpening','helper_return','s safe'),[
            ('(safe : Safe s)','(safe : True)'),('(opened s).pc=0x2b786','(opened s).pc=0x2b797')])
        self.mutations(self.contract('E1M1AimOpening','execution','s f safe'),[
            ('(safe : Safe s)','(safe : True)'),('⟨s,f,0x2b77f⟩','⟨s,f,0x2b781⟩')])

    def test_callback_prologue_requires_actual_two_sided_flag(self):
        args='s f hit pointer record isLine tagSafe pointerSafe flagsSafe two helperSafe'
        self.mutations(self.contract('E1M1AimOpening','from_callback',args),[
            ('(record : OriginalLineFinish.RecordAt s.memory (s.regs 0) hit pointer)','(record : True)'),
            ('(two : s.memory (pointer+16) &&& (4#8)≠0)','(two : True)'),
            ('(helperSafe : CallerSafe s)','(helperSafe : True)'),
            ('(flagsSafe : E1M1AimWall.Safe (s.regs 4) (pointer+16))','(flagsSafe : True)')])

    def test_heights_need_entry_representation_and_signed_choices(self):
        args='s front back ff fc bf bc safe side frontPtr backPtr frontFloor frontCeiling backFloor backCeiling'
        self.mutations(self.contract('E1M1OpeningHeights','heights',args),[
            ('(safe : Safe s front back)','(safe : True)'),
            ('(side : load16 s.memory (s.regs 0+(24#32)) ≠ 0xffff)','(side : True)'),
            ('(backPtr : load32 s.memory (s.regs 0+(50#32))=back)','(backPtr : True)'),
            ('(if bc.toInt≤fc.toInt then bc else fc)','(if bc.toInt≤fc.toInt then fc else bc)'),
            ('(if ff.toInt≤bf.toInt then bf else ff)','(if ff.toInt≤bf.toInt then ff else bf)')])

    def test_source_closed_case_requires_order_and_actual_back_sector(self):
        args='scene shooter thing path distance hit back nonempty first isLine two backSector closed'
        self.mutations(self.contract('E1M1AimPortalSource','first_closed',args),[
            ('(first : path.visited[0]! = hit)','(first : True)'),
            ('(backSector : scene.lines[hit.id]!.back=some back)','(backSector : True)'),
            ('(closed : min scene.lines[hit.id]!.front.ceiling.raw back.ceiling.raw ≤\n      max scene.lines[hit.id]!.front.floor.raw back.floor.raw)','(closed : True)'),
            ('stopped path 1','stopped path 2')])

    def test_closed_correspondence_needs_map_and_path(self):
        args='s f scene shooter angle distance thing path hit back frontPtr backPtr safe mapSafe side front backAddress ff fc bf bc traced nonempty first isLine two backSector closed'
        self.mutations(self.contract('E1M1AimPortalSource','closed_correspondence',args),[
            ('(mapSafe : E1M1OpeningHeights.Safe (OriginalAimOpening.called s) frontPtr backPtr)','(mapSafe : True)'),
            ('(traced : attackPath scene shooter angle distance=.ok (thing,path))','(traced : True)'),
            ('(fc : load32 (OriginalAimOpening.called s).memory (frontPtr+(4#32))=scene.lines[hit.id]!.front.ceiling.raw.toBitVec)','(fc : True)')])

if __name__=='__main__':unittest.main()
