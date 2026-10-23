"""Reject dropped entry images, clobbered operands, wrong arithmetic and paths."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_opening as prior
import verify_e1m1_aim_distance as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='''import Doom.Proofs.E1M1AimDistance
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1AimOpeningFrame (result Image MapSafe pushes writes)
attribute [local irreducible] load32 store32
'''
class AimDistanceTests(unittest.TestCase):
    lean=prior.AimOpeningTests.lean
    succeeds=prior.AimOpeningTests.succeeds
    rejects=prior.AimOpeningTests.rejects
    mutations=prior.AimOpeningTests.mutations
    def contract(self,module,name,args):
        s=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=re.search(r'^theorem '+name+r'(?: | :)',s,re.M).start()
        decl=s[a:s.index(' := by',a)]
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'

    def test_certificate_bytes_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),38)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimDistance.operands','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for m,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+)(?: | :)',(ROOT/f'Doom/Proofs/{m}.lean').read_text(),re.M))
        for index,value in [(12,15),(8,0xe3),(1,0xbc)]:
            changed=dict(raw);b=bytearray(raw['aimDistance']);self.assertNotEqual(b[index],value);b[index]=value
            changed['aimDistance']=bytes(b);self.rejects(proof.certificate(data,changed))

    def test_entry_map_transport_requires_image_and_write_separation(self):
        self.mutations(self.contract('E1M1AimOpeningFrame','transport','s line front back ff fc bf bc safe image'),[
            ('(safe : MapSafe s line front back)','(safe : True)'),
            ('(image : Image s.memory line front back ff fc bf bc)','(image : True)')])
        self.mutations(self.contract('E1M1AimOpeningFrame','output_frame','s a safe'),[
            ('(safe : ∀ b∈writes (s.regs 4), Apart a b)','(safe : True)')])
        self.mutations(self.contract('E1M1AimOpeningFrame','line_argument','s hit pointer record safe'),[
            ('(safe : E1M1AimWall.Safe (s.regs 4) (s.regs 0+8))','(safe : True)')])

    def test_mapped_closed_correspondence_needs_original_state_and_path(self):
        args='s f scene shooter angle distance thing path hit back line frontPtr backPtr h traced nonempty first two backSector closed'
        self.mutations(self.contract('E1M1AimMapped','closed_correspondence',args),[
            ('(traced : E1M1AimSource.attackPath scene shooter angle distance=.ok (thing,path))','(traced : True)'),
            ('(first : path.visited[0]! = hit)','(first : True)'),
            ('(result s).pc=0x2b8d2','(result s).pc=0x2b797'),
            ('⟨s,f,0x2b760⟩','⟨s,f,0x2b77f⟩')])

    def test_operands_are_derived_from_preserved_entry_memory(self):
        args='s hit line distance record helperSafe reads range'
        self.mutations(self.contract('E1M1AimDistance','operands',args),[
            ('(record : OriginalLineFinish.RecordAt s.memory (s.regs 0) hit line)','(record : True)'),
            ('(helperSafe : E1M1AimOpening.CallerSafe s)','(helperSafe : True)'),
            ('(reads : ReadSafe s)','(reads : True)'),
            ('(range : load32 s.memory (0x2b9b8#32)=distance.raw.toBitVec)','(range : True)')])

    def test_joined_distance_requires_open_gate_and_correct_operands(self):
        args='s f hit line front back ff fc bf bc distance h reads range pass'
        self.mutations(self.contract('E1M1AimDistance','execution',args),[
            ('(h : E1M1AimMapped.Inputs s hit line front back ff fc bf bc)','(h : True)'),
            ('(reads : ReadSafe s)','(reads : True)'),
            ('(pass : (if ff.toInt≤bf.toInt then bf else ff).toInt <\n      (if bc.toInt≤fc.toInt then bc else fc).toInt)','(pass : True)'),
            ('(distance*hit.frac).raw.toBitVec','(distance*distance).raw.toBitVec'),
            ('(result s).pc=0x2b7a6','(result s).pc=0x2b797')])

    def test_original_product_requires_both_input_words(self):
        self.mutations(self.contract('OriginalAimDistance','arithmetic','s distance frac r f'),[
            ('(r : range s=distance.raw.toBitVec)','(r : True)'),
            ('(f : fraction s=frac.raw.toBitVec)','(f : True)'),
            ('(distance*frac).raw.toBitVec','(distance+frac).raw.toBitVec')])

if __name__=='__main__':unittest.main()
