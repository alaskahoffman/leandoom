"""The first completed aim callback path must use real guards, records and RET."""
import re,unittest
from pathlib import Path
import test_e1m1_query_callback as prior
import verify_e1m1_aim_stop as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='''import Doom.Proofs.E1M1AimStop
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open Collision
open E1M1AimWall (Safe returned)
open E1M1AimSource (attackPath afterPath stopped)
attribute [local irreducible] load32 store32
'''
class AimStopTests(unittest.TestCase):
    lean=prior.QueryCallbackTests.lean
    succeeds=prior.QueryCallbackTests.succeeds
    rejects=prior.QueryCallbackTests.rejects
    mutations=prior.QueryCallbackTests.mutations

    def contract(self,module,name,args):
        s=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=re.search(r'^theorem '+name+r'(?: | :)',s,re.M).start()
        decl=s[a:s.index(' := by',a)]
        if module=='E1M1AimWall':decl=decl.replace('FloorCaller.cm program','FloorCaller.cm OriginalAimGuard.program')
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'

    def test_certificate_bytes_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),35)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimStop.execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for m,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+)(?: | :)',(ROOT/f'Doom/Proofs/{m}.lean').read_text(),re.M))
        for unit,index,value in [('aimGuard',11,1),('aimGuard',24,2),('aimStop',0,0x33)]:
            changed=dict(raw);b=bytearray(raw[unit]);self.assertNotEqual(b[index],value);b[index]=value
            changed[unit]=bytes(b);self.rejects(proof.certificate(data,changed))

    def test_real_wall_path_needs_record_flag_and_stack_contracts(self):
        args='s f hit pointer record isLine tagSafe pointerSafe flagsSafe oneSided'
        self.mutations(self.contract('E1M1AimWall','execution',args),[
            ('(record : OriginalLineFinish.RecordAt s.memory (s.regs 0) hit pointer)','(record : True)'),
            ('(isLine : hit.isLine=true)','(isLine : True)'),
            ('(pointerSafe : Safe (s.regs 4) (s.regs 0+8))','(pointerSafe : True)'),
            ('(flagsSafe : Safe (s.regs 4) (pointer+16))','(flagsSafe : True)'),
            ('(oneSided : s.memory (pointer+16) &&& (4#8)=0)','(oneSided : True)')])

    def test_parent_stop_requires_real_return_word(self):
        args='s hit pointer entry returnWord record isLine tagSafe pointerSafe flagsSafe oneSided'
        self.mutations(self.contract('E1M1AimStop','execution',args),[
            ('(returnWord : load32 s.core.memory (s.core.regs 4)=0x2c86d)','(returnWord : True)'),
            ('(entry : s.pc=0x2b760)','(entry : True)'),
            ('[] 24 s','[] 23 s'),
            ('(result s.core).pc=0x2c88c','(result s.core).pc=0x2c83a')])

    def test_live_first_wall_requires_actual_order_and_flag(self):
        self.mutations(self.contract('E1M1AimSource','first_wall','scene shooter thing path distance hit nonempty first isLine solid'),[
            ('(first : path.visited[0]! = hit)','(first : True)'),
            ('(isLine : hit.isLine=true)','(isLine : True)'),
            ('(solid : scene.lines[hit.id]!.twoSided=false)','(solid : True)'),
            ('stopped path 1','stopped path 2')])
        self.mutations(self.contract('E1M1AimSource','blocked_query','scene shooter angle distance thing path hit traced nonempty first isLine solid'),[
            ('(traced : attackPath scene shooter angle distance=.ok (thing,path))','(traced : True)')])

    def test_live_extraction_rejects_guard_and_stop_count_drift(self):
        s=(ROOT/'Doom/Proofs/E1M1AimSource.lean').read_text().split('/-- With a one-sided first wall')[0]
        s=s.replace('namespace Doom.Proofs.E1M1AimSource','namespace Doom.Proofs.ScratchAimSource')+'\nend Doom.Proofs.ScratchAimSource\n'
        self.mutations(s,[('if !line.twoSided then','if line.twoSided then')])
        # Check stop-count drift at the first-wall result, keeping the result
        # helper opaque. Comparing entire changed loops by rfl can exhaust the
        # elaborator; resource exhaustion must not count as a rejection.
        source=(ROOT/'Doom/Proofs/E1M1AimSource.lean').read_text()
        a=source.index('/-- This extraction');b=source.index('/-- With a one-sided first wall')
        source=source[:a]+'attribute [local irreducible] stopped\n'+source[b:]
        source=source.split('/-- The same early-stop result')[0]
        source=source.replace('namespace Doom.Proofs.E1M1AimSource','namespace Doom.Proofs.ScratchAimSource')+'\nend Doom.Proofs.ScratchAimSource\n'
        self.mutations(source,[('stopped path (i+1)','stopped path i')])

    def test_correspondence_requires_map_encoding_and_ordered_path(self):
        args='s hit pointer scene shooter angle distance thing path entry returnWord record isLine tagSafe pointerSafe flagsSafe flags solid traced nonempty first'
        self.mutations(self.contract('E1M1AimStop','correspondence',args),[
            ('(flags : (s.core.memory (pointer+16) &&& (4#8) != 0)=scene.lines[hit.id]!.twoSided)','(flags : True)'),
            ('(first : path.visited[0]! = hit)','(first : True)')])

if __name__=='__main__':unittest.main()
