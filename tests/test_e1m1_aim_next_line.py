"""Guard map persistence and construction of the actual next-line inputs."""
import re
import unittest
from pathlib import Path
import test_e1m1_aim_history_cycle as prior
import verify_e1m1_aim_next_line as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='''import Doom.Proofs.E1M1AimNextLine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1MinimumScan (address)
open E1M1SelectionHistory (History)
open E1M1HistoryDispatch (Selection)
open E1M1InterceptMark (consume)
open E1M1AimHistoryCycle (Frame)
open E1M1AimCycleInvariant (Layout QuerySafe)
open E1M1AimMapFrame (StableWord Region)
open E1M1AimNextLine (ClipGlobalsSafe)
attribute [local irreducible] load32 store32
'''
class AimNextLineTests(unittest.TestCase):
    lean=prior.AimHistoryCycleTests.lean
    succeeds=prior.AimHistoryCycleTests.succeeds
    rejects=prior.AimHistoryCycleTests.rejects
    mutations=prior.AimHistoryCycleTests.mutations
    def contract(self,module,name,args):
        source=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        start=re.search(r'^theorem '+name+r'(?: | :)',source,re.M).start()
        decl=source[start:source.index(' := by',start)]
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'
    def test_certificate_and_complete_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),42)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimMapFrame.image','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for m,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+)(?: | :)',(ROOT/f'Doom/Proofs/{m}.lean').read_text(),re.M))
    def test_map_word_requires_mark_pointer_and_protected_region(self):
        self.mutations(self.contract('E1M1AimMapFrame','word','s out marked a frame pointer bounded safe'),[
            ('(pointer : s.regs 3=address marked)','(pointer : True)'),
            ('(bounded : marked<128)','(bounded : True)'),
            ('(safe : StableWord s a)','(safe : True)'),
            ('(frame : Frame s out)','(frame : True)')])
    def test_byte_and_halfword_are_preserved_at_exact_addresses(self):
        self.mutations(self.contract('E1M1AimMapFrame','byte','s out marked a frame pointer bounded safe'),[
            ('out.core.memory a=s.memory a','out.core.memory (a+1)=s.memory a')])
        self.mutations(self.contract('E1M1AimMapFrame','half','s out marked a frame pointer bounded safe'),[
            ('load16 out.core.memory a=load16 s.memory a','load16 out.core.memory (a+2)=load16 s.memory a')])
    def test_map_image_carries_all_heights_pointers_and_flags(self):
        self.mutations(self.contract('E1M1AimMapFrame','image',proof.IMAGE_ARGS),[
            ('(safe : Region s line front back)','(safe : True)'),
            ('(before : E1M1AimOpeningFrame.Image s.memory line front back ff fc bf bc)','(before : True)'),
            ('E1M1AimOpeningFrame.Image out.core.memory line front back ff fc bf bc','E1M1AimOpeningFrame.Image out.core.memory line front back bf fc ff bc'),
            ('out.core.memory (line+(16#32))=s.memory (line+(16#32))','out.core.memory (line+(16#32))=0')])
    def test_map_and_clip_global_separation_survive_same_stack(self):
        self.mutations(self.contract('E1M1AimMapFrame','region','s t line front back stack safe'),[
            ('(stack : t.regs 4=s.regs 4)','(stack : True)')])
        self.mutations(self.contract('E1M1AimNextLine','clip_safe','s line front back safe globals'),[
            ('(globals : ClipGlobalsSafe s)','(globals : True)'),
            ('(safe : Region s line front back)','(safe : True)')])
    def test_fraction_read_protection_uses_actual_selected_record(self):
        self.mutations(self.contract('E1M1AimNextLine','distance_reads',
            's initial work seen visits resolve target sp distance j history selection records querySafe'),[
            ('(records : E1M1AimRecordFrame.RecordsSafe s.core work)','(records : True)'),
            ('(querySafe : QuerySafe s.core)','(querySafe : True)'),
            ('(selection : Selection initial work seen resolve target sp s distance j)','(selection : True)')])
    def test_next_line_requires_initial_flags_kind_and_sector_image(self):
        self.mutations(self.contract('E1M1AimNextLine','entry',proof.ENTRY_ARGS),[
            ('(two : s.memory (resolve initial[j]!+(16#32)) &&& (4#8)≠0)','(two : True)'),
            ('(isLine : initial[j]!.isLine=true)','(isLine : True)'),
            ('(mapImage : E1M1AimOpeningFrame.Image s.memory (resolve initial[j]!) front back ff fc bf bc)','(mapImage : True)')])
    def test_next_line_uses_actual_output_memory_and_preserved_protection(self):
        self.mutations(self.contract('E1M1AimNextLine','entry',proof.ENTRY_ARGS),[
            ('(mapRegion : Region s (resolve initial[j]!) front back)','(mapRegion : True)'),
            ('(frame : Frame s out)','(frame : True)'),
            ('E1M1AimMapped.Inputs out.core (consume hits marked)[j]!','E1M1AimMapped.Inputs s (consume hits marked)[j]!'),
            ('(globals : ClipGlobalsSafe s)','(globals : True)')])
if __name__=='__main__':unittest.main()
