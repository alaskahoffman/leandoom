"""Check concrete next-probe input transport and the continuous next ray/setup."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_call_frame as prior
import verify_e1m1_aim_retry_inputs as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimRetryInputs\n'+proof.HEADER+'''
set_option maxRecDepth 32768
attribute [local irreducible] load32 store32 SolidThing.shootHeight BitVec.add
'''
class AimRetryInputsTests(unittest.TestCase):
    lean=prior.AimCallFrameTests.lean
    succeeds=prior.AimCallFrameTests.succeeds
    rejects=prior.AimCallFrameTests.rejects
    mutations=prior.AimCallFrameTests.mutations
    def contract(self,module,name):
        args=next(args for m,n,args in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimRetryInputs.prepared','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_setup_and_payload_guards_require_restored_stack(self):
        for name in ['safe','payload_safe']:
            self.mutations(self.contract('E1M1AimRetryData',name),[
                ('(stack : t.regs 4=s.regs 4)','(stack : True)')])
    def test_complete_blockmap_image_and_frame_are_required(self):
        self.mutations(self.contract('E1M1AimRetryData','map'),[
            ('(before : E1M1PathMapQuery.MapInputs s base lines words w h)','(before : True)'),
            ('(kept : ∀ a∈Doom.Proofs.E1M1AimRetryData.mapReads base words, load32 t.memory a=load32 s.memory a)',
             '(kept : True)'),
            ('(stack : t.regs 4=s.regs 4)','(stack : True)')])
    def test_cell_payload_needs_its_own_reads(self):
        self.mutations(self.contract('E1M1AimRetryData','payload'),[
            ('(before : E1M1QueryImages.Payload m q c)','(before : True)'),
            ('Doom.Proofs.E1M1AimRetryData.cellReads q c','Doom.Proofs.E1M1AimRetryData.mapReads q.base q.words')])
    def test_read_sets_use_halfword_stride_and_actual_pointer_fields(self):
        self.mutations(HEADER+'''
example (base : Word) (words : Array Nat) :
    E1M1AimRetryData.mapReads base words =
      [(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120] ++
      (List.range words.size).map (fun i => base+BitVec.ofNat 32 (2*i)) := rfl
example (q : Context) (c : Cell) (node : E1M1ThingList.Node) (member : node∈c.nodes) :
    node.pointer+44∈E1M1AimRetryData.cellReads q c := by
  simp only [E1M1AimRetryData.cellReads,List.mem_append]
  exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨node,member,by simp⟩))
example (q : Context) (c : Cell) (i : Fin c.cell.ids.length) :
    E1M1ScanGeometry.linePointer q.lines c.cell.ids[i.val]+50∈E1M1AimRetryData.cellReads q c := by
  simp only [E1M1AimRetryData.cellReads,List.mem_append]
  exact Or.inl (Or.inl (List.mem_flatMap.mpr ⟨i,by simp,by simp⟩))
''',[
            ('(2*i)','(4*i)'),
            ('node.pointer+44∈','node.pointer+48∈'),
            ('c.cell.ids[i.val]+50∈','c.cell.ids[i.val]+54∈')])
    def test_new_angle_samples_require_tables_and_actual_registers(self):
        self.mutations(self.contract('E1M1AimRetryGeometry','samples'),[
            ('(tables : ThrustTables s.memory)','(tables : True)'),
            ('(angleReg : t.regs 2=angle.raw.toBitVec)','(angleReg : t.regs 1=angle.raw.toBitVec)'),
            ('(rangeReg : t.regs 3=distance.raw.toBitVec)','(rangeReg : True)')])
        self.mutations(self.contract('E1M1AimRetryGeometry','angle_bits'),[
            ('0xf8000000','0xfc000000')])
    def test_geometry_requires_same_shooter_and_frame(self):
        self.mutations(self.contract('E1M1AimRetryGeometry','geometry'),[
            ('(actor : t.regs 0=s.regs 0)','(actor : True)'),
            ('(stack : t.regs 4=s.regs 4)','(stack : True)'),
            ('(kept : ∀ a∈Doom.Proofs.E1M1AimRetryGeometry.reads s angle, load32 t.memory a=load32 s.memory a)',
             '(kept : True)')])
    def test_prepared_inputs_and_next_setup_need_actual_request(self):
        self.mutations(self.contract('E1M1AimRetryInputs','prepared'),[
            ('(request : E1M1AimRetryRequest.Request second s next)','(request : True)'),
            ('(controller : s.regs 6=s.regs 0 ∧ s.regs 1=angle.raw.toBitVec)','(controller : True)'),
            ('(tables : ThrustTables s.memory)','(tables : True)')])
        self.mutations(self.contract('E1M1AimRetryInputs','setup'),[
            ('(pc : next.pc=0x2bb80)','(pc : True)'),
            ('[] 36 next','[] 35 next')])
    def test_complete_execution_derives_next_inputs_and_runs_next_setup(self):
        source=self.contract('E1M1AimRetryInputs','retry')
        args=source.split(' :\n    let g :=')[0]
        for absent in ['(out :','(next :','(frame :','(miss :','Prepared','traversal s']:
            self.assertNotIn(absent,args)
        self.assertIn('ThrustTables s.memory',args)
        self.assertIn('(answer.target=none →',source)
        self.mutations(source,[
            ('((n+(4+(if second then 4 else 5)))+36)','((n+(4+(if second then 4 else 5)))+35)'),
            ('(tables : ThrustTables s.memory)','(tables : True)'),
            ('(nextData : ∀ c∈nextCells, E1M1QueryImages.Payload s.memory q c ∧ E1M1AimPreRayMemory.PayloadSafe s q c)',
             '(nextData : True)')])
if __name__=='__main__':unittest.main()
