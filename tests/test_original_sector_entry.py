"""Original floor/switch/secret/return composition and code-memory boundary."""
import json
from pathlib import Path
import struct,subprocess,sys,tempfile,unittest
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_sector_entry as proof

class SectorEntryTests(unittest.TestCase):
    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-sector-entry.json').read_text())
        self.raw={k:bytes.fromhex(v['hex']) for k,v in self.spec['units'].items()}
    def lean(self,source):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Entry.lean';p.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True)
    def test_certificate_and_strict_audit(self):
        r=self.lean(proof.certificate(self.raw,'test'));self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','unchecked._native.bv_decide.ax_1'),r.stdout.splitlines()[0],r.stdout+'extra']:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_floor_switch_and_table_mutations_rejected(self):
        for key,at,value in [('sectorEntryBytes',16,0x84),('sectorEntryBytes',30,0x05),
                             ('sectorEntryBytes',34,0x0b),('sectorEntryBytes',36,0x86),
                             ('sectorEntryBytes',48,0xfe),('sectorTableBytes',20,0xdd),
                             ('sectorReturnBytes',4,0x90)]:
            raw=dict(self.raw);code=bytearray(raw[key]);self.assertNotEqual(code[at],value)
            code[at]=value;raw[key]=bytes(code)
            r=self.lean(proof.certificate(raw,'mutation'));self.assertNotEqual(r.returncode,0,(key,at))
            with self.assertRaises(ValueError):proof.audit(r.stdout)
    def test_unsigned_carry_and_partial_register_semantics(self):
        r=self.lean('''import Doom.Proofs.OriginalSectorEntry
open Doom.Verification Doom.Verification.X86Memory Doom.Verification.X86Control
example : X86Routine.decode [0x66,0x83,0xfa,12] = some (.compareHalfRegister 2 12,[]) := by decide
example : X86Routine.decode [0x0f,0x87,0xde,0,0,0] = some (.jumpAbove 222,[]) := by decide
example (s : X86Memory.State) : X86Routine.execute (.jumpAbove 1) ⟨s,none,10⟩ = none := by rfl
example (s : X86Memory.State) : X86Routine.execute (.jumpAbove 1) ⟨s,some ⟨false,false,false,none⟩,10⟩ = none := by rfl
example (s : X86Memory.State) : (X86Routine.execute (.jumpAbove 1) ⟨s,some ⟨false,false,false,some false⟩,10⟩).map (·.pc) = some 11 := by rfl
example (s : X86Memory.State) : (X86Routine.execute (.jumpAbove 1) ⟨s,some ⟨false,false,false,some true⟩,10⟩).map (·.pc) = some 10 := by rfl
example (s : X86Memory.State) : (X86Routine.execute (.jumpAbove 1) ⟨s,some ⟨true,false,false,some false⟩,10⟩).map (·.pc) = some 10 := by rfl
example : X86Routine.decode [0x66,0x8b,0x51,0x0e] = some (.loadHalf 2 ⟨some 1,none,0,14⟩,[]) := by decide
example (s : X86Memory.State) : X86Routine.execute (.jumpCode ⟨none,none,0,0⟩) ⟨s,none,0⟩ = none := by rfl
''');self.assertEqual(r.returncode,0,r.stdout+r.stderr)
    def test_jump_table_reads_code_instead_of_data(self):
        r=self.lean('''import Doom.Proofs.OriginalSectorEntry
open Doom.Verification Doom.Verification.X86Memory Doom.Proofs.SectorEntry
example : load32 (codeMemory tableBytes) 0x2fb00 = 0x2fbdc := by decide
example : X86Routine.decode [0x2e,0xff,0x24,0x95,0xec,0xfa,2,0] =
    some (.jumpCode ⟨none,some 2,2,0x2faec⟩,[]) := by decide
example : X86Routine.decode [0xff,0x24,0x95,0xec,0xfa,2,0] = none := by decide
example : X86Routine.decode [0x2e,0xff,0x24,0x95,0xec,0xfa,2] = none := by decide
example : (X86CodeMemory.execute (codeMemory tableBytes) (.jumpCode ⟨none,none,0,0x2fb00⟩)
    ⟨⟨fun _ => 0,fun _ => 0xff⟩,none,0⟩).map (·.pc) = some 0x2fbdc := by decide
''');self.assertEqual(r.returncode,0,r.stdout+r.stderr)
    def test_initial_contract_cannot_omit_data_or_stack_relation(self):
        source='''import Doom.Proofs.OriginalSectorEntry
open Doom Doom.Verification Doom.Proofs.SectorEntry
example (s : X86Memory.State) (z floor : Fixed) (n : Int32) (h : Inputs s z floor n) : Inputs s z floor n :=
  { isSecret := h.isSecret, height := h.height, floor := h.floor, count := h.count,
    separate := h.separate, stack := h.stack, outside := h.outside }
'''
        r=self.lean(source);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        for field in ['isSecret','height','floor','count','separate','stack','outside']:
            bad=source.replace(field+' := h.'+field+', ','').replace(', '+field+' := h.'+field,'')
            r=self.lean(bad);self.assertNotEqual(r.returncode,0,field);self.assertIn('missing',r.stdout.lower())
    def test_code_relocations_require_explicit_object_permission(self):
        extraction=proof.secret.shared.extraction
        code=struct.pack('<I',0x2fbdc)
        spec={'units':{'table':{'code_offset':'0x0','file_offset':'0x0','hex':code.hex(),
            'relocations':[{'offset':0,'object':1,'target':'0x2fbdc'}]}}}
        with patch.object(extraction.original,'inspect_image',return_value=(code,list(range(4)),[(0,4)],0)), patch.object(extraction,'fixups',return_value=[(0,1,0x2fbdc)]):
            with self.assertRaises(ValueError):extraction.extract(b'',{},spec)
            self.assertEqual(extraction.extract(b'',{},spec,allowed_objects=(1,)),{'table':code})
        with patch.object(extraction.original,'inspect_image',return_value=(code,list(range(4)),[(0,4)],0)), patch.object(extraction,'fixups',return_value=[(0,3,0x2fbdc)]):
            with self.assertRaises(ValueError):extraction.extract(b'',{},spec,allowed_objects=(1,))
    def test_comparison_matrix_covers_both_floor_outcomes(self):
        cases=proof.cases();self.assertEqual(len(cases),50124)
        self.assertEqual(sum(z==floor for n,z,floor,a in cases),16708)
        self.assertTrue(any(z<floor for n,z,floor,a in cases));self.assertTrue(any(z>floor for n,z,floor,a in cases))
        self.assertTrue(any(z==-2147483648 and floor==2147483647 for n,z,floor,a in cases))
if __name__=='__main__':unittest.main()
