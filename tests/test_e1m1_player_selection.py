"""Universal certificate contracts, byte provenance and rejection checks."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_e1m1_player_selection as proof


class PlayerSelectionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.spec=json.loads((ROOT/'tests/reference/original-weapon-select.json').read_text())
        cls.exe=json.loads((ROOT/'tests/reference/original-mul.json').read_text())
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        cls.binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,cls.exe)
        cls.raw=proof.extraction.extract(cls.binary,cls.exe,cls.spec)

    def lean(self,source):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True)

    def reject(self,pairs):
        source=proof.certificate(self.raw)
        for old,new in pairs:
            with self.subTest(change=new):
                self.assertIn(old,source)
                result=self.lean(source.replace(old,new))
                self.assertNotEqual(result.returncode,0,result.stdout+result.stderr)
                self.assertIn('error:',result.stdout)

    def test_certificate_and_axiom_policy(self):
        result=self.lean(proof.certificate(self.raw))
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        proof.audit(result.stdout)
        for bad in [result.stdout.replace('Quot.sound','sorryAx'),result.stdout.replace('Quot.sound','bad._native.ax_1'),
                    result.stdout+'unexpected',result.stdout.replace('boundary_agrees','missing')]:
            with self.assertRaises(ValueError): proof.audit(bad)

    def test_changed_original_bytes_rejected(self):
        for offset in [2,11,23,25,113,142]:
            with self.subTest(offset=offset):
                raw=dict(self.raw);data=bytearray(raw['selection']);data[offset]^=1;raw['selection']=bytes(data)
                result=self.lean(proof.certificate(raw))
                self.assertNotEqual(result.returncode,0);self.assertIn('decide',result.stdout)

    def test_initial_transport_contracts_required(self):
        source=proof.certificate(self.raw)
        start=source.index('    (readSafe :')
        end=source.index('    (savedSafe :',start)
        self.reject([(source[start:end],'    (readSafe : True)\n'),
          ('(selection : WeaponSelect.Inputs s buttons choice)','(selection : True)'),
          ('(selectionSafe : ∀ a, a ∈ E1M1PlayerSelection.reads s choice → ∀ v, v ∈ E1M1PlayerSelection.priorWrites kind s sim.rng → Apart a v)','(selectionSafe : True)')])

    def test_entry_exit_and_bounds_bound(self):
        self.reject([('[0x33476] 591','[0x33475] 591'),('⟨s,f,0x333b1⟩','⟨s,f,0x333b2⟩'),
                     ('[0x33476] 24','[0x33476] 23'),('before.core.regs 3=s.regs 3','before.core.regs 3=s.regs 2')])

    def test_pending_weapon_and_rng_bound(self):
        self.reject([('c.select (if b &&& (4#8)=(0#8) then none else some w.val)',
                      'c.select none'),
                     ('(E1M1FloorCycle.afterFloor kind motion.z floor tick suit sim).rng','sim.rng'),
                     ('load32 (WeaponSelect.result s b w).core.memory (s.regs 2+116)',
                      'load32 (WeaponSelect.result s b w).core.memory (s.regs 2+112)')])

    def test_extraction_mapping_and_fixups(self):
        for field,value in [('file_offset','0x0'),('code_offset','0x333e6'),('relocations',[])]:
            bad=copy.deepcopy(self.spec);bad['units']['selection'][field]=value
            with self.assertRaises(ValueError): proof.extraction.extract(self.binary,self.exe,bad)

    def test_byte_registers_decoder_and_store_flags(self):
        result=self.lean('''import Doom.Proofs.OriginalWeaponSelect
open Doom.Verification X86 X86Memory X86Control
example : X86Routine.decodeAt [0x88,0xe0] 0=some (.moveByte 0 4,2) := by decide
example : X86Routine.decodeAt [0x88,0xc4] 0=some (.moveByte 4 0,2) := by decide
example : X86Routine.decodeAt [0xf6,0xc4,4] 0=some (.testByteImmediate 4 4,3) := by decide
example : X86Routine.decodeAt [0x24,56] 0=some (.andByteImmediate 0 56,2) := by decide
example : X86Routine.decodeAt [0xc6,0x43,7,0] 0=some (.storeByteImmediate ⟨some 3,none,0,7⟩ 0,4) := by decide
example : ((X86Routine.execute (.moveByte 0 4) ⟨⟨fun _ => 0xaabbccdd,fun _ => 0⟩,none,0⟩).map (fun s => s.core.regs 0))=some (0xaabbcccc#32) := by decide
example : ((X86Routine.execute (.moveByte 4 0) ⟨⟨fun _ => 0xaabbccdd,fun _ => 0⟩,none,0⟩).map (fun s => s.core.regs 0))=some (0xaabbdddd#32) := by decide
example : ((X86Routine.execute (.testByteImmediate 4 4) ⟨⟨fun _ => 0x0400,fun _ => 0⟩,none,0⟩).map (fun s => s.flags.map (·.zero)))=some (some false) := by decide
example (s : X86Memory.State) (f : Option Flags) (a : Word) (v : BitVec 8) :
  X86Routine.execute (.storeByteImmediate ⟨none,none,0,a⟩ v) ⟨s,f,0⟩=
    some ⟨{s with memory := fun b => if b=a then v else s.memory b},f,0⟩ := by
  simp [X86Routine.execute,X86Block.Address.eval]
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_real_command_byte_boundary(self):
        result=self.lean("""import Doom.Proofs.E1M1PlayerSelection
open Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
-- player.cmd starts at player+8; its buttons byte is player+15.
-- Updating viewz at player+16 must not require a four-byte read at player+15.
example (m : Memory) (p z : Word) :
    (store32 m (p+16) z) (p+15)=m (p+15) := by
  have word : load32 (store32 m (p+16) z) (p+12)=load32 m (p+12) :=
    load_store_apart _ _ _ _ (PlayerHeight.slots_apart p 3 4 (by decide))
  have byte := congrArg (fun v : Word => v.extractLsb' 24 8) word
  have after := E1M1PlayerSelection.command_byte (store32 m (p+16) z) (p+8)
  have before := E1M1PlayerSelection.command_byte m (p+8)
  simp only [BitVec.add_assoc] at after before
  exact after.symm.trans (byte.trans before)
""")
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_compiled_selector_has_no_ammo_or_health_gate(self):
        with tempfile.TemporaryDirectory() as d:
            inp=Path(d)/'in';out=Path(d)/'out'
            inp.write_text('select 1 9 7 2 0 0 0\nselect 1 9 3 2 100 200 50\nselect 2 1 7 2 100 0 0\nselect 1 2 7 9 0 0 0\n')
            subprocess.run([str(ROOT/'.lake/build/bin/weapon-probe'),str(inp),str(out)],check=True)
            self.assertEqual([int(s.split()[1]) for s in out.read_text().splitlines()],[2,9,1,2])


if __name__=='__main__': unittest.main()
