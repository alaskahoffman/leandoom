"""Original callback dispatch, table binding, returns, and strict proof audit."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_weapon_drop as proof
class WeaponDropTests(unittest.TestCase):
    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-weapon-drop.json').read_text())
        self.raw={k:bytes.fromhex(v['hex']) for k,v in self.spec['units'].items()}
        self.tables={k:bytes.fromhex(v['hex']) for k,v in self.spec['tables'].items()}
    def lean(self,source):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'Check.lean';path.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    def source(self):return proof.certificate(self.raw,self.tables,self.spec,'test')
    def test_certificate_and_strict_audit(self):
        result=self.lean(self.source());self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        proof.audit(result.stdout)
        for bad in [result.stdout.replace('Quot.sound','sorryAx'),result.stdout.replace('Quot.sound','bad._native.ax_1'),result.stdout+'unexpected',result.stdout.replace('live_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_call_dispatch_return_bytes_rejected(self):
        for name,offset in [('drop',0),('drop',19),('drop',30),('drop',34),('setter',34),('setter',52),('setter',84),('setter',110),('lower',5),('lower',59)]:
            with self.subTest(unit=name,offset=offset):
                raw=dict(self.raw);code=bytearray(raw[name]);code[offset]^=1;raw[name]=bytes(code)
                result=self.lean(proof.certificate(raw,self.tables,self.spec,'test'))
                self.assertNotEqual(result.returncode,0);self.assertIn('decide',result.stdout)
    def test_table_state_tics_misc_action_next_rejected(self):
        for name,offset in [('info0',0),('info1',0),('info2',0),('state0',8),('state1',12),('state2',16),('state2',20)]:
            with self.subTest(table=name,offset=offset):
                tables=dict(self.tables);raw=bytearray(tables[name]);raw[offset]^=1;tables[name]=bytes(raw)
                result=self.lean(proof.certificate(self.raw,tables,self.spec,'test'))
                self.assertNotEqual(result.returncode,0);self.assertIn('decide',result.stdout)
    def test_contract_wrong_result_and_wrong_return_rejected(self):
        source=self.source()
        for old,new in [('(h : Inputs s w y)','(h : True)'),('lowerHeight y true','lowerHeight y false'),('s.regs 4+4','s.regs 4+8'),('[0x2a38c] 55','[0x2a38d] 55')]:
            with self.subTest(change=new):
                self.assertNotEqual(self.lean(source.replace(old,new)).returncode,0)
    def test_joined_missing_lethal_and_entry_contract_rejected(self):
        source=self.source()
        for old,new in [('(h : KillWeaponDrop.Inputs s v d baby i body world w y)','(h : True)'),
                        ('(dead : (PlayerDamage.apply v d none false baby rng).killed=true)','(dead : True)'),
                        ('[0x2a38c] 213','[0x2a38c] 157')]:
            with self.subTest(change=new):
                self.assertIn(old,source)
                self.assertNotEqual(self.lean(source.replace(old,new)).returncode,0)
    def test_indirect_call_decoder_and_pre_push_target(self):
        result=self.lean((ROOT/'tests/reference/x86-indirect-call.lean').read_text())
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertEqual(result.stdout.split(),['true'])
    def test_table_loader_rejects_wrong_relocation(self):
        profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text())
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
        self.assertEqual(proof.table_data(binary,profile,self.spec),self.tables)
        for modify in ['object','target','missing']:
            spec=copy.deepcopy(self.spec);rel=spec['tables']['state1']['relocations']
            if modify=='object':rel[0]['object']=3
            elif modify=='target':rel[0]['target']='0x2d491'
            else:rel.clear()
            with self.assertRaises(ValueError):proof.table_data(binary,profile,spec)
if __name__=='__main__':unittest.main()
