"""Executable-bound death decisions, integer boundaries, and audit rejection."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_death_branches as proof
class DeathBranchesTests(unittest.TestCase):
    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-death-branches.json').read_text())
        self.raw={k:bytes.fromhex(v['hex']) for k,v in self.spec['units'].items()}
    def lean(self,source):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'Check.lean';path.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    def test_certificate_and_strict_audit(self):
        result=self.lean(proof.certificate(self.raw,'test'));self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        proof.audit(result.stdout)
        for bad in [result.stdout.replace('Quot.sound','sorryAx'),result.stdout.replace('Quot.sound','bad._native.ax_1'),result.stdout+'unexpected',result.stdout.replace('joined_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_changed_decision_bytes_rejected(self):
        for name,offset in [('guard',2),('guard',44),('guard',53),('choice',10),('choice',13),('choice',20),('choice',35),('choice',37)]:
            with self.subTest(unit=name,offset=offset):
                raw=dict(self.raw);code=bytearray(raw[name]);code[offset]^=1;raw[name]=bytes(code)
                result=self.lean(proof.certificate(raw,'test'))
                self.assertNotEqual(result.returncode,0);self.assertIn('decide',result.stdout)
    def test_missing_contract_and_wrong_result_rejected(self):
        source=proof.certificate(self.raw,'test')
        for old,new in [('(ins : DeathChoice.Inputs s hp info)','(ins : True)'),
                        ('(auto : (DeathAutomap.active s≠0) ↔ world.automap=true)','(auto : True)'),
                        ('s.regs 4-4','s.regs 4-8'),('Death.deathState hp info','info.normal'),
                        ('[0x24f90,0x30ea0] 26','[0x24f90,0x30ea0] 1')]:
            with self.subTest(change=new):
                self.assertIn(old,source);self.assertNotEqual(self.lean(source.replace(old,new)).returncode,0)
    def test_joined_entry_contract_and_lethality_required(self):
        source=proof.certificate(self.raw,'test')
        for old,new in [
            ('(h : KillDeathBranches.Inputs s v d baby i body world w y)', '(h : KillWeaponDrop.Inputs s v d baby i body world w y)'),
            ('(dead : (PlayerDamage.apply v d none false baby rng).killed=true)', '(dead : True)'),
            ('(site : pc ∈ PlayerDamageEntry.sites)', '(site : True)'),
            ('[0x24f90,0x30ea0] 239', '[0x24f90,0x30ea0] 213')]:
            with self.subTest(change=new):
                self.assertIn(old,source);self.assertNotEqual(self.lean(source.replace(old,new)).returncode,0)
    def test_joined_uses_post_damage_health_and_preserves_results(self):
        source=proof.certificate(self.raw,'test')
        for old,new in [
            ('Death.deathState (PlayerDamage.apply v d none false baby rng).state.health body.info', 'Death.deathState v.health body.info'),
            ('s.regs 4-56', 's.regs 4-52'),
            ('(KillBookkeeping.player i+248)=1', '(KillBookkeeping.player i+248)=2'),
            ('if Death.shouldStopAutomap i world then 0x2a3c8 else 0x2a3f1', 'if Death.shouldStopAutomap i world then 0x2a3f1 else 0x2a3c8')]:
            with self.subTest(change=new):
                self.assertIn(old,source);self.assertNotEqual(self.lean(source.replace(old,new)).returncode,0)
    def test_negation_decoder_semantics(self):
        result=self.lean((ROOT/'tests/reference/x86-negate.lean').read_text())
        self.assertEqual(result.returncode,0,result.stdout+result.stderr);self.assertEqual(result.stdout.split(),['true'])
    def test_pinned_extraction_and_relocations(self):
        profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
        self.assertEqual(proof.extraction.extract(binary,profile,self.spec),self.raw)
        for change in ['object','target','missing','file_offset']:
            spec=copy.deepcopy(self.spec);unit=spec['units']['guard'];rel=unit['relocations']
            if change=='object':rel[0]['object']=1
            elif change=='target':rel[0]['target']='0x2b3dd'
            elif change=='missing':rel.clear()
            else:unit['file_offset']='0x0'
            with self.assertRaises(ValueError):proof.extraction.extract(binary,profile,spec)
    def test_live_threshold_and_wrapped_negation(self):
        rows=[('-100 100 10 20',10),('-101 100 10 20',20),('-101 100 10 0',10),
              ('-2147483648 -2147483648 10 20',10),('2147483647 -2147483648 10 20',10),
              ('-1 0 4294967295 2147483648',2147483648)]
        with tempfile.TemporaryDirectory() as directory:
            inp=Path(directory)/'input';out=Path(directory)/'output';inp.write_text('\n'.join(r for r,_ in rows)+'\n')
            subprocess.run([str(ROOT/'.lake/build/bin/death-probe'),'choice',str(inp),str(out)],check=True)
            self.assertEqual(list(map(int,out.read_text().splitlines())),[v for _,v in rows])
if __name__=='__main__':unittest.main()
