"""Original zombieman action scheduling with independent collision/sight hooks.

The C action oracle defers A_PosAttack at the same boundary as the Lean brain;
actual hitscan/damage is covered separately by full-engine encounter traces.
"""
from pathlib import Path
import subprocess
import tempfile
import unittest
import imp_reference
import fidelity_reference

ROOT=Path(__file__).resolve().parents[1]

class EnemyStateTests(unittest.TestCase):
    def test_zombie_look_chase_range_pain_and_attack_request(self):
        commands=[]
        for seed in range(256):
            for x in [-256,48,128,512]:
                commands += [imp_reference.setup(x=x,target=0,seed=seed,look=seed%4,
                             heard=seed%2,ambush=(seed//2)%2,sight=(seed//4)%2,shadow=(seed//8)%2),
                             'enter 174']+['tick']*80
            for reaction in [0,8]:
                commands += [imp_reference.setup(x=128,seed=seed,reaction=reaction),'range',
                             'enter 187','tick','tick','tick','tick','tick','tick']
        with tempfile.TemporaryDirectory() as folder:
            p=Path(folder); (p/'commands').write_text('\n'.join(commands)+'\n')
            (p/'reference.c').write_text(imp_reference.oracle_source(fidelity_reference.sources(),zombie=True))
            lean=subprocess.check_output([str(ROOT/'.lake/build/bin/imp-probe'),str(p/'commands'),'zombie'])
            for opt in ['-O0','-O2']:
                subprocess.run(['cc','-std=c11','-fwrapv',opt,str(p/'reference.c'),'-o',str(p/'oracle')],check=True,capture_output=True)
                reference=subprocess.check_output([str(p/'oracle'),str(p/'commands')])
                if reference!=lean:
                    for i,(a,b) in enumerate(zip(reference.splitlines(),lean.splitlines())):
                        if a!=b:self.fail(f'{opt}: command {i} {commands[i]}: C {a!r}; Lean {b!r}')
                    self.fail('different trace lengths')
            self.assertEqual(len(lean.splitlines()),len(commands))

    def test_actor_clock_proofs_have_no_unchecked_axioms(self):
        with tempfile.TemporaryDirectory() as folder:
            p=Path(folder)/'Audit.lean'
            p.write_text('import Doom.Proofs.ActorClock\n#print axioms Doom.Proofs.actor_clock_matches_original\n#print axioms Doom.Proofs.actor_clock_preserves\n')
            out=subprocess.check_output([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,text=True)
            self.assertNotIn('sorryAx',out)
            self.assertNotIn('Lean.ofReduceBool',out)
            self.assertNotIn('native',out.lower())
            self.assertIn('actor_clock_matches_original',out)
