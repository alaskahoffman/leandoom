#!/usr/bin/env python3
"""Verify all supported flash timers against the original DOS flash phase."""
import argparse,json,re,subprocess
import verify_e1m1_psprite_light as light
import verify_e1m1_flash_update as update
ROOT,require=light.ROOT,light.require
NAMES=light.NAMES+['expiry_tables_checked','expired_checked','all_checked','supported_checked']
NAMES+=['Doom.Proofs.E1M1FlashExpiry.'+n for n in ['read_store','slot_summary','expired_correspondence','live_correspondence','supported_after']]

def certificate(raw,tables,spec):
    s=light.certificate(raw,tables,spec).split('#print axioms',1)[0]
    s=s.replace('import Doom.Proofs.E1M1PspriteLight','import Doom.Proofs.E1M1FlashExpiry')
    s+='''
 theorem expiry_tables_checked : E1M1FlashExpiry.Tables tableMemory := by
  constructor <;> decide
 theorem expired_checked (s : X86Memory.State) (f : Option Flags) (p : Word) (v : Weapon.State)
    (h : E1M1FlashUpdate.Inputs s p v) (supported : WeaponFlash.Supported v)
    (nonempty : v.flash.frame≠0) (expires : v.flash.tics.toBitVec=(1#32))
    (tables : E1M1FlashExpiry.Tables s.memory) (sep : E1M1FlashExpiry.Separated p (s.regs 4)) :
    ∃ n t, n ≤ 106 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteLight.program [] n ⟨s,f,0x2dc6f⟩ t ∧
      E1M1FlashUpdate.observe t.core.memory p=WeaponFlash.observe (Weapon.tickFlash v) :=
  E1M1FlashExpiry.expired_correspondence s f p v h supported nonempty expires tables sep
 theorem all_checked (s : X86Memory.State) (f : Option Flags) (p : Word) (v : Weapon.State)
    (h : E1M1FlashUpdate.Inputs s p v) (supported : WeaponFlash.Supported v)
    (expiry : ¬ E1M1FlashUpdate.NoTransition v → E1M1FlashExpiry.Tables s.memory ∧ E1M1FlashExpiry.Separated p (s.regs 4)) :
    ∃ n t, n ≤ 106 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteLight.program [] n ⟨s,f,0x2dc6f⟩ t ∧
      E1M1FlashUpdate.observe t.core.memory p=WeaponFlash.observe (Weapon.tickFlash v) :=
  E1M1FlashExpiry.live_correspondence s f p v h supported expiry
 theorem supported_checked (v : Weapon.State) (supported : WeaponFlash.Supported v) :
    WeaponFlash.Supported (Weapon.tickFlash v) := E1M1FlashExpiry.supported_after v supported
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedPspriteLight\n'

def audit(output):
    rest=output.strip()
    for short in NAMES:
        n=short if '.' in short else 'Doom.Verification.ExtractedPspriteLight.'+short
        m=re.match(re.escape(f"'{n}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+n)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms))
        rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-psprite-light.json').read_text())
    exe=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=light.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,exe)
    raw=light.extraction.extract(binary,exe,spec);tables=light.table_data(binary,exe,spec)
    out=ROOT/'artifacts/e1m1-flash-expiry';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/verify-e1m1-flash-update')],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1FlashExpiry'],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    p=out/'Checked.lean';p.write_text(certificate(raw,tables,spec))
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout);require(not checked.stderr.strip(),'unexpected stderr')
    native=update.cross_check(out,expiry_repetitions=128) if args.cross_check else None
    report=dict(audited_declarations=len(NAMES),axioms=checked.stdout.splitlines(),cross_check=native,
                scope='All supported flash timers through the original outer RET agree with the production helper, given initial fields plus table/separation contracts on expiry. Reachability, the weapon phase, whole-tic and whole-game correspondence remain open.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(checked.stdout,end='')
    print('PASS: all supported flash timers, original DOS execution to production Lean update.')
if __name__=='__main__':main()
