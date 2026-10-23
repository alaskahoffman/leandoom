#!/usr/bin/env python3
"""Verify original use gate, real CALL boundaries and preparation composition."""
import argparse,json,re,subprocess,random,struct
import verify_e1m1_player_selection as previous
ROOT,require,extraction=previous.ROOT,previous.require,previous.extraction
NAMES=['bytes_checked','gate_checked','resume_checked','joined_checked']
NAMES+=['Doom.Proofs.UseButtonCode.'+n for n in ['decoded','execution','resume_execution','call_argument','saved_return']]
NAMES+=['Doom.Proofs.E1M1UseButton.'+n for n in ['contains_use','contains_selection','append_use','joined_execution','runtime_selection']]

def certificate(raw):
    s='''import Doom.Proofs.E1M1UseButton
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
namespace Doom.Verification.ExtractedUseButton
open Doom Doom.Proofs X86 X86Memory X86Control BlockSummary
'''
    s+='def extracted : List UInt8 := ['+','.join(hex(b) for b in raw['use'])+']\n'
    s+='''theorem bytes_checked : extracted=UseButtonCode.code := by decide
 theorem gate_checked (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run (UseButtonCode.bytesProgram extracted) UseButtonCode.exits 6 ⟨s,f,0x33476⟩=some (UseButtonCode.result s) := by
  rw [bytes_checked]; exact UseButtonCode.execution s f
 theorem resume_checked (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run (UseButtonCode.bytesProgram extracted) [0x2dc60] 4 ⟨s,f,0x3348c⟩=some (UseButtonCode.resumed s f) := by
  rw [bytes_checked]; exact UseButtonCode.resume_execution s f
'''
    s+=(ROOT/'tests/reference/e1m1-use-button.lean').read_text()
    return s+'\n'+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedUseButton\n'

def audit(output):
    rest=output.strip()
    for short in NAMES:
        n=short if '.' in short else 'Doom.Verification.ExtractedUseButton.'+short
        m=re.match(re.escape(f"'{n}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+n)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms))
        rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw):
    import unicorn as u
    from unicorn import x86_const as x
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);CODE,DATA=0x100000,0x600000
    em.mem_map(CODE,0x40000);em.mem_map(DATA,0x3000)
    em.mem_write(CODE+0x33476,raw['use'])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes,visits=[],[]
    def visit(e,a,_n,_d):
        if a in [CODE+0x2bd10,CODE+0x2dc60]:e.emu_stop()
        else:visits.append(a-CODE)
    em.hook_add(u.UC_HOOK_CODE,visit)
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v)))
    r=random.Random(0x33476);count=0
    for resume in [False,True]:
      for buttons in range(256):
       for held in [0,1,0x80000000,0xffffffff]:
        for align in range(4):
            player=DATA+0x100+align;cmd=player+8;sp=DATA+0x2000+align
            rr=[r.getrandbits(32) for _ in regs];rr[2]=player;rr[3]=cmd;rr[4]=sp
            mem=bytearray(r.randbytes(0x3000));mem[cmd+7-DATA]=buttons
            struct.pack_into('<I',mem,player+192-DATA,held)
            em.mem_write(DATA,bytes(mem))
            for reg,value in zip(regs,rr):em.reg_write(reg,value)
            flags=2|(r.getrandbits(12)&0x8d5);em.reg_write(x.UC_X86_REG_EFLAGS,flags)
            visits.clear();writes.clear()
            em.emu_start(CODE+(0x3348c if resume else 0x33476),CODE+0x40000,count=7)
            request=bool(buttons&2 and held==0 and not resume)
            target=0x2bd10 if request else 0x2dc60
            ret=CODE+(0x3348c if request else 0x334a9)
            expected=[]
            if resume or not buttons&2:
                v=1 if resume else 0
                struct.pack_into('<I',mem,player+192-DATA,v);expected.append((player+192,4,v))
            struct.pack_into('<I',mem,sp-4-DATA,ret);expected.append((sp-4,4,ret))
            require(writes==expected,f'writes {count}')
            require(bytes(em.mem_read(DATA,len(mem)))==bytes(mem),f'memory {count}')
            rr[0]=player;rr[4]-=4
            require([em.reg_read(reg) for reg in regs]==rr,f'registers {count}')
            require(em.reg_read(x.UC_X86_REG_EIP)==CODE+target,f'callee {count}')
            want=flags&0x8c1 if resume else (0x40 if not buttons&2 or held==0 else (0x80 if held&0x80000000 else 0))
            require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==want,f'flags {count}')
            require(len(visits)<=(4 if resume else 6),f'bound {count}')
            count+=1
    return dict(cases=count,gate_cases=count//2,resume_cases=count//2,all_button_bytes=True,noncanonical_latches=True,
                embedded_player_command=True,all_registers=True,modeled_flags=True,ordered_writes=True,full_data_memory=True,
                scope='Local use gate and post-use continuation only. Stops at real callee entries; neither callee is executed or stubbed.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-use-button.json').read_text());exe=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text())
    sw=json.loads((ROOT/'tests/reference/shareware.json').read_text());binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,exe)
    raw=extraction.extract(binary,exe,spec);out=ROOT/'artifacts/e1m1-use-button';out.mkdir(parents=True,exist_ok=True)
    (out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/verify-e1m1-player-selection')],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1UseButton'],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    path=out/'Checked.lean';path.write_text(certificate(raw))
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout);require(not checked.stderr.strip(),'unexpected stderr')
    report=dict(units=spec,axioms=checked.stdout.splitlines(),audited_declarations=len(NAMES),
                scope='Conditional preparation through lethal floor damage, selection, use gate and actual CALL, bound 597. '
                      'Fresh use ends at P_UseLines entry; held/released use ends at P_MovePsprites entry. '
                      'Callee behavior, full-tic and startup/reachability proofs remain open.',
                cross_check=cross_check(raw) if args.cross_check else None)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(checked.stdout,end='');print('PASS: use gate and real callee handoff (597-instruction bound).')

if __name__=='__main__':main()
