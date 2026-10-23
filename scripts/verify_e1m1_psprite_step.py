#!/usr/bin/env python3
"""Check original psprite prologue/countdown/CALL and its continuous composition."""
import argparse,json,re,random,struct,subprocess
import verify_e1m1_use_button as previous
ROOT,require,extraction=previous.ROOT,previous.require,previous.extraction
NAMES=['bytes_checked','entry_checked','slot_checked','joined_checked']
NAMES+=['Doom.Proofs.PspriteStep.'+n for n in ['decoded','entry_execution','slot_execution','execution','dispatch_arguments']]
NAMES+=['Doom.Proofs.E1M1PspriteStep.'+n for n in ['contains_step','contains_use','prefix_trans','append_step','joined_execution']]

def certificate(raw):
    s='''import Doom.Proofs.E1M1PspriteStep
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
namespace Doom.Verification.ExtractedPspriteStep
open Doom Doom.Proofs X86 X86Memory X86Control BlockSummary
'''
    s+='def extracted : List UInt8 := ['+','.join(hex(x) for x in raw['psprite'])+']\n'
    s+='''theorem bytes_checked : extracted=PspriteStep.code := by decide
 theorem entry_checked (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run (PspriteStep.bytesProgram extracted) [0x2dc6f] 8 ⟨s,f,0x2dc60⟩=some (PspriteStep.entered s) := by
  rw [bytes_checked]; exact PspriteStep.entry_execution s f
 theorem slot_checked (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run (PspriteStep.bytesProgram extracted) PspriteStep.exits 15 ⟨s,f,0x2dc6f⟩=some (PspriteStep.result s) := by
  rw [bytes_checked]; exact PspriteStep.slot_execution s f
'''
    s+=(ROOT/'tests/reference/e1m1-psprite-step.lean').read_text()
    return s+'\n'+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedPspriteStep\n'

def audit(output):
    rest=output.strip()
    for short in NAMES:
        n=short if '.' in short else 'Doom.Verification.ExtractedPspriteStep.'+short
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
    em.mem_map(CODE,0x40000);em.mem_map(DATA,0x4000)
    em.mem_write(CODE+0x2dc60,raw['psprite'])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes,visits=[],[]
    def visit(e,a,_n,_d):
        if a in [CODE+0x2dc95,CODE+0x2d040]:e.emu_stop()
        else:visits.append(a-CODE)
    em.hook_add(u.UC_HOOK_CODE,visit)
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v)))
    r=random.Random(0x2dc60);cases=0;branches=dict(empty=0,infinite=0,countdown=0,dispatch=0)
    for entry in [False,True]:
      for align in range(4):
       for active in [False,True]:
        for timer in [0,1,2,3,0x7fffffff,0x80000000,0xfffffffe,0xffffffff]+[r.getrandbits(32) for _ in range(120)]:
            player=DATA+0x100+align;slot=player+244;state=DATA+0x1000+align;sp=DATA+0x3000+align
            rr=[r.getrandbits(32) for _ in regs];rr[4]=sp
            if entry:rr[0]=player
            else:rr[1]=slot;rr[6]=cases%2;rr[7]=player
            mem=bytearray(r.randbytes(0x4000));ptr=state if active else 0;nextstate=r.getrandbits(32)
            struct.pack_into('<II',mem,slot-DATA,ptr,timer);struct.pack_into('<I',mem,state+16-DATA,nextstate)
            em.mem_write(DATA,bytes(mem))
            for reg,v in zip(regs,rr):em.reg_write(reg,v)
            em.reg_write(x.UC_X86_REG_EFLAGS,2|(r.getrandbits(12)&0x8d5))
            writes.clear();visits.clear();expected=[]
            def write(a,v):
                struct.pack_into('<I',mem,a-DATA,v);expected.append((a,4,v))
            if entry:
                for reg in [3,1,2,6,7]:rr[4]-=4;write(rr[4],rr[reg])
                rr[7]=player;rr[1]=slot;rr[6]=0
            rr[3]=ptr;target=0x2dc95
            if not active:flags=0x40;branch='empty'
            else:
                rr[2]=timer
                if timer==0xffffffff:flags=0x40;branch='infinite'
                else:
                    rr[3]=(timer-1)&0xffffffff;write(slot+4,rr[3])
                    flags=(0x40 if rr[3]==0 else 0)|(0x80 if rr[3]&0x80000000 else 0)
                    branch='countdown'
                    if rr[3]==0:
                        branch='dispatch';rr[0]=rr[7];rr[2]=rr[6];rr[3]=nextstate;rr[4]-=4
                        write(rr[4],CODE+0x2dc95);target=0x2d040
            em.emu_start(CODE+(0x2dc60 if entry else 0x2dc6f),CODE+0x40000,count=24)
            require(writes==expected,f'writes {cases}')
            require(bytes(em.mem_read(DATA,len(mem)))==bytes(mem),f'memory {cases}')
            require([em.reg_read(reg) for reg in regs]==rr,f'registers {cases}')
            require(em.reg_read(x.UC_X86_REG_EIP)==CODE+target,f'pc {cases}')
            require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==flags,f'flags {cases}')
            require(len(visits)<=(23 if entry else 15),f'bound {cases}')
            branches[branch]+=1;cases+=1
    return dict(cases=cases,branches=branches,all_registers=True,modeled_flags=True,ordered_writes=True,full_data_memory=True,
                scope='Local prologue and individual slot only; stops before loop continuation or at actual P_SetPsprite entry. Neither callee nor whole 620-instruction chain is emulated here.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-psprite-step.json').read_text());exe=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text())
    sw=json.loads((ROOT/'tests/reference/shareware.json').read_text());binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,exe)
    raw=extraction.extract(binary,exe,spec);out=ROOT/'artifacts/e1m1-psprite-step';out.mkdir(parents=True,exist_ok=True)
    (out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/verify-e1m1-use-button')],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1PspriteStep'],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    path=out/'Checked.lean';path.write_text(certificate(raw))
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout);require(not checked.stderr.strip(),'unexpected stderr')
    report=dict(units=spec,axioms=checked.stdout.splitlines(),audited_declarations=len(NAMES),
                scope='Conditional preparation/lethal-floor/selection/use chain extended through actual psprite entry and first slot, bound 620. '
                      'Fresh use ends at P_UseLines. Other paths end before the next-slot loop or at P_SetPsprite. '
                      'Callee effects, loop completion, full tic and startup/reachability remain open.',
                cross_check=cross_check(raw) if args.cross_check else None)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(checked.stdout,end='')
    print('PASS: original psprite entry/countdown/CALL and continuous 620-instruction bound.')
if __name__=='__main__':main()
