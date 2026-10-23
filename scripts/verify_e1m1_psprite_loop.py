#!/usr/bin/env python3
"""Check original psprite loop, coordinate copy, stack return, and composition."""
import argparse,json,re,random,struct,subprocess
import verify_e1m1_psprite_step as previous
ROOT,require,extraction=previous.ROOT,previous.require,previous.extraction
NAMES=['bytes_checked','advance_checked','copy_checked','return_checked','suffix_checked','append_checked']
NAMES+=['Doom.Proofs.PspriteLoop.'+n for n in ['decoded','advance_execution','slot_order','copy_execution','return_execution','copied_coordinates','return_stack']]
NAMES+=['Doom.Proofs.E1M1PspriteLoop.'+n for n in ['contains_tail','contains_prior','contains_slot','slot_index','suffix_execution','append_loop']]

def certificate(raw):
    s='''import Doom.Proofs.E1M1PspriteLoop
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
namespace Doom.Verification.ExtractedPspriteLoop
open Doom Doom.Proofs X86 X86Memory X86Control BlockSummary
'''
    s+='def extracted : List UInt8 := ['+','.join(hex(x) for x in raw['tail'])+']\n'
    s+='''theorem bytes_checked : extracted=PspriteLoop.code := by decide
 theorem advance_checked (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run (PspriteLoop.bytesProgram extracted) [0x2dc6f,0x2dc9e] 4 ⟨s,f,0x2dc95⟩=some (PspriteLoop.advanced s) := by
  rw [bytes_checked]; exact PspriteLoop.advance_execution s f
 theorem copy_checked (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run (PspriteLoop.bytesProgram extracted) [0x2dcb6] 4 ⟨s,f,0x2dc9e⟩=some ⟨PspriteLoop.copied s,f,0x2dcb6⟩ := by
  rw [bytes_checked]; exact PspriteLoop.copy_execution s f
 theorem return_checked (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix (PspriteLoop.bytesProgram extracted) [] 6 ⟨s,f,0x2dcb6⟩ (PspriteLoop.returned s f) := by
  rw [bytes_checked]; exact PspriteLoop.return_execution s f
 theorem suffix_checked (s : X86Control.State) (pc : s.pc=0x2dc95)
    (weapon : s.core.regs 6=0) (flashDone : (E1M1PspriteLoop.flash s).pc=0x2dc95) :
    ∃ n, n ≤ 33 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteLoop.program [] n s (E1M1PspriteLoop.finished s) :=
  E1M1PspriteLoop.suffix_execution s pc weapon flashDone
 theorem append_checked (s t : X86Control.State)
    (earlier : ∃ n, n ≤ 620 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteStep.program [] n s t)
    (pc : t.pc=0x2dc95) (weapon : t.core.regs 6=0) (flashDone : (E1M1PspriteLoop.flash t).pc=0x2dc95) :
    ∃ n, n ≤ 653 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteLoop.program [] n s (E1M1PspriteLoop.finished t) :=
  E1M1PspriteLoop.append_loop s t earlier pc weapon flashDone
'''
    return s+'\n'+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedPspriteLoop\n'

def audit(output):
    rest=output.strip()
    for short in NAMES:
        n=short if '.' in short else 'Doom.Verification.ExtractedPspriteLoop.'+short
        m=re.match(re.escape(f"'{n}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+n)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms))
        rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw,step):
    import unicorn as u
    from unicorn import x86_const as x
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);CODE,DATA=0x100000,0x600000
    em.mem_map(CODE,0x40000);em.mem_map(DATA,0x4000)
    em.mem_write(CODE+0x2dc95,raw['tail']);em.mem_write(CODE+0x2dc60,step['psprite'])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes,visits,stops=[],[],set()
    def visit(e,a,_n,_d):
        if a in stops:e.emu_stop()
        else:visits.append(a-CODE)
    em.hook_add(u.UC_HOOK_CODE,visit)
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v)))
    rng=random.Random(0x2dc95);count=0;groups={}
    def cmpflags(a,b):
        d=(a-b)&0xffffffff
        return (0x40 if d==0 else 0)|(0x80 if d&0x80000000 else 0)|(1 if a<b else 0)|(0x800 if (a^b)&(a^d)&0x80000000 else 0)
    for mode in ['advance','copy_return','suffix']:
      group=0
      for case in range(1024):
        align=case%4;player=DATA+0x100+align;sp=DATA+0x3000+align
        rr=[rng.getrandbits(32) for _ in regs];rr[4]=sp;rr[7]=player
        flags=2|(rng.getrandbits(12)&0x8d5)
        mem=bytearray(rng.randbytes(0x4000));expected=[]
        saved=[rng.getrandbits(32) for _ in range(5)];ret=CODE+0x334a9
        struct.pack_into('<6I',mem,sp-DATA,*saved,ret)
        if mode=='advance':
            rr[6]=[0,1,2,0xffffffff,0x7fffffff,0x80000000][case] if case<6 else rng.getrandbits(32)
            stops.clear();stops.update([CODE+0x2dc6f,CODE+0x2dc9e]);entry=0x2dc95;limit=4
        else:
            rr[1]=player+244;rr[6]=0
            active=case%2;timer=[0,2,3,0xffffffff,0x80000000,0xfffffffe][case%6]
            struct.pack_into('<II',mem,player+260-DATA,DATA+0x1000 if active else 0,timer)
            stops.clear();stops.add(ret);entry=0x2dc9e if mode=='copy_return' else 0x2dc95;limit=10 if mode=='copy_return' else 33
        em.mem_write(DATA,bytes(mem))
        for reg,v in zip(regs,rr):em.reg_write(reg,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,flags);writes.clear();visits.clear()
        def write(a,v):
            struct.pack_into('<I',mem,a-DATA,v);expected.append((a,4,v))
        def read(a):return struct.unpack_from('<I',mem,a-DATA)[0]
        if mode=='advance':
            rr[6]=(rr[6]+1)&0xffffffff;rr[1]=(rr[1]+16)&0xffffffff
            wantflags=cmpflags(rr[6],2);signed=rr[6] if rr[6]<0x80000000 else rr[6]-0x100000000
            target=CODE+(0x2dc6f if signed<2 else 0x2dc9e)
        else:
            if mode=='suffix' and active and timer!=0xffffffff:write(player+264,(timer-1)&0xffffffff)
            write(player+268,read(player+252));write(player+272,read(player+256))
            for reg,v in zip([7,6,2,1,3],saved):rr[reg]=v
            rr[4]+=24;target=ret;wantflags=flags&0x8c1 if mode=='copy_return' else 0x40
        em.emu_start(CODE+entry,CODE+0x40000,count=limit+1)
        require(writes==expected,f'writes {mode}/{case}')
        require(bytes(em.mem_read(DATA,len(mem)))==bytes(mem),f'memory {mode}/{case}')
        require([em.reg_read(reg) for reg in regs]==rr,f'registers {mode}/{case}')
        require(em.reg_read(x.UC_X86_REG_EIP)==target,f'pc {mode}/{case}')
        require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==wantflags,f'flags {mode}/{case}')
        require(len(visits)<=limit,f'bound {mode}/{case}')
        count+=1;group+=1
      groups[mode]=group
    return dict(cases=count,groups=groups,all_registers=True,modeled_flags=True,ordered_writes=True,full_data_memory=True,
                scope='Local loop gate, copy/RET, and no-flash-transition continuation. Earlier 620-instruction prefix and setter actions are not emulated here.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-psprite-loop.json').read_text());exe=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text())
    sw=json.loads((ROOT/'tests/reference/shareware.json').read_text());binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,exe)
    raw=extraction.extract(binary,exe,spec);step=extraction.extract(binary,exe,json.loads((ROOT/'tests/reference/original-psprite-step.json').read_text()))
    out=ROOT/'artifacts/e1m1-psprite-loop';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/verify-e1m1-psprite-step')],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1PspriteLoop'],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    path=out/'Checked.lean';path.write_text(certificate(raw))
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout);require(not checked.stderr.strip(),'unexpected stderr')
    report=dict(units=spec,axioms=checked.stdout.splitlines(),audited_declarations=len(NAMES),
                scope='Loop advance, coordinate copy and actual RET. Conditional no-flash-transition continuation adds at most 33 instructions to a prior 620-instruction prefix. '
                      'Weapon completion/slot-index/flash completion remain explicit boundary conditions; setter actions and full-tic correspondence remain open.',
                cross_check=cross_check(raw,step) if args.cross_check else None)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(checked.stdout,end='')
    print('PASS: psprite loop/copy/return and conditional 653-instruction prefix.')
if __name__=='__main__':main()
