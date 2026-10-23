#!/usr/bin/env python3
"""Audit generic original P_SetPsprite branches and continuous local compositions."""
import argparse,json,random,re,struct,subprocess
import verify_e1m1_psprite_loop as previous
ROOT,require,extraction=previous.ROOT,previous.require,previous.extraction
NAMES=['bytes_checked','entry_checked','remove_checked','dispatch_checked','resume_checked','slot_checked']
NAMES+=['Doom.Proofs.PspriteSetter.'+n for n in ['decoded','entry_execution','return_execution','clear_execution','installed_execution','coordinates_execution','called_execution','successor_execution','coordinateGate_execution','actionGate_execution','afterAction_execution','next_execution','call_contract','return_contract']]
NAMES+=['Doom.Proofs.E1M1PspriteSetter.'+n for n in ['contains_setter','remove_execution','position_execution','dispatch_execution','resume_execution','setter_execution','slot_execution']]

def certificate(raw):
    s='''import Doom.Proofs.E1M1PspriteSetter
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace Doom.Verification.ExtractedPspriteSetter
open Doom Doom.Proofs X86 X86Memory X86Control
'''
    s+='def extracted : List UInt8 := ['+','.join(hex(x) for x in raw['setter'])+']\n'
    s+='''theorem bytes_checked : extracted=PspriteSetter.code := by decide
 theorem entry_checked (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run (PspriteSetter.bytesProgram extracted) [0x2d055,0x2d05e] 9 ⟨s,f,0x2d040⟩=some (PspriteSetter.entered s) := by
  rw [bytes_checked]; exact PspriteSetter.entry_execution s f
 theorem remove_checked (s : X86Memory.State) (f : Option Flags) (null : s.regs 3=0) :
    ∃ n, n ≤ 13 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteSetter.program [] n ⟨s,f,0x2d040⟩ (E1M1PspriteSetter.removed s) :=
  E1M1PspriteSetter.remove_execution s f null
 theorem dispatch_checked (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n ≤ 20 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteSetter.program [] n ⟨s,f,0x2d05e⟩ (E1M1PspriteSetter.dispatched s) :=
  E1M1PspriteSetter.dispatch_execution s f
 theorem resume_checked (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n ≤ 10 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteSetter.program [] n ⟨s,f,0x2d095⟩ (E1M1PspriteSetter.resumed s) :=
  E1M1PspriteSetter.resume_execution s f
 theorem slot_checked (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n ≤ 44 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteSetter.program [] n ⟨s,f,0x2dc6f⟩ (E1M1PspriteSetter.slotResult s) :=
  E1M1PspriteSetter.slot_execution s f
'''
    return s+'\n'+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedPspriteSetter\n'

def audit(output):
    rest=output.strip()
    for short in NAMES:
        n=short if '.' in short else 'Doom.Verification.ExtractedPspriteSetter.'+short
        m=re.match(re.escape(f"'{n}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+n)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms))
        rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw):
    import unicorn as u
    from unicorn import x86_const as x
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);CODE,DATA,HEAP=0x100000,0x10000,0x600000
    em.mem_map(CODE,0x40000);em.mem_write(CODE+0x2d040,raw['setter'])
    em.mem_map(DATA,0x10000);em.mem_map(HEAP,0x4000)
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes,visits,stops=[],[],set()
    def visit(e,a,_n,_d):
        if a in stops:e.emu_stop()
        else:visits.append(a-CODE)
    em.hook_add(u.UC_HOOK_CODE,visit)
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v)))
    rng=random.Random(0x2d040);groups={}
    def zflags(v):return (0x40 if v==0 else 0)|(0x80 if v&0x80000000 else 0)
    for mode in ['remove','dispatch','resume']:
      for case in range(1024):
        blocks={DATA:bytearray(rng.randbytes(0x10000)),HEAP:bytearray(rng.randbytes(0x4000))}
        expected=[];rr=[rng.getrandbits(32) for _ in regs];align=case%4
        player=HEAP+0x100+align;sp=HEAP+0x3000+align;psp=player+244+16*((case//4)%2)
        state=0x15a28+28*(1+case%127);rr[4]=sp
        def block(a):return DATA if DATA<=a<DATA+0x10000 else HEAP
        def read(a):return struct.unpack_from('<I',blocks[block(a)],a-block(a))[0]
        def put(a,v):struct.pack_into('<I',blocks[block(a)],a-block(a),v&0xffffffff)
        def write(a,v):put(a,v);expected.append((a,4,v&0xffffffff))
        if mode=='remove':
            rr[0]=player;rr[2]=(case//4)%2;rr[3]=0;put(sp,CODE+0x2dc95)
            entry=0x2d040;target=CODE+0x2dc95;limit=13
        elif mode=='dispatch':
            rr[0]=1+case%127;rr[3]=psp
            # All four coordinate/action combinations, independent of alignment.
            misc=0 if (case//4)%2==0 else rng.getrandbits(32) or 1
            callback=0 if (case//8)%2==0 else CODE+0x32000
            put(state+8,rng.getrandbits(32));put(state+20,misc);put(state+24,rng.getrandbits(32));put(state+12,callback)
            entry=0x2d05e;target=callback or CODE+0x2d09a;limit=20
        else:
            rr[3]=psp;active=(case//4)%2
            timer=[0,1,0xffffffff,0x80000000][(case//8)%4]
            nextid=0 if (case//32)%2==0 else rng.getrandbits(32) or 1
            put(psp,state if active else 0);put(psp+4,timer);put(state+16,nextid)
            entry=0x2d095;target=CODE+(0x2d0ac if not active or timer!=0 else 0x2d055 if nextid==0 else 0x2d05e);limit=10
        stops.clear();stops.add(target)
        for base,data in blocks.items():em.mem_write(base,bytes(data))
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5));writes.clear();visits.clear()
        if mode=='remove':
            rr[4]-=4;write(rr[4],rr[1]);rr[4]-=4;write(rr[4],rr[6])
            rr[6]=rr[0];rr[0]=rr[3];rr[2]=(rr[2]<<4)&0xffffffff;rr[3]=(rr[6]+244+rr[2])&0xffffffff
            write(rr[3],0);rr[6]=read(rr[4]);rr[4]+=4;rr[1]=read(rr[4]);rr[4]+=8;wantflags=0x40
        elif mode=='dispatch':
            rr[0]=(rr[0]*28)&0xffffffff;rr[1]=(0x15a28+rr[0])&0xffffffff
            write(rr[3],rr[1]);rr[0]=read(rr[1]+8);write(rr[3]+4,rr[0]);rr[2]=read(rr[1]+20)
            if rr[2]!=0:
                rr[0]=(rr[2]<<16)&0xffffffff;write(rr[3]+8,rr[0]);rr[0]=(read(rr[1]+24)<<16)&0xffffffff;write(rr[3]+12,rr[0])
            action=read(rr[1]+12);wantflags=zflags(action)
            if action:
                rr[0]=rr[6];rr[2]=rr[3];rr[4]-=4;write(rr[4],CODE+0x2d095)
        else:
            current=read(rr[3]);wantflags=zflags(current)
            if current:
                rr[0]=current;rr[2]=read(rr[3]+4);rr[0]=read(rr[0]+16)
                wantflags=zflags(rr[2] if rr[2]!=0 else rr[0])
        em.emu_start(CODE+entry,CODE+0x40000,count=limit+1)
        require(writes==expected,f'writes {mode}/{case}')
        for base,data in blocks.items():require(bytes(em.mem_read(base,len(data)))==bytes(data),f'memory {mode}/{case}')
        require([em.reg_read(r) for r in regs]==rr,f'registers {mode}/{case}')
        require(em.reg_read(x.UC_X86_REG_EIP)==target,f'pc {mode}/{case}')
        require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==wantflags,f'flags {mode}/{case}')
        require(len(visits)<=limit,f'bound {mode}/{case}')
      groups[mode]=1024
    return dict(cases=sum(groups.values()),groups=groups,all_registers=True,modeled_flags=True,ordered_writes=True,full_data_memory=True,
                scope='Local null removal/return, installation/action dispatch, and post-action successor decisions. Action bodies, repeated zero-tic chains and whole-game equivalence are not checked.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-weapon-drop.json').read_text());exe=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text())
    sw=json.loads((ROOT/'tests/reference/shareware.json').read_text());binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,exe)
    raw=extraction.extract(binary,exe,spec)
    out=ROOT/'artifacts/e1m1-psprite-setter';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/verify-e1m1-psprite-loop')],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1PspriteSetter'],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    path=out/'Checked.lean';path.write_text(certificate(raw))
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout);require(not checked.stderr.strip(),'unexpected stderr')
    report=dict(source='tests/reference/original-weapon-drop.json',audited_declarations=len(NAMES),axioms=checked.stdout.splitlines(),
                scope='Generic setter control flow: null removal/return, installation up to real action CALL, post-action successor decisions. Actions and whole-tic correspondence remain open.',
                cross_check=cross_check(raw) if args.cross_check else None)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(checked.stdout,end='')
    print('PASS: generic psprite setter branch proofs and local compositions.')
if __name__=='__main__':main()
