#!/usr/bin/env python3
"""Check action-free psprite chains and their complete flash-loop continuation."""
import argparse,json,re,random,struct,subprocess
import verify_e1m1_psprite_chain as previous
from verify_original_weapon_drop import table_data
ROOT,require,extraction=previous.ROOT,previous.require,previous.extraction
NAMES=['bytes_checked','tables_checked','actions_checked','advance_checked','chain_checked','suffix_checked']
NAMES+=['Doom.Proofs.PspriteLight.'+n for n in ['decoded_store','decoded_return','execution','effect','frame','return_address','live_actions']]
NAMES+=['Doom.Proofs.PspriteChainDriver.'+n for n in ['execution','mono']]
NAMES+=['Doom.Proofs.E1M1PspriteLight.'+n for n in ['contains_light','contains_prior','contains_setter','index_entry','advance_execution','chain_execution','chain_mono','contains_slot','contains_tail','complete_execution','slot_execution','finish_execution','suffix_execution']]

def certificate(raw,tables,spec):
    s='''import Doom.Proofs.E1M1PspriteLight
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace Doom.Verification.ExtractedPspriteLight
open Doom Doom.Proofs X86 X86Memory X86Control
'''
    for i in range(3):s+=f'def light{i} : List UInt8 := ['+','.join(hex(b) for b in raw['light'+str(i)])+']\n'
    s+='def extracted (i : Fin 3) := if i=0 then light0 else if i=1 then light1 else light2\n'
    for name,bs in tables.items():s+='def '+name+' : Array UInt8 := #['+','.join(hex(b) for b in bs)+']\n'
    s+='def tableMemory : Memory := fun a =>\n'
    for name,u in spec['tables'].items():
        lo=int(u['offset'],16);s+=f'  if {lo} ≤ a.toNat ∧ a.toNat < {lo+28} then {name}[a.toNat-{lo}]!.toBitVec else\n'
    s+='  0\n'
    s+='''theorem bytes_checked (i : Fin 3) : extracted i=PspriteLight.code i := by
  have cases : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases cases with rfl|rfl|rfl <;> decide
 theorem tables_checked (i : Fin 4) :
    load32 tableMemory (BitVec.ofNat 32 (0x15a28+28*PspriteLight.stateId i)+8)=(WeaponData.frames[PspriteLight.stateId i]!).tics.toBitVec ∧
    load32 tableMemory (BitVec.ofNat 32 (0x15a28+28*PspriteLight.stateId i)+16)=BitVec.ofNat 32 (WeaponData.frames[PspriteLight.stateId i]!).next ∧
    load32 tableMemory (BitVec.ofNat 32 (0x15a28+28*PspriteLight.stateId i)+12)=BitVec.ofNat 32 (PspriteLight.entry (PspriteLight.stateLight i)) ∧
    load32 tableMemory (BitVec.ofNat 32 (0x15a28+28*PspriteLight.stateId i)+20)=0 ∧
    load32 tableMemory (BitVec.ofNat 32 (0x15a28+28*PspriteLight.stateId i)+24)=0 := by
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases cases with rfl|rfl|rfl|rfl <;> decide
 theorem actions_checked (i : Fin 3) (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix (PspriteLight.bytesProgram extracted) [] 2 ⟨s,f,PspriteLight.entry i⟩ (PspriteLight.result i s f) := by
  have bytes : extracted=PspriteLight.code := funext bytes_checked
  rw [bytes]; exact PspriteLight.execution i s f
 theorem advance_checked (s : X86Memory.State) (f : Option Flags) (t : X86Control.State) (ok : E1M1PspriteLight.advance s=some t) :
    ∃ n, n ≤ 32 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteLight.program [] n ⟨s,f,0x2d05e⟩ t :=
  E1M1PspriteLight.advance_execution s f t ok
 theorem chain_checked (fuel : Nat) (s t : X86Control.State) (ok : E1M1PspriteLight.chain fuel s=some t) :
    ∃ n, n ≤ 32*fuel+4 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteLight.program [] n s t :=
  E1M1PspriteLight.chain_execution fuel s t ok
 theorem suffix_checked (fuel : Nat) (s t : X86Control.State)
    (pc : s.pc=0x2dc95) (weaponIndex : s.core.regs 6=(0#32)) (ok : E1M1PspriteLight.suffix fuel s=some t) :
    ∃ n, n ≤ 32*fuel+46 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteLight.program [] n s t :=
  E1M1PspriteLight.suffix_execution fuel s t pc weaponIndex ok
'''
    return s+'\n'+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedPspriteLight\n'

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

def cross_check(raw,tables,spec,setter,step,loop):
    import unicorn as u
    from unicorn import x86_const as x
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);CODE,DATA,HEAP=0x100000,0x10000,0x600000
    for base,size in [(CODE,0x40000),(DATA,0x10000),(HEAP,0x4000),(0,4096),(0xfffff000,4096)]:em.mem_map(base,size)
    for i in range(3):em.mem_write(CODE+0x2db40+16*i,raw['light'+str(i)])
    for pc,bs in [(0x2d040,setter['setter']),(0x2dc60,step['psprite']),(0x2dc95,loop['tail'])]:em.mem_write(CODE+pc,bs)
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes,visits,stops=[],[],set()
    def visit(e,a,_n,_d):
        if a in stops:e.emu_stop()
        else:visits.append(a-CODE)
    em.hook_add(u.UC_HOOK_CODE,visit)
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v)))
    rng=random.Random(0x2db40);groups={};light_counts=[0,0,0];aliased=0
    def zflags(v):return (0x40 if v==0 else 0)|(0x80 if v&0x80000000 else 0)
    for mode,total in [('actions',768),('setter',1024),('flash_suffix',1024)]:
      for case in range(total):
        blocks={base:bytearray(rng.randbytes(size)) for base,size in [(DATA,0x10000),(HEAP,0x4000),(0,4096),(0xfffff000,4096)]};expected=[]
        rr=[rng.getrandbits(32) for _ in regs];align=case%4;player=HEAP+0x100+align;sp=HEAP+0x3000+align
        def block(a):
            return next(base for base,data in blocks.items() if base<=a<base+len(data))
        def read(a):return struct.unpack_from('<I',blocks[block(a)],a-block(a))[0]
        def put(a,v):struct.pack_into('<I',blocks[block(a)],a-block(a),v&0xffffffff)
        def write(a,v):put(a,v);expected.append((a,4,v&0xffffffff))
        def push(v):rr[4]=(rr[4]-4)&0xffffffff;write(rr[4],v)
        def pop(r):rr[r]=read(rr[4]);rr[4]+=4
        for name,bs in tables.items():
            bs=bytearray(bs)
            for r in spec['tables'][name]['relocations']:struct.pack_into('<I',bs,r['offset'],CODE+int(r['target'],16))
            start=int(spec['tables'][name]['offset'],16);blocks[DATA][start-DATA:start-DATA+len(bs)]=bs
        rr[4]=sp;target=CODE+0x334a9;flags=2|(rng.getrandbits(12)&0x8d5)
        if mode=='actions':
            light=case//256;entry=0x2db40+16*light;limit=2
            if case%8==0:player=0xffffff40+align
            rr[0]=player
            if case%8==1:rr[4]=(player+232)&0xffffffff;aliased+=1
            put(rr[4],target)
        elif mode=='setter':
            rr[0]=player;rr[2]=(case//4)%2;rr[3]=[1,17,30,31][(case//8)%4];put(sp,target)
            entry=0x2d040;limit=32*3+13
        else:
            rr[1]=player+244;rr[6]=0;rr[7]=player
            saved=[rng.getrandbits(32) for _ in range(5)];struct.pack_into('<6I',blocks[HEAP],sp-HEAP,*saved,target)
            old=0x15a28+28*[17,30,31][(case//4)%3];put(player+260,old);put(player+264,1)
            entry=0x2dc95;limit=32*3+46
        for base,data in blocks.items():em.mem_write(base,bytes(data))
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,flags);writes.clear();visits.clear()
        if mode=='actions':
            write((rr[0]+232)&0xffffffff,light);target=read(rr[4]);rr[4]+=4;wantflags=flags&0x8c1;light_counts[light]+=1
        else:
            if mode=='flash_suffix':
                rr[6]+=1;rr[1]+=16;rr[3]=read(rr[1]);rr[2]=read(rr[1]+4);rr[3]=(rr[2]-1)&0xffffffff;write(rr[1]+4,rr[3])
                rr[3]=read(rr[1]);rr[0]=rr[7];rr[2]=rr[6];rr[3]=read(rr[3]+16);push(CODE+0x2dc95)
            push(rr[1]);push(rr[6]);rr[6]=rr[0];rr[0]=rr[3];rr[2]=(rr[2]<<4)&0xffffffff;rr[3]=(rr[6]+244+rr[2])&0xffffffff
            for _ in range(4):
                wantflags=zflags(rr[0])
                if rr[0]==0:write(rr[3],0);break
                rr[0]=(rr[0]*28)&0xffffffff;rr[1]=0x15a28+rr[0];write(rr[3],rr[1]);rr[0]=read(rr[1]+8);write(rr[3]+4,rr[0]);rr[2]=read(rr[1]+20)
                require(rr[2]==0,'unexpected misc1 in original flash table')
                action=read(rr[1]+12);light=(action-CODE-0x2db40)//16
                require(action==CODE+0x2db40+16*light and 0<=light<3,'unexpected callback')
                rr[0]=rr[6];rr[2]=rr[3];push(CODE+0x2d095);write((rr[0]+232)&0xffffffff,light);rr[4]+=4;light_counts[light]+=1
                current=read(rr[3]);wantflags=zflags(current)
                if not current:break
                rr[0]=current;rr[2]=read(rr[3]+4);rr[0]=read(rr[0]+16);wantflags=zflags(rr[2] if rr[2] else rr[0])
                if rr[2]:break
            else:raise ValueError('unexpected nonterminating original flash chain')
            pop(6);pop(1);rr[4]+=4
            if mode=='flash_suffix':
                rr[6]+=1;rr[1]+=16;wantflags=0x40
                rr[3]=read(rr[7]+252);write(rr[7]+268,rr[3]);rr[3]=read(rr[7]+256);write(rr[7]+272,rr[3])
                for r in [7,6,2,1,3]:pop(r)
                rr[4]+=4
        stops.clear();stops.add(target)
        em.emu_start(CODE+entry,CODE+0x40000,count=limit if mode=='actions' else limit+1)
        require(writes==expected,f'writes {mode}/{case}')
        for base,data in blocks.items():require(bytes(em.mem_read(base,len(data)))==bytes(data),f'memory {mode}/{case}')
        require([em.reg_read(r) for r in regs]==rr,f'registers {mode}/{case}')
        require(em.reg_read(x.UC_X86_REG_EIP)==target,f'pc {mode}/{case}')
        require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==wantflags,f'flags {mode}/{case}')
        require(len(visits)<=limit,f'bound {mode}/{case}')
      groups[mode]=total
    return dict(cases=sum(groups.values()),groups=groups,light_calls=light_counts,aliased_stack_cases=aliased,all_registers=True,modeled_flags=True,ordered_writes=True,full_data_memory=True,
                scope='All three light actions; original flash tables through setter returns and expiring flash-loop continuation. Synthetic player/stack states, not a reachable-E1M1 invariant or full renderer equivalence.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-psprite-light.json').read_text());exe=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,exe)
    raw=extraction.extract(binary,exe,spec);tables=table_data(binary,exe,spec)
    out=ROOT/'artifacts/e1m1-psprite-light';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/verify-e1m1-psprite-chain')],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1PspriteLight'],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    path=out/'Checked.lean';path.write_text(certificate(raw,tables,spec))
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout);require(not checked.stderr.strip(),'unexpected stderr')
    native=None
    if args.cross_check:
        old=[extraction.extract(binary,exe,json.loads((ROOT/'tests/reference'/name).read_text())) for name in ['original-weapon-drop.json','original-psprite-step.json','original-psprite-loop.json']]
        native=cross_check(raw,tables,spec,*old)
    report=dict(audited_declarations=len(NAMES),axioms=checked.stdout.splitlines(),cross_check=native,
                scope='Original light actions and flash-state metadata; checked callback chains through actual returns and flash-loop continuation. Reachable memory invariants and whole-game correspondence remain open.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(checked.stdout,end='')
    print('PASS: original light actions, flash tables, and callback-chain composition.')
if __name__=='__main__':main()
