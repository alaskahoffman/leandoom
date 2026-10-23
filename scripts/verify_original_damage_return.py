#!/usr/bin/env python3
"""Verify original floor damage through surviving damage bookkeeping and the handler RET."""
import argparse
import json
import random
import re
import struct
import subprocess
import tempfile
from pathlib import Path
import verify_original_inline_thrust as extraction

ROOT, require = extraction.ROOT, extraction.require
UNITS={'entry':'PlayerDamageEntry.entryBytes','tenCall':'PlayerDamageEntry.tenCallBytes',
       'fiveCall':'PlayerDamageEntry.fiveCallBytes','twentyCall':'PlayerDamageEntry.twentyCallBytes',
       'armor':'PlayerArmor.code','health':'PlayerHealth.code','actor':'ActorHealth.actorBytes',
       'tactile':'ActorHealth.tactileBytes','tactileReturn':'ActorHealth.tactileReturnBytes',
       'pain':'PlayerPain.painBytes','rng':'Doom19.playRandomBytes','table':'Doom19.randomTableBytes','handoff':'PainHandoff.code','setter':'Doom19.setMobjStateBytes','painState':'PainSetter.painStateBytes','tail':'code'}
NAMES=[name+'_checked' for name in UNITS]+['live_checked']+[
    'Doom.Proofs.DamageReturn.'+name for name in
    ['decoded','reset_execution','epilogue','execution','original_execution',
     'memory_frame','reaction_zero','stack_apart','saved_slots','contains_previous','contains_tail',
     'joined_execution','memory_observation','live_correspondence']]+[
    'Doom.Proofs.'+name+'.joined_execution_detailed' for name in
    ['PlayerHealth','ActorHealth','PlayerPain','PainHandoff','PainSetter']]


def table_data(binary, profile, spec):
    from verify_original_arithmetic import fixups
    le=int(profile['le_offset'],16)
    u32=lambda p:struct.unpack_from('<I',binary,p)[0]
    data=struct.unpack_from('<6I',binary,le+u32(le+0x40)+48)
    require(data==(0x85e10,0x70000,0x2043,71,38,0),'unexpected data object')
    start=int(spec['painState']['offset'],16);raw=bytearray()
    require(start==0x16b38,'wrong pain-state table address')
    for p in range(start,start+28):
        entry=le+u32(le+0x48)+4*(70+p//4096)
        require(binary[entry+3]==0,'unsupported table page')
        physical=int.from_bytes(binary[entry:entry+3],'big')
        require(physical>0,'unmapped table page')
        at=int(profile['data_pages_offset'],16)+(physical-1)*4096+p%4096
        require(at<len(binary),'truncated table page');raw.append(binary[at])
    require(raw.hex()==spec['painState']['hex'],'pain-state table mismatch')
    relocs=fixups(binary,range(70+start//4096,70+(start+27)//4096+1))
    require(not any(max(70*4096+start,p)<min(70*4096+start+28,p+4) for p,_,_ in relocs),
            'unexpected pain-state table relocation')
    require(struct.unpack('<7I',raw)==(28,6,4,0,157,0,0),'pain-state fields mismatch')
    return bytes(raw)


def certificate(raw,digest):
    result=f'''-- Original executable SHA-256 {digest}; extraction/loader checked externally.
import Doom.Proofs.OriginalDamageReturn
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace Doom.Verification.ExtractedDamageReturn
open Doom.Proofs DamageReturn X86Memory X86Control
'''
    for name,definition in UNITS.items():
        literal='['+','.join(hex(b) for b in raw[name])+']'
        result+=f'def {name} : List UInt8 := {literal}\ntheorem {name}_checked : {name} = {definition} := by decide\n'
    result+='''theorem live_checked (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : Doom.PlayerDamage.State) (d : Int32)
    (baby : Bool) (rngState : Doom.DoomRandom) (h : JoinedInputs s v d baby rngState.play)
    (applied : (Doom.PlayerDamage.apply v d none false baby rngState).applied = true)
    (alive : (Doom.PlayerDamage.apply v d none false baby rngState).killed = false) :
    (X86Routine.run (fun pc =>
        if 0x2a6df ≤ pc ∧ pc < 0x2a74e then bytesProgram tail pc
        else if 0x30ea0 ≤ pc ∧ pc < 0x30efb then PainSetter.bytesProgram setter pc
        else if 0x2a6c9 ≤ pc ∧ pc < 0x2a6df then PainHandoff.bytesProgram handoff pc
        else if (0x2a6b6 ≤ pc ∧ pc < 0x2a6c9) ∨ (0x24160 ≤ pc ∧ pc < 0x2417c) then PlayerPain.bytesProgram pain rng pc
        else if (0x2a650 ≤ pc ∧ pc < 0x2a6a6) ∨ (0x1bb50 ≤ pc ∧ pc < 0x1bb66) ∨
            (0x1bc41 ≤ pc ∧ pc < 0x1bc45) then ActorHealth.bytesProgram actor tactile tactileReturn pc
        else if 0x2a616 ≤ pc ∧ pc < 0x2a650 then
          (if 0x2a616 ≤ pc ∧ pc < 0x2a650 then X86Routine.decodeAt health (pc-0x2a616) else none)
        else PlayerDamageEntry.bytesProgram entry tenCall fiveCall twentyCall armor pc)
      exits 166 ⟨s,f,pc⟩).map (observation s) =
      some (liveObservation s (Doom.PlayerDamage.apply v d none false baby rngState)) := by
  rw [entry_checked,tenCall_checked,fiveCall_checked,twentyCall_checked,armor_checked,
    health_checked,actor_checked,tactile_checked,tactileReturn_checked,pain_checked,rng_checked,handoff_checked,setter_checked,tail_checked]
  exact live_correspondence s f pc site v d baby rngState h applied alive
'''
    return result+'\n'.join('#print axioms '+name for name in NAMES)+'\nend Doom.Verification.ExtractedDamageReturn\n'


def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedDamageReturn.'+short
        match=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing axiom audit: '+name)
        axioms={a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext','Classical.choice','Quot.sound'},'unexpected axioms: '+str(axioms))
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')


def cases():
    import verify_original_actor_health as actor
    result=[row+(n%256,) for n,row in enumerate(actor.cases())]
    # Every RNG index on survival, lethal damage and rejection, including 255 -> 0.
    result += [(d,100,0,0,shoot,0,0,0,100,0,i)
               for i in range(256) for d,shoot in [(5,1),(100,1),(5,0)]]
    return result


def cross_check(raw,spec,*,return_rejected=False):
    import unicorn as uc
    from unicorn import x86_const as x
    corpus=cases()
    timers=[0,1,18,100,-1,-2147483648,2147483647]
    with tempfile.TemporaryDirectory() as directory:
        commands=Path(directory)/'entry.txt';commands.write_text(''.join('player-return '+' '.join(map(str,c+(timers[i%len(timers)],)))+'\n' for i,c in enumerate(corpus)))
        answers=subprocess.check_output([str(ROOT/'.lake/build/bin/player-damage-probe'),str(commands)],text=True).splitlines()
    require(len(answers)==len(corpus),'probe count mismatch')
    em=uc.Uc(uc.UC_ARCH_X86,uc.UC_MODE_32);CODE=0x100000;DYNAMIC=0x600000
    em.mem_map(CODE,0x40000)
    for base in [0,0x400000]:em.mem_map(base,0x30000)
    em.mem_map(DYNAMIC,4096);em.mem_map(0xfffff000,4096)
    registers=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
               x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];visits=[];setter_calls=[];tail_calls=[]
    completed=False
    # Unicorn may expose the full source register for a byte store; compare
    # exactly the bits committed by this write's reported width.
    em.hook_add(uc.UC_HOOK_MEM_WRITE,lambda _e,_a,addr,size,value,_u:writes.append((addr,size,value&((1 << (8*size))-1))))
    def stop(e,addr,_size,_user):
        visits.append(addr-CODE)
        if addr==CODE+0x30ea0:
            setter_calls.append(tuple(e.reg_read(r) for r in registers))
        if addr==CODE+0x2a6df:tail_calls.append(tuple(e.reg_read(r) for r in registers))
        if addr in [CODE+0x2a6a6,CODE+0x2fb7b,CODE+0x2fba5,CODE+0x2fbd7] or (addr==CODE+0x2a747 and not completed):e.emu_stop()
    em.hook_add(uc.UC_HOOK_CODE,stop)
    u32=lambda n:n&0xffffffff
    def put(addr,value):em.mem_write(u32(addr),struct.pack('<I',u32(value)))
    rng=random.Random(0x464c4f4f52);accepted_count=0;blocked_count=0;last_base=None;calls=0;deaths=0;draws=0;pains=0;skips=0
    for i,(row,line) in enumerate(zip(corpus,answers)):
        damage,health,armor,kind,shoot,god,inv,baby,player_health,damage_count,seed=row
        base=[0,0x400000][i%2]
        if base!=last_base:
            for name in spec['units']:
                code=raw[name]
                relocated=bytearray(code)
                for reloc in spec['units'][name]['relocations']:
                    require(reloc['object']==3,'unexpected relocation object')
                    struct.pack_into('<I',relocated,reloc['offset'],base+int(reloc['target'],16))
                at=CODE+int(spec['units'][name]['code_offset'],16)
                em.mem_write(at,bytes(relocated));em.ctl_remove_cache(at,at+len(code))
            em.mem_write(base+0x1261c,raw['table'])
            em.mem_write(base+0x16b38,raw['painState'])
            last_base=base
        alignment=i%4
        obj=DYNAMIC+64+alignment if i%5 else 0xffffff80
        console_index=i%4
        local_player=bool((i//2)%2)
        player=base+0x2ae78+280*console_index if local_player else DYNAMIC+384+alignment
        subsector=DYNAMIC+800+alignment;sector=DYNAMIC+864+alignment;sp=DYNAMIC+3072+alignment
        put(base+0x2923c,0);put(base+0x2b3dc,console_index)
        put(obj+132,player);put(obj+52,subsector);put(subsector,sector)
        em.mem_write(sector+14,struct.pack('<H',[4,5,7,16][i%4]))
        put(obj+108,health)
        initial_reaction=timers[i%len(timers)]
        initial_threshold=[0,1,100,0xffffffff][(i//4)%4]
        initial_target=rng.getrandbits(32)
        put(obj+88,0);put(obj+124,initial_reaction);put(obj+128,initial_threshold);put(obj+120,initial_target)
        old_animation=tuple(rng.getrandbits(32) for _ in range(4))
        for off,value in zip([100,96,36,40],old_animation):put(obj+off,value)
        info=DYNAMIC+1100+alignment
        put(obj+92,info);put(info+28,156);put(info+32,255);put(base+0x12720,seed);put(base+0x1271c,197)
        em.mem_write(u32(obj+104),bytes([(rng.randrange(256)&~4)|(4 if shoot else 0)]))
        em.mem_write(u32(obj+107),bytes([rng.randrange(256)&~1]))
        put(player+36,armor);put(player+40,kind)
        put(player+32,player_health);put(player+220,damage_count);put(player+228,0x12345678)
        em.mem_write(player+196,bytes([(rng.randrange(256)&~2)|(2 if god else 0)]))
        put(player+44,rng.choice([1,7,0xffffffff]) if inv else 0)
        put(base+0x2b3e0,0 if baby else rng.choice([1,2,3,4,0xffffffff]))
        initial_flags=struct.unpack('<I',em.mem_read(u32(obj+104),4))[0]
        values=[rng.getrandbits(32) for _ in registers]
        values[0]=obj;values[1]=u32(damage);values[2]=values[3]=0;values[4]=sp
        for reg,value in zip(registers,values):em.reg_write(reg,value)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5))
        before={b:bytearray(em.mem_read(b,4096)) for b in {0,DYNAMIC,0xfffff000,player&~4095,(player+231)&~4095,(base+0x12720)&~4095}}
        site=[0x2fb76,0x2fba0,0x2fbd2][i%3]
        applied,left,expected_armor,expected_kind,expected_health,expected_count,expected_body,killed,expected_index,pain,expected_reaction=map(int,line.split())
        completed=bool(not killed and (applied or return_rejected))
        writes.clear();visits.clear();setter_calls.clear();tail_calls.clear();em.emu_start(CODE+site,CODE+0x40000,count=167)
        end=0x2a6a6 if killed else (site+5 if completed else 0x2a747)
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+end,f'wrong branch case {i}: {row}')
        require(em.reg_read(registers[4])==(sp if completed else sp-28) and em.reg_read(registers[6])==(values[6] if completed else obj),'stack/target mismatch')
        damage_regs=tail_calls[0] if applied and not killed else tuple(em.reg_read(r) for r in registers)
        require(0x2a4ba not in visits,'environmental damage entered thrust')
        expected_writes=[(sp-4,4,CODE+site+5),(sp-8,4,values[6]),(sp-12,4,values[7]),(sp-16,4,values[5]),(sp-28,4,0),(sp-24,4,0)]
        if applied:
            accepted_count+=1
            require(damage_regs[7]==u32(left),f'remaining damage case {i}: {row}')
            require(damage_regs[5]==player,'player pointer mismatch')
            if kind:
                adjusted=damage>>1 if baby else damage
                quota=(abs(adjusted)//(3 if kind==1 else 2))*(-1 if adjusted<0 else 1)
                if quota>=armor:expected_writes.append((player+40,4,0))
                expected_writes.append((player+36,4,u32(expected_armor)))
            after_health=u32(player_health-left)
            expected_writes.append((player+32,4,after_health))
            if after_health & 0x80000000:expected_writes.append((player+32,4,0))
            expected_writes.append((player+228,4,0))
            after_count=u32(damage_count+left)
            expected_writes.append((player+220,4,after_count))
            signed_count=after_count if after_count < 2**31 else after_count-2**32
            if signed_count>100:expected_writes.append((player+220,4,100))
            if local_player:
                calls+=1
                saved_ecx=armor if kind else damage
                expected_writes += [(sp-32,4,CODE+0x2a69a),(sp-36,4,u32(saved_ecx)),(sp-40,4,obj),(sp-44,4,u32(left))]
            expected_writes.append((u32(obj+108),4,u32(expected_body)))
            deaths+=killed
            if not killed:
                draws+=1;pains+=pain;skips+=not pain
                expected_writes += [(sp-32,4,CODE+0x2a6be),(base+0x12720,4,expected_index)]
                if pain:
                    expected_writes += [(u32(obj+104),1,(initial_flags & 255)|64),(sp-32,4,CODE+0x2a6df)]
                    require(len(setter_calls)==1 and setter_calls[0][0]==obj and setter_calls[0][2]==156,'wrong state-setter arguments')
                    expected_writes += [(sp-36,4,setter_calls[0][3]),(sp-40,4,obj),
                                        (u32(obj+100),4,base+0x16b38),(u32(obj+96),4,4),
                                        (u32(obj+36),4,28),(u32(obj+40),4,6)]
                    require(tail_calls[0][0]==1 and tail_calls[0][2]==157,'wrong setter result')
                    require(em.reg_read(registers[3])==setter_calls[0][3],'EBX not restored')
                    require(struct.unpack('<I',em.mem_read(sp-32,4))[0]==CODE+0x2a6df,'wrong setter return address')
                else:
                    require(em.reg_read(registers[0])==raw['table'][expected_index],'random draw mismatch')
                    require(tail_calls[0][2]==info,'info pointer not preserved by P_Random')
        else:blocked_count+=1
        if applied and not killed:
            expected_writes.append((u32(obj+124),4,0))
            require(em.reg_read(registers[2])==(0 if initial_threshold==0 else tail_calls[0][2]),'wrong source/threshold branch')
        if completed:
            require(visits.count(0x2a74d)==1,'missing damage RET')
            require(all(em.reg_read(registers[r])==values[r] for r in [4,5,6,7]),'caller registers not restored')
        require(struct.unpack('<I',em.mem_read(u32(obj+124),4))[0]==u32(expected_reaction),'reaction timer mismatch')
        require(struct.unpack('<I',em.mem_read(u32(obj+128),4))[0]==initial_threshold,'threshold changed')
        require(struct.unpack('<I',em.mem_read(u32(obj+120),4))[0]==initial_target,'retargeted null-source damage')
        require(visits.count(0x30efa)==pain and len(setter_calls)==pain,'setter CALL/RET count mismatch')
        animation=tuple(struct.unpack('<I',em.mem_read(u32(obj+off),4))[0] for off in [100,96,36,40])
        require(animation==((base+0x16b38,4,28,6) if pain else old_animation),'animation fields mismatch')
        require(visits.count(0x24160)==int(bool(applied and not killed)),'RNG call count mismatch')
        require(visits.count(0x2417b)==int(bool(applied and not killed)),'RNG RET missing')
        require(struct.unpack('<II',em.mem_read(base+0x1271c,8))==(197,expected_index),'RNG state mismatch')
        require((0x1bb50 in visits)==bool(applied and local_player),'tactile call decision mismatch')
        require((0x1bc44 in visits)==bool(applied and local_player),'missing real tactile RET')
        require(0x1bb66 not in visits,'entered enabled tactile-device path')
        require(struct.unpack('<I',em.mem_read(u32(obj+108),4))[0]==u32(expected_body),f'actor health mismatch {i}')
        require(struct.unpack('<I',em.mem_read(player+32,4))[0]==u32(expected_health),f'player health mismatch {i}')
        require(struct.unpack('<I',em.mem_read(player+220,4))[0]==u32(expected_count),f'damage count mismatch {i}')
        require(struct.unpack('<I',em.mem_read(player+228,4))[0]==(0 if applied else 0x12345678),f'attacker mismatch {i}')
        require(struct.unpack('<II',em.mem_read(player+36,8))==(u32(expected_armor),u32(expected_kind)),f'armor mismatch {i}')
        require(struct.unpack('<I',em.mem_read(u32(obj+104),4))[0]==(initial_flags|(64 if pain else 0)),'flags corruption')
        require(writes==expected_writes,f'write sequence mismatch {i}: {writes} != {expected_writes}')
        for addr,size,value in expected_writes:
            for off,byte in enumerate(value.to_bytes(size,'little')):
                at=u32(addr+off);before[at&~4095][at&4095]=byte
        require(all(em.mem_read(b,4096)==v for b,v in before.items()),f'memory mismatch {i}')
    return {'cases':len(corpus),'accepted':accepted_count,'rejected':blocked_count,'tactile_calls':calls,'death_branches':deaths,'rng_draws':draws,'pain_choices':pains,'surviving_no_pain':skips,'damage_returns':draws+(blocked_count if return_rejected else 0),'rejected_returns':blocked_count if return_rejected else 0,'reaction_timers':timers,'all_three_floor_calls':True,
            'data_bases':[0,0x400000],'four_alignments':True,'wrapping_object_pointer':True,
            'full_dynamic_memory_and_exact_writes':True,'expected_results_from_actual_PlayerDamage_apply':True}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-damage-return.json').read_text())
    profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec)
    raw['painState']=table_data(binary,profile,spec)
    import verify_original_arithmetic as arithmetic
    arithmetic_spec=json.loads((ROOT/'tests/reference/original-arithmetic.json').read_text())
    raw['table']=arithmetic.verify_units(binary,profile,arithmetic_spec)['randomTableBytes']
    out=ROOT/'artifacts/original-damage-return';out.mkdir(parents=True,exist_ok=True)
    path=out/'Extracted.lean';path.write_text(certificate(raw,profile['exe_sha256']))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalDamageReturn','player-damage-probe'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout)
    report={'exe_sha256':profile['exe_sha256'],'axioms':checked.stdout.splitlines(),
            'scope':'Continuous accepted surviving ordinary-floor damage CALL through bookkeeping, pain state, reaction reset and handler RET to the floor caller. Restores ESP/EBP/ESI/EDI and preserves earlier live results. Initial metadata/separation conditions. Rejected and lethal branches retain previous stops in the cross-check; these returns, kill handling, runtime wrapper and whole-game correspondence are outside this theorem.',
            'cross_check':cross_check(raw,spec) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f'PASS: surviving damage handler return; {len(NAMES)} audited declarations.')
    if args.cross_check:print('Continuous original-byte/live-apply comparisons:',report['cross_check'])

if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as error:
        print(error.stdout or '');print(error.stderr or '');raise
