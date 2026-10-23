#!/usr/bin/env python3
"""Verify original floor damage through disabled tactile and actor health."""
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
       'armor':'PlayerArmor.code','health':'PlayerHealth.code','actor':'actorBytes',
       'tactile':'tactileBytes','tactileReturn':'tactileReturnBytes'}
NAMES=[name+'_checked' for name in UNITS]+['live_checked']+[
    'Doom.Proofs.ActorHealth.'+name for name in
    ['cap_execution','console_execution','branch_execution','setup_execution','call_prefix','call_execution','body_execution',
     'decoded','stack_apart','saved_frame','execution','original_execution','memory_frame','health_value',
     'contains_health','contains_actor','joined_execution','finish_actor','live_answer','live_correspondence']]+[
    'Doom.Proofs.PlayerHealth.joined_execution_detailed']


def certificate(raw,digest):
    result=f'''-- Original executable SHA-256 {digest}; extraction/loader checked externally.
import Doom.Proofs.OriginalActorHealth
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace Doom.Verification.ExtractedActorHealth
open Doom.Proofs ActorHealth X86Memory X86Control
'''
    for name,definition in UNITS.items():
        literal='['+','.join(hex(b) for b in raw[name])+']'
        result+=f'def {name} : List UInt8 := {literal}\ntheorem {name}_checked : {name} = {definition} := by decide\n'
    result+='''theorem live_checked (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : Doom.PlayerDamage.State) (d : Int32)
    (baby : Bool) (rng : Doom.DoomRandom) (h : JoinedInputs s v d baby) :
    (X86Routine.run (fun pc =>
        if (0x2a650 ≤ pc ∧ pc < 0x2a6a6) ∨ (0x1bb50 ≤ pc ∧ pc < 0x1bb66) ∨
            (0x1bc41 ≤ pc ∧ pc < 0x1bc45) then bytesProgram actor tactile tactileReturn pc
        else if 0x2a616 ≤ pc ∧ pc < 0x2a650 then
          (if 0x2a616 ≤ pc ∧ pc < 0x2a650 then X86Routine.decodeAt health (pc-0x2a616) else none)
        else PlayerDamageEntry.bytesProgram entry tenCall fiveCall twentyCall armor pc)
      [0x2a6a6,0x2a6b6,0x2a747] 108 ⟨s,f,pc⟩).map (observation s) =
      some (liveObservation v (Doom.PlayerDamage.apply v d none false baby rng)) := by
  rw [entry_checked,tenCall_checked,fiveCall_checked,twentyCall_checked,armor_checked,
    health_checked,actor_checked,tactile_checked,tactileReturn_checked]
  exact live_correspondence s f pc site v d baby rng h
'''
    return result+'\n'.join('#print axioms '+name for name in NAMES)+'\nend Doom.Verification.ExtractedActorHealth\n'


def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedActorHealth.'+short
        match=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing axiom audit: '+name)
        axioms={a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext','Classical.choice','Quot.sound'},'unexpected axioms: '+str(axioms))
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')


def cases():
    import verify_original_player_damage_entry as entry
    rng=random.Random(0x2a616)
    edges=[-2**31,-1,0,1,99,100,101,2**31-1]
    result=[row+(rng.choice(edges),rng.choice(edges)) for row in entry.cases()]
    result += [(d,100,0,0,1,0,0,0,h,c) for d in edges for h in edges for c in edges]
    return result


def cross_check(raw,spec):
    import unicorn as uc
    from unicorn import x86_const as x
    corpus=cases()
    with tempfile.TemporaryDirectory() as directory:
        commands=Path(directory)/'entry.txt';commands.write_text(''.join('actor-health '+' '.join(map(str,c))+'\n' for c in corpus))
        answers=subprocess.check_output([str(ROOT/'.lake/build/bin/player-damage-probe'),str(commands)],text=True).splitlines()
    require(len(answers)==len(corpus),'probe count mismatch')
    em=uc.Uc(uc.UC_ARCH_X86,uc.UC_MODE_32);CODE=0x100000;DYNAMIC=0x600000
    em.mem_map(CODE,0x30000)
    for base in [0,0x400000]:em.mem_map(base,0x30000)
    em.mem_map(DYNAMIC,4096);em.mem_map(0xfffff000,4096)
    registers=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
               x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];visits=[]
    em.hook_add(uc.UC_HOOK_MEM_WRITE,lambda _e,_a,addr,size,value,_u:writes.append((addr,size,value&0xffffffff)))
    def stop(e,addr,_size,_user):
        visits.append(addr-CODE)
        if addr in [CODE+0x2a6a6,CODE+0x2a6b6,CODE+0x2a747]:e.emu_stop()
    em.hook_add(uc.UC_HOOK_CODE,stop)
    u32=lambda n:n&0xffffffff
    def put(addr,value):em.mem_write(u32(addr),struct.pack('<I',u32(value)))
    rng=random.Random(0x464c4f4f52);accepted_count=0;blocked_count=0;last_base=None;calls=0;deaths=0
    for i,(row,line) in enumerate(zip(corpus,answers)):
        damage,health,armor,kind,shoot,god,inv,baby,player_health,damage_count=row
        base=[0,0x400000][i%2]
        if base!=last_base:
            for name,code in raw.items():
                relocated=bytearray(code)
                for reloc in spec['units'][name]['relocations']:
                    require(reloc['object']==3,'unexpected relocation object')
                    struct.pack_into('<I',relocated,reloc['offset'],base+int(reloc['target'],16))
                at=CODE+int(spec['units'][name]['code_offset'],16)
                em.mem_write(at,bytes(relocated));em.ctl_remove_cache(at,at+len(code))
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
        em.mem_write(u32(obj+104),bytes([(rng.randrange(256)&~4)|(4 if shoot else 0)]))
        em.mem_write(u32(obj+107),bytes([rng.randrange(256)&~1]))
        put(player+36,armor);put(player+40,kind)
        put(player+32,player_health);put(player+220,damage_count);put(player+228,0x12345678)
        em.mem_write(player+196,bytes([(rng.randrange(256)&~2)|(2 if god else 0)]))
        put(player+44,rng.choice([1,7,0xffffffff]) if inv else 0)
        put(base+0x2b3e0,0 if baby else rng.choice([1,2,3,4,0xffffffff]))
        values=[rng.getrandbits(32) for _ in registers]
        values[0]=obj;values[1]=u32(damage);values[2]=values[3]=0;values[4]=sp
        for reg,value in zip(registers,values):em.reg_write(reg,value)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5))
        before={b:bytearray(em.mem_read(b,4096)) for b in {0,DYNAMIC,0xfffff000,player&~4095,(player+231)&~4095}}
        site=[0x2fb76,0x2fba0,0x2fbd2][i%3]
        writes.clear();visits.clear();em.emu_start(CODE+site,CODE+0x30000,count=109)
        applied,left,expected_armor,expected_kind,expected_health,expected_count,expected_body,killed=map(int,line.split())
        end=(0x2a6a6 if killed else 0x2a6b6) if applied else 0x2a747
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+end,f'wrong branch case {i}: {row}')
        require(em.reg_read(registers[4])==sp-28 and em.reg_read(registers[6])==obj,'stack/target mismatch')
        require(0x2a4ba not in visits,'environmental damage entered thrust')
        expected_writes=[(sp-4,4,CODE+site+5),(sp-8,4,values[6]),(sp-12,4,values[7]),(sp-16,4,values[5]),(sp-28,4,0),(sp-24,4,0)]
        if applied:
            accepted_count+=1
            require(em.reg_read(registers[7])==u32(left),f'remaining damage case {i}: {row}')
            require(em.reg_read(registers[5])==player,'player pointer mismatch')
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
        else:blocked_count+=1
        require((0x1bb50 in visits)==bool(applied and local_player),'tactile call decision mismatch')
        require((0x1bc44 in visits)==bool(applied and local_player),'missing real tactile RET')
        require(0x1bb66 not in visits,'entered enabled tactile-device path')
        require(struct.unpack('<I',em.mem_read(u32(obj+108),4))[0]==u32(expected_body),f'actor health mismatch {i}')
        require(struct.unpack('<I',em.mem_read(player+32,4))[0]==u32(expected_health),f'player health mismatch {i}')
        require(struct.unpack('<I',em.mem_read(player+220,4))[0]==u32(expected_count),f'damage count mismatch {i}')
        require(struct.unpack('<I',em.mem_read(player+228,4))[0]==(0 if applied else 0x12345678),f'attacker mismatch {i}')
        require(struct.unpack('<II',em.mem_read(player+36,8))==(u32(expected_armor),u32(expected_kind)),f'armor mismatch {i}')
        require(writes==expected_writes,f'write sequence mismatch {i}: {writes} != {expected_writes}')
        for addr,_size,value in expected_writes:
            for off,byte in enumerate(struct.pack('<I',value)):
                at=u32(addr+off);before[at&~4095][at&4095]=byte
        require(all(em.mem_read(b,4096)==v for b,v in before.items()),f'memory mismatch {i}')
    return {'cases':len(corpus),'accepted':accepted_count,'rejected':blocked_count,'tactile_calls':calls,'death_branches':deaths,'all_three_floor_calls':True,
            'data_bases':[0,0x400000],'four_alignments':True,'wrapping_object_pointer':True,
            'full_dynamic_memory_and_exact_writes':True,'expected_results_from_actual_PlayerDamage_apply':True}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-actor-health.json').read_text())
    profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec)
    out=ROOT/'artifacts/original-actor-health';out.mkdir(parents=True,exist_ok=True)
    path=out/'Extracted.lean';path.write_text(certificate(raw,profile['exe_sha256']))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalActorHealth','player-damage-probe'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout)
    report={'exe_sha256':profile['exe_sha256'],'axioms':checked.stdout.splitlines(),
            'scope':'Continuous original floor CALL/prologue/guards/armor/player bookkeeping from the call boundary under initial encoding and separation premises; ordinary sectors, non-skull-flying players, null inflictor/source. Includes disabled-device tactile CALL/RET, actor.health store and death/survival branch. Stops before kill/pain continuations or at rejection epilogue. No enabled tactile device, pain/death actions, handler return, Combat identity mapping or preceding-tic reachability proof.',
            'cross_check':cross_check(raw,spec) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f'PASS: actor health and tactile; {len(NAMES)} audited declarations.')
    if args.cross_check:print('Continuous original-byte/live-apply comparisons:',report['cross_check'])

if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as error:
        print(error.stdout or '');print(error.stderr or '');raise
