#!/usr/bin/env python3
"""Certify original lethal player damage through the kill CALL and corpse setup."""
import argparse
import json
import random
import re
import struct
import subprocess
import tempfile
from pathlib import Path
import verify_original_actor_health as previous

ROOT,require,extraction=previous.ROOT,previous.require,previous.extraction
UNITS={k:(('ActorHealth.'+v) if '.' not in v else v) for k,v in previous.UNITS.items()}
UNITS.update(killHandoff='KillEntry.handoffBytes',corpse='KillEntry.corpseBytes')
NAMES=[name+'_checked' for name in UNITS]+['live_checked']+[
    'Doom.Proofs.KillEntry.'+name for name in
    ['decoded','handoff_execution','prologue_execution','corpse_execution','byte_and_word',
     'memory_frame','corpse_fields','setup_frame','setup_registers','setup_execution','transport',
     'execution','original_execution','final_frame','contains_previous','contains_kill',
     'joined_execution','live_correspondence']]

def certificate(raw,digest):
    source=f'''-- Executable SHA-256 {digest}; extraction/loader checked externally.
import Doom.Proofs.OriginalKillEntry
set_option maxRecDepth 32768
namespace Doom.Verification.ExtractedKillEntry
open Doom.Proofs KillEntry X86Memory X86Control
'''
    for name,definition in UNITS.items():
        literal='['+','.join(hex(b) for b in raw[name])+']'
        source+=f'def {name} : List UInt8 := {literal}\ntheorem {name}_checked : {name} = {definition} := by decide\n'
    source+='''theorem live_checked (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : Doom.PlayerDamage.State) (d : Int32)
    (baby : Bool) (rng : Doom.DoomRandom) (body : Doom.Death.Body) (h : JoinedInputs s v d baby body)
    (dead : (Doom.PlayerDamage.apply v d none false baby rng).killed=true) :
    (X86Routine.run (fun pc =>
        if (0x2a6a6 ≤ pc ∧ pc < 0x2a6b1) ∨ (0x2a2b0 ≤ pc ∧ pc < 0x2a2e6) then
          KillEntry.bytesProgram killHandoff corpse pc
        else if (0x2a650 ≤ pc ∧ pc < 0x2a6a6) ∨ (0x1bb50 ≤ pc ∧ pc < 0x1bb66) ∨
            (0x1bc41 ≤ pc ∧ pc < 0x1bc45) then ActorHealth.bytesProgram actor tactile tactileReturn pc
        else if 0x2a616 ≤ pc ∧ pc < 0x2a650 then
          (if 0x2a616 ≤ pc ∧ pc < 0x2a650 then X86Routine.decodeAt health (pc-0x2a616) else none)
        else PlayerDamageEntry.bytesProgram entry tenCall fiveCall twentyCall armor pc)
      exits 131 ⟨s,f,pc⟩).map (observation s) =
      some (liveObservation (Doom.PlayerDamage.apply v d none false baby rng) body) := by
  rw [entry_checked,tenCall_checked,fiveCall_checked,twentyCall_checked,armor_checked,
    health_checked,actor_checked,tactile_checked,tactileReturn_checked,killHandoff_checked,corpse_checked]
  exact live_correspondence s f pc site v d baby rng body h dead
'''
    return source+'\n'.join('#print axioms '+name for name in NAMES)+'\nend Doom.Verification.ExtractedKillEntry\n'

def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedKillEntry.'+short
        match=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing axiom audit: '+name)
        axioms={a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext','Classical.choice','Quot.sound'},'unexpected axioms: '+str(axioms))
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw,spec):
    import unicorn as uc
    from unicorn import x86_const as x
    corpus=previous.cases()
    heights=[-2147483648,-7,-3,-1,0,1,3,4,56*65536,2147483647]
    flag_rng=random.Random(0x2a2b0)
    flags=[(flag_rng.getrandbits(32)&~0x1000004)|(4 if c[4] else 0) for c in corpus]
    with tempfile.TemporaryDirectory() as directory:
        commands=Path(directory)/'entry.txt';commands.write_text(''.join('actor-health '+' '.join(map(str,c))+'\ncorpse '+str(flags[i])+' '+str(heights[i%len(heights)])+'\n' for i,c in enumerate(corpus)))
        answers=subprocess.check_output([str(ROOT/'.lake/build/bin/player-damage-probe'),str(commands)],text=True).splitlines()
    require(len(answers)==2*len(corpus),'probe count mismatch')
    corpse_answers=answers[1::2];answers=answers[::2]
    em=uc.Uc(uc.UC_ARCH_X86,uc.UC_MODE_32);CODE=0x100000;DYNAMIC=0x600000
    em.mem_map(CODE,0x30000)
    for base in [0,0x400000]:em.mem_map(base,0x30000)
    em.mem_map(DYNAMIC,4096);em.mem_map(0xfffff000,4096)
    registers=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
               x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];visits=[];damage_regs=[];kill_regs=[]
    em.hook_add(uc.UC_HOOK_MEM_WRITE,lambda _e,_a,addr,size,value,_u:writes.append((addr,size,value&((1 << (8*size))-1))))
    def stop(e,addr,_size,_user):
        visits.append(addr-CODE)
        if addr==CODE+0x2a6a6:damage_regs.append(tuple(e.reg_read(r) for r in registers))
        if addr==CODE+0x2a2b0:kill_regs.append(tuple(e.reg_read(r) for r in registers))
        if addr in [CODE+0x2a2e6,CODE+0x2a6b6,CODE+0x2a747]:e.emu_stop()
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
        initial_flags=flags[i];initial_height=heights[i%len(heights)]
        put(obj+104,initial_flags);put(obj+88,0);put(obj+68,initial_height)
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
        writes.clear();visits.clear();damage_regs.clear();kill_regs.clear();em.emu_start(CODE+site,CODE+0x30000,count=132)
        applied,left,expected_armor,expected_kind,expected_health,expected_count,expected_body,killed=map(int,line.split())
        end=(0x2a2e6 if killed else 0x2a6b6) if applied else 0x2a747
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+end,f'wrong branch case {i}: {row}')
        end_regs=tuple(em.reg_read(r) for r in registers)
        old_regs=damage_regs[0] if killed else end_regs
        require(old_regs[4]==sp-28 and old_regs[6]==obj,'stack/target mismatch')
        require(0x2a4ba not in visits,'environmental damage entered thrust')
        expected_writes=[(sp-4,4,CODE+site+5),(sp-8,4,values[6]),(sp-12,4,values[7]),(sp-16,4,values[5]),(sp-28,4,0),(sp-24,4,0)]
        if applied:
            accepted_count+=1
            require(old_regs[7]==u32(left),f'remaining damage case {i}: {row}')
            require(old_regs[5]==player,'player pointer mismatch')
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
        expected_flags,expected_height=map(int,corpse_answers[i].split())
        if killed:
            require(len(kill_regs)==1,'missing original kill CALL')
            k=kill_regs[0]
            require(k[0]==0 and k[2]==obj and k[4]==sp-32,'kill arguments/stack mismatch')
            expected_writes += [(sp-32,4,CODE+0x2a6b1)]+[(sp-36-4*j,4,k[r]) for j,r in enumerate([3,1,6,7,5])]
            clear=initial_flags&0xfeffbffb
            expected_writes += [(u32(obj+104),4,clear),(u32(obj+105),1,(clear>>8)&0xfd),
                                (u32(obj+104),4,expected_flags),(u32(obj+68),4,u32(expected_height))]
            require(end_regs[1]==0 and end_regs[3]==obj and end_regs[4]==sp-52,'corpse continuation registers mismatch')
            require(end_regs[2]==clear and end_regs[5]==u32(expected_height) and end_regs[6]==0 and end_regs[7]==expected_flags,'corpse scratch registers mismatch')
        else:
            require(not kill_regs,'nonlethal outcome entered kill routine')
            expected_flags,expected_height=initial_flags,initial_height
        require(struct.unpack('<I',em.mem_read(u32(obj+104),4))[0]==expected_flags,'corpse flags mismatch')
        require(struct.unpack('<I',em.mem_read(u32(obj+68),4))[0]==u32(expected_height),'corpse height mismatch')
        require((0x1bb50 in visits)==bool(applied and local_player),'tactile call decision mismatch')
        require((0x1bc44 in visits)==bool(applied and local_player),'missing real tactile RET')
        require(0x1bb66 not in visits,'entered enabled tactile-device path')
        require(struct.unpack('<I',em.mem_read(u32(obj+108),4))[0]==u32(expected_body),f'actor health mismatch {i}')
        require(struct.unpack('<I',em.mem_read(player+32,4))[0]==u32(expected_health),f'player health mismatch {i}')
        require(struct.unpack('<I',em.mem_read(player+220,4))[0]==u32(expected_count),f'damage count mismatch {i}')
        require(struct.unpack('<I',em.mem_read(player+228,4))[0]==(0 if applied else 0x12345678),f'attacker mismatch {i}')
        require(struct.unpack('<II',em.mem_read(player+36,8))==(u32(expected_armor),u32(expected_kind)),f'armor mismatch {i}')
        require(writes==expected_writes,f'write sequence mismatch {i}: {writes} != {expected_writes}')
        for addr,size,value in expected_writes:
            for off,byte in enumerate(value.to_bytes(size,'little')):
                at=u32(addr+off);before[at&~4095][at&4095]=byte
        require(all(em.mem_read(b,4096)==v for b,v in before.items()),f'memory mismatch {i}')
    return {'cases':len(corpus),'accepted':accepted_count,'rejected':blocked_count,'tactile_calls':calls,'corpse_setups':deaths,'signed_heights':heights,'all_three_floor_calls':True,
            'data_bases':[0,0x400000],'four_alignments':True,'wrapping_object_pointer':True,
            'full_dynamic_memory_and_exact_writes':True,'expected_results_from_actual_PlayerDamage_apply_and_Death_corpse':True}

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-kill-entry.json').read_text())
    profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec)
    out=ROOT/'artifacts/original-kill-entry';out.mkdir(parents=True,exist_ok=True)
    path=out/'Extracted.lean';path.write_text(certificate(raw,profile['exe_sha256']))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalKillEntry','player-damage-probe'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout)
    report={'exe_sha256':profile['exe_sha256'],'axioms':checked.stdout.splitlines(),
            'scope':'Ordinary null-source lethal player damage through the original kill CALL and corpse setup. Stops at 0x2a2e6 before kill credit, player death bookkeeping, weapon lowering, death state/RNG and returns. Initial encoding, metadata and separation premises; not whole-tic/game equivalence.',
            'cross_check':cross_check(raw,spec) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    if args.cross_check:(out/'cross-check.json').write_text(json.dumps(report['cross_check'],indent=2)+'\n')
    print(f'PASS: kill CALL and player corpse setup; {len(NAMES)} audited declarations.')
    if args.cross_check:print('Continuous original-byte/live-apply comparisons:',report['cross_check'])

if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as error:
        print(error.stdout or '');print(error.stderr or '');raise
