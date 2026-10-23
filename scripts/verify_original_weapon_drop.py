#!/usr/bin/env python3
"""Certify the original dead-player weapon dispatch, callback and returns."""
import argparse
import json
import random
import re
import struct
import subprocess
import tempfile
from pathlib import Path
import verify_original_inline_thrust as extraction
import verify_original_weapon_lower as lower
ROOT,require=extraction.ROOT,extraction.require
UNITS={'drop':'dropCode','setter':'setterCode','lower':'WeaponLower.code'}
NAMES=[n+'_checked' for n in UNITS]+['tables_checked','live_checked','joined_checked']+[
    'Doom.Proofs.WeaponDrop.'+n for n in ['decoded','dispatch','setter_prefix','read_store',
    'lower_inputs','prefix_inputs','lower_keep','tail_execution','execution','frame','down_live','live_correspondence']]+['Doom.Proofs.KillWeaponDrop.joined_execution']

def table_data(binary,profile,spec):
    from verify_original_arithmetic import fixups
    le=int(profile['le_offset'],16);u32=lambda p:struct.unpack_from('<I',binary,p)[0]
    require(struct.unpack_from('<6I',binary,le+u32(le+0x40)+48)==(0x85e10,0x70000,0x2043,71,38,0),'unexpected data object')
    result={}
    for name,unit in spec['tables'].items():
        start=int(unit['offset'],16);size=len(bytes.fromhex(unit['hex']));raw=bytearray()
        for p in range(start,start+size):
            entry=le+u32(le+0x48)+4*(70+p//4096)
            require(binary[entry+3]==0,'unsupported table page')
            physical=int.from_bytes(binary[entry:entry+3],'big');require(physical>0,'unmapped table page')
            at=int(profile['data_pages_offset'],16)+(physical-1)*4096+p%4096
            require(at<len(binary),'truncated table page');raw.append(binary[at])
        require(raw.hex()==unit['hex'],name+': table mismatch')
        actual={(p-(70*4096+start),o,t) for p,o,t in fixups(binary,range(70+start//4096,70+(start+size-1)//4096+1))
                if max(70*4096+start,p)<min(70*4096+start+size,p+4)}
        expected={(r['offset'],r['object'],int(r['target'],16)) for r in unit['relocations']}
        require(actual==expected,name+': table relocation mismatch')
        for offset,obj,target in expected:
            require(obj==1 and struct.unpack_from('<I',raw,offset)[0]==target,'invalid action relocation')
        result[name]=bytes(raw)
    return result

def certificate(raw,tables,spec,digest):
    s=f'''-- DOOM.EXE SHA-256 {digest}; extraction and loader checked externally.
import Doom.Proofs.OriginalKillWeaponDrop
set_option linter.unusedSimpArgs false
namespace Doom.Verification.ExtractedWeaponDrop
open Doom.Proofs WeaponDrop X86 X86Memory X86Control
'''
    for name,definition in UNITS.items():
        s+=f'def {name} : List UInt8 := ['+','.join(hex(x) for x in raw[name])+f']\ntheorem {name}_checked : {name}={definition} := by decide\n'
    for name,raw in tables.items():
        s+=f'def {name} : Array UInt8 := #['+','.join(hex(x) for x in raw)+']\n'
    s+='def tableMemory : Memory := fun a =>\n'
    for name,unit in spec['tables'].items():
        lo=int(unit['offset'],16);hi=lo+len(tables[name])
        s+=f'  if {lo} ≤ a.toNat ∧ a.toNat < {hi} then {name}[a.toNat-{lo}]!.toBitVec else\n'
    s+='  0\n'
    s+='''theorem tables_checked (w : Fin 3) :
    load32 tableMemory (info w)=down w ∧
    load32 tableMemory (state w+8)=1 ∧
    load32 tableMemory (state w+20)=0 ∧
    load32 tableMemory (state w+12)=0x2d490 ∧
    load32 tableMemory (state w+16)=down w := by
  rcases w with ⟨w,hw⟩
  have cases : w=0 ∨ w=1 ∨ w=2 := by omega
  rcases cases with rfl|rfl|rfl <;> simp only [state,info,down,Fin.val_mk] <;> decide

theorem live_checked (s : X86Memory.State) (f : Option Flags) (w : Fin 3) (y : Doom.Fixed) (h : Inputs s w y) :
    ∃ t, X86Routine.run (bytesProgram drop setter lower) [0x2a38c] 55 ⟨s,f,0x2d2c0⟩=some t ∧
      load32 t.core.memory (psp s)=0x15a28+BitVec.ofNat 32 (Doom.Weapon.down w.val)*28 ∧
      load32 t.core.memory (psp s+4)=1 ∧
      load32 t.core.memory (psp s+12)=(Doom.Weapon.lowerHeight y true).raw.toBitVec ∧
      t.pc=0x2a38c ∧ t.core.regs=write (write s.regs 0 (down w)) 4 (s.regs 4+4) ∧
      PlayerHeight.Frame s.memory t.core.memory (writes s) := by
  rw [drop_checked,setter_checked,lower_checked]
  exact live_correspondence s f w y h
'''
    s+='''theorem joined_checked (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (site : pc ∈ PlayerDamageEntry.sites) (v : PlayerDamage.State) (d : Int32) (baby : Bool)
    (rng : DoomRandom) (i : Fin 4) (body : Death.Body) (world : Death.World) (w : Fin 3) (y : Fixed)
    (h : KillWeaponDrop.Inputs s v d baby i body world w y)
    (dead : (PlayerDamage.apply v d none false baby rng).killed=true) :
    ∃ t, X86Routine.run (fun pc => match KillBookkeeping.joined pc with
        | some op => some op
        | none => bytesProgram drop setter lower pc) [0x2a38c] 213 ⟨s,f,pc⟩=some t ∧
      KillBookkeeping.joinedObservation s i t=KillBookkeeping.joinedLiveObservation
        (PlayerDamage.apply v d none false baby rng) i body world ∧
      load32 t.core.memory (KillBookkeeping.player i+244)=0x15a28+BitVec.ofNat 32 (Weapon.down w.val)*28 ∧
      load32 t.core.memory (KillBookkeeping.player i+248)=1 ∧
      load32 t.core.memory (KillBookkeeping.player i+256)=(Weapon.lowerHeight y true).raw.toBitVec ∧
      t.pc=0x2a38c ∧ t.core.regs 4=s.regs 4-52 ∧
      PlayerHeight.Frame s.memory t.core.memory (KillWeaponDrop.priorWrites s i ++ WeaponDrop.writes (KillWeaponDrop.dropView s i)) := by
  rw [drop_checked,setter_checked,lower_checked]
  exact KillWeaponDrop.joined_execution s f pc site v d baby rng i body world w y h dead
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedWeaponDrop\n'

def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedWeaponDrop.'+short
        match=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+name)
        axioms={a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms))
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw,tables,spec):
    import unicorn as uc
    from unicorn import x86_const as x
    values=lower.cases();signed=lambda n:n if n<2**31 else n-2**32
    with tempfile.TemporaryDirectory() as directory:
        inp=Path(directory)/'commands';out=Path(directory)/'out'
        inp.write_text(''.join(f'reset {i%3} 50 8 1 0 0\nheight {signed(y)}\ndie\n' for i,y in enumerate(values)))
        subprocess.run([str(ROOT/'.lake/build/bin/weapon-probe'),str(inp),str(out)],check=True)
        rows=out.read_text().splitlines();require(len(rows)==3*len(values),'probe length mismatch')
        answers=[list(map(int,r.split('|')[0].split())) for r in rows[2::3]]
    em=uc.Uc(uc.UC_ARCH_X86,uc.UC_MODE_32);CODE=0x100000;DATA=0x600000
    em.mem_map(CODE,0x30000);em.mem_map(0x10000,0x10000)
    for a in [0,DATA,0xfffff000]:em.mem_map(a,4096)
    for name,unit in spec['units'].items():em.mem_write(CODE+int(unit['code_offset'],16),raw[name])
    for name,unit in spec['tables'].items():
        data=bytearray(tables[name])
        for r in unit['relocations']:struct.pack_into('<I',data,r['offset'],CODE+int(r['target'],16))
        em.mem_write(int(unit['offset'],16),bytes(data))
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];visits=[]
    em.hook_add(uc.UC_HOOK_MEM_WRITE,lambda _e,_a,addr,size,value,_u:writes.append((addr,size,value&((1<<(8*size))-1))))
    def visit(e,addr,_size,_u):
        visits.append(addr-CODE)
        if addr==CODE+0x2a38c:e.emu_stop()
    em.hook_add(uc.UC_HOOK_CODE,visit)
    put=lambda addr,v:em.mem_write(addr&0xffffffff,struct.pack('<I',v&0xffffffff))
    rng=random.Random(0x44524f50);clamps=0
    pages=[0,DATA,0xfffff000,0x12000,0x15000]
    for i,(y,answer) in enumerate(zip(values,answers)):
        w=i%3;down=3+8*w;state=0x15a28+28*down
        player=0xfffffef0 if i%13==0 and i%11!=0 else DATA+64+i%4
        sp=DATA+3072+i%4 if i%11 else 0
        psp=(player+244)&0xffffffff;ya=(psp+12)&0xffffffff
        put(player+4,1);put(player+112,w);put(ya,y);put(sp,CODE+0x2a38c)
        rr=[rng.getrandbits(32) for _ in regs];rr[0]=player;rr[4]=sp
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5))
        before={a:bytearray(em.mem_read(a,4096)) for a in pages}
        writes.clear();visits.clear();em.emu_start(CODE+0x2d2c0,CODE+0x30000,count=56)
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+0x2a38c,f'return {i}')
        advanced=(y+0x60000)&0xffffffff;clamp=signed(advanced)>=0x800000;clamps+=clamp
        expected=0x800000 if clamp else advanced
        require(answer[4]==down and answer[5]==1 and (answer[7]&0xffffffff)==expected,'live Weapon.drop mismatch')
        require(struct.unpack('<I',em.mem_read(psp,4))[0]==state,'psprite state')
        require(struct.unpack('<I',em.mem_read((psp+4)&0xffffffff,4))[0]==1,'psprite tics')
        require(struct.unpack('<I',em.mem_read(ya,4))[0]==expected,'height')
        expected_writes=[((sp-4)&0xffffffff,4,rr[3]),((sp-8)&0xffffffff,4,rr[2]),
            ((sp-12)&0xffffffff,4,CODE+0x2d2e0),((sp-16)&0xffffffff,4,rr[1]),((sp-20)&0xffffffff,4,rr[6]),
            (psp,4,state),((psp+4)&0xffffffff,4,1),((sp-24)&0xffffffff,4,CODE+0x2d095),
            ((sp-28)&0xffffffff,4,psp),((ya+2)&0xffffffff,2,((y>>16)+6)&65535)]
        if clamp:expected_writes.append((ya,4,0x800000))
        require(writes==expected_writes,f'ordered writes {i}')
        for addr,size,value in writes:
            for off,b in enumerate(value.to_bytes(size,'little')):
                a=(addr+off)&0xffffffff;before[a&~4095][a&4095]=b
        require(all(em.mem_read(a,4096)==v for a,v in before.items()),f'memory frame {i}')
        rr[0]=down;rr[4]=(sp+4)&0xffffffff
        require([em.reg_read(r) for r in regs]==rr,f'registers {i}')
        require(visits.count(0x2d490)==1 and visits.count(0x2d095)==1 and visits.count(0x2d2e0)==1,'callback/returns')
    return {'cases':len(values),'clamped':clamps,'below':len(values)-clamps,'actual_Weapon_drop':True,
            'all_65536_integer_halves':True,'wrapping_stack':True,'unaligned_player':True,
            'high_address_player':True,'all_registers_ordered_writes_and_memory':True}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--cross-check',action='store_true');args=p.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-weapon-drop.json').read_text())
    profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec);tables=table_data(binary,profile,spec)
    out=ROOT/'artifacts/original-weapon-drop';out.mkdir(parents=True,exist_ok=True)
    path=out/'Extracted.lean';path.write_text(certificate(raw,tables,spec,profile['exe_sha256']))
    subprocess.run([str(ROOT/'scripts/verify-original-kill-bookkeeping')],cwd=ROOT,check=True)
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalKillWeaponDrop','weapon-probe'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout)
    report={'exe_sha256':profile['exe_sha256'],'scope':spec['scope'],'axioms':checked.stdout.splitlines(),
            'cross_check':cross_check(raw,tables,spec) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f'PASS: original dead-player weapon call chain; {len(NAMES)} audited declarations.')
    if args.cross_check:print(report['cross_check'])
if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as e:
        print(e.stdout or '');print(e.stderr or '');raise
