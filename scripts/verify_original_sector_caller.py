#!/usr/bin/env python3
"""Original caller lookup, CALL, PUSHes and secret-sector handler through RET."""
import argparse,json,re,struct,subprocess,sys,tempfile,random
from pathlib import Path
import verify_original_sector_secret as secret
ROOT,require=secret.ROOT,secret.require
NAMES=['caller_checked','entry_checked','secret_checked','return_checked','table_checked',
       'call_checked','runtime_checked','Doom.Proofs.SectorCaller.call_prefix',
       'Doom.Proofs.SectorCaller.lookup_preserved','Doom.Proofs.SectorCaller.establishes_inputs',
       'Doom.Proofs.SectorCaller.execution','Doom.Proofs.SectorCaller.restores',
       'Doom.Proofs.SectorCaller.dispatched_execution']

def certificate(raw,digest):
    lit=lambda key:'['+','.join(hex(v) for v in raw[key])+']'
    return f'''-- Original executable SHA-256 {digest}.
import Doom.Proofs.OriginalSectorCaller
namespace Doom.Verification.ExtractedSectorCaller
open X86Memory X86Control Doom.Proofs SectorCaller
def caller : List UInt8 := {lit('sectorCallerBytes')}
def entry : List UInt8 := {lit('sectorEntryBytes')}
def secret : List UInt8 := {lit('sectorSecretBytes')}
def returns : List UInt8 := {lit('sectorReturnBytes')}
def table : List UInt8 := {lit('sectorTableBytes')}
theorem caller_checked : caller = callBytes := by decide
theorem entry_checked : entry = SectorEntry.entryBytes := by decide
theorem secret_checked : secret = SectorSecret.code := by decide
theorem return_checked : returns = SectorEntry.returnBytes := by decide
theorem table_checked : table = SectorEntry.tableBytes := by decide
theorem call_checked (s : X86Memory.State) (flags : Option Flags) (z floor : Doom.Fixed) (n : Int32)
    (h : Inputs s z floor n) :
    (X86CodeMemory.run (SectorEntry.codeMemory table) (bytesProgram caller entry secret returns)
      [0x333e5] 25 ⟨s,flags,0x333e0⟩).map (fun t =>
      (t.pc,load16 t.core.memory (SectorEntry.sector s+(14#32)),
        load32 t.core.memory (SectorEntry.player s+(212#32)),preserved t.core)) =
      some (0x333e5,BitVec.ofNat 16 (Doom.LevelSpecials.secret 9 z floor n).1,
        (Doom.LevelSpecials.secret 9 z floor n).2.toBitVec,preserved s) := by
  rw [caller_checked,entry_checked,secret_checked,return_checked,table_checked]
  exact observation s flags z floor n h
theorem runtime_checked (s : X86Memory.State) (flags : Option Flags) (z floor : Doom.Fixed) (n : Int32)
    (h : Inputs (argument s) z floor n) :
    (X86CodeMemory.run (SectorEntry.codeMemory table) (bytesProgram caller entry secret returns)
      [0x333e5] 31 ⟨s,flags,0x333d0⟩).map (fun t =>
      (t.pc,load16 t.core.memory (SectorDispatch.sector s+(14#32)),
        load32 t.core.memory (s.regs 2+(212#32)),preserved t.core)) =
      some (0x333e5,BitVec.ofNat 16 (Doom.LevelSpecials.secret 9 z floor n).1,
        (Doom.LevelSpecials.secret 9 z floor n).2.toBitVec,preserved s) := by
  rw [caller_checked,entry_checked,secret_checked,return_checked,table_checked]
  exact dispatched_observation s flags z floor n h
'''+ '\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedSectorCaller\n'

def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedSectorCaller.'+short
        match=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing axiom audit: '+name)
        axioms={a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Classical.choice','Quot.sound'},'unexpected axioms: '+str(axioms))
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def cases():
    signed=lambda v: ((v+2**31)%2**32)-2**31
    return [(n,z,signed(z+delta),align) for n,z,align in secret.cases() for delta in [0,-1,1]]

def cross_check(raw,spec):
    import unicorn as uc
    from unicorn import x86_const as x
    inputs=cases()
    with tempfile.TemporaryDirectory() as directory:
        path=Path(directory)/'commands.txt'
        path.write_text(''.join(f'secret {z} {floor} 9 {n}\n' for n,z,floor,_ in inputs))
        result=subprocess.run([str(ROOT/'.lake/build/bin/level-probe'),str(path)],cwd=ROOT,capture_output=True,text=True,check=True)
    require(not result.stderr.strip(),'unexpected native diagnostics')
    answers=[tuple(map(int,line.split())) for line in result.stdout.splitlines()]
    require(len(answers)==len(inputs),'wrong native answer count')
    em=uc.Uc(uc.UC_ARCH_X86,uc.UC_MODE_32)
    for base in [0,0x100000]:
        em.mem_map(base,0x40000)
        for name,code in raw.items():
            unit=spec['units'][name];patched=bytearray(code)
            for r in unit['relocations']:
                require(r['object']==1,'unexpected code relocation')
                struct.pack_into('<I',patched,r['offset'],base+int(r['target'],16))
            em.mem_write(base+int(unit['code_offset'],16),bytes(patched))
    DATA=0x800000;em.mem_map(DATA,4096)
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
          x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes,visited=[],[]
    em.hook_add(uc.UC_HOOK_MEM_WRITE,lambda _e,_a,addr,size,value,_u:writes.append((addr,size)))
    em.hook_add(uc.UC_HOOK_CODE,lambda _e,addr,_size,_u:visited.append(addr))
    rng=random.Random(0x333D02FB20)
    paths={'on_floor':0,'off_floor':0}
    for index,((n,z,floor,align),(special,total)) in enumerate(zip(inputs,answers)):
        base=[0,0x100000][index%2]
        player,obj,sub,sector,sp=[DATA+off+align for off in [32,512,1024,1536,2048]]
        target=base+0x333e5
        em.mem_write(DATA,b'\xa5'*4096)
        values={player:obj,obj+52:sub,sub:sector,obj+20:z,sector:floor,player+212:n}
        for addr,value in values.items(): em.mem_write(addr,struct.pack('<I',value&0xffffffff))
        em.mem_write(sector+14,struct.pack('<H',9))
        initial=[rng.getrandbits(32) for _ in regs];initial[2],initial[4]=player,sp
        for reg,value in zip(regs,initial):em.reg_write(reg,value)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5))
        expected=bytearray(em.mem_read(DATA,4096))
        for offset,value in zip([4,8,12,16,20],[target,initial[3],initial[1],initial[2],initial[6]]):
            struct.pack_into('<I',expected,sp-offset-DATA,value)
        struct.pack_into('<i',expected,player+212-DATA,total)
        struct.pack_into('<H',expected,sector+14-DATA,special)
        writes.clear();visited.clear()
        em.emu_start(base+0x333d0,target,count=31)
        require(em.reg_read(x.UC_X86_REG_EIP)==target,f'return {index}')
        require(bytes(em.mem_read(DATA,4096))==bytes(expected),f'memory/native mismatch {index}')
        ground=z==floor
        require(writes==([(sp-offset,4) for offset in [4,8,12,16,20]]+([(player+212,4),(sector+14,2)] if ground else [])),f'write path {index}')
        require((base+0x2fb4f in visited)==ground and (base+0x2fbdc in visited)==ground,f'dispatch path {index}')
        require(len(visited)==(31 if ground else 23),f'instruction count {index}')
        after=initial.copy();after[0]=obj
        require([em.reg_read(r) for r in regs]==after,f'registers {index}')
        paths['on_floor' if ground else 'off_floor']+=1
    return {'cases':len(inputs),'paths':paths,'code_bases':[0,0x100000],'unaligned_addresses':True,
            'checks':['compiled live secret helper','floor branch','actual relocated code-table jump','five actual stack writes followed by secret writes',
                      'entire dynamic memory page','all registers','CALL-generated return address and restored caller ESP']}

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-sector-caller.json').read_text())
    profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text())
    sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=secret.shared.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=secret.shared.extraction.extract(binary,profile,spec,allowed_objects=(1,))
    out=ROOT/'artifacts/original-sector-caller';out.mkdir(parents=True,exist_ok=True)
    source=out/'Extracted.lean';source.write_text(certificate(raw,profile['exe_sha256']))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalSectorCaller','level-probe'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout)
    report={'exe_sha256':profile['exe_sha256'],'units':spec['units'],'axioms':checked.stdout.splitlines(),
      'scope':'Original sector lookup at 0x333d0 through CALL, four PUSHes, floor/switch/secret-or-no-op path and RET to 0x333e5. Both floor outcomes match the live helper. Saved words and return are derived from execution under initial field encoding and stack/field separation. Earlier preparation composition, other sector types, loader and whole-tic equivalence remain open.',
      'cross_check':cross_check(raw,spec) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f'PASS: original sector lookup/CALL/prologue/handler/RET; {len(NAMES)} audited declarations.')
    if args.cross_check:print('Independent original-byte/native comparisons:',report['cross_check']['cases'])
if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as error:
        print(error.stdout or '',file=sys.stderr);print(error.stderr or '',file=sys.stderr);raise
