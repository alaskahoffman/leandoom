#!/usr/bin/env python3
"""Extract and independently compare DOS P_CalcHeight with the live Lean function.
The kernel certificate proves the complete routine under an explicit entry contract.
Independent native/emulator comparisons additionally check the model and compiled runtime.
"""
import argparse, json, random, re, struct, subprocess, sys
import verify_original_player_joined as joined
ROOT, require = joined.ROOT, joined.require

NAMES=['bytes_checked','recovery_checked','ceiling_checked','airborne_checked',
       'amplitude_checked','offset_checked','function_checked','caller_bytes_checked','caller_checked',
       'Doom.Proofs.PlayerHeight.Caller.establishes_function',
       'Doom.Proofs.PlayerHeight.Caller.entry_return',
       'Doom.Proofs.PlayerHeight.Caller.execution',
       'reaction_bytes_checked','movement_bytes_checked','state_bytes_checked',
       'Doom.Proofs.PlayerGround.reaction_ground',
       'Doom.Proofs.PlayerHeightJoin.establishes_height',
       'Doom.Proofs.PlayerHeightJoin.observation',
       'preparation_checked','Doom.Proofs.PlayerPreparation.execution',
       'prepared_state_checked','runtime_checked',
       'Doom.Proofs.PreparedState.retained_safe','Doom.Proofs.PreparedState.execution',
       'Doom.Proofs.PreparedState.observation','Doom.Proofs.PreparedRuntime.prepare',
       'Doom.Proofs.PreparedRuntime.correspondence',
       'Doom.Proofs.PlayerHeight.Shared.execute_shift',
       'Doom.Proofs.PlayerHeight.Shared.lift_prefix',
       'Doom.Proofs.PlayerHeight.Shared.entry_return',
       'Doom.Proofs.PlayerHeight.Shared.execution',
       'Doom.Proofs.PlayerHeight.Function.execution_bytes',
       'Doom.Proofs.PlayerHeight.quarter_word','Doom.Proofs.PlayerHeight.half_word',
       'Doom.Proofs.PlayerHeight.bob_index','Doom.Proofs.PlayerHeight.bob_table_address',
       'Doom.Proofs.PlayerHeight.decoded','Doom.Proofs.PlayerHeight.recover_runtime',
       'Doom.Proofs.PlayerHeight.clamp_runtime','Doom.Proofs.PlayerHeight.airborne_previous_store']

def certificate(raw,digest):
    literal='['+','.join(hex(v) for v in raw['calcHeightBytes'])+']'
    lit=lambda key:'['+','.join(hex(v) for v in raw[key])+']'
    caller_literal='['+','.join(hex(v) for v in raw['calcHeightCallerBytes'])+']'
    audits='\n'.join('#print axioms '+n for n in NAMES)
    return f'''-- Original executable SHA-256 {digest}.
import Doom.Proofs.OriginalPreparedRuntime
set_option maxRecDepth 32768
namespace Doom.Verification.ExtractedPlayerHeight
open X86Memory X86Control Doom.Proofs.PlayerHeight
def extracted : List UInt8 := {literal}
theorem bytes_checked : extracted = code := by decide
theorem recovery_checked (s : X86Memory.State) (flags : Option Flags) (v : Doom.ViewState)
    (live : s.regs 5 = 0)
    (height : load32 s.memory (s.regs 1+(20#32)) = v.height.raw.toBitVec)
    (delta : load32 s.memory (s.regs 1+(24#32)) = v.delta.raw.toBitVec) :
    (X86Routine.run (X86Routine.decodeAt extracted) [263] 30 ⟨s,flags,177⟩).map (fun t =>
      (t.pc,load32 t.core.memory (s.regs 1+(20#32)),load32 t.core.memory (s.regs 1+(24#32)),t.core.regs 0,t.core.regs 1,t.core.regs 4)) =
      some (263,(v.recoverHeight).height.raw.toBitVec,(v.recoverHeight).delta.raw.toBitVec,s.regs 0,s.regs 1,s.regs 4) := by
  rw [bytes_checked]
  exact recovery_observation s flags v live height delta

theorem ceiling_checked (s : X86Memory.State) (flags : Option Flags)
    (b : Doom.Motion) (height offset : Doom.Fixed)
    (safe : Doom.Proofs.BlockSummary.Apart (viewObject s+(60#32)) (s.regs 1+(16#32)))
    (hz : load32 s.memory (viewObject s+(20#32)) = b.z.raw.toBitVec)
    (hh : load32 s.memory (s.regs 1+(20#32)) = height.raw.toBitVec)
    (hc : load32 s.memory (viewObject s+(60#32)) = b.ceilingz.raw.toBitVec)
    (ho : s.regs 0 = offset.raw.toBitVec) :
    (X86Routine.run (X86Routine.decodeAt extracted) [295] 12 ⟨s,flags,263⟩).map (fun t =>
      (t.pc,load32 t.core.memory (s.regs 1+(16#32)),t.core.regs 1,t.core.regs 4)) =
      some (295,(Doom.ViewState.clampZ b height offset).raw.toBitVec,s.regs 1,s.regs 4) := by
  rw [bytes_checked]
  exact ceiling_observation s flags b height offset safe hz hh hc ho

theorem airborne_checked (s : X86Memory.State) (flags : Option Flags)
    (b : Doom.Motion) (height : Doom.Fixed)
    (hz : load32 s.memory (viewObject s+(20#32)) = b.z.raw.toBitVec)
    (hh : load32 s.memory (s.regs 1+(20#32)) = height.raw.toBitVec) :
    (X86Routine.run (X86Routine.decodeAt extracted) [295] 6 ⟨s,flags,115⟩).map (fun t =>
      (t.pc,load32 t.core.memory (s.regs 1+(16#32)),t.core.regs 1,t.core.regs 4)) =
      some (295,(b.z+height).raw.toBitVec,s.regs 1,s.regs 4) := by
  rw [bytes_checked]
  exact airborne_observation s flags b height hz hh
theorem amplitude_checked (s : X86Memory.State) (flags : Option Flags)
    (mx my : Doom.Fixed)
    (hx : load32 s.memory (load32 s.memory (s.regs 0)+(72#32)) = mx.raw.toBitVec)
    (hy : load32 s.memory (load32 s.memory (s.regs 0)+(76#32)) = my.raw.toBitVec) :
    (X86Routine.run (X86Routine.decodeAt extracted) [64] 20 ⟨s,flags,6⟩).map (fun t =>
      (t.pc,load32 t.core.memory (s.regs 0+(28#32)),t.core.regs 1,t.core.regs 4)) =
      some (64,(Doom.ViewState.bobAmplitude mx my).raw.toBitVec,s.regs 0,s.regs 4) := by
  rw [bytes_checked]
  exact amplitude_observation s flags mx my hx hy

theorem offset_checked (s : X86Memory.State) (flags : Option Flags)
    (bob : Doom.Fixed) (time : Int32)
    (ht : load32 s.memory 184192 = time.toBitVec)
    (hb : load32 s.memory (s.regs 1+(28#32)) = bob.raw.toBitVec)
    (tables : Doom.Proofs.ThrustTables s.memory) :
    (X86Routine.run (X86Routine.decodeAt extracted) [170] 10 ⟨s,flags,130⟩).map (fun t =>
      (t.pc,t.core.regs 0,t.core.regs 1,t.core.regs 4,t.core.memory)) =
      some (170,(Doom.ViewState.bobOffset bob time).raw.toBitVec,s.regs 1,s.regs 4,s.memory) := by
  rw [bytes_checked]
  exact offset_observation s flags bob time ht hb tables
theorem function_checked (s : X86Memory.State) (flags : Option Flags)
    (body : Doom.Motion) (v : Doom.ViewState) (time : Int32) (ground live : Bool)
    (h : Function.Inputs s body v time ground live) :
    (X86Routine.run (X86Routine.decodeAt extracted) [(load32 s.memory (s.regs 4)).toNat]
      100 ⟨s,flags,0⟩).map (Function.observe (s.regs 0)) =
      some ((load32 s.memory (s.regs 4)).toNat,
        (v.calcHeight body time ground live).height.raw.toBitVec,
        (v.calcHeight body time ground live).delta.raw.toBitVec,
        (v.calcHeight body time ground live).z.raw.toBitVec,
        (v.calcHeight body time ground live).bob.raw.toBitVec,
        (s.regs 3,s.regs 1,s.regs 2,s.regs 6,s.regs 7,s.regs 5,s.regs 4+(4#32))) := by
  rw [bytes_checked]
  exact Function.observation s flags body v time ground live h
def extractedCaller : List UInt8 := {caller_literal}
theorem caller_bytes_checked : extractedCaller = Caller.callBytes := by decide
theorem caller_checked (s : X86Memory.State) (flags : Option Flags)
    (b : Doom.Motion) (v : Doom.ViewState) (time : Int32) (ground live : Bool)
    (h : Caller.Inputs s b v time ground live) :
    (X86Routine.run (Caller.bytesProgram extractedCaller extracted) [0x3a0] 101
      ⟨s,flags,0x39b⟩).map (Function.observe (s.regs 0)) =
      some (0x3a0,(v.calcHeight b time ground live).height.raw.toBitVec,
        (v.calcHeight b time ground live).delta.raw.toBitVec,
        (v.calcHeight b time ground live).z.raw.toBitVec,
        (v.calcHeight b time ground live).bob.raw.toBitVec,Function.preservedRegisters s) := by
  rw [caller_bytes_checked,bytes_checked]
  exact Caller.observation s flags b v time ground live h
def reactionCode : List UInt8 := {lit('playerReactionBytes')}
def movementCode : List UInt8 := {lit('playerFunctionBytes')}
def stateCode : List UInt8 := {lit('setMobjStateBytes')}
theorem reaction_bytes_checked : reactionCode = Doom.Proofs.PlayerReactionProof.callerBytes := by decide
theorem movement_bytes_checked : movementCode = Doom.Proofs.PlayerFunction.functionBytes := by decide
theorem state_bytes_checked : stateCode = Doom19.setMobjStateBytes := by decide
theorem preparation_checked (s : X86Memory.State) (flags : Option Flags)
    (body : Doom.Motion) (anim : Doom.PlayerAnim.State) (cmd : Doom.Ticcmd) (timer : Int32)
    (v : Doom.ViewState) (time : Int32) (cached live : Bool)
    (h : Doom.Proofs.PlayerHeightJoin.Inputs s body anim cmd timer v time cached live) :
    (X86Routine.run (Doom.Proofs.PlayerPreparation.bytesProgram reactionCode movementCode stateCode extractedCaller extracted)
      [0x333d0] 225 ⟨s,flags,0x333b1⟩).map (Doom.Proofs.PlayerPreparation.observe (s.regs 2)) =
      some (0x333d0,
        (v.calcHeight (Doom.PlayerReaction.move body timer cmd) time (Doom.Proofs.PlayerGround.ground body timer cached) live).height.raw.toBitVec,
        (v.calcHeight (Doom.PlayerReaction.move body timer cmd) time (Doom.Proofs.PlayerGround.ground body timer cached) live).delta.raw.toBitVec,
        (v.calcHeight (Doom.PlayerReaction.move body timer cmd) time (Doom.Proofs.PlayerGround.ground body timer cached) live).z.raw.toBitVec,
        (v.calcHeight (Doom.PlayerReaction.move body timer cmd) time (Doom.Proofs.PlayerGround.ground body timer cached) live).bob.raw.toBitVec,s.regs 4) := by
  rw [reaction_bytes_checked,movement_bytes_checked,state_bytes_checked,caller_bytes_checked,bytes_checked]
  exact Doom.Proofs.PlayerPreparation.observation s flags body anim cmd timer v time cached live h
theorem prepared_state_checked (s : X86Memory.State) (flags : Option Flags)
    (body : Doom.Motion) (anim : Doom.PlayerAnim.State) (cmd : Doom.Ticcmd) (timer : Int32)
    (v : Doom.ViewState) (time : Int32) (cached live : Bool)
    (h : Doom.Proofs.PlayerHeightJoin.Inputs s body anim cmd timer v time cached live) :
    (X86Routine.run (Doom.Proofs.PlayerPreparation.bytesProgram reactionCode movementCode stateCode extractedCaller extracted)
      [0x333d0] 225 ⟨s,flags,0x333b1⟩).map
      (Doom.Proofs.PreparedState.observe (s.regs 2) (Doom.Proofs.PlayerCaller.object s)) =
      some (0x333d0,Doom.Proofs.PreparedState.expected body anim cmd timer v time cached live,s.regs 4) := by
  rw [reaction_bytes_checked,movement_bytes_checked,state_bytes_checked,caller_bytes_checked,bytes_checked]
  exact Doom.Proofs.PreparedState.observation s flags body anim cmd timer v time cached live h

theorem runtime_checked (s : X86Memory.State) (flags : Option Flags)
    (m : Doom.Map) (p : Doom.Player) (keys : UInt32) (cmd : Doom.Ticcmd)
    (scene : Doom.Collision.Scene) (actor : Doom.Collision.SolidThing)
    (sync : p.syncScene m = .ok scene) (found : scene.things[0]? = some actor)
    (supported : actor.moveFlags.floating = false)
    (h : Doom.Proofs.PlayerHeightJoin.Inputs s (actor.motion p.body) p.animation cmd p.reactionTime
      p.view p.levelTime p.cachedOnGround true) :
    (X86Routine.run (Doom.Proofs.PlayerPreparation.bytesProgram reactionCode movementCode stateCode extractedCaller extracted)
      [0x333d0] 225 ⟨s,flags,0x333b1⟩).map
      (fun t => Doom.Proofs.PreparedState.read (s.regs 2) (Doom.Proofs.PlayerCaller.object s) t.core.memory) =
      Doom.Proofs.PreparedRuntime.output (p.prepareTick m keys (some cmd)) := by
  rw [reaction_bytes_checked,movement_bytes_checked,state_bytes_checked,caller_bytes_checked,bytes_checked]
  exact Doom.Proofs.PreparedRuntime.correspondence s flags m p keys cmd scene actor sync found supported h
{audits}
end Doom.Verification.ExtractedPlayerHeight
'''

def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedPlayerHeight.'+short
        match=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing axiom audit: '+name)
        axioms={a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Classical.choice','Quot.sound'},'unexpected proof axioms: '+str(axioms))
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def cases():
    rng=random.Random(0x33030)
    # h, delta, object z, ceiling, momx, momy, time, cached ground, no momentum, live.
    result=[]
    for phase in range(8192):
        for live in [0,1]:
            result.append((41*65536,0,0,128*65536,7*65536,-9*65536,phase,1,0,live))
    edges=[0,1,-1,1343487,1343488,1343489,2686975,2686976,2686977,-16385,-16384,-16383,2147483647,-2147483648]
    for h in edges:
        for d in edges:
            for ground,nm,live in [(0,0,1),(0,1,1),(1,1,1),(1,0,1),(1,0,0)]:
                result.append((h,d,rng.choice(edges),rng.choice(edges),rng.choice(edges),rng.choice(edges),rng.choice(edges),ground,nm,live))
    for _ in range(32768):
        signed=lambda:rng.randrange(-2**31,2**31)
        result.append(tuple(signed() for _ in range(7))+(rng.randrange(2),rng.randrange(2),rng.randrange(2)))
    return result

def cross_check(raw,table,spec,caller_context=False):
    import capstone
    import unicorn as uc
    from unicorn import x86_const as x
    md=capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32)
    code=raw['calcHeightBytes'];unit=spec['units']['calcHeightBytes']
    insts=list(md.disasm(code,0x33030))
    require(b''.join(bytes(i.bytes) for i in insts)==code,'incomplete independent disassembly')
    if caller_context:
        call=raw['calcHeightCallerBytes']
        caller_insts=list(md.disasm(call,0x333cb))
        require(len(caller_insts)==1 and caller_insts[0].mnemonic=='call' and
                caller_insts[0].op_str=='0x33030','unexpected original height CALL')
    return_pc=0x3a0 if caller_context else 0x800
    inputs=cases()
    answers=[tuple(map(int,line.split())) for line in joined.thrust.probe(['calc-height '+' '.join(map(str,c)) for c in inputs])]
    require(len(answers)==len(inputs),'wrong probe response count')
    em=uc.Uc(uc.UC_ARCH_X86,uc.UC_MODE_32);CODE,DATA=0x100000,0x800000
    em.mem_map(CODE,4096);em.mem_map(DATA,4096)
    for base in [0,0x400000]:
        em.mem_map(base,0x30000);em.mem_write(base+0x5a84,table)
        em.mem_write(base+0x13584,struct.pack('<I',base+0x7a84))
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];visited=[]
    em.hook_add(uc.UC_HOOK_MEM_WRITE,lambda _e,_a,addr,size,_v,_u:writes.append((addr,size)))
    def observe(machine,addr,size,user):
        visited.append(addr-CODE)
        if addr==CODE+return_pc:machine.emu_stop()
    em.hook_add(uc.UC_HOOK_CODE,observe)
    paths={'airborne_or_no_momentum':0,'grounded':0,'live_recovery':0,'not_live':0,'bob_cap':0,'upper_height_clamp':0,'lower_height_clamp':0,'delta_zero_sentinel':0,'final_ceiling_clamp':0,'overwritten_early_clamp':0}
    rng=random.Random(0x3315e)
    u32=lambda v:struct.pack('<I',v&0xffffffff)
    for i,(case,answer) in enumerate(zip(inputs,answers)):
        h,d,z,ceiling,mx,my,time,ground,nm,live=case
        base=[0,0x400000][i%2]
        patched=bytearray(code)
        for r in unit['relocations']:struct.pack_into('<I',patched,r['offset'],base+int(r['target'],16))
        em.mem_write(CODE,bytes(patched))
        if caller_context:em.mem_write(CODE+0x39b,call)
        em.ctl_remove_cache(CODE,CODE+4096)
        player,obj,sp=DATA+32+i%4,DATA+512+(i//4)%4,DATA+1024+(i//16)%4
        em.mem_write(DATA,b'\xa5'*4096)
        fields={player:obj,player+4:0 if live else [1,2,-1,-2147483648][i%4],player+16:rng.getrandbits(32),player+20:h,player+24:d,player+28:rng.getrandbits(32),player+196:(rng.getrandbits(32)&~4)|(4 if nm else 0),obj+20:z,obj+60:ceiling,obj+72:mx,obj+76:my,sp:rng.getrandbits(32) if caller_context else CODE+return_pc}
        for a,v in fields.items():em.mem_write(a,u32(v))
        em.mem_write(base+0x2cf80,u32(time));em.mem_write(base+0x2cf90,u32(([-1,1,42][i%3]) if ground else 0))
        initial=[rng.getrandbits(32) for _ in regs];initial[0]=player;initial[4]=sp
        for r,v in zip(regs,initial):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,0x202)
        expected=bytearray(em.mem_read(DATA,4096))
        if caller_context:struct.pack_into('<I',expected,sp-DATA-4,CODE+return_pc)
        function_sp=sp-4 if caller_context else sp
        for n,reg in enumerate([3,1,2,6,7,5],1):struct.pack_into('<I',expected,function_sp-DATA-4*n,initial[reg])
        for offset,v in zip([20,24,16,28],answer):struct.pack_into('<I',expected,player-DATA+offset,v&0xffffffff)
        writes.clear();visited.clear()
        try:em.emu_start(CODE+(0x39b if caller_context else 0),0,count=110)
        except uc.UcError as error:raise AssertionError(f'x86 fault at case {i}: {case}: {error}') from error
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+return_pc,f'no return at case {i}')
        observed=tuple(struct.unpack('<i',em.mem_read(player+offset,4))[0] for offset in [20,24,16,28])
        require(observed==answer,f'height mismatch case {i}: {case}; DOS={observed}, Lean={answer}')
        require(bytes(em.mem_read(DATA,4096))==bytes(expected),f'memory/frame mismatch case {i}')
        for j in [1,2,3,5,6,7]:require(em.reg_read(regs[j])==initial[j],f'register {j} not preserved at {i}')
        require(em.reg_read(regs[4])==(sp if caller_context else sp+4),f'stack not restored at {i}')
        allowed={sp-4*n for n in range(1,8 if caller_context else 7)}|{player+16,player+20,player+24,player+28}
        require(all(a in allowed and size==4 for a,size in writes),f'unexpected store at {i}: {writes}')
        for key,address in [('bob_cap',0x33069),('upper_height_clamp',0x330f4),('lower_height_clamp',0x33107),('delta_zero_sentinel',0x33130),('overwritten_early_clamp',0x330a0)]:
            paths[key]+=int(address-0x33030 in visited)
        if nm or not ground:paths['airborne_or_no_momentum']+=1
        else:
            paths['grounded']+=1;paths['live_recovery' if live else 'not_live']+=1
            paths['final_ceiling_clamp']+=int(0x33154-0x33030 in visited)
    return {'cases':len(inputs),'caller_context':caller_context,'paths':paths,'all_bob_phases':8192,'data_bases':[0,0x400000],'unaligned_addresses':True,
        'checks':['four live view fields','full dynamic memory page','six preserved registers','stack and return','store footprint'],
        'disassembly':[f'{i.address:#x}: {i.mnemonic} {i.op_str}' for i in insts]}

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--cross-check',action='store_true');parser.add_argument('--caller-context',action='store_true');parser.add_argument('--preparation-context',action='store_true');args=parser.parse_args()
    require(not (args.caller_context or args.preparation_context) or args.cross_check,'context modes require --cross-check')
    require(not (args.caller_context and args.preparation_context),'choose only one context mode')
    spec=json.loads((ROOT/'tests/reference/original-player-height.json').read_text())
    profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=joined.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=joined.extraction.extract(binary,profile,spec)
    _,table=joined.thrust.extract(binary,profile,json.loads((ROOT/'tests/reference/original-thrust.json').read_text()))
    out=ROOT/'artifacts/original-player-height';out.mkdir(parents=True,exist_ok=True)
    source=out/'Extracted.lean';source.write_text(certificate(raw,profile['exe_sha256']))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalPreparedRuntime','fidelity-probe'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout);print(checked.stdout,end='',flush=True)
    comparison=None
    if args.cross_check:
        if args.preparation_context:
            import verify_original_player_preparation as preparation
            reaction_spec=json.loads((ROOT/'tests/reference/original-player-reaction.json').read_text())
            run_table=joined.animation.table_data(binary,profile,reaction_spec)
            comparison=preparation.cross_check(raw,table,run_table,spec,cases(),joined.thrust.probe,require)
        else:
            comparison=cross_check(raw,table,spec,args.caller_context)
    report={'axioms':checked.stdout.splitlines(),'exe_sha256':profile['exe_sha256'],'units':spec['units'],'sine_table':joined.thrust.check_tables(table),
        'scope':'Universal original-byte P_CalcHeight function-entry theorem: all four live Lean view fields, six saved registers, stack/return and an external-memory frame. Also proves the original P_PlayerThink height CALL and derives its function-entry contract and return address. Assumes encoded inputs, initialized sine table and explicit read/write/stack separation; only the standalone function theorem assumes a return address. The reaction/movement output now establishes the height call input contract from initial-state premises, and a single uninterrupted 225-instruction-bound execution at absolute DOS code-object offsets. The strengthened theorem observes eleven preparation fields, restored caller ESP, and a combined initial-to-final memory frame. It also relates those fields directly to live Player.prepareTick with an explicit Ticcmd, assuming successful scene synchronization, an actor at index zero, a nonfloating player, and the DOS entry relation for that synchronized actor. DOS loading, table initialization, compilation, keyboard translation, whole-game reachability and the rest of the player tic remain outside.',
        'cross_check':comparison}
    out=ROOT/'artifacts/original-player-height';out.mkdir(parents=True,exist_ok=True)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: original P_CalcHeight bytes and relocations; block, function, CALL/RET, dataflow, continuous eleven-field preparation, and live Player.prepareTick certificates.')
    if report['cross_check']:print('Independent '+('continuous player-preparation' if args.preparation_context else 'P_CalcHeight')+' x86 comparisons:',report['cross_check']['cases'])

if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as error:
        print(error.stdout or '',file=sys.stderr)
        print(error.stderr or '',file=sys.stderr)
        raise
