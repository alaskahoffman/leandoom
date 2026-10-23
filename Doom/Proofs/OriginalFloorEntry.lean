import Doom.Proofs.OriginalFloorDamage
import Doom.Verification.X86CodeBridge

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.FloorEntry
open Verification X86 X86Memory X86Control BlockSummary
open FloorDamage (Kind)

def bytesProgram (entry cases rng : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2fb20 ≤ pc ∧ pc < 0x2fb20+entry.length then X86Routine.decodeAt entry (pc-0x2fb20)
  else FloorDamage.bytesProgram cases rng pc

def program := bytesProgram SectorEntry.entryBytes FloorDamage.code Doom19.playRandomBytes
abbrev cm := SectorEntry.codeMemory SectorEntry.tableBytes
abbrev listed := SectorEntry.listed
abbrev prepared := SectorEntry.prepared
abbrev zWord := SectorEntry.zWord
abbrev floorWord := SectorEntry.floorWord
abbrev special := SectorEntry.special

def index (kind : Kind) : Nat := kind.special-4

def afterSwitch (s : X86Memory.State) (kind : Kind) := put (prepared s) 2 (BitVec.ofNat 32 (index kind))

theorem entry_decoded (pc : Nat) (h : listed pc ≠ none) : program pc = listed pc := by
  fun_cases SectorEntry.listed pc <;> simp_all [listed,SectorEntry.listed] <;> decide

theorem table (kind : Kind) :
    load32 cm ((0x2faec#32) + (BitVec.ofNat 32 (index kind) <<< 2)) = BitVec.ofNat 32 kind.entry := by
  cases kind <;> decide

theorem loaded_index (kind : Kind) (z : Word) :
    (((z &&& (0xffff0000#32)) ||| (BitVec.ofNat 32 kind.special)) + (-4#32)).extractLsb' 0 16 = BitVec.ofNat _ (index kind) ∧
    (((z &&& (0xffff0000#32)) ||| (BitVec.ofNat 32 kind.special)) + (-4#32)) &&& (65535#32) = BitVec.ofNat _ (index kind) := by
  have low : ((((z &&& (0xffff0000#32)) ||| (BitVec.ofNat 32 kind.special)) + (-4#32))).setWidth 16 = (BitVec.ofNat 16 (index kind)) := by
    cases kind <;>
      rw [BitVec.setWidth_add _ _ (by decide)] <;>
      simp [BitVec.setWidth_or,BitVec.setWidth_and,index,Kind.special]
  constructor
  · rw [← BitVec.setWidth_eq_extractLsb' (by decide : 16 ≤ 32)]
    exact low
  · change _ &&& (BitVec.allOnes 16).setWidth (16+16) = _
    rw [BitVec.and_setWidth_allOnes 16 16,low]
    cases kind <;> rfl

theorem loaded_low (kind : Kind) (z : Word) :
    (((z &&& (0xffff0000#32)) ||| (BitVec.ofNat 32 kind.special)) + (4294967292#32)).extractLsb' 0 16 = (BitVec.ofNat 16 (index kind)) :=
  (loaded_index kind z).1
theorem loaded_mask (kind : Kind) (z : Word) :
    (((z &&& (0xffff0000#32)) ||| (BitVec.ofNat 32 kind.special)) + (4294967292#32)) &&& (65535#32) = (BitVec.ofNat 32 (index kind)) :=
  (loaded_index kind z).2

theorem switch_run (kind : Kind) (s : X86Memory.State) (flags : Option Flags)
    (isKind : load16 s.memory (s.regs 1+(14#32)) = (BitVec.ofNat 16 kind.special)) :
    X86CodeMemory.run cm listed [0x2fb4f,0x2fc39] 5 ⟨s,flags,0x2fb38⟩ =
      some ⟨put s 2 (BitVec.ofNat 32 (index kind)),some {(logical32 (BitVec.ofNat 32 (index kind))) with carry := some false},0x2fb4f⟩ := by
  let v := (s.regs 2 &&& (0xffff0000#32)) ||| (BitVec.ofNat 32 kind.special)
  let s1 := put s 2 v
  let s2 := put s 2 (v + (4294967292#32))
  let f : Flags := {(X86Routine.compare16 (BitVec.ofNat 16 (index kind)) (12#16)) with carry := some (decide (index kind < 12))}
  have overwrite (t : X86Memory.State) (r : Reg) (a b : Word) : put (put t r a) r b = put t r b := by
    simp only [put]; congr 1; funext q; simp [write]; split <;> simp_all
  have path : X86CodeMemory.Prefix cm listed [0x2fb4f,0x2fc39] 5
      ⟨s,flags,0x2fb38⟩ ⟨put s 2 (BitVec.ofNat 32 (index kind)),some {(logical32 (BitVec.ofNat 32 (index kind))) with carry := some false},0x2fb4f⟩ := by
    apply X86CodeMemory.Prefix.step (middle := ⟨s1,flags,0x2fb3c⟩)
      (by simp) (show listed 0x2fb38 = _ from rfl) (by
        simp [X86CodeMemory.execute,X86Routine.execute,X86Block.Address.eval,isKind,s1,v]; cases kind <;> rfl)
    apply X86CodeMemory.Prefix.step (middle := ⟨s2,none,0x2fb3f⟩)
      (by simp) (show listed 0x2fb3c = _ from rfl) (by
        simp [X86CodeMemory.execute,X86Routine.execute,s1,s2,show (put s 2 v).regs 2 = v from by simp [put,write],overwrite])
    apply X86CodeMemory.Prefix.step (middle := ⟨s2,some f,0x2fb43⟩)
      (by simp) (show listed 0x2fb3f = _ from rfl) (by
        simp [X86CodeMemory.execute,X86Routine.execute,s2,put,write,v,loaded_low,f]; cases kind <;> rfl)
    apply X86CodeMemory.Prefix.step (middle := ⟨s2,some f,0x2fb49⟩)
      (by simp) (show listed 0x2fb43 = _ from rfl) (by cases kind <;> rfl)
    apply X86CodeMemory.Prefix.step (middle := ⟨put s 2 (BitVec.ofNat 32 (index kind)),some {(logical32 (BitVec.ofNat 32 (index kind))) with carry := some false},0x2fb4f⟩)
      (by simp) (show listed 0x2fb49 = _ from rfl) (by
        have mask : s2.regs 2 &&& (65535#32) = (BitVec.ofNat 32 (index kind)) := by simp [s2,put,write,v,loaded_mask]
        simp only [X86CodeMemory.execute,X86Routine.execute,mask]
        simp [s2,put,write,v,loaded_mask]
        funext r
        by_cases h : r = 2 <;> simp [write,h])
    exact X86CodeMemory.Prefix.nil _
  rw [show 5 = 5+0 from rfl,path.run 0]
  simp [X86CodeMemory.run]


def selectExits : List Nat := [0x2fb57,0x2fb80,0x2fbaa,0x2fc39]

theorem select_prefix (kind : Kind) (s : X86Memory.State) (flags : Option Flags) (isKind : special s = BitVec.ofNat 16 kind.special) :
    X86CodeMemory.run cm listed [0x2fb4f,0x2fc39] 12 ⟨s,flags,0x2fb24⟩ =
      some (if zWord s = floorWord s then
        ⟨afterSwitch s kind,some {(logical32 (BitVec.ofNat 32 (index kind))) with carry := some false},0x2fb4f⟩
      else ⟨prepared s,some (compare32 (zWord s) (floorWord s)),0x2fc39⟩) := by
  rw [(SectorEntry.floor_prefix s flags).run 6]
  have d : listed 0x2fb32 = some (.control (.jumpZero false 257),6) := rfl
  by_cases ground : zWord s = floorWord s
  · rw [if_pos ground]
    have jump : X86CodeMemory.execute cm (.control (.jumpZero false 257))
        ⟨prepared s,some (compare32 (zWord s) (floorWord s)),0x2fb38⟩ =
        some ⟨prepared s,some (compare32 (zWord s) (floorWord s)),0x2fb38⟩ := by
      simp [X86CodeMemory.execute,X86Routine.execute,X86Control.execute,compare32,ground]
    have tail := switch_run kind (prepared s) (some (compare32 (zWord s) (floorWord s)))
      (by simpa [SectorEntry.prepared,put,write,SectorEntry.special] using isKind)
    have step : X86CodeMemory.Prefix cm listed [0x2fb4f,0x2fc39] 1
        ⟨prepared s,some (compare32 (zWord s) (floorWord s)),0x2fb32⟩
        ⟨prepared s,some (compare32 (zWord s) (floorWord s)),0x2fb38⟩ :=
      .step (by simp [selectExits]) d jump (.nil _)
    rw [show 6 = 1+5 from rfl,step.run 5]
    exact tail

  · rw [if_neg ground]
    have jump : X86CodeMemory.execute cm (.control (.jumpZero false 257))
        ⟨prepared s,some (compare32 (zWord s) (floorWord s)),0x2fb38⟩ =
        some ⟨prepared s,some (compare32 (zWord s) (floorWord s)),0x2fc39⟩ := by
      simp [X86CodeMemory.execute,X86Routine.execute,X86Control.execute,compare32,SectorEntry.sub_zero,ground]
    have step : X86CodeMemory.Prefix cm listed [0x2fb4f,0x2fc39] 1
        ⟨prepared s,some (compare32 (zWord s) (floorWord s)),0x2fb32⟩
        ⟨prepared s,some (compare32 (zWord s) (floorWord s)),0x2fc39⟩ :=
      .step (by simp [selectExits]) d jump (.nil _)
    rw [show 6 = 1+5 from rfl,step.run 5]
    simp [X86CodeMemory.run,selectExits] <;> cases kind <;> decide

theorem select (kind : Kind) (s : X86Memory.State) (flags : Option Flags) (isKind : special s = BitVec.ofNat 16 kind.special) :
    X86CodeMemory.run cm program selectExits 13 ⟨s,flags,0x2fb24⟩ =
      some (if zWord s = floorWord s then
        ⟨afterSwitch s kind,some {(logical32 (BitVec.ofNat 32 (index kind))) with carry := some false},kind.entry⟩
      else ⟨prepared s,some (compare32 (zWord s) (floorWord s)),0x2fc39⟩) := by
  have pre := select_prefix kind s flags isKind
  obtain ⟨k,bound,path,_⟩ := X86CodeMemory.run_path pre
  -- The prefix visits only the entry listing, never either final exit.
  have first := path.transfer program selectExits entry_decoded (by
    intro pc hd
    fun_cases SectorEntry.listed pc <;> simp_all [listed,SectorEntry.listed,selectExits])
  by_cases ground : zWord s = floorWord s
  · rw [if_pos ground] at first
    have d : program 0x2fb4f = some (.jumpCode ⟨none,some 2,2,0x2faec⟩,8) := by decide
    have jump : X86CodeMemory.execute cm (.jumpCode ⟨none,some 2,2,0x2faec⟩)
        ⟨afterSwitch s kind,some {(logical32 (BitVec.ofNat 32 (index kind))) with carry := some false},0x2fb57⟩ =
        some ⟨afterSwitch s kind,some {(logical32 (BitVec.ofNat 32 (index kind))) with carry := some false},kind.entry⟩ := by
      have ht : (load32 cm ((BitVec.ofNat 32 (index kind) <<< 2) + (0x2faec#32))).toNat = kind.entry := by
        rw [BitVec.add_comm,table]
        cases kind <;> rfl
      simpa [X86CodeMemory.execute,X86Block.Address.eval,afterSwitch,put,write] using ht
    have tail : X86CodeMemory.run cm program selectExits 1
        ⟨afterSwitch s kind,some {(logical32 (BitVec.ofNat 32 (index kind))) with carry := some false},0x2fb4f⟩ =
        some ⟨afterSwitch s kind,some {(logical32 (BitVec.ofNat 32 (index kind))) with carry := some false},kind.entry⟩ := by
      have step : X86CodeMemory.Prefix cm program selectExits 1
          ⟨afterSwitch s kind,some {(logical32 (BitVec.ofNat 32 (index kind))) with carry := some false},0x2fb4f⟩
          ⟨afterSwitch s kind,some {(logical32 (BitVec.ofNat 32 (index kind))) with carry := some false},kind.entry⟩ :=
        .step (by simp [selectExits]) d jump (.nil _)
      rw [show 1 = 1+0 from rfl,step.run 0]
      simp [X86CodeMemory.run,selectExits] <;> cases kind <;> decide

    simpa [ground] using first.finish tail 13 (by omega)
  · rw [if_neg ground] at first
    have tail : X86CodeMemory.run cm program selectExits 0
        ⟨prepared s,some (compare32 (zWord s) (floorWord s)),0x2fc39⟩ =
        some ⟨prepared s,some (compare32 (zWord s) (floorWord s)),0x2fc39⟩ := by simp [X86CodeMemory.run,selectExits] <;> cases kind <;> decide
    simpa [ground] using first.finish tail 13 (by omega)



/-- The case bytes occupy disjoint code intervals from the entry sequence. -/
theorem contains_floor (pc : Nat) (h : FloorDamage.program pc ≠ none) :
    program pc = FloorDamage.program pc := by
  have size : SectorEntry.entryBytes.length = 55 := by decide
  unfold program bytesProgram
  rw [size]
  split
  · rename_i range
    have before : ¬(0x2fb57 ≤ pc ∧ pc < 0x2fb57+FloorDamage.code.length) := by omega
    have after : ¬(0x24160 ≤ pc ∧ pc < 0x24160+Doom19.playRandomBytes.length) := by
      have : Doom19.playRandomBytes.length = 28 := by decide
      omega
    simp [FloorDamage.program,FloorDamage.bytesProgram,before,after] at h
  · rfl

theorem ordinary (pc : Nat) (op : X86Routine.Op) (len : Nat)
    (h : FloorDamage.program pc = some (op,len)) : X86CodeMemory.routineOnly op = true := by
  have check : ((FloorDamage.program pc).map (fun p => X86CodeMemory.routineOnly p.1)).getD true = true := by
    simp only [FloorDamage.program,FloorDamage.bytesProgram]
    split
    · exact X86CodeMemory.routine_decode _ (by decide) _
    · split
      · exact X86CodeMemory.routine_decode _ (by decide) _
      · rfl
  simpa only [h,Option.map_some,Option.getD_some] using check

theorem transfer_floor {n : Nat} {s t : X86Control.State}
    (path : X86CodeMemory.Prefix cm FloorDamage.program FloorDamage.exits n s t) :
    X86CodeMemory.Prefix cm program FloorDamage.exits n s t := by
  induction path with
  | nil => exact .nil _
  | @step n s middle last op len active decoded executed rest ih =>
    exact .step active ((contains_floor s.pc (by simp [decoded])).trans decoded) executed ih

theorem case_execution (kind : Kind) (s : X86Memory.State) (flags : Option Flags) (rng : DoomRandom)
    (h : FloorDamage.suitWord s ≠ (0#32) → FloorDamage.RandomInputs s rng.play (FloorDamage.randomByte rng.play)) :
    X86CodeMemory.run cm program FloorDamage.exits 18 ⟨s,flags,kind.entry⟩ = some (FloorDamage.result kind s rng) := by
  have proof := FloorDamage.execution kind s flags rng h
  obtain ⟨k,hk,path,done⟩ := X86Routine.run_path proof
  have path := X86CodeMemory.lift_routine path cm ordinary
  have lift := transfer_floor path
  exact lift.finish (fuel := 0) (by simp [X86CodeMemory.run,done]) 18 (by omega)

def result (kind : Kind) (s : X86Memory.State) (rng : DoomRandom) : X86Control.State :=
  if zWord s = floorWord s then FloorDamage.result kind (afterSwitch s kind) rng
  else ⟨prepared s,some (compare32 (zWord s) (floorWord s)),0x2fc39⟩

/-- A single original-byte run from the floor check, through dispatch and the
actual random call if needed, to either the damage CALL or skip epilogue. -/
theorem execution (kind : Kind) (s : X86Memory.State) (flags : Option Flags) (rng : DoomRandom)
    (isKind : special s = BitVec.ofNat 16 kind.special)
    (h : FloorDamage.suitWord (afterSwitch s kind) ≠ (0#32) →
      FloorDamage.RandomInputs (afterSwitch s kind) rng.play (FloorDamage.randomByte rng.play)) :
    X86CodeMemory.run cm program FloorDamage.exits 31 ⟨s,flags,0x2fb24⟩ = some (result kind s rng) := by
  -- Lift only the entry listing so case boundaries cease being exits.
  -- The earlier selection proof uses the full decoder; its encountered PCs
  -- are recovered instead from the smaller pre-switch listing.
  obtain ⟨j,hj,pre,_⟩ := X86CodeMemory.run_path (select_prefix kind s flags isKind)
  have pre := pre.transfer program FloorDamage.exits entry_decoded (by
    intro pc hd; fun_cases SectorEntry.listed pc <;> simp_all [listed,SectorEntry.listed,FloorDamage.exits])
  by_cases ground : zWord s = floorWord s
  · rw [if_pos ground] at pre
    have jump : X86CodeMemory.Prefix cm program FloorDamage.exits 1
        ⟨afterSwitch s kind,some {(logical32 (BitVec.ofNat 32 (index kind))) with carry := some false},0x2fb4f⟩
        ⟨afterSwitch s kind,some {(logical32 (BitVec.ofNat 32 (index kind))) with carry := some false},kind.entry⟩ := by
      apply X86CodeMemory.Prefix.step (by simp [FloorDamage.exits]) (show program 0x2fb4f = some (.jumpCode ⟨none,some 2,2,0x2faec⟩,8) from by decide)
        (show X86CodeMemory.execute cm _ _ = some _ from ?_) (.nil _)
      have ht : (load32 cm ((BitVec.ofNat 32 (index kind) <<< 2) + (0x2faec#32))).toNat = kind.entry := by
        rw [BitVec.add_comm,table]; cases kind <;> rfl
      simpa [X86CodeMemory.execute,X86Block.Address.eval,afterSwitch,put,write] using ht
    have tail := case_execution kind (afterSwitch s kind) (some {(logical32 (BitVec.ofNat 32 (index kind))) with carry := some false}) rng h
    have joined := jump.finish tail 19 (by decide)
    simpa [result,ground] using pre.finish joined 31 (by omega)
  · rw [if_neg ground] at pre
    have tail : X86CodeMemory.run cm program FloorDamage.exits 0
        ⟨prepared s,some (compare32 (zWord s) (floorWord s)),0x2fc39⟩ =
        some ⟨prepared s,some (compare32 (zWord s) (floorWord s)),0x2fc39⟩ := by rfl
    simpa [result,ground] using pre.finish tail 31 (by omega)

/-- Input facts are about the original state, before the floor check loads any
register. Memory conditions name explicit potential CALL/index stores only. -/
structure Inputs (kind : Kind) (s : X86Memory.State) (z floor : Fixed) (time : Nat)
    (suit : Bool) (rng : DoomRandom) : Prop where
  isKind : special s = BitVec.ofNat 16 kind.special
  height : zWord s = z.raw.toBitVec
  floor : floorWord s = floor.raw.toBitVec
  suit : load32 s.memory (s.regs 0+(56#32)) = (0#32) ↔ suit = false
  clock : s.memory (0x2cf80#32) = BitVec.ofNat 8 time
  index : load32 s.memory (0x12720#32) = BitVec.ofNat 32 rng.play.toNat
  misc : load32 s.memory (0x1271c#32) = BitVec.ofNat 32 rng.misc.toNat
  random : load32 s.memory (s.regs 0+(56#32)) ≠ (0#32) →
    FloorDamage.RandomInputs s rng.play (FloorDamage.randomByte rng.play)
  clockSafe : FloorDamage.randomMemory (FloorDamage.called s) rng.play (0x2cf80#32) = s.memory (0x2cf80#32)
  targetSafe : load32 (FloorDamage.randomMemory (FloorDamage.called s) rng.play) (s.regs 0) = load32 s.memory (s.regs 0)
  miscSafe : load32 (FloorDamage.randomMemory (FloorDamage.called s) rng.play) (0x1271c#32) = load32 s.memory (0x1271c#32)

theorem case_inputs (kind : Kind) (s : X86Memory.State) (z floor : Fixed) (time : Nat)
    (suit : Bool) (rng : DoomRandom) (h : Inputs kind s z floor time suit rng) :
    FloorDamage.Inputs (afterSwitch s kind) time suit rng := by
  have mem : (afterSwitch s kind).memory = s.memory := rfl
  have sp : (afterSwitch s kind).regs 4 = s.regs 4 := by simp [afterSwitch,SectorEntry.prepared,put,write]
  have p : FloorDamage.player (afterSwitch s kind) = s.regs 0 := by
    simp [FloorDamage.player,afterSwitch,SectorEntry.prepared,SectorEntry.player,put,write]
  have rm : FloorDamage.randomMemory (FloorDamage.called (afterSwitch s kind)) rng.play =
      FloorDamage.randomMemory (FloorDamage.called s) rng.play := by
    simp [FloorDamage.randomMemory,FloorDamage.called,X86Routine.pushWord,mem,sp]
  refine ⟨?_,h.clock,h.index,h.misc,?_,?_,?_,?_,?_⟩
  · simpa [FloorDamage.suitWord,p,mem] using h.suit
  · simp [afterSwitch,SectorEntry.prepared,SectorEntry.object,FloorDamage.player,
      SectorEntry.player,put,write]
  · intro suitOn
    have old := h.random (by simpa [FloorDamage.suitWord,p,mem] using suitOn)
    constructor
    · simpa [FloorDamage.called,X86Routine.pushWord,mem,sp] using old.index
    · simpa [rm] using old.table
    · rw [rm]
      simpa [FloorDamage.called,X86Routine.pushWord,put,write,sp] using old.ret
  · simpa [rm,mem] using h.clockSafe
  · simpa [rm,p,mem] using h.targetSafe
  · simpa [rm,mem] using h.miscSafe

theorem floor_relation (kind : Kind) (s : X86Memory.State) (z floor : Fixed) (time : Nat)
    (suit : Bool) (rng : DoomRandom) (h : Inputs kind s z floor time suit rng) :
    zWord s = floorWord s ↔ z = floor := by
  rw [h.height,h.floor,Int32.toBitVec_inj]
  cases z; cases floor; simp

theorem correspondence (kind : Kind) (s : X86Memory.State) (flags : Option Flags)
    (z floor : Fixed) (time : Nat) (suit : Bool) (rng : DoomRandom)
    (h : Inputs kind s z floor time suit rng) :
    (X86CodeMemory.run cm program FloorDamage.exits 31 ⟨s,flags,0x2fb24⟩).map FloorDamage.observe =
      let answer := LevelSpecials.floorDamage kind.special z floor suit time rng
      some (answer.1,BitVec.ofNat 32 answer.2.play.toNat,BitVec.ofNat 32 answer.2.misc.toNat) := by
  have hc := case_inputs kind s z floor time suit rng h
  rw [execution kind s flags rng h.isKind hc.random,Option.map_some]
  by_cases onFloor : z = floor
  · have ground := (floor_relation kind s z floor time suit rng h).mpr onFloor
    simp only [result,ground,↓reduceIte]
    rw [FloorDamage.result_observation kind (afterSwitch s kind) time suit rng z floor onFloor hc]
  · have ground : zWord s ≠ floorWord s := fun eq => onFloor ((floor_relation kind s z floor time suit rng h).mp eq)
    have off : (z != floor) = true := by
      change (!(z.raw == floor.raw)) = true
      have raw : z.raw ≠ floor.raw := by intro eq; apply onFloor; cases z; cases floor; simp_all
      simp [raw]
    simp [result,ground,FloorDamage.observe,FloorDamage.requested,SectorEntry.prepared,
      put,LevelSpecials.floorDamage,off,h.index,h.misc]


/-- The initial pointer chain supplies the damage target; the proof also
identifies the original damage CALL in the joined byte image. -/
theorem damage_arguments (kind : Kind) (s : X86Memory.State) (z floor : Fixed)
    (time : Nat) (suit : Bool) (rng : DoomRandom) (h : Inputs kind s z floor time suit rng)
    (nonzero : FloorDamage.requested (result kind s rng) ≠ 0) :
    let t := result kind s rng
    t.core.regs 0 = SectorEntry.object s ∧ t.core.regs 2 = (0#32) ∧ t.core.regs 3 = (0#32) ∧
    program t.pc = some (.call ((0x2a460 : Int)-(t.pc+5)),5) := by
  by_cases ground : zWord s = floorWord s
  · have hc := case_inputs kind s z floor time suit rng h
    simp only [result,ground,↓reduceIte] at nonzero ⊢
    obtain ⟨target,inflictor,source,call⟩ := FloorDamage.damage_arguments kind (afterSwitch s kind)
      time suit rng hc nonzero
    refine ⟨?_,inflictor,source,?_⟩
    · simpa [afterSwitch,SectorEntry.prepared,FloorDamage.player,SectorEntry.player,
        SectorEntry.object,put,write] using target
    · rw [contains_floor _ (by rw [call]; simp),call]
  · simp [result,ground,FloorDamage.requested] at nonzero

/-- No floor contact means no RNG or other memory write. On contact, the only
possible stores are the existing RNG CALL return slot and gameplay index. -/
theorem memory_frame (kind : Kind) (s : X86Memory.State) (rng : DoomRandom) :
    (result kind s rng).core.memory =
      if zWord s = floorWord s ∧ (kind = .four ∨ kind = .sixteen) ∧
          load32 s.memory (s.regs 0+(56#32)) ≠ (0#32)
      then FloorDamage.randomMemory (FloorDamage.called s) rng.play else s.memory := by
  by_cases ground : zWord s = floorWord s
  · simp only [result,ground,↓reduceIte]
    rw [FloorDamage.memory_frame]
    simp [ground,afterSwitch,SectorEntry.prepared,SectorEntry.player,FloorDamage.suitWord,
      FloorDamage.player,FloorDamage.randomMemory,FloorDamage.called,X86Routine.pushWord,put,write]
  · simp [result,ground,SectorEntry.prepared,put]

theorem stack_preserved (kind : Kind) (s : X86Memory.State) (rng : DoomRandom) :
    (result kind s rng).core.regs 4 = s.regs 4 := by
  by_cases ground : zWord s = floorWord s
  · simp only [result,ground,↓reduceIte]
    rw [FloorDamage.stack_preserved]
    simp [afterSwitch,SectorEntry.prepared,put,write]
  · simp [result,ground,SectorEntry.prepared,put,write]

end Doom.Proofs.FloorEntry
