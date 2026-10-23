import Doom.Proofs.OriginalThrust
import Doom.Hitscan
import Doom.Verification.X86Routine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalAimQuery
open Verification X86 X86Memory X86Control BlockSummary
def rayBytes : List UInt8 := [0x51,0x56,0x57,0x55,0x8b,0xd,0x84,0x35,0x1,0x0,0x89,0xde,0xc1,0xea,0x13,0xc1,0xfe,0x10,0x8b,0xc,0x91,0xf,0xaf,0xce,0xf,0xaf,0x34,0x95,0x84,0x5a,0x0,0x0]
def retBytes : List UInt8 := [0x83,0x3d,0xf8,0xb9,0x2,0x0,0x0,0x74,0xa,0xa1,0xb4,0xb9,0x2,0x0,0x5d,0x5f,0x5e,0x59,0xc3,0x31,0xc0,0x5d,0x5f,0x5e,0x59,0xc3]
def bytesProgram (ray ret : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2bb80 ≤ pc ∧ pc < 0x2bba0 then X86Routine.decodeAt ray (pc-0x2bb80)
  else if 0x2bbff ≤ pc ∧ pc < 0x2bc19 then X86Routine.decodeAt ret (pc-0x2bbff) else none
def program := bytesProgram rayBytes retBytes

def listed : X86Routine.Program
  | 0x2bb80 => some (.push 1,1)
  | 0x2bb81 => some (.push 6,1)
  | 0x2bb82 => some (.push 7,1)
  | 0x2bb83 => some (.push 5,1)
  | 0x2bb84 => some (.control (.block (.load 1 ⟨none,none,0,0x13584⟩)),6)
  | 0x2bb8a => some (.control (.block (.legacy (.mov 6 3))),2)
  | 0x2bb8c => some (.control (.block (.shr 2 19)),3)
  | 0x2bb8f => some (.sar 6 16,3)
  | 0x2bb92 => some (.control (.block (.load 1 ⟨some 1,some 2,2,0⟩)),3)
  | 0x2bb95 => some (.multiplyRegister 1 6,3)
  | 0x2bb98 => some (.multiplyLoaded 6 ⟨none,some 2,2,0x5a84⟩,8)
  | 0x2bbff => some (.control (.cmpImmediate ⟨none,none,0,0x2b9f8⟩ 0),7)
  | 0x2bc06 => some (.control (.jumpZero true 10),2)
  | 0x2bc08 => some (.control (.block (.load 0 ⟨none,none,0,0x2b9b4⟩)),5)
  | 0x2bc0d => some (.pop 5,1)
  | 0x2bc0e => some (.pop 7,1)
  | 0x2bc0f => some (.pop 6,1)
  | 0x2bc10 => some (.pop 1,1)
  | 0x2bc11 => some (.ret,1)
  | 0x2bc12 => some (.xorRegister 0 0,2)
  | 0x2bc14 => some (.pop 5,1)
  | 0x2bc15 => some (.pop 7,1)
  | 0x2bc16 => some (.pop 6,1)
  | 0x2bc17 => some (.pop 1,1)
  | 0x2bc18 => some (.ret,1)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def saved (s : X86Memory.State) :=
  X86Routine.pushWord (X86Routine.pushWord (X86Routine.pushWord
    (X86Routine.pushWord s (s.regs 1)) (s.regs 6)) (s.regs 7)) (s.regs 5)
def index (s : X86Memory.State) := s.regs 2 >>> 19
def units (s : X86Memory.State) := (s.regs 3).sshiftRight 16
def cosinePointer (s : X86Memory.State) := load32 (saved s).memory 0x13584
def cosine (s : X86Memory.State) := load32 (saved s).memory (cosinePointer s+(index s <<< 2))
def sine (s : X86Memory.State) := load32 (saved s).memory ((index s <<< 2)+0x5a84)
def ray (s : X86Memory.State) : X86Control.State :=
  ⟨put (put (put (saved s) 2 (index s)) 1 (cosine s*units s)) 6 (units s*sine s),none,0x2bba0⟩

theorem ray_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 11 ⟨s,f,0x2bb80⟩ (ray s) := by
  let c1 := X86Routine.pushWord s (s.regs 1)
  let c2 := X86Routine.pushWord c1 (s.regs 6)
  let c3 := X86Routine.pushWord c2 (s.regs 7)
  let c4 := X86Routine.pushWord c3 (s.regs 5)
  let c5 := put c4 1 (cosinePointer s)
  let c6 := put c5 6 (s.regs 3)
  let c7 := put c6 2 (index s)
  let c8 := put c7 6 (units s)
  let c9 := put c8 1 (cosine s)
  let c10 := put c9 1 (cosine s*units s)
  let c11 := put c10 6 (units s*sine s)
  have path : X86Routine.Prefix listed [] 11 ⟨s,f,0x2bb80⟩ ⟨c11,none,0x2bba0⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨c1,f,0x2bb81⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c1,cosinePointer,cosine,sine,index,units,saved])
    apply X86Routine.Prefix.step (middle := ⟨c2,f,0x2bb82⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c2,c1,cosinePointer,cosine,sine,index,units,saved])
    apply X86Routine.Prefix.step (middle := ⟨c3,f,0x2bb83⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c3,c2,c1,cosinePointer,cosine,sine,index,units,saved])
    apply X86Routine.Prefix.step (middle := ⟨c4,f,0x2bb84⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c4,c3,c2,c1,cosinePointer,cosine,sine,index,units,saved])
    apply X86Routine.Prefix.step (middle := ⟨c5,f,0x2bb8a⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c5,c4,c3,c2,c1,cosinePointer,cosine,sine,index,units,saved])
    apply X86Routine.Prefix.step (middle := ⟨c6,f,0x2bb8c⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c6,c5,c4,c3,c2,c1,cosinePointer,cosine,sine,index,units,saved])
    apply X86Routine.Prefix.step (middle := ⟨c7,none,0x2bb8f⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c7,c6,c5,c4,c3,c2,c1,cosinePointer,cosine,sine,index,units,saved])
    apply X86Routine.Prefix.step (middle := ⟨c8,none,0x2bb92⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c8,c7,c6,c5,c4,c3,c2,c1,cosinePointer,cosine,sine,index,units,saved])
    apply X86Routine.Prefix.step (middle := ⟨c9,none,0x2bb95⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c9,c8,c7,c6,c5,c4,c3,c2,c1,cosinePointer,cosine,sine,index,units,saved])
    apply X86Routine.Prefix.step (middle := ⟨c10,none,0x2bb98⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,cosinePointer,cosine,sine,index,units,saved])
    apply X86Routine.Prefix.step (middle := ⟨c11,none,0x2bba0⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,cosinePointer,cosine,sine,index,units,saved])
    exact X86Routine.Prefix.nil _
  have eq : (⟨c11,none,0x2bba0⟩ : X86Control.State)=ray s := by
    simp [ray,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,saved,put,write]
    funext r
    by_cases h1 : r=1 <;> by_cases h2 : r=2 <;> by_cases h4 : r=4 <;> by_cases h6 : r=6 <;> simp_all [write]
  rw [eq] at path
  exact path.transfer program [] decoded (by simp)

def saveWrites (s : X86Memory.State) : List Word := [s.regs 4-4,s.regs 4-8,s.regs 4-12,s.regs 4-16]
theorem saved_frame (s : X86Memory.State) (a : Word) (safe : ∀ b, b ∈ saveWrites s → Apart a b) :
    load32 (saved s).memory a=load32 s.memory a := by
  simp only [saved,X86Routine.pushWord,put,write,ite_true]
  simp [BitVec.sub_sub]
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp [saveWrites]))]

/-- Only initial table reads and their separation from the four saves are needed. -/
structure RayInputs (s : X86Memory.State) (angle : Angle) (distance : Fixed) : Prop where
  angleReg : s.regs 2=angle.raw.toBitVec
  rangeReg : s.regs 3=distance.raw.toBitVec
  tables : ThrustTables s.memory
  tableSafe : ∀ (a : Word), a ∈ [(0x13584 : Word),(angle.raw.toBitVec >>> 19 <<< 2)+0x7a84,
    (angle.raw.toBitVec >>> 19 <<< 2)+0x5a84] → ∀ b, b ∈ saveWrites s → Apart a b

theorem selected_tables (s : X86Memory.State) (angle : Angle) (distance : Fixed)
    (h : RayInputs s angle distance) :
    cosine s=angle.fineCosine.raw.toBitVec ∧ sine s=angle.fineSine.raw.toBitVec := by
  have tables := thrust_selected_tables s.memory angle h.tables
  have ptr : cosinePointer s=0x7a84 := by
    rw [cosinePointer,saved_frame s _ (h.tableSafe _ (by simp)),h.tables.cosinePointer]
  constructor
  · unfold cosine
    rw [ptr]
    simp only [index,h.angleReg]
    rw [BitVec.add_comm,saved_frame s _ (h.tableSafe _ (by simp))]
    simpa only [h.tables.cosinePointer] using tables.1
  · unfold sine
    simp only [index,h.angleReg]
    rw [saved_frame s _ (h.tableSafe _ (by simp))]
    exact tables.2

/-- These are the actual production endpoint offsets, for all 32-bit ranges.
The caller separately restricts its accepted range to positive values. -/
theorem live_endpoint (s : X86Memory.State) (thing : Collision.SolidThing)
    (angle : Angle) (distance : Fixed) (h : RayInputs s angle distance) :
    (thing.x.raw.toBitVec+(ray s).core.regs 1,thing.y.raw.toBitVec+(ray s).core.regs 6)=
      ((thing.attackEndpoint angle distance).1.raw.toBitVec,
       (thing.attackEndpoint angle distance).2.raw.toBitVec) := by
  have tab := selected_tables s angle distance h
  simp only [ray,put,write]
  simp [tab.1,tab.2,units,h.rangeReg,Collision.SolidThing.attackEndpoint,Fixed.add]
  constructor
  · change _+angle.fineCosine.raw.toBitVec*distance.raw.toBitVec.sshiftRight 16 =
      _+distance.raw.toBitVec.sshiftRight 16*angle.fineCosine.raw.toBitVec
    rw [BitVec.mul_comm]
  · rfl

def target (s : X86Memory.State) := load32 s.memory 0x2b9f8
def chosen (s : X86Memory.State) : Word := if target s=0 then 0 else load32 s.memory 0x2b9b4
def returnFlags (s : X86Memory.State) : Option Flags :=
  if target s=0 then some (logical32 0) else some (compare32 (target s) 0)
def pop (s : X86Memory.State) (r : Reg) := put (put s 4 (s.regs 4+4)) r (load32 s.memory (s.regs 4))
def returned (s : X86Memory.State) : X86Control.State :=
  let t := pop (pop (pop (pop (put s 0 (chosen s)) 5) 7) 6) 1
  ⟨put t 4 (t.regs 4+4),returnFlags s,(load32 t.memory (t.regs 4)).toNat⟩

theorem return_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 8 ⟨s,f,0x2bbff⟩ (returned s) := by
  have path : X86Routine.Prefix listed [] 8 ⟨s,f,0x2bbff⟩ (returned s) := by
    by_cases h : target s=(0#32)
    · let c1 := put s 0 (chosen s)
      let c2 := pop c1 5
      let c3 := pop c2 7
      let c4 := pop c3 6
      let c5 := pop c4 1
      apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (target s) 0),0x2bc06⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,target])
      apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (target s) 0),0x2bc12⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,compare32,h])
      apply X86Routine.Prefix.step (middle := ⟨c1,some (logical32 0),0x2bc14⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c1,chosen,returnFlags,pop,h,logical32])
      apply X86Routine.Prefix.step (middle := ⟨c2,some (logical32 0),0x2bc15⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c2,c1,chosen,returnFlags,pop,h,logical32])
      apply X86Routine.Prefix.step (middle := ⟨c3,some (logical32 0),0x2bc16⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c3,c2,c1,chosen,returnFlags,pop,h,logical32])
      apply X86Routine.Prefix.step (middle := ⟨c4,some (logical32 0),0x2bc17⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c4,c3,c2,c1,chosen,returnFlags,pop,h,logical32])
      apply X86Routine.Prefix.step (middle := ⟨c5,some (logical32 0),0x2bc18⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c5,c4,c3,c2,c1,chosen,returnFlags,pop,h,logical32])
      apply X86Routine.Prefix.step (middle := returned s) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,returned,returnFlags,c5,c4,c3,c2,c1,pop,h])
      exact X86Routine.Prefix.nil _
    · let c1 := put s 0 (chosen s)
      let c2 := pop c1 5
      let c3 := pop c2 7
      let c4 := pop c3 6
      let c5 := pop c4 1
      apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (target s) 0),0x2bc06⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,target])
      apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (target s) 0),0x2bc08⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,compare32,h])
      apply X86Routine.Prefix.step (middle := ⟨c1,some (compare32 (target s) 0),0x2bc0d⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c1,chosen,returnFlags,pop,h,logical32])
      apply X86Routine.Prefix.step (middle := ⟨c2,some (compare32 (target s) 0),0x2bc0e⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c2,c1,chosen,returnFlags,pop,h,logical32])
      apply X86Routine.Prefix.step (middle := ⟨c3,some (compare32 (target s) 0),0x2bc0f⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c3,c2,c1,chosen,returnFlags,pop,h,logical32])
      apply X86Routine.Prefix.step (middle := ⟨c4,some (compare32 (target s) 0),0x2bc10⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c4,c3,c2,c1,chosen,returnFlags,pop,h,logical32])
      apply X86Routine.Prefix.step (middle := ⟨c5,some (compare32 (target s) 0),0x2bc11⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,c5,c4,c3,c2,c1,chosen,returnFlags,pop,h,logical32])
      apply X86Routine.Prefix.step (middle := returned s) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,X86Memory.execute,put,write,X86Routine.pushWord,blockPreservesFlags,returned,returnFlags,c5,c4,c3,c2,c1,pop,h])
      exact X86Routine.Prefix.nil _
  exact path.transfer program [] decoded (by simp)

theorem return_memory (s : X86Memory.State) : (returned s).core.memory=s.memory := rfl
theorem return_value (s : X86Memory.State) : (returned s).core.regs 0=chosen s := by
  simp [returned,pop,put,write]
theorem return_miss (s : X86Memory.State) (miss : target s=0) : (returned s).core.regs 0=0 := by
  rw [return_value]; exact if_pos miss
theorem return_hit (s : X86Memory.State) (hit : target s≠0) :
    (returned s).core.regs 0=load32 s.memory 0x2b9b4 := by
  rw [return_value]; exact if_neg hit

theorem restores (s : X86Memory.State) :
    ((returned s).core.regs 5,(returned s).core.regs 7,(returned s).core.regs 6,
      (returned s).core.regs 1,(returned s).core.regs 4,(returned s).pc)=
    (load32 s.memory (s.regs 4),load32 s.memory (s.regs 4+4),load32 s.memory (s.regs 4+8),
      load32 s.memory (s.regs 4+12),s.regs 4+20,(load32 s.memory (s.regs 4+16)).toNat) := by
  simp [returned,pop,put,write,BitVec.add_assoc]
end Doom.Proofs.OriginalAimQuery
