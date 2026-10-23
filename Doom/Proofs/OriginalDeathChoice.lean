import Doom.Proofs.OriginalWeaponDrop
import Doom.Death
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.DeathChoice
open Verification X86 X86Memory X86Control BlockSummary
def code : List UInt8 := [0x8b,0x43,0x5c,0x8b,0x50,0x8,0x8b,0x73,0x6c,0xf7,0xda,0x39,0xf2,0x7e,0xd,0x8b,0x78,0x34,0x85,0xff,0x74,0x6,0x89,0xfa,0x89,0xd8,0xeb,0x8,0x8b,0x53,0x5c,0x89,0xd8,0x8b,0x52,0x30,0xe8,0xaf,0x6a,0x0,0x0]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2a3c8 ≤ pc ∧ pc < 0x2a3f1 then X86Routine.decodeAt bytes (pc-0x2a3c8) else none
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x2a3c8 => some (.control (.block (.legacy (.load 0 3 92))),3)
  | 0x2a3cb => some (.control (.block (.legacy (.load 2 0 8))),3)
  | 0x2a3ce => some (.control (.block (.legacy (.load 6 3 108))),3)
  | 0x2a3d1 => some (.negateRegister 2,2)
  | 0x2a3d3 => some (.compareRegisters 2 6,2)
  | 0x2a3d5 => some (.jumpSigned 1 13,2)
  | 0x2a3d7 => some (.control (.block (.legacy (.load 7 0 52))),3)
  | 0x2a3da => some (.control (.testWord 7 7),2)
  | 0x2a3dc => some (.control (.jumpZero true 6),2)
  | 0x2a3de => some (.control (.block (.legacy (.mov 2 7))),2)
  | 0x2a3e0 => some (.control (.block (.legacy (.mov 0 3))),2)
  | 0x2a3e2 => some (.jump 8,2)
  | 0x2a3e4 => some (.control (.block (.legacy (.load 2 3 92))),3)
  | 0x2a3e7 => some (.control (.block (.legacy (.mov 0 3))),2)
  | 0x2a3e9 => some (.control (.block (.legacy (.load 2 2 48))),3)
  | 0x2a3ec => some (.call 27311,5)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def infoPointer (s : X86Memory.State) := load32 s.memory (s.regs 3+(92#32))
def health (s : X86Memory.State) := load32 s.memory (s.regs 3+(108#32))
def spawn (s : X86Memory.State) := load32 s.memory (infoPointer s+(8#32))
def normal (s : X86Memory.State) := load32 s.memory (infoPointer s+(48#32))
def extreme (s : X86Memory.State) := load32 s.memory (infoPointer s+(52#32))
abbrev overkill (s : X86Memory.State) := (health s).toInt < (-spawn s).toInt
def chosen (s : X86Memory.State) := if overkill s ∧ extreme s≠0 then extreme s else normal s

def middle (s : X86Memory.State) : X86Control.State :=
  ⟨⟨write (write (write s.regs 0 (infoPointer s)) 2 (-spawn s)) 6 (health s),s.memory⟩,none,0x2a3d3⟩
def result (s : X86Memory.State) : X86Control.State :=
  ⟨⟨write (write (write (write (write s.regs 0 (s.regs 3)) 2 (chosen s)) 6 (health s))
      7 (if overkill s then extreme s else s.regs 7)) 4 (s.regs 4-(4#32)),
    store32 s.memory (s.regs 4-(4#32)) 0x2a3f1⟩,
    some (if overkill s then logical32 (extreme s) else compare32 (-spawn s) (health s)),0x30ea0⟩

theorem prologue (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix listed [0x30ea0] 4 ⟨s,f,0x2a3c8⟩ (middle s) := by
  let c1 := put s 0 (infoPointer s)
  let c2 := put c1 2 (spawn s)
  let c3 := put c2 6 (health s)
  apply X86Routine.Prefix.step (middle := ⟨c1,f,0x2a3cb⟩) (by simp) (by rfl) (by rfl)
  apply X86Routine.Prefix.step (middle := ⟨c2,f,0x2a3ce⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      blockPreservesFlags,c1,c2,put,write,spawn])
  apply X86Routine.Prefix.step (middle := ⟨c3,f,0x2a3d1⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      blockPreservesFlags,c1,c2,c3,put,write,health])
  apply X86Routine.Prefix.step (middle := middle s) (by simp) (by rfl) (by
    simp [X86Routine.execute,middle,c1,c2,c3,put,write]
    funext r
    by_cases h0 : r=0 <;> by_cases h2 : r=2 <;> by_cases h6 : r=6 <;> simp_all [write])
  exact X86Routine.Prefix.nil _

theorem execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run listed [0x30ea0] 13 ⟨s,f,0x2a3c8⟩=some (result s) := by
  apply (prologue s f).finish (fuel := 9) ?_ 13 (by decide)
  by_cases over : overkill s <;> by_cases has : extreme s=(0#32)
  all_goals
    simp only [overkill,health,spawn,infoPointer] at over
    simp only [extreme,infoPointer] at has
    simp (config := { maxSteps := 200000 }) [X86Routine.run,listed,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      blockPreservesFlags,X86Block.Address.eval,put,write,X86Routine.pushWord,middle,
      result,chosen,overkill,infoPointer,health,spawn,normal,extreme,logical32,
      cmp32_signed_le,cmp32_zero,← Int.not_lt,over,has]
  all_goals funext r
  all_goals by_cases h0 : r=0 <;> by_cases h2 : r=2 <;> by_cases h4 : r=4 <;>
    by_cases h6 : r=6 <;> by_cases h7 : r=7 <;> simp_all [write]

structure Inputs (s : X86Memory.State) (hp : Int32) (info : Death.Info) : Prop where
  health : health s=hp.toBitVec
  spawn : spawn s=info.spawnHealth.toBitVec
  normal : normal s=BitVec.ofNat 32 info.normal
  extreme : extreme s=BitVec.ofNat 32 info.extreme
  extremeBound : info.extreme < 4294967296

theorem chosen_live (s : X86Memory.State) (hp : Int32) (info : Death.Info) (h : Inputs s hp info) :
    chosen s=BitVec.ofNat 32 (Death.deathState hp info) := by
  have zero : BitVec.ofNat 32 info.extreme=(0#32) ↔ info.extreme=0 := by
    constructor
    · intro eq; have eq := congrArg BitVec.toNat eq
      simpa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt h.extremeBound] using eq
    · intro eq; simp [eq]
  have neg : -info.spawnHealth.toBitVec=(-info.spawnHealth).toBitVec := rfl
  unfold chosen overkill
  rw [h.health,h.spawn,h.normal,h.extreme,neg,Int32.toInt_toBitVec,Int32.toInt_toBitVec]
  simp only [zero,Death.deathState,ne_eq,bne_iff_ne, Bool.and_eq_true,decide_eq_true_eq,Int32.lt_iff_toInt_lt]
  by_cases hlt : hp.toInt < (-info.spawnHealth).toInt <;>
    by_cases hz : info.extreme=0 <;> simp_all
  split <;> simp_all

theorem original_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x30ea0] 13 ⟨s,f,0x2a3c8⟩=some (result s) := by
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [execution]; simp)]
  exact execution s f

theorem frame (s : X86Memory.State) :
    PlayerHeight.Frame s.memory (result s).core.memory [s.regs 4-(4#32)] := by
  intro a safe
  exact load_store_apart _ _ _ _ (safe _ (by simp))

theorem live_correspondence (s : X86Memory.State) (f : Option Flags) (hp : Int32) (info : Death.Info)
    (h : Inputs s hp info) :
    ∃ t, X86Routine.run program [0x30ea0] 13 ⟨s,f,0x2a3c8⟩=some t ∧
      t.pc=0x30ea0 ∧ t.core.regs 0=s.regs 3 ∧
      t.core.regs 2=BitVec.ofNat 32 (Death.deathState hp info) ∧
      t.core.regs 3=s.regs 3 ∧ t.core.regs 4=s.regs 4-4 ∧
      load32 t.core.memory (s.regs 4-4)=0x2a3f1 ∧
      PlayerHeight.Frame s.memory t.core.memory [s.regs 4-4] := by
  refine ⟨result s,original_execution s f,rfl,?_,?_,?_,?_,?_,frame s⟩
  all_goals simp [result,write,load_store,chosen_live s hp info h]

end Doom.Proofs.DeathChoice
