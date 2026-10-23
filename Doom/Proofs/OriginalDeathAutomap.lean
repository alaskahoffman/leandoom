import Doom.Proofs.OriginalWeaponDrop
import Doom.Death
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.DeathAutomap
open Verification X86 X86Memory X86Control BlockSummary
def code : List UInt8 := [0x8b,0x15,0xdc,0xb3,0x2,0x0,0x8d,0x4,0xd5,0x0,0x0,0x0,0x0,0x1,0xd0,0x8d,0x4,0x85,0x0,0x0,0x0,0x0,0x29,0xd0,0x8d,0x4,0xc5,0x0,0x0,0x0,0x0,0x8b,0x93,0x84,0x0,0x0,0x0,0x5,0x78,0xae,0x2,0x0,0x39,0xd0,0x75,0xe,0x83,0x3d,0x5c,0x2c,0x1,0x0,0x0,0x74,0x5,0xe8,0xc8,0xab,0xff,0xff]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2a38c ≤ pc ∧ pc < 0x2a3c8 then X86Routine.decodeAt bytes (pc-0x2a38c) else none
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x2a38c => some (.control (.block (.load 2 ⟨none,none,0,0x2b3dc⟩)),6)
  | 0x2a392 => some (.control (.block (.lea 0 ⟨none,some 2,3,0⟩)),7)
  | 0x2a399 => some (.control (.block (.arithmetic (.add 0 2))),2)
  | 0x2a39b => some (.control (.block (.lea 0 ⟨none,some 0,2,0⟩)),7)
  | 0x2a3a2 => some (.control (.block (.arithmetic (.sub 0 2))),2)
  | 0x2a3a4 => some (.control (.block (.lea 0 ⟨none,some 0,3,0⟩)),7)
  | 0x2a3ab => some (.control (.block (.load 2 ⟨some 3,none,0,132⟩)),6)
  | 0x2a3b1 => some (.addImmediate 0 0x2ae78,5)
  | 0x2a3b6 => some (.compareRegisters 0 2,2)
  | 0x2a3b8 => some (.control (.jumpZero false 14),2)
  | 0x2a3ba => some (.control (.cmpImmediate ⟨none,none,0,0x12c5c⟩ 0),7)
  | 0x2a3c1 => some (.control (.jumpZero true 5),2)
  | 0x2a3c3 => some (.call (-21560),5)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def player (i : Fin 4) : Word := 0x2ae78+BitVec.ofNat 32 (280*i.val)
def active (s : X86Memory.State) := load32 s.memory (0x12c5c#32)
def stops (s : X86Memory.State) (victim console : Fin 4) : Prop := victim=console ∧ active s≠0
instance (s : X86Memory.State) (v c : Fin 4) : Decidable (stops s v c) := inferInstanceAs (Decidable (v=c ∧ active s≠0))
def middle (s : X86Memory.State) (victim console : Fin 4) : X86Control.State :=
  ⟨⟨write (write s.regs 0 (player console)) 2 (player victim),s.memory⟩,none,0x2a3b6⟩
def branchFlags (s : X86Memory.State) (victim console : Fin 4) :=
  if victim=console then compare32 (active s) 0 else compare32 (player console) (player victim)
def result (s : X86Memory.State) (victim console : Fin 4) : X86Control.State :=
  if stops s victim console then
    ⟨X86Routine.pushWord (middle s victim console).core 0x2a3c8,some (branchFlags s victim console),0x24f90⟩
  else ⟨(middle s victim console).core,some (branchFlags s victim console),0x2a3c8⟩

theorem player_injective (v c : Fin 4) : player c=player v ↔ v=c := by
  have all : ∀ v c : Fin 4, player c=player v ↔ v=c := by decide
  exact all v c

theorem prologue (s : X86Memory.State) (f : Option Flags) (v c : Fin 4)
    (console : load32 s.memory (0x2b3dc#32)=BitVec.ofNat 32 c.val)
    (victim : load32 s.memory (s.regs 3+(132#32))=player v) :
    X86Routine.Prefix listed [0x24f90,0x2a3c8] 8 ⟨s,f,0x2a38c⟩ (middle s v c) := by
  let ix := BitVec.ofNat 32 c.val
  have offset : ((((ix <<< 3)+ix) <<< 2)-ix) <<< 3+(0x2ae78#32)=player c := by
    rcases c with ⟨c,hc⟩; have cases : c=0 ∨ c=1 ∨ c=2 ∨ c=3 := by omega
    rcases cases with rfl|rfl|rfl|rfl <;> simp only [ix,player,Fin.val_mk] <;> decide
  simp only [ix] at offset
  let c1 := put s 2 ix
  let c2 := put c1 0 (ix <<< 3)
  let c3 := put c2 0 ((ix <<< 3)+ix)
  let c4 := put c3 0 (((ix <<< 3)+ix) <<< 2)
  let c5 := put c4 0 ((((ix <<< 3)+ix) <<< 2)-ix)
  let c6 := put c5 0 (((((ix <<< 3)+ix) <<< 2)-ix) <<< 3)
  let c7 := put c6 2 (player v)
  apply X86Routine.Prefix.step (middle := ⟨c1,f,0x2a392⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
      blockPreservesFlags,X86Block.Address.eval,put,write,c1,
      middle,console,victim,ix,offset])
  apply X86Routine.Prefix.step (middle := ⟨c2,f,0x2a399⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
      blockPreservesFlags,X86Block.Address.eval,put,write,c1,c2,
      middle,console,victim,ix,offset])
  apply X86Routine.Prefix.step (middle := ⟨c3,none,0x2a39b⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
      blockPreservesFlags,X86Block.Address.eval,put,write,c1,c2,c3,
      middle,console,victim,ix,offset])
  apply X86Routine.Prefix.step (middle := ⟨c4,none,0x2a3a2⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
      blockPreservesFlags,X86Block.Address.eval,put,write,c1,c2,c3,c4,
      middle,console,victim,ix,offset])
  apply X86Routine.Prefix.step (middle := ⟨c5,none,0x2a3a4⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
      blockPreservesFlags,X86Block.Address.eval,put,write,c1,c2,c3,c4,c5,
      middle,console,victim,ix,offset])
  apply X86Routine.Prefix.step (middle := ⟨c6,none,0x2a3ab⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
      blockPreservesFlags,X86Block.Address.eval,put,write,c1,c2,c3,c4,c5,c6,
      middle,console,victim,ix,offset])
  apply X86Routine.Prefix.step (middle := ⟨c7,none,0x2a3b1⟩) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
      blockPreservesFlags,X86Block.Address.eval,put,write,c1,c2,c3,c4,c5,c6,c7,
      middle,console,victim,ix,offset])
  apply X86Routine.Prefix.step (middle := middle s v c) (by simp) (by rfl) (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
      blockPreservesFlags,X86Block.Address.eval,put,write,c1,c2,c3,c4,c5,c6,c7,
      middle,console,victim,ix,offset]
    funext r
    by_cases h0 : r=0 <;> by_cases h2 : r=2 <;> simp_all [write])
  exact X86Routine.Prefix.nil _

theorem execution (s : X86Memory.State) (f : Option Flags) (v c : Fin 4)
    (console : load32 s.memory (0x2b3dc#32)=BitVec.ofNat 32 c.val)
    (victim : load32 s.memory (s.regs 3+(132#32))=player v) :
    X86Routine.run program [0x24f90,0x2a3c8] 13 ⟨s,f,0x2a38c⟩=some (result s v c) := by
  have run : X86Routine.run listed [0x24f90,0x2a3c8] 13 ⟨s,f,0x2a38c⟩=some (result s v c) := by
    apply (prologue s f v c console victim).finish (fuel := 5) ?_ 13 (by decide)
    by_cases same : v=c <;> by_cases zero : active s=(0#32)
    all_goals
      simp only [active] at zero
      simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,X86Block.Address.eval,
        result,middle,branchFlags,stops,active,put,write,X86Routine.pushWord,
        cmp32_zero,player_injective,same,zero]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem live_guard (s : X86Memory.State) (v : Fin 4) (world : Death.World)
    (auto : (active s≠0) ↔ world.automap=true) :
    stops s v world.console ↔ Death.shouldStopAutomap v world=true := by
  simpa only [stops,Death.shouldStopAutomap,Bool.and_eq_true,beq_iff_eq] using and_congr_right (fun _ => auto)

def writes (s : X86Memory.State) (v c : Fin 4) := if stops s v c then [s.regs 4-(4#32)] else []
theorem frame (s : X86Memory.State) (v c : Fin 4) :
    PlayerHeight.Frame s.memory (result s v c).core.memory (writes s v c) := by
  intro a safe
  by_cases stop : stops s v c
  · simp only [writes,stop,if_true,List.mem_singleton] at safe
    simpa [result,stop,X86Routine.pushWord,middle,write] using load_store_apart s.memory (s.regs 4-(4#32)) a 0x2a3c8 (safe _ rfl)
  · simp [result,stop,middle]

end Doom.Proofs.DeathAutomap
