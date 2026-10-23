import Doom.Proofs.OriginalWeaponAmmo
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.WeaponFire
open Verification X86 X86Memory X86Control BlockSummary
def code : List UInt8 := [0x53,0x51,0x52,0x89,0xc1,0xe8,0x46,0x0,0x0,0x0,0x85,0xc0,0x74,0x31,0xba,0x9a,0x0,0x0,0x0,0x8b,0x1,0xe8,0x76,0x3a,0x0,0x0,0x8b,0x51,0x70,0x8d,0x4,0x95,0x0,0x0,0x0,0x0,0x29,0xd0,0x8b,0x1c,0xc5,0xa0,0x2d,0x1,0x0,0x31,0xd2,0x89,0xc8,0xe8,0xfa,0xfb,0xff,0xff,0x8b,0x11,0x89,0xd0,0xe8,0xd1,0x9b,0xff,0xff,0x5a,0x59,0x5b,0xc3]
def bytesProgram (bs : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2d410 ≤ pc ∧ pc < 0x2d453 then X86Routine.decodeAt bs (pc-0x2d410) else none
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x2d410 => some (.push 3,1)
  | 0x2d411 => some (.push 1,1)
  | 0x2d412 => some (.push 2,1)
  | 0x2d413 => some (.control (.block (.legacy (.mov 1 0))),2)
  | 0x2d415 => some (.call 70,5)
  | 0x2d41a => some (.control (.testWord 0 0),2)
  | 0x2d41c => some (.control (.jumpZero true 49),2)
  | 0x2d41e => some (.immediate 2 154,5)
  | 0x2d423 => some (.control (.block (.legacy (.load 0 1 0))),2)
  | 0x2d425 => some (.call 14966,5)
  | 0x2d42a => some (.control (.block (.legacy (.load 2 1 112))),3)
  | 0x2d42d => some (.control (.block (.lea 0 ⟨none,some 2,2,0⟩)),7)
  | 0x2d434 => some (.control (.block (.arithmetic (.sub 0 2))),2)
  | 0x2d436 => some (.control (.block (.load 3 ⟨none,some 0,3,0x12da0⟩)),7)
  | 0x2d43d => some (.xorRegister 2 2,2)
  | 0x2d43f => some (.control (.block (.legacy (.mov 0 1))),2)
  | 0x2d441 => some (.call (-1030),5)
  | 0x2d446 => some (.control (.block (.legacy (.load 2 1 0))),2)
  | 0x2d448 => some (.control (.block (.legacy (.mov 0 2))),2)
  | 0x2d44a => some (.call (-25647),5)
  | 0x2d44f => some (.pop 2,1)
  | 0x2d450 => some (.pop 1,1)
  | 0x2d451 => some (.pop 3,1)
  | 0x2d452 => some (.ret,1)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def saved (s : X86Memory.State) := X86Routine.pushWord (X86Routine.pushWord
  (X86Routine.pushWord s (s.regs 3)) (s.regs 1)) (s.regs 2)
def checkCall (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨X86Routine.pushWord (put (saved s) 1 (s.regs 0)) 0x2d41a,f,0x2d460⟩
theorem check_call_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2d460] 5 ⟨s,f,0x2d410⟩=some (checkCall s f) := by
  have run : X86Routine.run listed [0x2d460] 5 ⟨s,f,0x2d410⟩=some (checkCall s f) := by
    simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,put,write,saved,checkCall,X86Routine.pushWord,blockPreservesFlags]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

def branch (s : X86Memory.State) : X86Control.State :=
  ⟨s,some (logical32 (s.regs 0)),if s.regs 0=(0#32) then 0x2d44f else 0x2d41e⟩
theorem branch_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2d44f,0x2d41e] 2 ⟨s,f,0x2d41a⟩=some (branch s) := by
  have run : X86Routine.run listed [0x2d44f,0x2d41e] 2 ⟨s,f,0x2d41a⟩=some (branch s) := by
    by_cases h : s.regs 0=(0#32) <;>
      simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,branch,logical32,h]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

def poseCall (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨X86Routine.pushWord (put (put s 2 154) 0 (load32 s.memory (s.regs 1))) 0x2d42a,f,0x30ea0⟩
theorem pose_call_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x30ea0] 3 ⟨s,f,0x2d41e⟩=some (poseCall s f) := by
  have run : X86Routine.run listed [0x30ea0] 3 ⟨s,f,0x2d41e⟩=some (poseCall s f) := by
    simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,put,write,poseCall,X86Routine.pushWord,blockPreservesFlags]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

def weapon (s : X86Memory.State) := load32 s.memory (s.regs 1+(112#32))
def attackState (s : X86Memory.State) := load32 s.memory ((((weapon s <<< 2)-weapon s) <<< 3)+(0x12da0#32))
def attackCall (s : X86Memory.State) : X86Control.State :=
  ⟨X86Routine.pushWord (put (put (put s 0 (s.regs 1)) 2 0) 3 (attackState s)) 0x2d446,some (logical32 0),0x2d040⟩
theorem attack_call_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2d040] 7 ⟨s,f,0x2d42a⟩=some (attackCall s) := by
  have run : X86Routine.run listed [0x2d040] 7 ⟨s,f,0x2d42a⟩=some (attackCall s) := by
    simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86.execute,X86Block.Address.eval,put,write,attackCall,attackState,weapon,
      X86Routine.pushWord,blockPreservesFlags,logical32,BitVec.sub_eq_add_neg]
    funext r
    by_cases h0 : r=0 <;> by_cases h2 : r=2 <;> by_cases h3 : r=3 <;> by_cases h4 : r=4 <;> simp_all [write]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

def noiseCall (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  let actor := load32 s.memory (s.regs 1)
  ⟨X86Routine.pushWord (put (put s 2 actor) 0 actor) 0x2d44f,f,0x27020⟩
theorem noise_call_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x27020] 3 ⟨s,f,0x2d446⟩=some (noiseCall s f) := by
  have run : X86Routine.run listed [0x27020] 3 ⟨s,f,0x2d446⟩=some (noiseCall s f) := by
    simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,put,write,noiseCall,X86Routine.pushWord,blockPreservesFlags]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

def returned (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  let t := PspriteLoop.popped (PspriteLoop.popped (PspriteLoop.popped s 2) 1) 3
  ⟨put t 4 (t.regs 4+4),f,(load32 t.memory (t.regs 4)).toNat⟩
theorem return_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 4 ⟨s,f,0x2d44f⟩ (returned s f) := by
  let a := PspriteLoop.popped s 2
  let b := PspriteLoop.popped a 1
  let c := PspriteLoop.popped b 3
  have p : X86Routine.Prefix listed [] 4 ⟨s,f,0x2d44f⟩ (returned s f) := by
    apply X86Routine.Prefix.step (middle := ⟨a,f,0x2d450⟩) (by simp) (by rfl) rfl
    apply X86Routine.Prefix.step (middle := ⟨b,f,0x2d451⟩) (by simp) (by rfl) rfl
    apply X86Routine.Prefix.step (middle := ⟨c,f,0x2d452⟩) (by simp) (by rfl) rfl
    apply X86Routine.Prefix.step (middle := returned s f) (by simp) (by rfl) rfl
    exact X86Routine.Prefix.nil _
  exact p.transfer program [] decoded (by simp)


/-- The state requested by the real CALL is the live weapon's attack state.
The table/weapon relation is explicit at this call site. -/
theorem attack_live (s : X86Memory.State) (w : Fin 3)
    (hw : weapon s=BitVec.ofNat 32 w.val)
    (table : load32 s.memory (0x12da0+24*BitVec.ofNat 32 w.val)=BitVec.ofNat 32 (Weapon.attackState w.val)) :
    (attackCall s).core.regs 0=s.regs 1 ∧ (attackCall s).core.regs 2=0 ∧
    (attackCall s).core.regs 3=BitVec.ofNat 32 (Weapon.attackState w.val) ∧
    load32 (attackCall s).core.memory ((attackCall s).core.regs 4)=0x2d446 := by
  have cases : w.val=0 ∨ w.val=1 ∨ w.val=2 := by omega
  rcases cases with h | h | h <;>
    simp [h] at hw table ⊢ <;>
    simpa [attackCall,attackState,hw,put,write,X86Routine.pushWord,load_store] using table
end Doom.Proofs.WeaponFire
