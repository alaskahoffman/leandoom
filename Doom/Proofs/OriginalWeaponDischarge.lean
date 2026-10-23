import Doom.Verification.X86Routine
import Doom.Proofs.BlockSummary
import Doom.Proofs.WeaponActions
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

/-! Actual DOS discharge instructions. Execution stops at each real callee;
sound, actor-state setting, psprite setting and autoaim are not assumed executed.
The debit/flash segment starts at the return from the actor setter. -/
namespace Doom.Proofs.OriginalWeaponDischarge
open Verification X86 X86Memory X86Control BlockSummary
def pistolBytes : List UInt8 := [0x53,0x51,0x89,0xc1,0xba,0x1,0x0,0x0,0x0,0x8b,0x0,0xe8,0xd0,0x1a,0x1,0x0,0xba,0x9b,0x0,0x0,0x0,0x8b,0x1,0xe8,0xf4,0x35,0x0,0x0,0x8b,0x51,0x70,0x8d,0x4,0x95,0x0,0x0,0x0,0x0,0x29,0xd0,0x8b,0x4,0xc5,0x90,0x2d,0x1,0x0,0xff,0x8c,0x81,0x9c,0x0,0x0,0x0,0x8b,0x51,0x70,0x8d,0x4,0x95,0x0,0x0,0x0,0x0,0x29,0xd0,0xba,0x1,0x0,0x0,0x0,0x8b,0x1c,0xc5,0xa4,0x2d,0x1,0x0,0x89,0xc8,0xe8,0x5b,0xf7,0xff,0xff,0x8b,0x1,0xe8,0xd4,0xfe,0xff,0xff]
def shotgunBytes : List UInt8 := [0x53,0x51,0x56,0x89,0xc1,0xba,0x2,0x0,0x0,0x0,0x8b,0x0,0xe8,0x4f,0x1a,0x1,0x0,0xba,0x9b,0x0,0x0,0x0,0x8b,0x1,0xe8,0x73,0x35,0x0,0x0,0x8b,0x59,0x70,0x8d,0x4,0x9d,0x0,0x0,0x0,0x0,0x29,0xd8,0x8b,0x4,0xc5,0x90,0x2d,0x1,0x0,0xff,0x8c,0x81,0x9c,0x0,0x0,0x0,0x8b,0x59,0x70,0x8d,0x4,0x9d,0x0,0x0,0x0,0x0,0x29,0xd8,0xba,0x1,0x0,0x0,0x0,0x8b,0x1c,0xc5,0xa4,0x2d,0x1,0x0,0x89,0xc8,0xe8,0xda,0xf6,0xff,0xff,0x8b,0x1,0xe8,0x53,0xfe,0xff,0xff]
def bytesProgram (pistol shotgun : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2d890 ≤ pc ∧ pc < 0x2d8ec then X86Routine.decodeAt pistol (pc-0x2d890)
  else if 0x2d910 ≤ pc ∧ pc < 0x2d96d then X86Routine.decodeAt shotgun (pc-0x2d910) else none
def program := bytesProgram pistolBytes shotgunBytes
def listed : X86Routine.Program
  | 0x2d890 => some (.push 3,1)
  | 0x2d891 => some (.push 1,1)
  | 0x2d892 => some (.control (.block (.legacy (.mov 1 0))),2)
  | 0x2d894 => some (.immediate 2 1,5)
  | 0x2d899 => some (.control (.block (.legacy (.load 0 0 0))),2)
  | 0x2d89b => some (.call 72400,5)
  | 0x2d8a0 => some (.immediate 2 155,5)
  | 0x2d8a5 => some (.control (.block (.legacy (.load 0 1 0))),2)
  | 0x2d8a7 => some (.call 13812,5)
  | 0x2d8ac => some (.control (.block (.legacy (.load 2 1 112))),3)
  | 0x2d8af => some (.control (.block (.lea 0 ⟨none,some 2,2,0⟩)),7)
  | 0x2d8b6 => some (.control (.block (.arithmetic (.sub 0 2))),2)
  | 0x2d8b8 => some (.control (.block (.load 0 ⟨none,some 0,3,0x12d90⟩)),7)
  | 0x2d8bf => some (.decrementMemory ⟨some 1,some 0,2,156⟩,7)
  | 0x2d8c6 => some (.control (.block (.legacy (.load 2 1 112))),3)
  | 0x2d8c9 => some (.control (.block (.lea 0 ⟨none,some 2,2,0⟩)),7)
  | 0x2d8d0 => some (.control (.block (.arithmetic (.sub 0 2))),2)
  | 0x2d8d2 => some (.immediate 2 1,5)
  | 0x2d8d7 => some (.control (.block (.load 3 ⟨none,some 0,3,0x12da4⟩)),7)
  | 0x2d8de => some (.control (.block (.legacy (.mov 0 1))),2)
  | 0x2d8e0 => some (.call (-2213),5)
  | 0x2d8e5 => some (.control (.block (.legacy (.load 0 1 0))),2)
  | 0x2d8e7 => some (.call (-300),5)
  | 0x2d910 => some (.push 3,1)
  | 0x2d911 => some (.push 1,1)
  | 0x2d912 => some (.push 6,1)
  | 0x2d913 => some (.control (.block (.legacy (.mov 1 0))),2)
  | 0x2d915 => some (.immediate 2 2,5)
  | 0x2d91a => some (.control (.block (.legacy (.load 0 0 0))),2)
  | 0x2d91c => some (.call 72271,5)
  | 0x2d921 => some (.immediate 2 155,5)
  | 0x2d926 => some (.control (.block (.legacy (.load 0 1 0))),2)
  | 0x2d928 => some (.call 13683,5)
  | 0x2d92d => some (.control (.block (.legacy (.load 3 1 112))),3)
  | 0x2d930 => some (.control (.block (.lea 0 ⟨none,some 3,2,0⟩)),7)
  | 0x2d937 => some (.control (.block (.arithmetic (.sub 0 3))),2)
  | 0x2d939 => some (.control (.block (.load 0 ⟨none,some 0,3,0x12d90⟩)),7)
  | 0x2d940 => some (.decrementMemory ⟨some 1,some 0,2,156⟩,7)
  | 0x2d947 => some (.control (.block (.legacy (.load 3 1 112))),3)
  | 0x2d94a => some (.control (.block (.lea 0 ⟨none,some 3,2,0⟩)),7)
  | 0x2d951 => some (.control (.block (.arithmetic (.sub 0 3))),2)
  | 0x2d953 => some (.immediate 2 1,5)
  | 0x2d958 => some (.control (.block (.load 3 ⟨none,some 0,3,0x12da4⟩)),7)
  | 0x2d95f => some (.control (.block (.legacy (.mov 0 1))),2)
  | 0x2d961 => some (.call (-2342),5)
  | 0x2d966 => some (.control (.block (.legacy (.load 0 1 0))),2)
  | 0x2d968 => some (.call (-429),5)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc ≠ none) : program pc = listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def entry : Fire.Gun → Nat | .pistol => 0x2d890 | .shotgun => 0x2d910
def afterSound : Fire.Gun → Nat | .pistol => 0x2d8a0 | .shotgun => 0x2d921
def afterPose : Fire.Gun → Nat | .pistol => 0x2d8ac | .shotgun => 0x2d92d
def afterFlash : Fire.Gun → Nat | .pistol => 0x2d8e5 | .shotgun => 0x2d966
def afterAim : Fire.Gun → Nat | .pistol => 0x2d8ec | .shotgun => 0x2d96d
def soundSteps : Fire.Gun → Nat | .pistol => 6 | .shotgun => 7
def soundId : Fire.Gun → Word | .pistol => 1 | .shotgun => 2

def saved (gun : Fire.Gun) (s : X86Memory.State) : X86Memory.State :=
  let t := X86Routine.pushWord (X86Routine.pushWord s (s.regs 3)) (s.regs 1)
  match gun with | .pistol => t | .shotgun => X86Routine.pushWord t (s.regs 6)
def soundCall (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  let t := saved gun s
  ⟨X86Routine.pushWord (put (put (put t 1 (s.regs 0)) 2 (soundId gun))
      0 (load32 t.memory (s.regs 0))) (BitVec.ofNat 32 (afterSound gun)), f, 0x3f370⟩
def poseCall (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨X86Routine.pushWord (put (put s 2 155) 0 (load32 s.memory (s.regs 1)))
    (BitVec.ofNat 32 (afterPose gun)), f, 0x30ea0⟩
def weapon (s : X86Memory.State) := load32 s.memory (s.regs 1+112)
def tableOffset (w : Word) := ((w <<< 2)-w) <<< 3
def ammoType (s : X86Memory.State) := load32 s.memory (tableOffset (weapon s)+0x12d90)
def ammoAddress (s : X86Memory.State) := s.regs 1+(ammoType s <<< 2)+156
def debited (s : X86Memory.State) : X86Memory.State :=
  {s with memory := store32 s.memory (ammoAddress s) (load32 s.memory (ammoAddress s)-1)}
/-- Re-read the weapon table after DEC, as the binary does. No hidden aliasing
assumption is needed for this complete register/memory execution summary. -/
def flash (s : X86Memory.State) := load32 s.memory (tableOffset (weapon s)+0x12da4)
def flashCall (gun : Fire.Gun) (s : X86Memory.State) : X86Control.State :=
  let t := debited s
  ⟨X86Routine.pushWord (put (put (put t 0 (s.regs 1)) 2 1) 3 (flash t))
    (BitVec.ofNat 32 (afterFlash gun)), none, 0x2d040⟩
def aimCall (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨X86Routine.pushWord (put s 0 (load32 s.memory (s.regs 1)))
    (BitVec.ofNat 32 (afterAim gun)), f, 0x2d7c0⟩

theorem sound_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x3f370] (soundSteps gun)
      ⟨s,f,entry gun⟩ = some (soundCall gun s f) := by
  have run : X86Routine.run listed [0x3f370] (soundSteps gun)
      ⟨s,f,entry gun⟩ = some (soundCall gun s f) := by
    cases gun <;> simp only [entry, afterSound, afterPose, afterFlash, afterAim, soundSteps] <;> simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,
      X86Block.execute,X86Memory.execute,put,write,saved,soundCall,entry,soundId,afterSound,soundSteps,
      X86Routine.pushWord,blockPreservesFlags] <;> rfl
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem pose_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x30ea0] 3 ⟨s,f,afterSound gun⟩ = some (poseCall gun s f) := by
  have run : X86Routine.run listed [0x30ea0] 3 ⟨s,f,afterSound gun⟩ = some (poseCall gun s f) := by
    cases gun <;> simp only [entry, afterSound, afterPose, afterFlash, afterAim, soundSteps] <;> simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,
      X86Block.execute,X86Memory.execute,put,write,poseCall,afterSound,afterPose,
      X86Routine.pushWord,blockPreservesFlags]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

/-- Twelve actual instructions, including the indexed memory DEC and real CALL.
All registers and byte memory are specified, including the return-address write. -/
theorem debit_flash_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2d040] 12 ⟨s,f,afterPose gun⟩ = some (flashCall gun s) := by
  have run : X86Routine.run listed [0x2d040] 12 ⟨s,f,afterPose gun⟩ = some (flashCall gun s) := by
    cases gun with
    | pistol =>
      let a1 : X86Memory.State := put s 2 (weapon s)
      let a2 : X86Memory.State := put a1 0 (weapon s <<< 2)
      let a3 : X86Memory.State := put a2 0 ((weapon s <<< 2)-weapon s)
      let a4 : X86Memory.State := put a3 0 (ammoType s)
      let a5 : X86Memory.State := {a4 with memory := (debited s).memory}
      let a6 : X86Memory.State := put a5 2 (weapon (debited s))
      let a7 : X86Memory.State := put a6 0 (weapon (debited s) <<< 2)
      let a8 : X86Memory.State := put a7 0 ((weapon (debited s) <<< 2)-weapon (debited s))
      let a9 : X86Memory.State := put a8 2 1
      let a10 : X86Memory.State := put a9 3 (flash (debited s))
      let a11 : X86Memory.State := put a10 0 (s.regs 1)
      let a12 : X86Memory.State := X86Routine.pushWord a11 (BitVec.ofNat 32 (afterFlash .pistol))
      have path : X86Routine.Prefix listed [0x2d040] 12 ⟨s,f,0x2d8ac⟩ ⟨a12,none,0x2d040⟩ := by
        apply X86Routine.Prefix.step (middle := ⟨a1,f,0x2d8af⟩) (by simp) (by rfl) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,
            a1,weapon,ammoType,ammoAddress,tableOffset,debited,flash,afterFlash])
        apply X86Routine.Prefix.step (middle := ⟨a2,f,0x2d8b6⟩) (by simp) (by rfl) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,
            a2,a1,weapon,ammoType,ammoAddress,tableOffset,debited,flash,afterFlash])
        apply X86Routine.Prefix.step (middle := ⟨a3,none,0x2d8b8⟩) (by simp) (by rfl) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,
            a3,a2,a1,weapon,ammoType,ammoAddress,tableOffset,debited,flash,afterFlash])
        apply X86Routine.Prefix.step (middle := ⟨a4,none,0x2d8bf⟩) (by simp) (by rfl) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,
            a4,a3,a2,a1,weapon,ammoType,ammoAddress,tableOffset,debited,flash,afterFlash])
        apply X86Routine.Prefix.step (middle := ⟨a5,none,0x2d8c6⟩) (by simp) (by rfl) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,
            a5,a4,a3,a2,a1,weapon,ammoType,ammoAddress,tableOffset,debited,flash,afterFlash])
        apply X86Routine.Prefix.step (middle := ⟨a6,none,0x2d8c9⟩) (by simp) (by rfl) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,
            a6,a5,a4,a3,a2,a1,weapon,ammoType,ammoAddress,tableOffset,debited,flash,afterFlash])
        apply X86Routine.Prefix.step (middle := ⟨a7,none,0x2d8d0⟩) (by simp) (by rfl) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,
            a7,a6,a5,a4,a3,a2,a1,weapon,ammoType,ammoAddress,tableOffset,debited,flash,afterFlash])
        apply X86Routine.Prefix.step (middle := ⟨a8,none,0x2d8d2⟩) (by simp) (by rfl) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,
            a8,a7,a6,a5,a4,a3,a2,a1,weapon,ammoType,ammoAddress,tableOffset,debited,flash,afterFlash])
        apply X86Routine.Prefix.step (middle := ⟨a9,none,0x2d8d7⟩) (by simp) (by rfl) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,
            a9,a8,a7,a6,a5,a4,a3,a2,a1,weapon,ammoType,ammoAddress,tableOffset,debited,flash,afterFlash])
        apply X86Routine.Prefix.step (middle := ⟨a10,none,0x2d8de⟩) (by simp) (by rfl) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,
            a10,a9,a8,a7,a6,a5,a4,a3,a2,a1,weapon,ammoType,ammoAddress,tableOffset,debited,flash,afterFlash])
        apply X86Routine.Prefix.step (middle := ⟨a11,none,0x2d8e0⟩) (by simp) (by rfl) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,
            a11,a10,a9,a8,a7,a6,a5,a4,a3,a2,a1,weapon,ammoType,ammoAddress,tableOffset,debited,flash,afterFlash])
        apply X86Routine.Prefix.step (middle := ⟨a12,none,0x2d040⟩) (by simp) (by rfl) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,
            a12,a11,a10,a9,a8,a7,a6,a5,a4,a3,a2,a1,weapon,ammoType,ammoAddress,tableOffset,debited,flash,afterFlash])
        exact X86Routine.Prefix.nil _
      have eq : (⟨a12,none,0x2d040⟩ : X86Control.State) = flashCall .pistol s := by
        simp [a12,a11,a10,a9,a8,a7,a6,a5,a4,a3,a2,a1,flashCall,put,X86Routine.pushWord,debited,write]
        funext r
        by_cases h0 : r=0 <;> by_cases h2 : r=2 <;> by_cases h3 : r=3 <;>
          by_cases h4 : r=4 <;> simp_all [write]
      rw [eq] at path
      exact path.finish (fuel := 0) (by rfl) 12 (by omega)
    | shotgun =>
      let a1 : X86Memory.State := put s 3 (weapon s)
      let a2 : X86Memory.State := put a1 0 (weapon s <<< 2)
      let a3 : X86Memory.State := put a2 0 ((weapon s <<< 2)-weapon s)
      let a4 : X86Memory.State := put a3 0 (ammoType s)
      let a5 : X86Memory.State := {a4 with memory := (debited s).memory}
      let a6 : X86Memory.State := put a5 3 (weapon (debited s))
      let a7 : X86Memory.State := put a6 0 (weapon (debited s) <<< 2)
      let a8 : X86Memory.State := put a7 0 ((weapon (debited s) <<< 2)-weapon (debited s))
      let a9 : X86Memory.State := put a8 2 1
      let a10 : X86Memory.State := put a9 3 (flash (debited s))
      let a11 : X86Memory.State := put a10 0 (s.regs 1)
      let a12 : X86Memory.State := X86Routine.pushWord a11 (BitVec.ofNat 32 (afterFlash .shotgun))
      have path : X86Routine.Prefix listed [0x2d040] 12 ⟨s,f,0x2d92d⟩ ⟨a12,none,0x2d040⟩ := by
        apply X86Routine.Prefix.step (middle := ⟨a1,f,0x2d930⟩) (by simp) (by rfl) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,
            a1,weapon,ammoType,ammoAddress,tableOffset,debited,flash,afterFlash])
        apply X86Routine.Prefix.step (middle := ⟨a2,f,0x2d937⟩) (by simp) (by rfl) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,
            a2,a1,weapon,ammoType,ammoAddress,tableOffset,debited,flash,afterFlash])
        apply X86Routine.Prefix.step (middle := ⟨a3,none,0x2d939⟩) (by simp) (by rfl) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,
            a3,a2,a1,weapon,ammoType,ammoAddress,tableOffset,debited,flash,afterFlash])
        apply X86Routine.Prefix.step (middle := ⟨a4,none,0x2d940⟩) (by simp) (by rfl) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,
            a4,a3,a2,a1,weapon,ammoType,ammoAddress,tableOffset,debited,flash,afterFlash])
        apply X86Routine.Prefix.step (middle := ⟨a5,none,0x2d947⟩) (by simp) (by rfl) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,
            a5,a4,a3,a2,a1,weapon,ammoType,ammoAddress,tableOffset,debited,flash,afterFlash])
        apply X86Routine.Prefix.step (middle := ⟨a6,none,0x2d94a⟩) (by simp) (by rfl) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,
            a6,a5,a4,a3,a2,a1,weapon,ammoType,ammoAddress,tableOffset,debited,flash,afterFlash])
        apply X86Routine.Prefix.step (middle := ⟨a7,none,0x2d951⟩) (by simp) (by rfl) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,
            a7,a6,a5,a4,a3,a2,a1,weapon,ammoType,ammoAddress,tableOffset,debited,flash,afterFlash])
        apply X86Routine.Prefix.step (middle := ⟨a8,none,0x2d953⟩) (by simp) (by rfl) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,
            a8,a7,a6,a5,a4,a3,a2,a1,weapon,ammoType,ammoAddress,tableOffset,debited,flash,afterFlash])
        apply X86Routine.Prefix.step (middle := ⟨a9,none,0x2d958⟩) (by simp) (by rfl) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,
            a9,a8,a7,a6,a5,a4,a3,a2,a1,weapon,ammoType,ammoAddress,tableOffset,debited,flash,afterFlash])
        apply X86Routine.Prefix.step (middle := ⟨a10,none,0x2d95f⟩) (by simp) (by rfl) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,
            a10,a9,a8,a7,a6,a5,a4,a3,a2,a1,weapon,ammoType,ammoAddress,tableOffset,debited,flash,afterFlash])
        apply X86Routine.Prefix.step (middle := ⟨a11,none,0x2d961⟩) (by simp) (by rfl) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,
            a11,a10,a9,a8,a7,a6,a5,a4,a3,a2,a1,weapon,ammoType,ammoAddress,tableOffset,debited,flash,afterFlash])
        apply X86Routine.Prefix.step (middle := ⟨a12,none,0x2d040⟩) (by simp) (by rfl) (by
          simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
            X86.execute,X86Block.Address.eval,put,write,X86Routine.pushWord,blockPreservesFlags,
            a12,a11,a10,a9,a8,a7,a6,a5,a4,a3,a2,a1,weapon,ammoType,ammoAddress,tableOffset,debited,flash,afterFlash])
        exact X86Routine.Prefix.nil _
      have eq : (⟨a12,none,0x2d040⟩ : X86Control.State) = flashCall .shotgun s := by
        simp [a12,a11,a10,a9,a8,a7,a6,a5,a4,a3,a2,a1,flashCall,put,X86Routine.pushWord,debited,write]
        funext r
        by_cases h0 : r=0 <;> by_cases h2 : r=2 <;> by_cases h3 : r=3 <;>
          by_cases h4 : r=4 <;> simp_all [write]
      rw [eq] at path
      exact path.finish (fuel := 0) (by rfl) 12 (by omega)
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem aim_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2d7c0] 2 ⟨s,f,afterFlash gun⟩ = some (aimCall gun s f) := by
  have run : X86Routine.run listed [0x2d7c0] 2 ⟨s,f,afterFlash gun⟩ = some (aimCall gun s f) := by
    cases gun <;> simp only [entry, afterSound, afterPose, afterFlash, afterAim, soundSteps] <;> simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,
      X86Block.execute,X86Memory.execute,put,write,aimCall,afterFlash,afterAim,
      X86Routine.pushWord,blockPreservesFlags]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

/-- Supported weapon numbers in the pinned executable's weaponinfo table. -/
def weaponNumber : Fire.Gun → Word | .pistol => 1 | .shotgun => 2
def playerAmmo (gun : Fire.Gun) (s : X86Memory.State) : Word :=
  s.regs 1+(BitVec.ofNat 32 gun.ammoIndex.val <<< 2)+156

/-- Relation at the return from P_SetMobjState. Callers must establish it after
sound and pose execution. Table/stack separation is explicit and byte-level. -/
structure Inputs (gun : Fire.Gun) (s : X86Memory.State) (c : Weapon.Context) : Prop where
  ready : weapon s = weaponNumber gun
  kind : load32 s.memory (tableOffset (weaponNumber gun)+0x12d90) = BitVec.ofNat 32 gun.ammoIndex.val
  flash : load32 s.memory (tableOffset (weaponNumber gun)+0x12da4) = BitVec.ofNat 32 (WeaponActions.flashFrame gun)
  ammo : load32 s.memory (playerAmmo gun s) = c.player.ammo[gun.ammoIndex].toBitVec
  readySafe : Apart (s.regs 1+112) (playerAmmo gun s)
  flashSafe : Apart (tableOffset (weaponNumber gun)+0x12da4) (playerAmmo gun s)
  stackSafe : Apart (playerAmmo gun s) (s.regs 4-4)

theorem related_address (gun : Fire.Gun) (s : X86Memory.State) (c : Weapon.Context)
    (h : Inputs gun s c) : ammoAddress s = playerAmmo gun s := by
  simp only [ammoAddress, ammoType, h.ready, h.kind, playerAmmo]

theorem related_flash (gun : Fire.Gun) (s : X86Memory.State) (c : Weapon.Context)
    (h : Inputs gun s c) : flash (debited s) = BitVec.ofNat 32 (WeaponActions.flashFrame gun) := by
  have ready : weapon (debited s) = weaponNumber gun := by
    change load32 (store32 s.memory (ammoAddress s) _) (s.regs 1+112) = _
    rw [related_address gun s c h, load_store_apart _ _ _ _ h.readySafe]
    exact h.ready
  unfold flash
  rw [ready]
  change load32 (store32 s.memory (ammoAddress s) _) (tableOffset (weaponNumber gun)+0x12da4) = _
  rw [related_address gun s c h, load_store_apart _ _ _ _ h.flashSafe]
  exact h.flash

/-- Correspondence to the production action, for every 32-bit ammo value.
The return-address write is included and cannot overlap the observed ammo. -/
theorem action_ammo (gun : Fire.Gun) (s : X86Memory.State) (c : Weapon.Context)
    (h : Inputs gun s c) :
    load32 (flashCall gun s).core.memory (playerAmmo gun s) =
      (Weapon.fireAction gun c).player.ammo[gun.ammoIndex].toBitVec := by
  rw [WeaponActions.action_ammo_bits]
  change load32 (store32 (store32 s.memory (ammoAddress s) (load32 s.memory (ammoAddress s)-1))
    (s.regs 4-4) (BitVec.ofNat 32 (afterFlash gun))) _ = _
  rw [load_store_apart _ _ _ _ h.stackSafe, related_address gun s c h, load_store, h.ammo]

theorem call_arguments (gun : Fire.Gun) (s : X86Memory.State) (c : Weapon.Context)
    (h : Inputs gun s c) :
    (flashCall gun s).core.regs 0 = s.regs 1 ∧
    (flashCall gun s).core.regs 2 = 1 ∧
    (flashCall gun s).core.regs 3 = BitVec.ofNat 32 (WeaponActions.flashFrame gun) ∧
    load32 (flashCall gun s).core.memory ((flashCall gun s).core.regs 4) =
      BitVec.ofNat 32 (afterFlash gun) := by
  simp [flashCall,X86Routine.pushWord,put,write,debited,load_store]
  exact related_flash gun s c h

/-- Any disjoint word is unchanged by this entire original instruction segment.
This covers other ammo and unrelated fields without pretending the stack write
or arbitrary pointer aliases do not exist. -/
theorem memory_frame (gun : Fire.Gun) (s : X86Memory.State) (a : Word)
    (debitSafe : Apart a (ammoAddress s)) (stackSafe : Apart a (s.regs 4-4)) :
    load32 (flashCall gun s).core.memory a = load32 s.memory a := by
  change load32 (store32 (store32 s.memory (ammoAddress s) (load32 s.memory (ammoAddress s)-1))
    (s.regs 4-4) (BitVec.ofNat 32 (afterFlash gun))) _ = _
  rw [load_store_apart _ _ _ _ stackSafe, load_store_apart _ _ _ _ debitSafe]

/-- Original-byte execution joined to the actual production tick. This is a
callee-to-callee segment, not an assumption that either callee corresponds. -/
theorem live_tick (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : Inputs gun s c)
    (frame : c.state.weapon.frame = WeaponActions.windup gun)
    (timer : c.state.weapon.tics = 1) :
    ∃ t, X86Routine.run program [0x2d040] 12 ⟨s,f,afterPose gun⟩ = some t ∧
      load32 t.core.memory (playerAmmo gun s) = (Weapon.tick c).player.ammo[gun.ammoIndex].toBitVec ∧
      t.core.regs 0 = s.regs 1 ∧ t.core.regs 2 = 1 ∧
      t.core.regs 3 = BitVec.ofNat 32 (Weapon.tick c).state.flash.frame ∧ t.pc = 0x2d040 := by
  refine ⟨flashCall gun s, debit_flash_execution gun s f, ?_, ?_, ?_, ?_, rfl⟩
  · rw [WeaponActions.tick_ammo gun c frame timer, action_ammo gun s c h,
      WeaponActions.action_ammo]
  · exact (call_arguments gun s c h).1
  · exact (call_arguments gun s c h).2.1
  · rw [(WeaponActions.tick_outputs gun c frame timer).2.2.2.1]
    exact (call_arguments gun s c h).2.2.1

end Doom.Proofs.OriginalWeaponDischarge
