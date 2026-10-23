import Doom.Proofs.E1M1PspriteLoop
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.PspriteSetter
open Verification X86 X86Memory X86Control BlockSummary

/-- Reuse the setter bytes already pinned for the weapon-lowering proof. -/
def code := WeaponDrop.setterCode
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2d040 ≤ pc ∧ pc < 0x2d0af then X86Routine.decodeAt bytes (pc-0x2d040) else none
def program := bytesProgram code

def listed : X86Routine.Program
  | 0x2d040 => some (.push 1,1)
  | 0x2d041 => some (.push 6,1)
  | 0x2d042 => some (.control (.block (.legacy (.mov 6 0))),2)
  | 0x2d044 => some (.control (.block (.legacy (.mov 0 3))),2)
  | 0x2d046 => some (.control (.block (.legacy (.shl 2 4))),3)
  | 0x2d049 => some (.control (.block (.lea 3 ⟨some 6,none,0,244⟩)),6)
  | 0x2d04f => some (.control (.block (.arithmetic (.add 3 2))),2)
  | 0x2d051 => some (.control (.testWord 0 0),2)
  | 0x2d053 => some (.control (.jumpZero false 9),2)
  | 0x2d055 => some (.storeImmediate ⟨some 3,none,0,0⟩ 0,6)
  | 0x2d05b => some (.pop 6,1)
  | 0x2d05c => some (.pop 1,1)
  | 0x2d05d => some (.ret,1)
  | 0x2d05e => some (.multiplyImmediate 0 0 28,3)
  | 0x2d061 => some (.immediate 1 0x15a28,5)
  | 0x2d066 => some (.control (.block (.arithmetic (.add 1 0))),2)
  | 0x2d068 => some (.control (.block (.store ⟨some 3,none,0,0⟩ 1)),2)
  | 0x2d06a => some (.control (.block (.legacy (.load 0 1 8))),3)
  | 0x2d06d => some (.control (.block (.store ⟨some 3,none,0,4⟩ 0)),3)
  | 0x2d070 => some (.control (.block (.legacy (.load 2 1 20))),3)
  | 0x2d073 => some (.control (.testWord 2 2),2)
  | 0x2d075 => some (.control (.jumpZero true 17),2)
  | 0x2d077 => some (.control (.block (.legacy (.mov 0 2))),2)
  | 0x2d079 => some (.control (.block (.legacy (.shl 0 16))),3)
  | 0x2d07c => some (.control (.block (.store ⟨some 3,none,0,8⟩ 0)),3)
  | 0x2d07f => some (.control (.block (.legacy (.load 0 1 24))),3)
  | 0x2d082 => some (.control (.block (.legacy (.shl 0 16))),3)
  | 0x2d085 => some (.control (.block (.store ⟨some 3,none,0,12⟩ 0)),3)
  | 0x2d088 => some (.control (.cmpImmediate ⟨some 1,none,0,12⟩ 0),4)
  | 0x2d08c => some (.control (.jumpZero true 12),2)
  | 0x2d08e => some (.control (.block (.legacy (.mov 0 6))),2)
  | 0x2d090 => some (.control (.block (.legacy (.mov 2 3))),2)
  | 0x2d092 => some (.callMemory ⟨some 1,none,0,12⟩,3)
  | 0x2d095 => some (.control (.cmpImmediate ⟨some 3,none,0,0⟩ 0),3)
  | 0x2d098 => some (.control (.jumpZero true 18),2)
  | 0x2d09a => some (.control (.block (.legacy (.load 0 3 0))),2)
  | 0x2d09c => some (.control (.block (.legacy (.load 2 3 4))),3)
  | 0x2d09f => some (.control (.block (.legacy (.load 0 0 16))),3)
  | 0x2d0a2 => some (.control (.testWord 2 2),2)
  | 0x2d0a4 => some (.control (.jumpZero false 6),2)
  | 0x2d0a6 => some (.control (.testWord 0 0),2)
  | 0x2d0a8 => some (.control (.jumpZero true (-85)),2)
  | 0x2d0aa => some (.jump (-78),2)
  | 0x2d0ac => some (.pop 6,1)
  | 0x2d0ad => some (.pop 1,1)
  | 0x2d0ae => some (.ret,1)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def store (s : X86Memory.State) (a v : Word) : X86Memory.State :=
  {s with memory := store32 s.memory a v}
def prepared (s : X86Memory.State) : X86Memory.State :=
  let saved := X86Routine.pushWord (X86Routine.pushWord s (s.regs 1)) (s.regs 6)
  put (put (put (put saved 6 (s.regs 0)) 0 (s.regs 3)) 2 (s.regs 2 <<< 4))
    3 (s.regs 0+244+(s.regs 2 <<< 4))
def entered (s : X86Memory.State) : X86Control.State :=
  ⟨prepared s,some (logical32 (s.regs 3)),if s.regs 3=0 then 0x2d055 else 0x2d05e⟩

private theorem prepare_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix listed [0x2d055,0x2d05e] 7 ⟨s,f,0x2d040⟩ ⟨prepared s,none,0x2d051⟩ := by
  let c1 := X86Routine.pushWord s (s.regs 1)
  let c2 := X86Routine.pushWord c1 (c1.regs 6)
  let c3 := put c2 6 (c2.regs 0)
  let c4 := put c3 0 (c3.regs 3)
  let c5 := put c4 2 (c4.regs 2 <<< 4)
  let c6 := put c5 3 (c5.regs 6+244)
  let c7 := put c6 3 (c6.regs 3+c6.regs 2)
  apply X86Routine.Prefix.step (middle := ⟨c1,f,0x2d041⟩) (by simp) rfl (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
      X86Block.Address.eval,blockPreservesFlags,prepared,X86Routine.pushWord,put,write,c1])
  apply X86Routine.Prefix.step (middle := ⟨c2,f,0x2d042⟩) (by simp) rfl (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
      X86Block.Address.eval,blockPreservesFlags,prepared,X86Routine.pushWord,put,write,c2,c1])
  apply X86Routine.Prefix.step (middle := ⟨c3,f,0x2d044⟩) (by simp) rfl (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
      X86Block.Address.eval,blockPreservesFlags,prepared,X86Routine.pushWord,put,write,c3,c2,c1])
  apply X86Routine.Prefix.step (middle := ⟨c4,f,0x2d046⟩) (by simp) rfl (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
      X86Block.Address.eval,blockPreservesFlags,prepared,X86Routine.pushWord,put,write,c4,c3,c2,c1])
  apply X86Routine.Prefix.step (middle := ⟨c5,none,0x2d049⟩) (by simp) rfl (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
      X86Block.Address.eval,blockPreservesFlags,prepared,X86Routine.pushWord,put,write,c5,c4,c3,c2,c1])
  apply X86Routine.Prefix.step (middle := ⟨c6,none,0x2d04f⟩) (by simp) rfl (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
      X86Block.Address.eval,blockPreservesFlags,prepared,X86Routine.pushWord,put,write,c6,c5,c4,c3,c2,c1])
  apply X86Routine.Prefix.step (middle := ⟨prepared s,none,0x2d051⟩) (by simp) rfl (by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
      X86Block.Address.eval,blockPreservesFlags,prepared,X86Routine.pushWord,put,write,c7,c6,c5,c4,c3,c2,c1]
    funext r; by_cases h : r=3 <;> simp_all [write])
  exact X86Routine.Prefix.nil _

theorem entry_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2d055,0x2d05e] 9 ⟨s,f,0x2d040⟩=some (entered s) := by
  have tail : X86Routine.run listed [0x2d055,0x2d05e] 2 ⟨prepared s,none,0x2d051⟩=some (entered s) := by
    by_cases h : s.regs 3=(0#32) <;>
    simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,entered,prepared,
      logical32,X86Routine.pushWord,put,write,h]
  have run := (prepare_execution s f).finish tail 9 (by decide)
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

/-- Reads the actual saved registers and return word, even for aliased memory. -/
def returned (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  let t := PspriteLoop.popped (PspriteLoop.popped s 6) 1
  ⟨put t 4 (t.regs 4+4),f,(load32 t.memory (t.regs 4)).toNat⟩

theorem return_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 3 ⟨s,f,0x2d0ac⟩ (returned s f) := by
  have path : X86Routine.Prefix listed [] 3 ⟨s,f,0x2d0ac⟩ (returned s f) := by
    apply X86Routine.Prefix.step (middle := ⟨PspriteLoop.popped s 6,f,0x2d0ad⟩) (by simp) rfl rfl
    apply X86Routine.Prefix.step (middle := ⟨PspriteLoop.popped (PspriteLoop.popped s 6) 1,f,0x2d0ae⟩) (by simp) rfl rfl
    apply X86Routine.Prefix.step (middle := returned s f) (by simp) rfl rfl
    exact X86Routine.Prefix.nil _
  exact path.transfer program [] decoded (by simp)

def cleared (s : X86Memory.State) := store s (s.regs 3) 0

theorem clear_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 4 ⟨s,f,0x2d055⟩ (returned (cleared s) f) := by
  have path : X86Routine.Prefix listed [] 4 ⟨s,f,0x2d055⟩ (returned (cleared s) f) := by
    apply X86Routine.Prefix.step (middle := ⟨cleared s,f,0x2d05b⟩) (by simp) rfl (by
      simp [X86Routine.execute,X86Block.Address.eval,cleared,store])
    apply X86Routine.Prefix.step (middle := ⟨PspriteLoop.popped (cleared s) 6,f,0x2d05c⟩) (by simp) rfl rfl
    apply X86Routine.Prefix.step (middle := ⟨PspriteLoop.popped (PspriteLoop.popped (cleared s) 6) 1,f,0x2d05d⟩) (by simp) rfl rfl
    apply X86Routine.Prefix.step (middle := returned (cleared s) f) (by simp) rfl rfl
    exact X86Routine.Prefix.nil _
  exact path.transfer program [] decoded (by simp)


def installed (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  let c1 := put s 0 (s.regs 0*28)
  let c2 := put c1 1 0x15a28
  let c3 := put c2 1 (c2.regs 1+c2.regs 0)
  let c4 := store c3 (c3.regs 3) (c3.regs 1)
  let c5 := put c4 0 (load32 c4.memory (c4.regs 1+8))
  let c6 := store c5 (c5.regs 3+4) (c5.regs 0)
  let c7 := put c6 2 (load32 c6.memory (c6.regs 1+20))
  ⟨c7,none,0x2d073⟩

theorem installed_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 7 ⟨s,f,0x2d05e⟩ (installed s f) := by
  let c1 := put s 0 (s.regs 0*28)
  let c2 := put c1 1 0x15a28
  let c3 := put c2 1 (c2.regs 1+c2.regs 0)
  let c4 := store c3 (c3.regs 3) (c3.regs 1)
  let c5 := put c4 0 (load32 c4.memory (c4.regs 1+8))
  let c6 := store c5 (c5.regs 3+4) (c5.regs 0)
  let c7 := put c6 2 (load32 c6.memory (c6.regs 1+20))
  have path : X86Routine.Prefix listed [] 7 ⟨s,f,0x2d05e⟩ (installed s f) := by
    apply X86Routine.Prefix.step (middle := ⟨c1,none,0x2d061⟩) (by simp) rfl (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,installed,c1,store,put,write,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨c2,none,0x2d066⟩) (by simp) rfl (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,installed,c2,c1,store,put,write,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨c3,none,0x2d068⟩) (by simp) rfl (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,installed,c3,c2,c1,store,put,write,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨c4,none,0x2d06a⟩) (by simp) rfl (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,installed,c4,c3,c2,c1,store,put,write,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨c5,none,0x2d06d⟩) (by simp) rfl (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,installed,c5,c4,c3,c2,c1,store,put,write,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨c6,none,0x2d070⟩) (by simp) rfl (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,installed,c6,c5,c4,c3,c2,c1,store,put,write,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := installed s f) (by simp) rfl (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,installed,c7,c6,c5,c4,c3,c2,c1,store,put,write,X86Routine.pushWord])
    exact X86Routine.Prefix.nil _
  exact path.transfer program [] decoded (by simp)

def coordinates (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  let c1 := put s 0 (s.regs 2)
  let c2 := put c1 0 (c1.regs 0 <<< 16)
  let c3 := store c2 (c2.regs 3+8) (c2.regs 0)
  let c4 := put c3 0 (load32 c3.memory (c3.regs 1+24))
  let c5 := put c4 0 (c4.regs 0 <<< 16)
  let c6 := store c5 (c5.regs 3+12) (c5.regs 0)
  ⟨c6,none,0x2d088⟩

theorem coordinates_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 6 ⟨s,f,0x2d077⟩ (coordinates s f) := by
  let c1 := put s 0 (s.regs 2)
  let c2 := put c1 0 (c1.regs 0 <<< 16)
  let c3 := store c2 (c2.regs 3+8) (c2.regs 0)
  let c4 := put c3 0 (load32 c3.memory (c3.regs 1+24))
  let c5 := put c4 0 (c4.regs 0 <<< 16)
  let c6 := store c5 (c5.regs 3+12) (c5.regs 0)
  have path : X86Routine.Prefix listed [] 6 ⟨s,f,0x2d077⟩ (coordinates s f) := by
    apply X86Routine.Prefix.step (middle := ⟨c1,f,0x2d079⟩) (by simp) rfl (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,coordinates,c1,store,put,write,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨c2,none,0x2d07c⟩) (by simp) rfl (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,coordinates,c2,c1,store,put,write,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨c3,none,0x2d07f⟩) (by simp) rfl (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,coordinates,c3,c2,c1,store,put,write,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨c4,none,0x2d082⟩) (by simp) rfl (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,coordinates,c4,c3,c2,c1,store,put,write,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨c5,none,0x2d085⟩) (by simp) rfl (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,coordinates,c5,c4,c3,c2,c1,store,put,write,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := coordinates s f) (by simp) rfl (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,coordinates,c6,c5,c4,c3,c2,c1,store,put,write,X86Routine.pushWord])
    exact X86Routine.Prefix.nil _
  exact path.transfer program [] decoded (by simp)

def called (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  let c1 := put s 0 (s.regs 6)
  let c2 := put c1 2 (c1.regs 3)
  let c3 := X86Routine.pushWord c2 0x2d095
  ⟨c3,f,(load32 s.memory (s.regs 1+12)).toNat⟩

theorem called_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 3 ⟨s,f,0x2d08e⟩ (called s f) := by
  let c1 := put s 0 (s.regs 6)
  let c2 := put c1 2 (c1.regs 3)
  let c3 := X86Routine.pushWord c2 0x2d095
  have path : X86Routine.Prefix listed [] 3 ⟨s,f,0x2d08e⟩ (called s f) := by
    apply X86Routine.Prefix.step (middle := ⟨c1,f,0x2d090⟩) (by simp) rfl (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,called,c1,store,put,write,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨c2,f,0x2d092⟩) (by simp) rfl (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,called,c2,c1,store,put,write,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := called s f) (by simp) rfl (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,called,c3,c2,c1,store,put,write,X86Routine.pushWord])
    exact X86Routine.Prefix.nil _
  exact path.transfer program [] decoded (by simp)

def successor (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  let c1 := put s 0 (load32 s.memory (s.regs 3))
  let c2 := put c1 2 (load32 c1.memory (c1.regs 3+4))
  let c3 := put c2 0 (load32 c2.memory (c2.regs 0+16))
  ⟨c3,f,0x2d0a2⟩

theorem successor_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 3 ⟨s,f,0x2d09a⟩ (successor s f) := by
  let c1 := put s 0 (load32 s.memory (s.regs 3))
  let c2 := put c1 2 (load32 c1.memory (c1.regs 3+4))
  let c3 := put c2 0 (load32 c2.memory (c2.regs 0+16))
  have path : X86Routine.Prefix listed [] 3 ⟨s,f,0x2d09a⟩ (successor s f) := by
    apply X86Routine.Prefix.step (middle := ⟨c1,f,0x2d09c⟩) (by simp) rfl (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,successor,c1,store,put,write,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨c2,f,0x2d09f⟩) (by simp) rfl (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,successor,c2,c1,store,put,write,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := successor s f) (by simp) rfl (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
        X86Block.Address.eval,blockPreservesFlags,successor,c3,c2,c1,store,put,write,X86Routine.pushWord])
    exact X86Routine.Prefix.nil _
  exact path.transfer program [] decoded (by simp)


def coordinateGate (s : X86Memory.State) : X86Control.State :=
  ⟨s,some (logical32 (s.regs 2)),if s.regs 2=0 then 0x2d088 else 0x2d077⟩

theorem coordinateGate_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2d088,0x2d077] 2 ⟨s,f,0x2d073⟩=some (coordinateGate s) := by
  have run : X86Routine.run listed [0x2d088,0x2d077] 2 ⟨s,f,0x2d073⟩=some (coordinateGate s) := by
    by_cases h : s.regs 2=(0#32) <;>
    simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,X86Block.Address.eval,
      coordinateGate,logical32,WeaponSelect.compare_zero,h]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

def actionGate (s : X86Memory.State) : X86Control.State :=
  ⟨s,some (compare32 (load32 s.memory (s.regs 1+12)) 0),if load32 s.memory (s.regs 1+12)=0 then 0x2d09a else 0x2d08e⟩

theorem actionGate_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2d09a,0x2d08e] 2 ⟨s,f,0x2d088⟩=some (actionGate s) := by
  have run : X86Routine.run listed [0x2d09a,0x2d08e] 2 ⟨s,f,0x2d088⟩=some (actionGate s) := by
    by_cases h : load32 s.memory (s.regs 1+(12#32))=(0#32) <;>
    simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,X86Block.Address.eval,
      actionGate,logical32,WeaponSelect.compare_zero,h]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

def afterAction (s : X86Memory.State) : X86Control.State :=
  ⟨s,some (compare32 (load32 s.memory (s.regs 3)) 0),if load32 s.memory (s.regs 3)=0 then 0x2d0ac else 0x2d09a⟩

theorem afterAction_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2d0ac,0x2d09a] 2 ⟨s,f,0x2d095⟩=some (afterAction s) := by
  have run : X86Routine.run listed [0x2d0ac,0x2d09a] 2 ⟨s,f,0x2d095⟩=some (afterAction s) := by
    by_cases h : load32 s.memory (s.regs 3)=(0#32) <;>
    simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,X86Block.Address.eval,
      afterAction,logical32,WeaponSelect.compare_zero,h]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

/-- Zero-tic states continue immediately, including S_NULL removal. The next
state was read from the current psprite state after any action, not a cached entry. -/
def next (s : X86Memory.State) : X86Control.State :=
  if s.regs 2≠0 then ⟨s,some (logical32 (s.regs 2)),0x2d0ac⟩
  else ⟨s,some (logical32 (s.regs 0)),if s.regs 0=0 then 0x2d055 else 0x2d05e⟩

theorem next_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2d0ac,0x2d055,0x2d05e] 5 ⟨s,f,0x2d0a2⟩=some (next s) := by
  have run : X86Routine.run listed [0x2d0ac,0x2d055,0x2d05e] 5 ⟨s,f,0x2d0a2⟩=some (next s) := by
    by_cases t : s.regs 2=(0#32) <;> by_cases n : s.regs 0=(0#32) <;>
    simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,next,logical32,t,n]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]


/-- The target is read before pushing, and both action arguments and the actual
return word are supplied. This also covers an operand aliasing the stack write. -/
theorem call_contract (s : X86Memory.State) (f : Option Flags) :
    (called s f).pc=(load32 s.memory (s.regs 1+12)).toNat ∧
    (called s f).core.regs 0=s.regs 6 ∧ (called s f).core.regs 2=s.regs 3 ∧
    (called s f).core.regs 4=s.regs 4-4 ∧
    load32 (called s f).core.memory (s.regs 4-4)=0x2d095 := by
  simp [called,X86Routine.pushWord,put,write,load_store]

theorem return_contract (s : X86Memory.State) (f : Option Flags) :
    (returned s f).pc=(load32 s.memory (s.regs 4+8)).toNat ∧
    (returned s f).core.regs 4=s.regs 4+12 ∧
    (returned s f).core.memory=s.memory ∧ (returned s f).flags=f := by
  simp [returned,PspriteLoop.popped,put,write,BitVec.add_assoc]

end Doom.Proofs.PspriteSetter
