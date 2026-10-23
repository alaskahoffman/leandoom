import Doom.Proofs.OriginalWeaponSelect
import Doom.UseButton
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.UseButtonCode
open Verification X86 X86Memory X86Control BlockSummary

def code : List UInt8 := [0xf6,0x43,0x7,0x2,0x74,0x1c,0x83,0xba,0xc0,0x0,0x0,0x0,0x0,0x75,0x1d,0x89,0xd0,0xe8,0x84,0x88,0xff,0xff,0xc7,0x82,0xc0,0x0,0x0,0x0,0x1,0x0,0x0,0x0,0xeb,0xa,0xc7,0x82,0xc0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x89,0xd0,0xe8,0xb7,0xa7,0xff,0xff]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x33476 ≤ pc ∧ pc < 0x334a9 then X86Routine.decodeAt bytes (pc-0x33476) else none
def program := bytesProgram code
def exits := [0x2bd10,0x2dc60]
def listed : X86Routine.Program
  | 0x33476 => some (.testMemoryByte ⟨some 3,none,0,7⟩ 2,4)
  | 0x3347a => some (.control (.jumpZero true 28),2)
  | 0x3347c => some (.control (.cmpImmediate ⟨some 2,none,0,192⟩ 0),7)
  | 0x33483 => some (.control (.jumpZero false 29),2)
  | 0x33485 => some (.control (.block (.legacy (.mov 0 2))),2)
  | 0x33487 => some (.call (-30588),5)
  | 0x3348c => some (.storeImmediate ⟨some 2,none,0,192⟩ 1,10)
  | 0x33496 => some (.jump 10,2)
  | 0x33498 => some (.storeImmediate ⟨some 2,none,0,192⟩ 0,10)
  | 0x334a2 => some (.control (.block (.legacy (.mov 0 2))),2)
  | 0x334a4 => some (.call (-22601),5)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def pressed (s : X86Memory.State) : Bool := s.memory (s.regs 3+7) &&& (2#8) != (0#8)
def held (s : X86Memory.State) : Word := load32 s.memory (s.regs 2+192)
def requested (s : X86Memory.State) : Bool := UseButton.request (held s != 0) (pressed s)
def beforeCall (s : X86Memory.State) : X86Memory.State :=
  put (if pressed s then s else {s with memory := store32 s.memory (s.regs 2+192) 0}) 0 (s.regs 2)
def result (s : X86Memory.State) : X86Control.State :=
  ⟨X86Routine.pushWord (beforeCall s) (if requested s then 0x3348c else 0x334a9),
    some (if pressed s then compare32 (held s) 0 else logical8 0),
    if requested s then 0x2bd10 else 0x2dc60⟩

/-- All three gate paths include the actual CALL and its return-address store.
Fresh use stops at P_UseLines entry; its geometry/actions are not assumed proved. -/
theorem execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program exits 6 ⟨s,f,0x33476⟩=some (result s) := by
  have run : X86Routine.run listed exits 6 ⟨s,f,0x33476⟩=some (result s) := by
    by_cases button : s.memory (s.regs 3+(7#32)) &&& (2#8)=(0#8) <;>
    by_cases down : load32 s.memory (s.regs 2+(192#32))=(0#32) <;>
    simp [X86Routine.run,listed,exits,X86Routine.execute,X86Control.execute,X86Block.execute,
      X86Memory.execute,X86Block.Address.eval,X86.execute,blockPreservesFlags,
      WeaponSelect.compare_zero,result,beforeCall,requested,pressed,held,UseButton.request,
      put,write,X86Routine.pushWord,button,down,logical8,BitVec.msb_eq_getLsbD_last]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

/-- The post-use continuation commits usedown before calling P_MovePsprites.
The incoming state must be the actual callee return; this does not model the callee. -/
def resumed (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨X86Routine.pushWord (put {s with memory := store32 s.memory (s.regs 2+192) 1} 0 (s.regs 2)) 0x334a9,f,0x2dc60⟩

theorem resume_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2dc60] 4 ⟨s,f,0x3348c⟩=some (resumed s f) := by
  have run : X86Routine.run listed [0x2dc60] 4 ⟨s,f,0x3348c⟩=some (resumed s f) := by
    simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,X86Block.execute,
      X86Memory.execute,X86Block.Address.eval,X86.execute,blockPreservesFlags,resumed,put,write,X86Routine.pushWord]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem call_argument (s : X86Memory.State) :
    (result s).core.regs 0=s.regs 2 ∧ (result s).core.regs 4=s.regs 4-4 := by
  simp [result,beforeCall,X86Routine.pushWord,put,write]; split <;> rfl

theorem saved_return (s : X86Memory.State) :
    load32 (result s).core.memory ((result s).core.regs 4)=
      if requested s then 0x3348c else 0x334a9 := by
  simp [result,X86Routine.pushWord,write,load_store]

end Doom.Proofs.UseButtonCode
