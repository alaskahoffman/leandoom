import Doom.Proofs.OriginalDeathTiming
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.DeathReturn
open Verification X86 X86Memory X86Control BlockSummary

/-- Complete DOS dispatch/epilogue bytes, including the unexecuted monster branches. -/
def code : List UInt8 := [0x8b,0x43,0x58,0x83,0xf8,0x02,0x72,0x10,0x76,0x1a,0x83,0xf8,0x0a,0x72,0x35,0x76,0x1a,0x83,0xf8,0x17,0x74,0x07,0xeb,0x2c,0x83,0xf8,0x01,0x75,0x27,0xb9,0x3f,0,0,0,0xeb,0x0c,0xb9,0x4d,0,0,0,0xeb,0x05,0xb9,0x49,0,0,0,0x8b,0x53,0x10,0x8b,0x43,0x0c,0xbb,0,0,0,0x80,0xe8,0xf3,0x70,0,0,0x80,0x48,0x6a,0x02,0x5d,0x5f,0x5e,0x59,0x5b,0xc3]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2a40d ≤ pc ∧ pc < 0x2a457 then X86Routine.decodeAt bytes (pc-0x2a40d) else none
def program := bytesProgram code

def listed : X86Routine.Program
  | 0x2a40d => some (.control (.block (.legacy (.load 0 3 88))),3)
  | 0x2a410 => some (.compareRegister 0 2,3)
  | 0x2a413 => some (.jumpUnsigned 0 16,2)
  | 0x2a425 => some (.compareRegister 0 1,3)
  | 0x2a428 => some (.control (.jumpZero false 39),2)
  | 0x2a451 => some (.pop 5,1)
  | 0x2a452 => some (.pop 7,1)
  | 0x2a453 => some (.pop 6,1)
  | 0x2a454 => some (.pop 1,1)
  | 0x2a455 => some (.pop 3,1)
  | 0x2a456 => some (.ret,1)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

/-- This is the stack the original epilogue actually reads, with wrapping addresses. -/
def result (s : X86Memory.State) : X86Control.State :=
  ⟨⟨write (write (write (write (write (write (write s.regs 0 0)
    5 (load32 s.memory (s.regs 4))) 7 (load32 s.memory (s.regs 4+4)))
    6 (load32 s.memory (s.regs 4+8))) 1 (load32 s.memory (s.regs 4+12)))
    3 (load32 s.memory (s.regs 4+16))) 4 (s.regs 4+24),s.memory⟩,
    some (compare32 0 1),(load32 s.memory (s.regs 4+20)).toNat⟩

theorem execution (s : X86Memory.State) (f : Option Flags)
    (kind : load32 s.memory (s.regs 3+88)=0)
    (outside : (result s).pc < 0x2a40d ∨ 0x2a457 ≤ (result s).pc) :
    X86Routine.run listed [(result s).pc] 11 ⟨s,f,0x2a40d⟩=some (result s) := by
  have neq (pc : Nat) (lo : 0x2a40d ≤ pc) (hi : pc < 0x2a457) : pc ≠ (result s).pc := by omega
  have h0 := neq 0x2a40d (by decide) (by decide)
  have h1 := neq 0x2a410 (by decide) (by decide)
  have h2 := neq 0x2a413 (by decide) (by decide)
  have h3 := neq 0x2a425 (by decide) (by decide)
  have h4 := neq 0x2a428 (by decide) (by decide)
  have h5 := neq 0x2a451 (by decide) (by decide)
  have h6 := neq 0x2a452 (by decide) (by decide)
  have h7 := neq 0x2a453 (by decide) (by decide)
  have h8 := neq 0x2a454 (by decide) (by decide)
  have h9 := neq 0x2a455 (by decide) (by decide)
  have h10 := neq 0x2a456 (by decide) (by decide)
  simp [result] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 kind
  simp [X86Routine.run,listed,X86Routine.execute,X86Control.execute,X86Block.execute,
    X86Memory.execute,X86.execute,put,write,blockPreservesFlags,compare32,kind,result,
    h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,BitVec.add_assoc]
  funext r
  by_cases r0 : r=0 <;> by_cases r1 : r=1 <;> by_cases r3 : r=3 <;>
    by_cases r4 : r=4 <;> by_cases r5 : r=5 <;> by_cases r6 : r=6 <;>
    by_cases r7 : r=7 <;> simp_all [write]

theorem original_execution (s : X86Memory.State) (f : Option Flags)
    (kind : load32 s.memory (s.regs 3+88)=0)
    (outside : (result s).pc < 0x2a40d ∨ 0x2a457 ≤ (result s).pc) :
    X86Routine.run program [(result s).pc] 11 ⟨s,f,0x2a40d⟩=some (result s) := by
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [execution s f kind outside]; simp)]
  exact execution s f kind outside

theorem memory_unchanged (s : X86Memory.State) : (result s).core.memory=s.memory := rfl

theorem live_no_drop (body : Death.Body) (world : Death.World) (kind : body.kind=0) :
    Death.dropItem body world=(body,world) := by
  simp [Death.dropItem,kind]

end Doom.Proofs.DeathReturn
