import Doom.Proofs.OriginalPathYStep
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalPathCell
open Verification X86 X86Memory X86Control BlockSummary
def code : List UInt8 := [0xf6,0x44,0x24,0x40,0x1,0x74,0x16,0xbb,0xf0,0xc5,0x2,0x0,0x89,0xf0,0x89,0xca,0xe8,0x8c,0xfa,0xff,0xff,0x85,0xc0,0xf,0x84,0x6f,0x0,0x0,0x0,0xf6,0x44,0x24,0x40,0x2,0x74,0x12,0xbb,0x20,0xc7,0x2,0x0,0x89,0xf0,0x89,0xca,0xe8,0xef,0xfa,0xff,0xff,0x85,0xc0,0x74,0x56]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2ca7f≤pc ∧ pc<0x2cab5 then X86Routine.decodeAt bytes (pc-0x2ca7f) else none
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x2ca7f => some (.testMemoryByte ⟨some 4,none,0,64⟩ 1,5)
  | 0x2ca84 => some (.control (.jumpZero true 22),2)
  | 0x2ca86 => some (.immediate 3 0x2c5f0,5)
  | 0x2ca8b => some (.control (.block (.legacy (.mov 0 6))),2)
  | 0x2ca8d => some (.control (.block (.legacy (.mov 2 1))),2)
  | 0x2ca8f => some (.call (-1396),5)
  | 0x2ca94 => some (.control (.testWord 0 0),2)
  | 0x2ca96 => some (.control (.jumpZero true 111),6)
  | 0x2ca9c => some (.testMemoryByte ⟨some 4,none,0,64⟩ 2,5)
  | 0x2caa1 => some (.control (.jumpZero true 18),2)
  | 0x2caa3 => some (.immediate 3 0x2c720,5)
  | 0x2caa8 => some (.control (.block (.legacy (.mov 0 6))),2)
  | 0x2caaa => some (.control (.block (.legacy (.mov 2 1))),2)
  | 0x2caac => some (.call (-1297),5)
  | 0x2cab1 => some (.control (.testWord 0 0),2)
  | 0x2cab3 => some (.control (.jumpZero true 86),2)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def gatePc (line : Bool) : Nat := if line then 0x2ca7f else 0x2ca9c
def callPc (line : Bool) : Nat := if line then 0x2ca86 else 0x2caa3
def skipPc (line : Bool) : Nat := if line then 0x2ca9c else 0x2cab5
def returnPc (line : Bool) : Nat := if line then 0x2ca94 else 0x2cab1
def callee (line : Bool) : Nat := if line then 0x2c520 else 0x2c5a0
def callback (line : Bool) : Word := if line then 0x2c5f0 else 0x2c720
def mask (line : Bool) : BitVec 8 := if line then 1 else 2
def optionBits (line : Bool) (s : X86Memory.State) := s.memory (s.regs 4+64) &&& mask line
def enabled (line : Bool) (s : X86Memory.State) : Bool := optionBits line s != 0
def gateFlags (line : Bool) (s : X86Memory.State) := some (logical8 (optionBits line s))
def gate (line : Bool) (s : X86Memory.State) : X86Control.State :=
  ⟨s,gateFlags line s,if enabled line s then callPc line else skipPc line⟩

theorem gate_execution (line : Bool) (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 2 ⟨s,f,gatePc line⟩ (gate line s) := by
  have path : X86Routine.Prefix listed [] 2 ⟨s,f,gatePc line⟩ (gate line s) := by
    cases line
    · apply X86Routine.Prefix.step (middle := ⟨s,gateFlags false s,0x2caa1⟩) (by simp) (by rfl) (by simp [gatePc,gate,gateFlags,optionBits,enabled,mask,callPc,skipPc,X86Routine.execute,X86Control.execute,X86Block.Address.eval,logical8])
      apply X86Routine.Prefix.step (middle := gate false s) (by simp) (by rfl) (by
        by_cases h : optionBits false s=0 <;> simp_all [gatePc,gate,gateFlags,optionBits,enabled,mask,callPc,skipPc,X86Routine.execute,X86Control.execute,X86Block.Address.eval,logical8])
      exact .nil _
    · apply X86Routine.Prefix.step (middle := ⟨s,gateFlags true s,0x2ca84⟩) (by simp) (by rfl) (by simp [gatePc,gate,gateFlags,optionBits,enabled,mask,callPc,skipPc,X86Routine.execute,X86Control.execute,X86Block.Address.eval,logical8])
      apply X86Routine.Prefix.step (middle := gate true s) (by simp) (by rfl) (by
        by_cases h : optionBits true s=0 <;> simp_all [gatePc,gate,gateFlags,optionBits,enabled,mask,callPc,skipPc,X86Routine.execute,X86Control.execute,X86Block.Address.eval,logical8])
      exact .nil _
  exact path.transfer program [] decoded (by simp)

def c1 (line : Bool) (s : X86Memory.State) := put s 3 (callback line)
def c2 (line : Bool) (s : X86Memory.State) := put (c1 line s) 0 (s.regs 6)
def c3 (line : Bool) (s : X86Memory.State) := put (c2 line s) 2 (s.regs 1)
def called (line : Bool) (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨X86Routine.pushWord (c3 line s) (BitVec.ofNat 32 (returnPc line)),f,callee line⟩

theorem call_execution (line : Bool) (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 4 ⟨s,f,callPc line⟩ (called line s f) := by
  have path : X86Routine.Prefix listed [] 4 ⟨s,f,callPc line⟩ (called line s f) := by
    cases line
    · apply X86Routine.Prefix.step (middle := ⟨c1 false s,f,0x2caa8⟩) (by simp) (by rfl) (by simp [callPc,called,returnPc,callee,callback,c3,c2,c1,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,X86Routine.pushWord,put,write,blockPreservesFlags])
      apply X86Routine.Prefix.step (middle := ⟨c2 false s,f,0x2caaa⟩) (by simp) (by rfl) (by simp [callPc,called,returnPc,callee,callback,c3,c2,c1,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,X86Routine.pushWord,put,write,blockPreservesFlags])
      apply X86Routine.Prefix.step (middle := ⟨c3 false s,f,0x2caac⟩) (by simp) (by rfl) (by simp [callPc,called,returnPc,callee,callback,c3,c2,c1,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,X86Routine.pushWord,put,write,blockPreservesFlags])
      apply X86Routine.Prefix.step (middle := called false s f) (by simp) (by rfl) (by simp [callPc,called,returnPc,callee,callback,c3,c2,c1,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,X86Routine.pushWord,put,write,blockPreservesFlags])
      exact .nil _
    · apply X86Routine.Prefix.step (middle := ⟨c1 true s,f,0x2ca8b⟩) (by simp) (by rfl) (by simp [callPc,called,returnPc,callee,callback,c3,c2,c1,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,X86Routine.pushWord,put,write,blockPreservesFlags])
      apply X86Routine.Prefix.step (middle := ⟨c2 true s,f,0x2ca8d⟩) (by simp) (by rfl) (by simp [callPc,called,returnPc,callee,callback,c3,c2,c1,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,X86Routine.pushWord,put,write,blockPreservesFlags])
      apply X86Routine.Prefix.step (middle := ⟨c3 true s,f,0x2ca8f⟩) (by simp) (by rfl) (by simp [callPc,called,returnPc,callee,callback,c3,c2,c1,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,X86Routine.pushWord,put,write,blockPreservesFlags])
      apply X86Routine.Prefix.step (middle := called true s f) (by simp) (by rfl) (by simp [callPc,called,returnPc,callee,callback,c3,c2,c1,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,X86Routine.pushWord,put,write,blockPreservesFlags])
      exact .nil _
  exact path.transfer program [] decoded (by simp)

def enter (line : Bool) (s : X86Memory.State) : X86Control.State :=
  if enabled line s then called line s (gateFlags line s) else gate line s

theorem enter_execution (line : Bool) (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤6 ∧ X86Routine.Prefix program [] n ⟨s,f,gatePc line⟩ (enter line s) := by
  have a := gate_execution line s f
  by_cases h : enabled line s=true
  · have b := call_execution line s (gateFlags line s)
    have eq : (⟨s,gateFlags line s,callPc line⟩ : X86Control.State)=gate line s := by simp [gate,h]
    rw [eq] at b
    exact ⟨6,by omega,by simpa only [enter,if_pos h] using OriginalGroupBounds.prefix_join a b⟩
  · exact ⟨2,by omega,by simpa only [enter,if_neg h] using a⟩

/-- The real return-site test; false aborts before any later visitor can run. -/
def resumed (line : Bool) (s : X86Memory.State) : X86Control.State :=
  ⟨s,some (logical32 (s.regs 0)),if s.regs 0=0 then 0x2cb0b else skipPc line⟩
theorem resume_execution (line : Bool) (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 2 ⟨s,f,returnPc line⟩ (resumed line s) := by
  have path : X86Routine.Prefix listed [] 2 ⟨s,f,returnPc line⟩ (resumed line s) := by
    cases line
    · apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x2cab3⟩) (by simp) (by rfl) (by simp [returnPc,skipPc,resumed,X86Routine.execute,X86Control.execute,logical32])
      apply X86Routine.Prefix.step (middle := resumed false s) (by simp) (by rfl) (by
        by_cases h : s.regs 0=0 <;> simp_all [returnPc,skipPc,resumed,X86Routine.execute,X86Control.execute,logical32])
      exact .nil _
    · apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x2ca96⟩) (by simp) (by rfl) (by simp [returnPc,skipPc,resumed,X86Routine.execute,X86Control.execute,logical32])
      apply X86Routine.Prefix.step (middle := resumed true s) (by simp) (by rfl) (by
        by_cases h : s.regs 0=0 <;> simp_all [returnPc,skipPc,resumed,X86Routine.execute,X86Control.execute,logical32])
      exact .nil _
  exact path.transfer program [] decoded (by simp)

/-- Coordinates, callback and real return word delivered to either iterator. -/
theorem call_inputs (line : Bool) (s : X86Memory.State) (f : Option Flags) :
    (called line s f).core.regs 0=s.regs 6 ∧ (called line s f).core.regs 2=s.regs 1 ∧
    (called line s f).core.regs 3=callback line ∧ (called line s f).core.regs 4=s.regs 4-4 ∧
    load32 (called line s f).core.memory (s.regs 4-4)=BitVec.ofNat 32 (returnPc line) ∧
    (called line s f).pc=callee line := by
  simp [called,c3,c2,c1,X86Routine.pushWord,put,write,load_store]

theorem call_frame (line : Bool) (s : X86Memory.State) (f : Option Flags) (a : Word)
    (safe : Apart a (s.regs 4-4)) :
    load32 (called line s f).core.memory a=load32 s.memory a := by
  change load32 (store32 s.memory (s.regs 4-4) _) a=_
  exact load_store_apart _ _ _ _ safe


/-- Try lines first; only a disabled line flag can skip directly to things. -/
def firstVisit (s : X86Memory.State) : X86Control.State :=
  if enabled true s then enter true s else enter false s

theorem first_visit_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤8 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2ca7f⟩ (firstVisit s) := by
  by_cases h : enabled true s=true
  · obtain ⟨n,hn,a⟩ := enter_execution true s f
    exact ⟨n,by omega,by simpa only [firstVisit,if_pos h,gatePc,↓reduceIte] using a⟩
  · have a := gate_execution true s f
    have eq : gate true s=⟨s,gateFlags true s,gatePc false⟩ := by simp [gate,h,skipPc,gatePc]
    rw [eq] at a
    obtain ⟨n,hn,b⟩ := enter_execution false s (gateFlags true s)
    exact ⟨2+n,by omega,by simpa only [firstVisit,if_neg h,gatePc,↓reduceIte] using OriginalGroupBounds.prefix_join a b⟩

/-- Start at the real line return site. Failure aborts; success tests things.
This contract does not assume or model how the line iterator returned. -/
def afterLine (s : X86Memory.State) : X86Control.State :=
  if s.regs 0=(0#32) then resumed true s else enter false s

theorem after_line_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤8 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2ca94⟩ (afterLine s) := by
  have a := resume_execution true s f
  by_cases h : s.regs 0=(0#32)
  · exact ⟨2,by omega,by simpa only [afterLine,if_pos h,returnPc,↓reduceIte] using a⟩
  · have eq : resumed true s=⟨s,some (logical32 (s.regs 0)),gatePc false⟩ := by
      simp [resumed,h,skipPc,gatePc]
    rw [eq] at a
    obtain ⟨n,hn,b⟩ := enter_execution false s (some (logical32 (s.regs 0)))
    exact ⟨2+n,by omega,by simpa only [afterLine,if_neg h,returnPc,↓reduceIte] using OriginalGroupBounds.prefix_join a b⟩

/- No claim about either iterator body is hidden in the dispatcher: these
prefixes stop at the actual call entry or at the next caller-side gate. -/
end Doom.Proofs.OriginalPathCell
