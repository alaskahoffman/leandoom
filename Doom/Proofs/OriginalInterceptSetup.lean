import Doom.Proofs.E1M1InterceptGate
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalInterceptSetup
open Verification X86 X86Memory X86Control BlockSummary
attribute [local irreducible] load32 store32
def setupCode : List UInt8 := [0x53,0x51,0x56,0x57,0x83,0xec,0x4,0x8b,0xd,0x28,0xc0,0x2,0x0,0x89,0x4,0x24,0x89,0xd7,0x89,0xca,0x81,0xea,0x20,0xba,0x2,0x0,0xbb,0xc,0x0,0x0,0x0,0x89,0xd0,0xc1,0xfa,0x1f,0xf7,0xfb,0x89,0xc6,0x31,0xdb,0x89,0xf0,0x4e,0x85,0xc0,0x74,0x46]
def handoffCode : List UInt8 := [0x8b,0x44,0x24,0x44,0xba,0x0,0x0,0x1,0x0,0xe8,0x5,0xfd,0xff,0xff]
def bytesProgram (setup handoff : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2c810≤pc ∧ pc<0x2c841 then X86Routine.decodeAt setup (pc-0x2c810)
  else if 0x2cafd≤pc ∧ pc<0x2cb0b then X86Routine.decodeAt handoff (pc-0x2cafd) else none
def program := bytesProgram setupCode handoffCode
def listed : X86Routine.Program
  | 0x2cafd => some (.control (.block (.load 0 ⟨some 4,none,0,68⟩)),4)
  | 0x2cb01 => some (.immediate 2 65536,5)
  | 0x2cb06 => some (.call (-763),5)
  | 0x2c810 => some (.push 3,1)
  | 0x2c811 => some (.push 1,1)
  | 0x2c812 => some (.push 6,1)
  | 0x2c813 => some (.push 7,1)
  | 0x2c814 => some (.addImmediate 4 (-4),3)
  | 0x2c817 => some (.control (.block (.load 1 ⟨none,none,0,0x2c028⟩)),6)
  | 0x2c81d => some (.control (.block (.store ⟨some 4,none,0,0⟩ 0)),3)
  | 0x2c820 => some (.control (.block (.legacy (.mov 7 2))),2)
  | 0x2c822 => some (.control (.block (.legacy (.mov 2 1))),2)
  | 0x2c824 => some (.addImmediate 2 (-0x2ba20),6)
  | 0x2c82a => some (.immediate 3 12,5)
  | 0x2c82f => some (.control (.block (.legacy (.mov 0 2))),2)
  | 0x2c831 => some (.sar 2 31,3)
  | 0x2c834 => some (.signedDivide 3,2)
  | 0x2c836 => some (.control (.block (.legacy (.mov 6 0))),2)
  | 0x2c838 => some (.xorRegister 3 3,2)
  | 0x2c83a => some (.control (.block (.legacy (.mov 0 6))),2)
  | 0x2c83c => some (.addImmediate 6 (-1),1)
  | 0x2c83d => some (.control (.testWord 0 0),2)
  | 0x2c83f => some (.control (.jumpZero true 70),2)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def callback (s : X86Memory.State) := load32 s.memory (s.regs 4+68)
def called (s : X86Memory.State) := X86Routine.pushWord (put (put s 0 (callback s)) 2 65536) 0x2cb0b
def push1 (s : X86Memory.State) := X86Routine.pushWord s (s.regs 3)
def push2 (s : X86Memory.State) := X86Routine.pushWord (push1 s) (s.regs 1)
def push3 (s : X86Memory.State) := X86Routine.pushWord (push2 s) (s.regs 6)
def push4 (s : X86Memory.State) := X86Routine.pushWord (push3 s) (s.regs 7)
def localFrame (s : X86Memory.State) := put (push4 s) 4 ((push4 s).regs 4-4)
def cursor (s : X86Memory.State) := load32 (localFrame s).memory 0x2c028
def saved (s : X86Memory.State) : X86Memory.State :=
  {put (localFrame s) 1 (cursor s) with
    memory := store32 (localFrame s).memory ((localFrame s).regs 4) (s.regs 0)}
def prepared (s : X86Memory.State) := put (saved s) 7 (s.regs 2)
def delta (s : X86Memory.State) := s.regs 1-0x2ba20
def counted (s : X86Memory.State) (n : Nat) := put (put (put (put s 0 (BitVec.ofNat 32 n)) 2 0) 3 0) 6 (BitVec.ofNat 32 n-1)
def ready (s : X86Memory.State) (n : Nat) : X86Control.State :=
  ⟨counted s n,some (logical32 (BitVec.ofNat 32 n)),if n=0 then 0x2c887 else 0x2c841⟩

/-- The collection exit loads its callback argument, fixes maxfrac to one,
and calls the actual traversal entry. -/
theorem handoff_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 3 ⟨s,f,0x2cafd⟩ ⟨called s,f,0x2c810⟩ := by
  have run : X86Routine.Prefix listed [] 3 ⟨s,f,0x2cafd⟩ ⟨called s,f,0x2c810⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨put s 0 (callback s),f,0x2cb01⟩) (by simp) (by rfl) (by
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          X86Block.Address.eval,X86Routine.pushWord,put,write,blockPreservesFlags,
          callback,called,push1,push2,push3,push4,localFrame,cursor,saved,prepared,delta,counted,ready,BitVec.sub_eq_add_neg,BitVec.add_assoc,logical32]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨put (put s 0 (callback s)) 2 65536,f,0x2cb06⟩) (by simp) (by rfl) (by
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          X86Block.Address.eval,X86Routine.pushWord,put,write,blockPreservesFlags,
          callback,called,push1,push2,push3,push4,localFrame,cursor,saved,prepared,delta,counted,ready,BitVec.sub_eq_add_neg,BitVec.add_assoc,logical32]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨called s,f,0x2c810⟩) (by simp) (by rfl) (by
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          X86Block.Address.eval,X86Routine.pushWord,put,write,blockPreservesFlags,
          callback,called,push1,push2,push3,push4,localFrame,cursor,saved,prepared,delta,counted,ready,BitVec.sub_eq_add_neg,BitVec.add_assoc,logical32]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
    exact .nil _
  exact run.transfer program [] decoded (by simp)

/-- The actual prologue retains all aliasing effects of its stack stores. -/
theorem prologue_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 8 ⟨s,f,0x2c810⟩ ⟨prepared s,none,0x2c822⟩ := by
  have run : X86Routine.Prefix listed [] 8 ⟨s,f,0x2c810⟩ ⟨prepared s,none,0x2c822⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨push1 s,f,0x2c811⟩) (by simp) (by rfl) (by
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          X86Block.Address.eval,X86Routine.pushWord,put,write,blockPreservesFlags,
          callback,called,push1,push2,push3,push4,localFrame,cursor,saved,prepared,delta,counted,ready,BitVec.sub_eq_add_neg,BitVec.add_assoc,logical32]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨push2 s,f,0x2c812⟩) (by simp) (by rfl) (by
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          X86Block.Address.eval,X86Routine.pushWord,put,write,blockPreservesFlags,
          callback,called,push1,push2,push3,push4,localFrame,cursor,saved,prepared,delta,counted,ready,BitVec.sub_eq_add_neg,BitVec.add_assoc,logical32]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨push3 s,f,0x2c813⟩) (by simp) (by rfl) (by
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          X86Block.Address.eval,X86Routine.pushWord,put,write,blockPreservesFlags,
          callback,called,push1,push2,push3,push4,localFrame,cursor,saved,prepared,delta,counted,ready,BitVec.sub_eq_add_neg,BitVec.add_assoc,logical32]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨push4 s,f,0x2c814⟩) (by simp) (by rfl) (by
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          X86Block.Address.eval,X86Routine.pushWord,put,write,blockPreservesFlags,
          callback,called,push1,push2,push3,push4,localFrame,cursor,saved,prepared,delta,counted,ready,BitVec.sub_eq_add_neg,BitVec.add_assoc,logical32]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨localFrame s,none,0x2c817⟩) (by simp) (by rfl) (by
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          X86Block.Address.eval,X86Routine.pushWord,put,write,blockPreservesFlags,
          callback,called,push1,push2,push3,push4,localFrame,cursor,saved,prepared,delta,counted,ready,BitVec.sub_eq_add_neg,BitVec.add_assoc,logical32]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨put (localFrame s) 1 (cursor s),none,0x2c81d⟩) (by simp) (by rfl) (by
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          X86Block.Address.eval,X86Routine.pushWord,put,write,blockPreservesFlags,
          callback,called,push1,push2,push3,push4,localFrame,cursor,saved,prepared,delta,counted,ready,BitVec.sub_eq_add_neg,BitVec.add_assoc,logical32]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨saved s,none,0x2c820⟩) (by simp) (by rfl) (by
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          X86Block.Address.eval,X86Routine.pushWord,put,write,blockPreservesFlags,
          callback,called,push1,push2,push3,push4,localFrame,cursor,saved,prepared,delta,counted,ready,BitVec.sub_eq_add_neg,BitVec.add_assoc,logical32]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
    apply X86Routine.Prefix.step (middle := ⟨prepared s,none,0x2c822⟩) (by simp) (by rfl) (by
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          X86Block.Address.eval,X86Routine.pushWord,put,write,blockPreservesFlags,
          callback,called,push1,push2,push3,push4,localFrame,cursor,saved,prepared,delta,counted,ready,BitVec.sub_eq_add_neg,BitVec.add_assoc,logical32]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
    exact .nil _
  exact run.transfer program [] decoded (by simp)

/-- A valid cursor yields a nonnegative byte distance, without wraparound. -/
theorem byte_distance (n : Nat) (h : n≤128) :
    (E1M1MinimumScan.address n-0x2ba20).toInt=12*(n:Int) := by
  have eq : E1M1MinimumScan.address n-0x2ba20=BitVec.ofNat 32 (12*n) := by
    simp [E1M1MinimumScan.address,BitVec.ofNat_add,BitVec.add_comm,BitVec.add_sub_cancel]
  rw [eq,BitVec.toInt_ofNat',Int.bmod_eq_of_le (by omega) (by omega)]
  simp

/-- The original signed division recovers count, then the post-decrement loop
condition bypasses scanning when the collection is empty. -/
theorem count_execution (s : X86Memory.State) (f : Option Flags) (n : Nat)
    (bound : n≤128) (limit : s.regs 1=E1M1MinimumScan.address n) :
    X86Routine.Prefix program [] 12 ⟨s,f,0x2c822⟩ (ready s n) := by
  have distance : (delta s).toInt=12*(n:Int) := by
    unfold delta; rw [limit]; exact byte_distance n bound
  have wide := PlayerArmor.dividend (delta s)
  have quotient : ((delta s).sshiftRight 31 ++ delta s).toInt.tdiv 12=(n:Int) := by rw [wide,distance]; simp
  have remainder : ((delta s).sshiftRight 31 ++ delta s).toInt.tmod 12=0 := by rw [wide,distance]; simp
  have fits : ¬((n:Int) < -2147483648 ∨ 2147483647<(n:Int)) := by omega
  have zero : (BitVec.ofNat 32 n=0) ↔ n=0 := by
    rw [←BitVec.toNat_inj]
    simp [Nat.mod_eq_of_lt (show n<2^32 by omega)]
  have run : X86Routine.Prefix listed [] 12 ⟨s,f,0x2c822⟩ (ready s n) := by
    by_cases empty : n=0
    ·
      apply X86Routine.Prefix.step (middle := ⟨put s 2 (s.regs 1),f,0x2c824⟩) (by simp) (by rfl) (by
        simp only [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          put,write,ite_true,ite_false,show (31:Nat)%32=31 from rfl]
        try simp only [←BitVec.sub_eq_add_neg]
        try change _ = _
        all_goals simp_all [delta,counted,ready,blockPreservesFlags,logical32,put,write,
          BitVec.sub_eq_add_neg,BitVec.ofInt_natCast]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
      apply X86Routine.Prefix.step (middle := ⟨put s 2 (delta s),none,0x2c82a⟩) (by simp) (by rfl) (by
        simp only [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          put,write,ite_true,ite_false,show (31:Nat)%32=31 from rfl]
        try simp only [←BitVec.sub_eq_add_neg]
        try change _ = _
        all_goals simp_all [delta,counted,ready,blockPreservesFlags,logical32,put,write,
          BitVec.sub_eq_add_neg,BitVec.ofInt_natCast]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
      apply X86Routine.Prefix.step (middle := ⟨put (put s 2 (delta s)) 3 12,none,0x2c82f⟩) (by simp) (by rfl) (by
        simp only [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          put,write,ite_true,ite_false,show (31:Nat)%32=31 from rfl]
        try simp only [←BitVec.sub_eq_add_neg]
        try change _ = _
        all_goals simp_all [delta,counted,ready,blockPreservesFlags,logical32,put,write,
          BitVec.sub_eq_add_neg,BitVec.ofInt_natCast]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
      apply X86Routine.Prefix.step (middle := ⟨put (put (put s 2 (delta s)) 3 12) 0 (delta s),none,0x2c831⟩) (by simp) (by rfl) (by
        simp only [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          put,write,ite_true,ite_false,show (31:Nat)%32=31 from rfl]
        try simp only [←BitVec.sub_eq_add_neg]
        try change _ = _
        all_goals simp_all [delta,counted,ready,blockPreservesFlags,logical32,put,write,
          BitVec.sub_eq_add_neg,BitVec.ofInt_natCast]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
      apply X86Routine.Prefix.step (middle := ⟨put (put (put (put s 2 (delta s)) 3 12) 0 (delta s)) 2 ((delta s).sshiftRight 31),none,0x2c834⟩) (by simp) (by rfl) (by
        simp only [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          put,write,ite_true,ite_false,show (31:Nat)%32=31 from rfl]
        try simp only [←BitVec.sub_eq_add_neg]
        try change _ = _
        all_goals simp_all [delta,counted,ready,blockPreservesFlags,logical32,put,write,
          BitVec.sub_eq_add_neg,BitVec.ofInt_natCast]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
      apply X86Routine.Prefix.step (middle := ⟨put (put (put (put (put s 2 (delta s)) 3 12) 0 (delta s)) 0 (BitVec.ofNat 32 n)) 2 0,none,0x2c836⟩) (by simp) (by rfl) (by
        simp only [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          put,write,ite_true,ite_false,show (31:Nat)%32=31 from rfl]
        try simp only [←BitVec.sub_eq_add_neg]
        try change _ = _
        all_goals simp_all [delta,counted,ready,blockPreservesFlags,logical32,put,write,
          BitVec.sub_eq_add_neg,BitVec.ofInt_natCast]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
      apply X86Routine.Prefix.step (middle := ⟨put (put (put (put (put (put s 2 (delta s)) 3 12) 0 (delta s)) 0 (BitVec.ofNat 32 n)) 2 0) 6 (BitVec.ofNat 32 n),none,0x2c838⟩) (by simp) (by rfl) (by
        simp only [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          put,write,ite_true,ite_false,show (31:Nat)%32=31 from rfl]
        try simp only [←BitVec.sub_eq_add_neg]
        try change _ = _
        all_goals simp_all [delta,counted,ready,blockPreservesFlags,logical32,put,write,
          BitVec.sub_eq_add_neg,BitVec.ofInt_natCast]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
      apply X86Routine.Prefix.step (middle := ⟨put (put (put (put (put (put (put s 2 (delta s)) 3 12) 0 (delta s)) 0 (BitVec.ofNat 32 n)) 2 0) 6 (BitVec.ofNat 32 n)) 3 0,some {(logical32 0) with carry := some false},0x2c83a⟩) (by simp) (by rfl) (by
        simp only [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          put,write,ite_true,ite_false,show (31:Nat)%32=31 from rfl]
        try simp only [←BitVec.sub_eq_add_neg]
        try change _ = _
        all_goals simp_all [delta,counted,ready,blockPreservesFlags,logical32,put,write,
          BitVec.sub_eq_add_neg,BitVec.ofInt_natCast]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
      apply X86Routine.Prefix.step (middle := ⟨put (put (put (put (put (put (put s 2 (delta s)) 3 12) 0 (delta s)) 0 (BitVec.ofNat 32 n)) 2 0) 6 (BitVec.ofNat 32 n)) 3 0,some {(logical32 0) with carry := some false},0x2c83c⟩) (by simp) (by rfl) (by
        simp only [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          put,write,ite_true,ite_false,show (31:Nat)%32=31 from rfl]
        try simp only [←BitVec.sub_eq_add_neg]
        try change _ = _
        all_goals simp_all [delta,counted,ready,blockPreservesFlags,logical32,put,write,
          BitVec.sub_eq_add_neg,BitVec.ofInt_natCast]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
      apply X86Routine.Prefix.step (middle := ⟨counted s n,none,0x2c83d⟩) (by simp) (by rfl) (by
        simp only [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          put,write,ite_true,ite_false,show (31:Nat)%32=31 from rfl]
        try simp only [←BitVec.sub_eq_add_neg]
        try change _ = _
        all_goals simp_all [delta,counted,ready,blockPreservesFlags,logical32,put,write,
          BitVec.sub_eq_add_neg,BitVec.ofInt_natCast]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
      apply X86Routine.Prefix.step (middle := ⟨counted s n,some (logical32 (BitVec.ofNat 32 n)),0x2c83f⟩) (by simp) (by rfl) (by
        simp only [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          put,write,ite_true,ite_false,show (31:Nat)%32=31 from rfl]
        try simp only [←BitVec.sub_eq_add_neg]
        try change _ = _
        all_goals simp_all [delta,counted,ready,blockPreservesFlags,logical32,put,write,
          BitVec.sub_eq_add_neg,BitVec.ofInt_natCast]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
      apply X86Routine.Prefix.step (middle := ready s n) (by simp) (by rfl) (by
        simp only [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          put,write,ite_true,ite_false,show (31:Nat)%32=31 from rfl]
        try simp only [←BitVec.sub_eq_add_neg]
        try change _ = _
        all_goals simp_all [delta,counted,ready,blockPreservesFlags,logical32,put,write,
          BitVec.sub_eq_add_neg,BitVec.ofInt_natCast]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
      exact .nil _
    ·
      apply X86Routine.Prefix.step (middle := ⟨put s 2 (s.regs 1),f,0x2c824⟩) (by simp) (by rfl) (by
        simp only [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          put,write,ite_true,ite_false,show (31:Nat)%32=31 from rfl]
        try simp only [←BitVec.sub_eq_add_neg]
        try change _ = _
        all_goals simp_all [delta,counted,ready,blockPreservesFlags,logical32,put,write,
          BitVec.sub_eq_add_neg,BitVec.ofInt_natCast]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
      apply X86Routine.Prefix.step (middle := ⟨put s 2 (delta s),none,0x2c82a⟩) (by simp) (by rfl) (by
        simp only [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          put,write,ite_true,ite_false,show (31:Nat)%32=31 from rfl]
        try simp only [←BitVec.sub_eq_add_neg]
        try change _ = _
        all_goals simp_all [delta,counted,ready,blockPreservesFlags,logical32,put,write,
          BitVec.sub_eq_add_neg,BitVec.ofInt_natCast]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
      apply X86Routine.Prefix.step (middle := ⟨put (put s 2 (delta s)) 3 12,none,0x2c82f⟩) (by simp) (by rfl) (by
        simp only [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          put,write,ite_true,ite_false,show (31:Nat)%32=31 from rfl]
        try simp only [←BitVec.sub_eq_add_neg]
        try change _ = _
        all_goals simp_all [delta,counted,ready,blockPreservesFlags,logical32,put,write,
          BitVec.sub_eq_add_neg,BitVec.ofInt_natCast]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
      apply X86Routine.Prefix.step (middle := ⟨put (put (put s 2 (delta s)) 3 12) 0 (delta s),none,0x2c831⟩) (by simp) (by rfl) (by
        simp only [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          put,write,ite_true,ite_false,show (31:Nat)%32=31 from rfl]
        try simp only [←BitVec.sub_eq_add_neg]
        try change _ = _
        all_goals simp_all [delta,counted,ready,blockPreservesFlags,logical32,put,write,
          BitVec.sub_eq_add_neg,BitVec.ofInt_natCast]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
      apply X86Routine.Prefix.step (middle := ⟨put (put (put (put s 2 (delta s)) 3 12) 0 (delta s)) 2 ((delta s).sshiftRight 31),none,0x2c834⟩) (by simp) (by rfl) (by
        simp only [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          put,write,ite_true,ite_false,show (31:Nat)%32=31 from rfl]
        try simp only [←BitVec.sub_eq_add_neg]
        try change _ = _
        all_goals simp_all [delta,counted,ready,blockPreservesFlags,logical32,put,write,
          BitVec.sub_eq_add_neg,BitVec.ofInt_natCast]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
      apply X86Routine.Prefix.step (middle := ⟨put (put (put (put (put s 2 (delta s)) 3 12) 0 (delta s)) 0 (BitVec.ofNat 32 n)) 2 0,none,0x2c836⟩) (by simp) (by rfl) (by
        simp only [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          put,write,ite_true,ite_false,show (31:Nat)%32=31 from rfl]
        try simp only [←BitVec.sub_eq_add_neg]
        try change _ = _
        all_goals simp_all [delta,counted,ready,blockPreservesFlags,logical32,put,write,
          BitVec.sub_eq_add_neg,BitVec.ofInt_natCast]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
      apply X86Routine.Prefix.step (middle := ⟨put (put (put (put (put (put s 2 (delta s)) 3 12) 0 (delta s)) 0 (BitVec.ofNat 32 n)) 2 0) 6 (BitVec.ofNat 32 n),none,0x2c838⟩) (by simp) (by rfl) (by
        simp only [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          put,write,ite_true,ite_false,show (31:Nat)%32=31 from rfl]
        try simp only [←BitVec.sub_eq_add_neg]
        try change _ = _
        all_goals simp_all [delta,counted,ready,blockPreservesFlags,logical32,put,write,
          BitVec.sub_eq_add_neg,BitVec.ofInt_natCast]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
      apply X86Routine.Prefix.step (middle := ⟨put (put (put (put (put (put (put s 2 (delta s)) 3 12) 0 (delta s)) 0 (BitVec.ofNat 32 n)) 2 0) 6 (BitVec.ofNat 32 n)) 3 0,some {(logical32 0) with carry := some false},0x2c83a⟩) (by simp) (by rfl) (by
        simp only [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          put,write,ite_true,ite_false,show (31:Nat)%32=31 from rfl]
        try simp only [←BitVec.sub_eq_add_neg]
        try change _ = _
        all_goals simp_all [delta,counted,ready,blockPreservesFlags,logical32,put,write,
          BitVec.sub_eq_add_neg,BitVec.ofInt_natCast]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
      apply X86Routine.Prefix.step (middle := ⟨put (put (put (put (put (put (put s 2 (delta s)) 3 12) 0 (delta s)) 0 (BitVec.ofNat 32 n)) 2 0) 6 (BitVec.ofNat 32 n)) 3 0,some {(logical32 0) with carry := some false},0x2c83c⟩) (by simp) (by rfl) (by
        simp only [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          put,write,ite_true,ite_false,show (31:Nat)%32=31 from rfl]
        try simp only [←BitVec.sub_eq_add_neg]
        try change _ = _
        all_goals simp_all [delta,counted,ready,blockPreservesFlags,logical32,put,write,
          BitVec.sub_eq_add_neg,BitVec.ofInt_natCast]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
      apply X86Routine.Prefix.step (middle := ⟨counted s n,none,0x2c83d⟩) (by simp) (by rfl) (by
        simp only [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          put,write,ite_true,ite_false,show (31:Nat)%32=31 from rfl]
        try simp only [←BitVec.sub_eq_add_neg]
        try change _ = _
        all_goals simp_all [delta,counted,ready,blockPreservesFlags,logical32,put,write,
          BitVec.sub_eq_add_neg,BitVec.ofInt_natCast]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
      apply X86Routine.Prefix.step (middle := ⟨counted s n,some (logical32 (BitVec.ofNat 32 n)),0x2c83f⟩) (by simp) (by rfl) (by
        simp only [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          put,write,ite_true,ite_false,show (31:Nat)%32=31 from rfl]
        try simp only [←BitVec.sub_eq_add_neg]
        try change _ = _
        all_goals simp_all [delta,counted,ready,blockPreservesFlags,logical32,put,write,
          BitVec.sub_eq_add_neg,BitVec.ofInt_natCast]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
      apply X86Routine.Prefix.step (middle := ready s n) (by simp) (by rfl) (by
        simp only [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          put,write,ite_true,ite_false,show (31:Nat)%32=31 from rfl]
        try simp only [←BitVec.sub_eq_add_neg]
        try change _ = _
        all_goals simp_all [delta,counted,ready,blockPreservesFlags,logical32,put,write,
          BitVec.sub_eq_add_neg,BitVec.ofInt_natCast]
        all_goals try omega
        all_goals (funext r; by_cases h0 : r=0 <;> by_cases h2 : r=2 <;>
          by_cases h3 : r=3 <;> by_cases h6 : r=6 <;> simp_all [write]))
      exact .nil _
  exact run.transfer program [] decoded (by simp)
end Doom.Proofs.OriginalInterceptSetup
