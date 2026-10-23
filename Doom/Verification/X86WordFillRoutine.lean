import Doom.Verification.X86FillRoutine
/-! Conservative opt-in projection for the aligned word filler. SHR by two keeps
only ZF: OF is undefined and is NEVER assigned a Boolean. SF/CF are deliberately
forgotten too. Unknown signed/carry consumers fail closed. DEC defines ZF/SF/OF,
preserving CF when known. All legacy interpreters are unchanged. -/
namespace Doom.Verification.X86WordFillRoutine
open X86 X86Memory X86Control
inductive Knowledge where
  | legacy (flags : Option Flags)
  | zeroOnly (zero : Bool)
  deriving DecidableEq
def Knowledge.carry : Knowledge → Option Bool
  | .legacy flags => flags.bind Flags.carry
  | .zeroOnly _ => none
structure State where
  core : X86Memory.State
  flags : Knowledge
  pc : Nat
def embed (s : X86Control.State) : State := ⟨s.core,.legacy s.flags,s.pc⟩
inductive Op where
  | base (op : X86FillRoutine.Op)
  | decrement (dst : Reg)
  | shiftRightTwo (dst : Reg)
  deriving DecidableEq
/-- Only these old operations can carry partial ZF through unchanged. -/
def preserves : X86FillRoutine.Op → Bool
  | .base (.base (.base (.control (.block b)))) => blockPreservesFlags b
  | .base (.base (.base (.push _))) | .base (.base (.base (.pop _)))
  | .base (.base (.base (.call _))) | .base (.base (.base .ret))
  | .base (.base (.base (.moveByte _ _))) => true
  | _ => false
def execute (op : Op) (s : State) : Option State :=
  match op with
  | .decrement dst =>
      let result := s.core.regs dst-1
      some ⟨put s.core dst result,.legacy (some
        {compare32 (s.core.regs dst) 1 with carry:=s.flags.carry}),s.pc⟩
  | .shiftRightTwo dst =>
      let result := s.core.regs dst >>> 2
      some ⟨put s.core dst result,.zeroOnly (result==0),s.pc⟩
  | .base op => match s.flags with
      | .legacy flags => (X86FillRoutine.execute op ⟨s.core,flags,s.pc⟩).map embed
      | .zeroOnly z => match op with
          | .base (.base (.base (.control (.jumpZero whenZero offset)))) =>
              if z=whenZero then
                let pc := (s.pc:Int)+offset
                if pc<0 then none else some {s with pc:=pc.toNat}
              else some s
          | _ => do
              let t ← X86FillRoutine.execute op ⟨s.core,none,s.pc⟩
              pure ⟨t.core,if preserves op then s.flags else .legacy t.flags,t.pc⟩
def decode (bytes : List UInt8) : Option (Op × List UInt8) :=
  match bytes with
  | 0xc1 :: m :: 2 :: tail =>
      if m.toNat/64=3 ∧ m.toNat/8%8=5 then some (.shiftRightTwo (rm m),tail)
      else (X86FillRoutine.decode bytes).map fun (op,rest)=>(.base op,rest)
  | b :: tail =>
      if 0x48≤b.toNat ∧ b.toNat<0x50 then some (.decrement (Fin.ofNat 8 (b.toNat-0x48)),tail)
      else (X86FillRoutine.decode bytes).map fun (op,rest)=>(.base op,rest)
  | [] => none
def decodeAt (bytes : List UInt8) (pc : Nat) : Option (Op × Nat) :=
  (decode (bytes.drop pc)).map fun (op,tail)=>(op,(bytes.drop pc).length-tail.length)
abbrev Program := Nat → Option (Op × Nat)
def liftProgram (p : X86FillRoutine.Program) : Program := fun pc =>
  (p pc).map fun (op,len)=>(.base op,len)
inductive Prefix (program : Program) (exits : List Nat) : Nat → State → State → Prop
  | nil (s) : Prefix program exits 0 s s
  | step {n s middle last op length}
      (active : s.pc ∉ exits)
      (decoded : program s.pc=some (op,length))
      (executed : execute op {s with pc:=s.pc+length}=some middle)
      (rest : Prefix program exits n middle last) : Prefix program exits (n+1) s last
theorem Prefix.trans {p exits n m s t u} (a : Prefix p exits n s t)
    (b : Prefix p exits m t u) : Prefix p exits (n+m) s u := by
  induction a with
  | nil => simpa using b
  | step active decoded executed rest ih =>
    simpa [Nat.succ_add] using Prefix.step active decoded executed (ih b)
theorem Prefix.transfer {p exits n s t} (path : Prefix p exits n s t)
    (q : Program) (outer : List Nat)
    (agree : ∀ pc, p pc≠none → q pc=p pc)
    (active : ∀ pc, p pc≠none → pc∉outer) : Prefix q outer n s t := by
  induction path with
  | nil => exact .nil _
  | @step n s middle last op len ha hd hx rest ih =>
    have valid : p s.pc≠none := by simp [hd]
    exact .step (active s.pc valid) ((agree s.pc valid).trans hd) hx ih
theorem lift_prefix {p exits n s t} (path : X86FillRoutine.Prefix p exits n s t) :
    Prefix (liftProgram p) exits n (embed s) (embed t) := by
  induction path with
  | nil => exact .nil _
  | @step n s middle last op len active decoded executed rest ih =>
    exact .step (op:=.base op) (length:=len) active
      (by simp [liftProgram,embed,decoded])
      (by simpa [execute,embed] using congrArg (Option.map embed) executed) ih
end Doom.Verification.X86WordFillRoutine
