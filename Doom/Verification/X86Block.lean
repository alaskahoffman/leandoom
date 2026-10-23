import Doom.Verification.X86Memory

/-! Straight-line block decoding and composition. This extends the existing
register/memory projection, not a complete CPU: flags, faults, segmentation,
fetch, stack/call control and timing remain outside its semantics. -/
namespace Doom.Verification.X86Block
open X86 X86Memory

structure Address where
  base : Option Reg := none
  index : Option Reg := none
  scale : Nat := 0
  offset : Word := 0
  deriving DecidableEq

def Address.eval (a : Address) (rs : Registers) : Word :=
  (a.base.map rs).getD 0 + ((a.index.map rs).getD 0 <<< a.scale) + a.offset

inductive Op where
  | legacy (op : X86Memory.Op)
  | arithmetic (op : X86.Instruction)
  | shr (dst : Reg) (amount : UInt8)
  | load (dst : Reg) (address : Address)
  | lea (dst : Reg) (address : Address)
  | store (address : Address) (src : Reg)
  | movsx8 (dst src : Reg)
  | subEax (value : Word)
  deriving DecidableEq

def word : List UInt8 → Option (Word × List UInt8)
  | a :: b :: c :: d :: rest => some ((d.toBitVec ++ c.toBitVec) ++ (b.toBitVec ++ a.toBitVec), rest)
  | _ => none

/-- Full 32-bit ModRM/SIB addressing for the listed load/LEA forms only. -/
def operand (m : UInt8) (rest : List UInt8) : Option (Address × List UInt8) := do
  let mode := m.toNat / 64
  if mode = 3 then none else do
    let (a, tail) ← if m.toNat % 8 = 4 then do
      let sib :: tail := rest | none
      let base := rm sib
      let index := reg sib
      pure ({ base := if mode = 0 && base.val = 5 then none else some base,
              index := if index.val = 4 then none else some index,
              scale := sib.toNat / 64 : Address }, tail)
    else pure ({ base := if mode = 0 && (rm m).val = 5 then none else some (rm m) : Address }, rest)
    if mode = 0 && a.base.isNone || mode = 2 then do
      let (offset, tail) ← word tail
      pure ({ a with offset }, tail)
    else if mode = 1 then do
      let d :: tail := tail | none
      pure ({ a with offset := displacement d }, tail)
    else pure (a, tail)

def decode (code : List UInt8) : Option (Op × List UInt8) :=
  match X86Memory.decode code with
  | some (op, rest) => some (.legacy op, rest)
  | none => match X86.decode code with
    | some (op, rest) => some (.arithmetic op, rest)
    | none => match code with
      | 0x2d :: rest => do
        let (value, rest) ← word rest
        pure (.subEax value, rest)
      | 0x0f :: 0xbe :: m :: rest =>
        if m.toNat / 64 = 3 then some (.movsx8 (reg m) (rm m), rest) else none
      | 0xc1 :: m :: amount :: rest =>
        if m.toNat / 8 = 29 then some (.shr (rm m) amount, rest) else none
      | opcode :: m :: rest => do
        let (a, rest) ← operand m rest
        match opcode with
        | 0x8b => pure (.load (reg m) a, rest)
        | 0x8d => pure (.lea (reg m) a, rest)
        | 0x89 => pure (.store a (reg m), rest)
        | _ => none
      | _ => none

def execute (op : Op) (s : State) : State := match op with
  | .legacy op => X86Memory.execute op s
  | .arithmetic op => { s with regs := X86.execute op s.regs }
  | .shr dst amount => put s dst (s.regs dst >>> (amount.toNat % 32))
  | .load dst a => put s dst (load32 s.memory (a.eval s.regs))
  | .lea dst a => put s dst (a.eval s.regs)
  | .store a src => { s with memory := store32 s.memory (a.eval s.regs) (s.regs src) }
  | .movsx8 dst src =>
      let value := (s.regs (Fin.ofNat 8 (src.val % 4))).extractLsb'
        (if src.val < 4 then 0 else 8) 8
      put s dst (value.signExtend 32)
  | .subEax value => put s eax (s.regs eax - value)

/-- Require exactly the declared instruction count and consume all bytes. -/
def decodeBlock : Nat → List UInt8 → Option (List Op)
  | 0, [] => some []
  | 0, _ :: _ => none
  | n+1, code => do
    let (op, rest) ← decode code
    let ops ← decodeBlock n rest
    pure (op :: ops)

def eval : List Op → State → State
  | [], s => s
  | op :: ops, s => eval ops (execute op s)

def run (n : Nat) (code : List UInt8) (s : State) : Option State :=
  (decodeBlock n code).map (fun ops => eval ops s)

/-- Reuse a proved block summary inside a larger decoded program. -/
theorem eval_append (a b : List Op) (s : State) :
    eval (a ++ b) s = eval b (eval a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons op ops ih => exact ih (execute op s)

/-- The byte-to-summary bridge: an untrusted generator may propose `ops` and
`summary`; neither is accepted until both obligations have been proved. -/
theorem of_decoded_summary (code : List UInt8) (ops : List Op) (n : Nat)
    (summary : State → State) (decoded : decodeBlock n code = some ops)
    (correct : ∀ s, eval ops s = summary s) (s : State) :
    run n code s = some (summary s) := by
  simp only [run, decoded, Option.map_some, correct]

end Doom.Verification.X86Block
