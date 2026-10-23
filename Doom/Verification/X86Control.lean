import Doom.Verification.X86Block

/-! Bounded control flow over the same byte-addressed memory as X86Block.
ZF/SF/OF are projected, with optional CF for supported unsigned comparisons. Instructions whose flags are not modeled invalidate
that projection; a conditional consumer of unknown flags fails closed. Code is
an immutable byte list, PC is a code-relative natural offset, and exits must be
explicitly designated. This is not a model of fetch faults or the DOS loader. -/
namespace Doom.Verification.X86Control
open X86 X86Memory

structure Flags where
  zero : Bool
  sign : Bool
  overflow : Bool
  carry : Option Bool
  deriving DecidableEq

def Flags.lessEqual (f : Flags) : Bool := f.zero || (f.sign != f.overflow)

structure State where
  core : X86Memory.State
  flags : Option Flags := none
  pc : Nat := 0

def compare32 (a b : Word) : Flags :=
  let result := a - b
  ⟨result == 0, result.msb, (a.msb != b.msb) && (result.msb != a.msb), some (a.ult b)⟩

def logical32 (v : Word) : Flags := ⟨v == 0, v.msb, false, some false⟩
def logical8 (v : BitVec 8) : Flags := ⟨v == 0, v.msb, false, some false⟩

/-- The x86 encoding 0..7 denotes AL/CL/DL/BL/AH/CH/DH/BH. -/
def byteReg (r : Reg) : Reg := Fin.ofNat 8 (r.val % 4)
def readByte (rs : Registers) (r : Reg) : BitVec 8 :=
  if r.val < 4 then (rs (byteReg r)).extractLsb' 0 8
  else (rs (byteReg r)).extractLsb' 8 8

def putByte (s : X86Memory.State) (r : Reg) (value : BitVec 8) : X86Memory.State :=
  let old := s.regs (byteReg r)
  let value := if r.val < 4 then (old &&& 0xffffff00) ||| value.zeroExtend 32
    else (old &&& 0xffff00ff) ||| (value.zeroExtend 32 <<< 8)
  X86Memory.put s (byteReg r) value

inductive Op where
  | block (op : X86Block.Op)
  | cmpMemory (lhs : Reg) (rhs : X86Block.Address)
  | cmpImmediate (lhs : X86Block.Address) (rhs : Word)
  | setle (dst : Reg)
  | andEax (mask : Word)
  | loadByte (dst : Reg) (src : X86Block.Address)
  | storeEax (dst : Word)
  | testByte (a b : Reg)
  | testWord (a b : Reg)
  | jumpZero (whenZero : Bool) (offset : Int)
  deriving DecidableEq

def relative8 (b : UInt8) : Int := b.toBitVec.toInt

def decode (code : List UInt8) : Option (Op × List UInt8) :=
  match code with
  | 0x3b :: m :: tail => do
    let (a, tail) ← X86Block.operand m tail
    pure (.cmpMemory (X86Memory.reg m) a, tail)
  | 0x83 :: m :: tail => do
    if m.toNat / 8 % 8 != 7 then none else do
      let (a, tail) ← X86Block.operand m tail
      let v :: tail := tail | none
      pure (.cmpImmediate a (v.toBitVec.signExtend 32), tail)
  | 0x0f :: 0x9e :: m :: tail =>
    if m.toNat / 64 = 3 then some (.setle (X86Memory.rm m), tail) else none
  | 0x25 :: tail => do
    let (v, tail) ← X86Block.word tail
    pure (.andEax v, tail)
  | 0x8a :: m :: tail => do
    let (a, tail) ← X86Block.operand m tail
    pure (.loadByte (X86Memory.reg m) a, tail)
  | 0xa3 :: tail => do
    let (a, tail) ← X86Block.word tail
    pure (.storeEax a, tail)
  | 0x84 :: m :: tail =>
    if m.toNat / 64 = 3 then some (.testByte (X86Memory.rm m) (X86Memory.reg m), tail) else none
  | 0x85 :: m :: tail =>
    if m.toNat / 64 = 3 then some (.testWord (X86Memory.rm m) (X86Memory.reg m), tail) else none
  | 0x74 :: d :: tail => some (.jumpZero true (relative8 d), tail)
  | 0x75 :: d :: tail => some (.jumpZero false (relative8 d), tail)
  | _ => (X86Block.decode code).map (fun (op, rest) => (.block op, rest))

/-- MOV/LEA/MOVSX preserve flags. Arithmetic with unmodeled flags clears them.
A zero shift count also preserves flags, as on x86. -/
def blockPreservesFlags : X86Block.Op → Bool
  | .legacy (.mov ..) | .legacy (.lea ..) | .legacy (.load ..)
  | .legacy (.movsx16 ..) | .load .. | .lea .. | .store .. | .movsx8 .. => true
  | .legacy (.shl _ amount) | .shr _ amount => amount.toNat % 32 == 0
  | _ => false

/-- PC has already advanced past this instruction when execute is called. -/
def execute (op : Op) (s : State) : Option State := match op with
  | .block op => some { s with core := X86Block.execute op s.core, flags := if blockPreservesFlags op then s.flags else none }
  | .cmpMemory lhs rhs => some { s with flags := some (compare32 (s.core.regs lhs) (load32 s.core.memory (rhs.eval s.core.regs))) }
  | .cmpImmediate lhs rhs => some { s with flags := some (compare32 (load32 s.core.memory (lhs.eval s.core.regs)) rhs) }
  | .setle dst => do
      let flags ← s.flags
      pure { s with core := (putByte s.core dst
        (if flags.lessEqual then 1 else 0)) }
  | .andEax mask =>
      let v := s.core.regs eax &&& mask
      some { s with core := X86Memory.put s.core eax v, flags := some (logical32 v) }
  | .loadByte dst src => some { s with core := (putByte s.core dst
      (s.core.memory (src.eval s.core.regs))) }
  | .storeEax dst => some { s with core := { s.core with
      memory := store32 s.core.memory dst (s.core.regs eax) } }
  | .testByte a b => some { s with flags := some (logical8 (readByte s.core.regs a &&& readByte s.core.regs b)) }
  | .testWord a b => some { s with flags := some (logical32 (s.core.regs a &&& s.core.regs b)) }
  | .jumpZero whenZero offset => do
      let flags ← s.flags
      if flags.zero = whenZero then
        let pc := (s.pc : Int) + offset
        if pc < 0 then none else pure { s with pc := pc.toNat }
      else pure s

abbrev Program := Nat → Option (Op × Nat)

def decodeAt (code : List UInt8) (pc : Nat) : Option (Op × Nat) :=
  (decode (code.drop pc)).map (fun (op, rest) => (op, (code.drop pc).length - rest.length))

/-- Fuel exhaustion and unsupported bytes are failures, never successful exits. -/
def runProgram (program : Program) (exits : List Nat) : Nat → State → Option State
  | fuel, s =>
      if s.pc ∈ exits then some s else match fuel with
      | 0 => none
      | n+1 => do
        let (op, length) ← program s.pc
        let next ← execute op { s with pc := s.pc + length }
        runProgram program exits n next

def run (code : List UInt8) := runProgram (decodeAt code)

/-- A proposed control-flow listing is accepted only when each listed instruction
is proved equal to decoding the original bytes. Missing reachable instructions
fail rather than silently terminating. -/
theorem runProgram_sound (code : List UInt8) (program : Program)
    (sound : ∀ pc, program pc ≠ none → decodeAt code pc = program pc)
    (exits : List Nat) (fuel : Nat) (s : State)
    (valid : runProgram program exits fuel s ≠ none) :
    run code exits fuel s = runProgram program exits fuel s := by
  unfold run
  induction fuel generalizing s with
  | zero => simp [runProgram]
  | succ n ih =>
    unfold runProgram
    split
    · rfl
    · cases hp : program s.pc with
      | none => simp [runProgram, *] at valid
      | some pair =>
        have hd := sound s.pc (by simp [hp])
        rw [hd, hp]
        rcases pair with ⟨op, length⟩
        dsimp only
        cases he : execute op { s with pc := s.pc + length } with
        | none => simp [he]
        | some next =>
          have hn : runProgram program exits n next ≠ none := by
            simpa [runProgram, hp, he, *] using valid
          simpa [he] using ih next hn

end Doom.Verification.X86Control
