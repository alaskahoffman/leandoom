import Doom.Verification.X86

/-!
Small x86 routine semantics used for DOOM's FixedDiv and RNG proofs.
Registers and relevant data accesses are modeled; saved registers use an abstract
call-local stack. RET returns to the modeled caller. No claim about physical
stack addresses, instruction fetch, segmentation, interrupts, or timing.
`less` projects SF xor OF. Shifts and IDIV leave it unknown (their flags are
not needed by these routines); a conditional operation on unknown flags fails.
Data addresses are offsets in the relocated data object (checked by the extractor).
The read-only byte table and writable dwords occupy disjoint regions for these
routines. This is not a general aliasing memory model or a complete x86 emulator.
-/
namespace Doom.Verification.X86Routine
open X86

abbrev Word := BitVec 32
abbrev ecx : Reg := 1
abbrev esi : Reg := 6

inductive Fault where
  | divideByZero | quotientOverflow
  deriving BEq, DecidableEq, Repr

structure State where
  regs : Registers := fun _ => 0
  saved : List Word := []
  words : Nat → Word := fun _ => 0
  bytes : Nat → BitVec 8 := fun _ => 0
  less : Option Bool := none
  pc : Nat := 0

inductive Result where
  | running (state : State)
  | returned (state : State)
  | fault (reason : Fault)
  | unsupported

inductive Op where
  | push (r : Reg) | pop (r : Reg) | ret | cdq
  | mov (dst src : Reg) | xor (dst src : Reg) | sub (dst src : Reg)
  | cmp (dst src : Reg) | test (dst src : Reg)
  | sar (r : Reg) (n : UInt8) | shl (r : Reg) (n : UInt8)
  | shld (dst src : Reg) (n : UInt8) | idiv (r : Reg)
  | jl (displacement : Int) | setlAl
  | andEax (n : Word) | addEax (n : Word) | inc (r : Reg)
  | loadEax (addr : Nat) | storeEax (addr : Nat) | store (src : Reg) (addr : Nat)
  | loadAl (base : Nat)
  deriving DecidableEq

def little32 (a b c d : UInt8) : Nat :=
  a.toNat + 256*b.toNat + 65536*c.toNat + 16777216*d.toNat

def rm (b : UInt8) : Reg := Fin.ofNat 8 (b.toNat % 8)
def reg (b : UInt8) : Reg := Fin.ofNat 8 (b.toNat / 8 % 8)

/-- The returned length includes opcode, addressing bytes, and immediate. -/
def decode : List UInt8 → Option (Op × Nat)
  | 0x99 :: _ => some (.cdq, 1)
  | 0xc3 :: _ => some (.ret, 1)
  | 0x7c :: d :: _ => some (.jl (if d.toNat < 128 then d.toNat else (d.toNat : Int)-256), 2)
  | 0x0f :: 0x9c :: 0xc0 :: _ => some (.setlAl, 3)
  | 0x0f :: 0xa4 :: m :: n :: _ =>
      if m.toNat / 64 = 3 then some (.shld (rm m) (reg m) n, 4) else none
  | 0xc1 :: m :: n :: _ =>
      if m.toNat / 8 = 31 then some (.sar (rm m) n, 3)
      else if m.toNat / 8 = 28 then some (.shl (rm m) n, 3) else none
  | 0xf7 :: m :: _ =>
      if m.toNat / 8 = 31 then some (.idiv (rm m), 2) else none
  | 0x25 :: a :: b :: c :: d :: _ => some (.andEax (BitVec.ofNat 32 (little32 a b c d)), 5)
  | 0x05 :: a :: b :: c :: d :: _ => some (.addEax (BitVec.ofNat 32 (little32 a b c d)), 5)
  | 0xa1 :: a :: b :: c :: d :: _ => some (.loadEax (little32 a b c d), 5)
  | 0xa3 :: a :: b :: c :: d :: _ => some (.storeEax (little32 a b c d), 5)
  | 0x8a :: 0x80 :: a :: b :: c :: d :: _ => some (.loadAl (little32 a b c d), 6)
  | 0x89 :: 0x15 :: a :: b :: c :: d :: _ => some (.store edx (little32 a b c d), 6)
  | op :: m :: _ =>
      if op.toNat / 8 = 10 then some (.push (rm op), 1)
      else if op.toNat / 8 = 11 then some (.pop (rm op), 1)
      else if op.toNat / 8 = 8 then some (.inc (rm op), 1)
      else if m.toNat / 64 = 3 then
        match op.toNat with
        | 0x89 => some (.mov (rm m) (reg m), 2)
        | 0x31 => some (.xor (rm m) (reg m), 2)
        | 0x29 => some (.sub (rm m) (reg m), 2)
        | 0x39 => some (.cmp (rm m) (reg m), 2)
        | 0x85 => some (.test (rm m) (reg m), 2)
        | _ => none
      else none
  | [op] =>
      if op.toNat / 8 = 10 then some (.push (rm op), 1)
      else if op.toNat / 8 = 11 then some (.pop (rm op), 1)
      else if op.toNat / 8 = 8 then some (.inc (rm op), 1) else none
  | _ => none

def signMask (w : Word) : Word := if w.toInt < 0 then BitVec.allOnes 32 else 0

def lowByte (w : Word) (b : BitVec 8) : Word :=
  BitVec.ofNat 32 (w.toNat / 256 * 256 + b.toNat)

def put (s : State) (r : Reg) (v : Word) : State := { s with regs := write s.regs r v }

def putWord (s : State) (addr : Nat) (v : Word) : State :=
  { s with words := fun a => if a = addr then v else s.words a }

def execute (op : Op) (s : State) : Result :=
  match op with
  | .ret => if s.saved.isEmpty then .returned s else .unsupported
  | .push r => .running { s with saved := s.regs r :: s.saved }
  | .pop r => match s.saved with
    | [] => .unsupported
    | v :: rest => .running { put s r v with saved := rest }
  | .mov dst src => .running (put s dst (s.regs src))
  | .cdq => .running (put s edx (signMask (s.regs eax)))
  | .xor dst src =>
      let v := s.regs dst ^^^ s.regs src
      .running { put s dst v with less := some (v.toInt < 0) }
  | .sub dst src => .running { put s dst (s.regs dst - s.regs src) with
      less := some ((s.regs dst).toInt < (s.regs src).toInt) }
  | .cmp dst src => .running { s with less := some ((s.regs dst).toInt < (s.regs src).toInt) }
  | .test dst src => .running { s with less := some ((s.regs dst &&& s.regs src).toInt < 0) }
  | .sar r n => .running { put s r ((s.regs r).sshiftRight (n.toNat % 32)) with less := none }
  | .shl r n => .running { put s r (s.regs r <<< (n.toNat % 32)) with less := none }
  | .shld dst src n => .running { put s dst
      (((s.regs dst ++ s.regs src) <<< (n.toNat % 32)).extractLsb' 32 32) with less := none }
  | .jl d => match s.less with
    | none => .unsupported
    | some flag => .running { s with pc := if flag then (s.pc + d).toNat else s.pc }
  | .setlAl => match s.less with
    | none => .unsupported
    | some flag => .running (put s eax (lowByte (s.regs eax) (if flag then 1 else 0)))
  | .andEax n =>
      let v := s.regs eax &&& n
      .running { put s eax v with less := some (v.toInt < 0) }
  | .addEax n => .running { put s eax (s.regs eax + n) with
      less := some ((s.regs eax).toInt + n.toInt < 0) }
  | .inc r => .running { put s r (s.regs r + 1) with less := some ((s.regs r).toInt + 1 < 0) }
  | .loadEax addr => .running (put s eax (s.words addr))
  | .storeEax addr => .running (putWord s addr (s.regs eax))
  | .store src addr => .running (putWord s addr (s.regs src))
  | .loadAl base => .running (put s eax (lowByte (s.regs eax) (s.bytes (base + (s.regs eax).toNat))))
  | .idiv r =>
      let d := (s.regs r).toInt
      let dividend := (s.regs edx ++ s.regs eax).toInt
      let q := dividend.tdiv d
      if d = 0 then .fault .divideByZero
      else if q < -2147483648 ∨ 2147483647 < q then .fault .quotientOverflow
      else .running { put (put s eax (BitVec.ofInt 32 q)) edx (BitVec.ofInt 32 (dividend.tmod d))
        with less := none }

def runProgram (program : Nat → Option (Op × Nat)) : Nat → State → Result
  | 0, _ => .unsupported
  | n+1, s => match program s.pc with
    | none => .unsupported
    | some (op, len) => match execute op { s with pc := s.pc+len } with
      | .running next => runProgram program n next
      | result => result

def run (code : List UInt8) := runProgram (fun pc => decode (code.drop pc))

def resultWord : Result → Option (Except Fault Word)
  | .returned s => some (.ok (s.regs eax))
  | .fault f => some (.error f)
  | _ => none

/-- A decoded control-flow listing may omit unreachable byte offsets. Every
instruction it *does* execute must be certified against the byte decoder. -/
theorem runProgram_sound (code : List UInt8) (program : Nat → Option (Op × Nat))
    (sound : ∀ pc, program pc ≠ none → decode (code.drop pc) = program pc)
    (fuel : Nat) (s : State) (valid : runProgram program fuel s ≠ .unsupported) :
    run code fuel s = runProgram program fuel s := by
  unfold run
  induction fuel generalizing s with
  | zero => exact False.elim (valid rfl)
  | succ n ih =>
    cases hp : program s.pc with
    | none => simp [runProgram, hp] at valid
    | some op =>
      rcases op with ⟨op, len⟩
      have hd := sound s.pc (by simp [hp])
      rw [runProgram, runProgram, hd, hp]
      cases he : execute op { s with pc := s.pc + len } with
      | running next =>
          simp only [he]
          apply ih
          simpa only [runProgram, hp, he] using valid
      | returned st => simp only [he]
      | fault f => simp only [he]
      | unsupported => simp only [he]

end Doom.Verification.X86Routine
