import Doom.Verification.X86

/-!
A straight-line 32-bit x86 register/memory projection. Byte-addressed memory
preserves overlap and unaligned accesses; effective-address arithmetic wraps.
Memory is total and flat: access faults, segmentation, physical instruction
fetch, EFLAGS, interrupts and timing are outside this model. In particular,
this cannot justify a branch on flags. The turning block's subsequent CMP
establishes fresh flags before any conditional use.
Only the listed encodings are accepted; SIB, prefixes and other operations fail.
-/
namespace Doom.Verification.X86Memory
open X86
abbrev Word := BitVec 32
abbrev Memory := Word → BitVec 8
abbrev ecx : Reg := 1
abbrev esi : Reg := 6

structure State where
  regs : Registers
  memory : Memory

def load16 (m : Memory) (a : Word) : BitVec 16 := m (a+1) ++ m a

def load32 (m : Memory) (a : Word) : Word :=
  (m (a+3) ++ m (a+2)) ++ (m (a+1) ++ m a)

def store32 (m : Memory) (a value : Word) : Memory := fun b =>
  if b = a then value.extractLsb' 0 8
  else if b = a+1 then value.extractLsb' 8 8
  else if b = a+2 then value.extractLsb' 16 8
  else if b = a+3 then value.extractLsb' 24 8 else m b

inductive Op where
  | mov (dst src : Reg)
  | lea (dst base : Reg) (offset : Word)
  | load (dst base : Reg) (offset : Word)
  | movsx16 (dst base : Reg) (offset : Word)
  | shl (dst : Reg) (amount : UInt8)
  | addMemory (base src : Reg) (offset : Word)
  deriving DecidableEq

def rm (m : UInt8) : Reg := Fin.ofNat 8 (m.toNat % 8)
def reg (m : UInt8) : Reg := Fin.ofNat 8 (m.toNat / 8 % 8)
def displacement (b : UInt8) : Word := b.toBitVec.signExtend 32

/-- ModRM memory operands with no SIB, either no displacement or disp8.
The no-displacement EBP encoding actually means disp32 and is rejected. -/
def address (m : UInt8) (rest : List UInt8) : Option (Reg × Word × List UInt8) :=
  if m.toNat % 8 = 4 then none
  else if m.toNat / 64 = 0 && m.toNat % 8 != 5 then some (rm m, 0, rest)
  else if m.toNat / 64 = 1 then match rest with
    | d :: tail => some (rm m, displacement d, tail)
    | [] => none
  else none

def decode : List UInt8 → Option (Op × List UInt8)
  | 0x89 :: m :: rest =>
    if m.toNat / 64 = 3 then some (.mov (rm m) (reg m), rest) else none
  | 0xc1 :: m :: amount :: rest =>
    if m.toNat / 8 = 28 then some (.shl (rm m) amount, rest) else none
  | 0x0f :: 0xbf :: m :: rest => do
    let (base, offset, tail) ← address m rest
    return (.movsx16 (reg m) base offset, tail)
  | op :: m :: rest => do
    let (base, offset, tail) ← address m rest
    match op with
    | 0x8d => return (.lea (reg m) base offset, tail)
    | 0x8b => return (.load (reg m) base offset, tail)
    | 0x01 => return (.addMemory base (reg m) offset, tail)
    | _ => none
  | _ => none

def put (s : State) (dst : Reg) (value : Word) : State :=
  { s with regs := write s.regs dst value }

def execute (op : Op) (s : State) : State := match op with
  | .mov dst src => put s dst (s.regs src)
  | .lea dst base offset => put s dst (s.regs base + offset)
  | .load dst base offset => put s dst (load32 s.memory (s.regs base + offset))
  | .movsx16 dst base offset => put s dst ((load16 s.memory (s.regs base + offset)).signExtend 32)
  | .shl dst amount => put s dst (s.regs dst <<< (amount.toNat % 32))
  | .addMemory base src offset =>
    let a := s.regs base + offset
    { s with memory := store32 s.memory a (load32 s.memory a + s.regs src) }

def run : Nat → List UInt8 → State → Option State
  | 0, [], s => some s
  | 0, _ :: _, _ => none
  | n+1, code, s => do
    let (op, rest) ← decode code
    run n rest (execute op s)

end Doom.Verification.X86Memory
