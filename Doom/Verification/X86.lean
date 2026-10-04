import Init.Data.BitVec.Lemmas

/-!
A small, explicit register-result semantics for the 32-bit, register-only forms
of one-operand IMUL, immediate SHRD, ADD and SUB. See Intel SDM volume 2.
This is NOT a full x86 emulator: flags, instruction fetch, faults, memory,
interrupts and timing are outside the model. Neither instruction reads flags;
projecting them away is sufficient for the multiplication result theorem.
Unsupported encodings fail decoding, rather than silently becoming no-ops.
-/
namespace Doom.Verification.X86

abbrev Reg := Fin 8
abbrev eax : Reg := 0
abbrev edx : Reg := 2
abbrev ebx : Reg := 3

abbrev Registers := Reg → BitVec 32

def write (regs : Registers) (dst : Reg) (value : BitVec 32) : Registers :=
  fun r => if r = dst then value else regs r

inductive Instruction where
  | imul (src : Reg)
  | shrd (dst src : Reg) (immediate : UInt8)
  | add (dst src : Reg)
  | sub (dst src : Reg)
  deriving DecidableEq, Repr

/-- Register addressing only, 32-bit default operand size, no prefixes.
F7 /5: signed EAX × r/m32 → EDX:EAX. 0F AC /r ib: SHRD r/m32, r32, imm8. -/
def decode : List UInt8 → Option (Instruction × List UInt8)
  | 0x01 :: modrm :: rest =>
      if modrm.toNat / 64 = 3 then
        some (.add (Fin.ofNat 8 (modrm.toNat % 8)) (Fin.ofNat 8 (modrm.toNat / 8 % 8)), rest)
      else none
  | 0x29 :: modrm :: rest =>
      if modrm.toNat / 64 = 3 then
        some (.sub (Fin.ofNat 8 (modrm.toNat % 8)) (Fin.ofNat 8 (modrm.toNat / 8 % 8)), rest)
      else none
  | 0xf7 :: modrm :: rest =>
      if modrm.toNat / 8 = 29 then
        some (.imul (Fin.ofNat 8 (modrm.toNat % 8)), rest)
      else none
  | 0x0f :: 0xac :: modrm :: imm :: rest =>
      if modrm.toNat / 64 = 3 then
        some (.shrd (Fin.ofNat 8 (modrm.toNat % 8))
          (Fin.ofNat 8 (modrm.toNat / 8 % 8)) imm, rest)
      else none
  | _ => none

def execute (ins : Instruction) (regs : Registers) : Registers :=
  match ins with
  | .add dst src => write regs dst (regs dst + regs src)
  | .sub dst src => write regs dst (regs dst - regs src)
  | .imul src =>
      let product := BitVec.ofInt 64 ((regs eax).toInt * (regs src).toInt)
      write (write regs eax (product.extractLsb' 0 32)) edx (product.extractLsb' 32 32)
  | .shrd dst src imm =>
      -- Concatenate source above destination, shift right, keep the low 32 bits.
      -- x86 masks the count to five bits; zero leaves the destination unchanged.
      write regs dst (((regs src ++ regs dst) >>> (imm.toNat % 32)).setWidth 32)

/-- Execute exactly `fuel` instructions and require the complete byte list to
be consumed. A truncated, unsupported, or trailing instruction is an error. -/
def run : Nat → List UInt8 → Registers → Option Registers
  | 0, [], regs => some regs
  | 0, _ :: _, _ => none
  | n + 1, bytes, regs => do
      let (ins, rest) ← decode bytes
      run n rest (execute ins regs)

end Doom.Verification.X86
