import Doom.Proofs.E1M1WeaponRejection
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.NoiseAlert
open Verification X86 X86Memory X86Control BlockSummary
def entryBytes : List UInt8 := [0xa3,0x58,0xb9,0x2,0x0,0x8b,0x42,0x34,0x8b,0x15,0x80,0x35,0x1,0x0,0x42,0x8b,0x0,0x89,0x15,0x80,0x35,0x1,0x0,0x31,0xd2,0xe9,0x22,0xff,0xff,0xff]
def sectorBytes : List UInt8 := [0x53,0x51,0x56,0x57,0x55,0x83,0xec,0x4,0x89,0xc3,0x89,0xd1,0x8b,0x15,0x80,0x35,0x1,0x0,0x3b,0x50,0x42,0x75,0xc,0x8d,0x41,0x1,0x3b,0x43,0x12,0xf,0x8d,0x8e,0x0,0x0,0x0,0xa1,0x80,0x35,0x1,0x0,0x89,0x43,0x42,0x8d,0x41,0x1,0x8b,0x7b,0x4e,0x89,0x43,0x12,0xa1,0x58,0xb9,0x2,0x0,0x31,0xf6,0x89,0x43,0x16,0x85,0xff,0xf,0x8e,0x6b,0x0,0x0,0x0]
def bytesProgram (entry sector : List UInt8) : X86Routine.Program := fun pc =>
  if 0x27020≤pc ∧ pc<0x2703e then X86Routine.decodeAt entry (pc-0x27020)
  else if 0x26f60≤pc ∧ pc<0x26fa6 then X86Routine.decodeAt sector (pc-0x26f60) else none
def program := bytesProgram entryBytes sectorBytes

def listed : X86Routine.Program
  | 0x27020 => some (.control (.storeEax 0x2b958),5)
  | 0x27025 => some (.control (.block (.legacy (.load 0 2 52))),3)
  | 0x27028 => some (.control (.block (.load 2 ⟨none,none,0,0x13580⟩)),6)
  | 0x2702e => some (.addImmediate 2 1,1)
  | 0x2702f => some (.control (.block (.legacy (.load 0 0 0))),2)
  | 0x27031 => some (.control (.block (.store ⟨none,none,0,0x13580⟩ 2)),6)
  | 0x27037 => some (.xorRegister 2 2,2)
  | 0x27039 => some (.jump (-222),5)
  | 0x26f60 => some (.push 3,1)
  | 0x26f61 => some (.push 1,1)
  | 0x26f62 => some (.push 6,1)
  | 0x26f63 => some (.push 7,1)
  | 0x26f64 => some (.push 5,1)
  | 0x26f65 => some (.addImmediate 4 (-4),3)
  | 0x26f68 => some (.control (.block (.legacy (.mov 3 0))),2)
  | 0x26f6a => some (.control (.block (.legacy (.mov 1 2))),2)
  | 0x26f6c => some (.control (.block (.load 2 ⟨none,none,0,0x13580⟩)),6)
  | 0x26f72 => some (.control (.cmpMemory 2 ⟨some 0,none,0,66⟩),3)
  | 0x26f75 => some (.control (.jumpZero false 12),2)
  | 0x26f77 => some (.control (.block (.legacy (.lea 0 1 1))),3)
  | 0x26f7a => some (.control (.cmpMemory 0 ⟨some 3,none,0,18⟩),3)
  | 0x26f7d => some (.jumpSigned 0 142,6)
  | 0x26f83 => some (.control (.block (.load 0 ⟨none,none,0,0x13580⟩)),5)
  | 0x26f88 => some (.control (.block (.store ⟨some 3,none,0,66⟩ 0)),3)
  | 0x26f8b => some (.control (.block (.legacy (.lea 0 1 1))),3)
  | 0x26f8e => some (.control (.block (.legacy (.load 7 3 78))),3)
  | 0x26f91 => some (.control (.block (.store ⟨some 3,none,0,18⟩ 0)),3)
  | 0x26f94 => some (.control (.block (.load 0 ⟨none,none,0,0x2b958⟩)),5)
  | 0x26f99 => some (.xorRegister 6 6,2)
  | 0x26f9b => some (.control (.block (.store ⟨some 3,none,0,22⟩ 0)),3)
  | 0x26f9e => some (.control (.testWord 7 7),2)
  | 0x26fa0 => some (.jumpSigned 1 107,6)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

end Doom.Proofs.NoiseAlert
