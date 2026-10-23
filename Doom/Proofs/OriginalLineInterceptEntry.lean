import Doom.Proofs.OriginalLineCell
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalLineInterceptEntry
open Verification X86 X86Memory X86Control BlockSummary
def entryBytes : List UInt8 := [0x53,0x51,0x52,0x56,0x55,0x83,0xec,0x10,0x89,0xc1,0x8b,0x15,0x18,0xba,0x2,0x0,0x81,0xfa,0x0,0x0,0x10,0x0,0x7f,0x1e,0x8b,0x1d,0x1c,0xba,0x2,0x0,0x81,0xfb,0x0,0x0,0x10,0x0,0x7f,0x10,0x81,0xfa,0x0,0x0,0xf0,0xff,0x7c,0x8,0x81,0xfb,0x0,0x0,0xf0,0xff,0x7d,0x27,0x8b,0x1,0xbb,0x10,0xba,0x2,0x0,0x8b,0x50,0x4,0x8b,0x0,0xe8,0xa9,0xfb,0xff,0xff]
def shortBytes : List UInt8 := [0x8b,0x15,0x14,0xba,0x2,0x0,0xa1,0x10,0xba,0x2,0x0,0x89,0xcb,0xe8,0xb1,0xf9,0xff,0xff]
def bytesProgram (entry short : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2c5f0≤pc ∧ pc<0x2c637 then X86Routine.decodeAt entry (pc-0x2c5f0)
  else if 0x2c64d≤pc ∧ pc<0x2c65f then X86Routine.decodeAt short (pc-0x2c64d) else none
def program := bytesProgram entryBytes shortBytes
def listed : X86Routine.Program
  | 0x2c5f0 => some (.push 3,1)
  | 0x2c5f1 => some (.push 1,1)
  | 0x2c5f2 => some (.push 2,1)
  | 0x2c5f3 => some (.push 6,1)
  | 0x2c5f4 => some (.push 5,1)
  | 0x2c5f5 => some (.addImmediate 4 (-16),3)
  | 0x2c5f8 => some (.control (.block (.legacy (.mov 1 0))),2)
  | 0x2c5fa => some (.control (.block (.load 2 ⟨none,none,0,0x2ba18⟩)),6)
  | 0x2c600 => some (.compareRegister 2 0x100000,6)
  | 0x2c606 => some (.jumpSigned 2 30,2)
  | 0x2c608 => some (.control (.block (.load 3 ⟨none,none,0,0x2ba1c⟩)),6)
  | 0x2c60e => some (.compareRegister 3 0x100000,6)
  | 0x2c614 => some (.jumpSigned 2 16,2)
  | 0x2c616 => some (.compareRegister 2 0xfff00000,6)
  | 0x2c61c => some (.jumpSigned 3 8,2)
  | 0x2c61e => some (.compareRegister 3 0xfff00000,6)
  | 0x2c624 => some (.jumpSigned 0 39,2)
  | 0x2c626 => some (.control (.block (.legacy (.load 0 1 0))),2)
  | 0x2c628 => some (.immediate 3 0x2ba10,5)
  | 0x2c62d => some (.control (.block (.legacy (.load 2 0 4))),3)
  | 0x2c630 => some (.control (.block (.legacy (.load 0 0 0))),2)
  | 0x2c632 => some (.call (-1111),5)
  | 0x2c64d => some (.control (.block (.load 2 ⟨none,none,0,0x2ba14⟩)),6)
  | 0x2c653 => some (.control (.block (.load 0 ⟨none,none,0,0x2ba10⟩)),5)
  | 0x2c658 => some (.control (.block (.legacy (.mov 3 1))),2)
  | 0x2c65a => some (.call (-1615),5)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide
def p1 (s : X86Memory.State) := X86Routine.pushWord s (s.regs 3)
def p2 (s : X86Memory.State) := X86Routine.pushWord (p1 s) (s.regs 1)
def p3 (s : X86Memory.State) := X86Routine.pushWord (p2 s) (s.regs 2)
def p4 (s : X86Memory.State) := X86Routine.pushWord (p3 s) (s.regs 6)
def p5 (s : X86Memory.State) := X86Routine.pushWord (p4 s) (s.regs 5)
def p6 (s : X86Memory.State) := put (p5 s) 4 (s.regs 4-36)
def p7 (s : X86Memory.State) := put (p6 s) 1 (s.regs 0)
def prepared (s : X86Memory.State) := put (p7 s) 2 (load32 (p5 s).memory 0x2ba18)

theorem prepare_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 8 ⟨s,f,0x2c5f0⟩ ⟨prepared s,none,0x2c600⟩ := by
  have path : X86Routine.Prefix listed [] 8 ⟨s,f,0x2c5f0⟩ ⟨prepared s,none,0x2c600⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨p1 s,f,0x2c5f1⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,prepared,p7,p6,p5,p4,p3,p2,p1,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨p2 s,f,0x2c5f2⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,prepared,p7,p6,p5,p4,p3,p2,p1,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨p3 s,f,0x2c5f3⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,prepared,p7,p6,p5,p4,p3,p2,p1,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨p4 s,f,0x2c5f4⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,prepared,p7,p6,p5,p4,p3,p2,p1,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨p5 s,f,0x2c5f5⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,prepared,p7,p6,p5,p4,p3,p2,p1,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨p6 s,none,0x2c5f8⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,prepared,p7,p6,p5,p4,p3,p2,p1,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨p7 s,none,0x2c5fa⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,prepared,p7,p6,p5,p4,p3,p2,p1,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := ⟨prepared s,none,0x2c600⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,prepared,p7,p6,p5,p4,p3,p2,p1,X86Routine.pushWord])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

def dx (s : X86Memory.State) := s.regs 2
def dy (s : X86Memory.State) := load32 s.memory 0x2ba1c
def withY (s : X86Memory.State) := put s 3 (dy s)
def usesDivline (s : X86Memory.State) : Bool :=
  decide (1048576<(dx s).toInt ∨ 1048576<(dy s).toInt ∨ (dx s).toInt< -1048576 ∨ (dy s).toInt< -1048576)
def gate (s : X86Memory.State) : X86Control.State :=
  if 1048576<(dx s).toInt then ⟨s,some (compare32 (dx s) 0x100000),0x2c626⟩
  else if 1048576<(dy s).toInt then ⟨withY s,some (compare32 (dy s) 0x100000),0x2c626⟩
  else if (dx s).toInt< -1048576 then ⟨withY s,some (compare32 (dx s) 0xfff00000),0x2c626⟩
  else ⟨withY s,some (compare32 (dy s) 0xfff00000),if (dy s).toInt< -1048576 then 0x2c626 else 0x2c64d⟩

theorem gate_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤9 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2c600⟩ (gate s) := by
  have path : ∃ n, n≤9 ∧ X86Routine.Prefix listed [] n ⟨s,f,0x2c600⟩ (gate s) := by
    by_cases h0 : 1048576<(dx s).toInt
    · refine ⟨2,by omega,?_⟩
      apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dx s) 0x100000),0x2c606⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
      apply X86Routine.Prefix.step (middle := gate s) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
      exact .nil _
    · by_cases h1 : 1048576<(dy s).toInt
      · refine ⟨5,by omega,?_⟩
        apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dx s) 0x100000),0x2c606⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
        apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dx s) 0x100000),0x2c608⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
        apply X86Routine.Prefix.step (middle := ⟨withY s,some (compare32 (dx s) 0x100000),0x2c60e⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
        apply X86Routine.Prefix.step (middle := ⟨withY s,some (compare32 (dy s) 0x100000),0x2c614⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
        apply X86Routine.Prefix.step (middle := gate s) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
        exact .nil _
      · by_cases h2 : (dx s).toInt< -1048576
        · refine ⟨7,by omega,?_⟩
          apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dx s) 0x100000),0x2c606⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
          apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dx s) 0x100000),0x2c608⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
          apply X86Routine.Prefix.step (middle := ⟨withY s,some (compare32 (dx s) 0x100000),0x2c60e⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
          apply X86Routine.Prefix.step (middle := ⟨withY s,some (compare32 (dy s) 0x100000),0x2c614⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
          apply X86Routine.Prefix.step (middle := ⟨withY s,some (compare32 (dy s) 0x100000),0x2c616⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
          apply X86Routine.Prefix.step (middle := ⟨withY s,some (compare32 (dx s) 0xfff00000),0x2c61c⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
          apply X86Routine.Prefix.step (middle := gate s) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
          exact .nil _
        · by_cases h3 : (dy s).toInt< -1048576
          · refine ⟨9,by omega,?_⟩
            apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dx s) 0x100000),0x2c606⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dx s) 0x100000),0x2c608⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨withY s,some (compare32 (dx s) 0x100000),0x2c60e⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨withY s,some (compare32 (dy s) 0x100000),0x2c614⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨withY s,some (compare32 (dy s) 0x100000),0x2c616⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨withY s,some (compare32 (dx s) 0xfff00000),0x2c61c⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨withY s,some (compare32 (dx s) 0xfff00000),0x2c61e⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨withY s,some (compare32 (dy s) 0xfff00000),0x2c624⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := gate s) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
            exact .nil _
          · refine ⟨9,by omega,?_⟩
            apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dx s) 0x100000),0x2c606⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (dx s) 0x100000),0x2c608⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨withY s,some (compare32 (dx s) 0x100000),0x2c60e⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨withY s,some (compare32 (dy s) 0x100000),0x2c614⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨withY s,some (compare32 (dy s) 0x100000),0x2c616⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨withY s,some (compare32 (dx s) 0xfff00000),0x2c61c⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨withY s,some (compare32 (dx s) 0xfff00000),0x2c61e⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨withY s,some (compare32 (dy s) 0xfff00000),0x2c624⟩) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := gate s) (by simp) (by rfl) (by simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,gate,withY,dx,dy,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,PlayerArmor.cmp_lt] <;> repeat (first | rfl | omega | split))
            exact .nil _
  obtain ⟨n,hn,path⟩ := path
  exact ⟨n,hn,path.transfer program [] decoded (by simp)⟩

def vertex (s : X86Memory.State) := load32 s.memory (s.regs 1)
def long1 (s : X86Memory.State) := put s 0 (vertex s)
def long2 (s : X86Memory.State) := put (long1 s) 3 0x2ba10
def long3 (s : X86Memory.State) := put (long2 s) 2 (load32 s.memory (vertex s+4))
def long4 (s : X86Memory.State) := put (long3 s) 0 (load32 s.memory (vertex s))
def short1 (s : X86Memory.State) := put s 2 (load32 s.memory 0x2ba14)
def short2 (s : X86Memory.State) := put (short1 s) 0 (load32 s.memory 0x2ba10)
def short3 (s : X86Memory.State) := put (short2 s) 3 (s.regs 1)
def callPc (wide : Bool) : Nat := if wide then 0x2c626 else 0x2c64d
def returnPc (wide : Bool) : Word := if wide then 0x2c637 else 0x2c65f
def callee (wide : Bool) : Nat := if wide then 0x2c1e0 else 0x2c010
def called (wide : Bool) (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨X86Routine.pushWord (if wide then long4 s else short3 s) (returnPc wide),f,callee wide⟩

theorem call_execution (wide : Bool) (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] (if wide then 5 else 4) ⟨s,f,callPc wide⟩ (called wide s f) := by
  have path : X86Routine.Prefix listed [] (if wide then 5 else 4) ⟨s,f,callPc wide⟩ (called wide s f) := by
    cases wide
    · apply X86Routine.Prefix.step (middle := ⟨short1 s,f,0x2c653⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,called,callPc,returnPc,callee,long4,long3,long2,long1,short3,short2,short1,vertex,X86Routine.pushWord])
      apply X86Routine.Prefix.step (middle := ⟨short2 s,f,0x2c658⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,called,callPc,returnPc,callee,long4,long3,long2,long1,short3,short2,short1,vertex,X86Routine.pushWord])
      apply X86Routine.Prefix.step (middle := ⟨short3 s,f,0x2c65a⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,called,callPc,returnPc,callee,long4,long3,long2,long1,short3,short2,short1,vertex,X86Routine.pushWord])
      apply X86Routine.Prefix.step (middle := called false s f) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,called,callPc,returnPc,callee,long4,long3,long2,long1,short3,short2,short1,vertex,X86Routine.pushWord])
      exact .nil _
    · apply X86Routine.Prefix.step (middle := ⟨long1 s,f,0x2c628⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,called,callPc,returnPc,callee,long4,long3,long2,long1,short3,short2,short1,vertex,X86Routine.pushWord])
      apply X86Routine.Prefix.step (middle := ⟨long2 s,f,0x2c62d⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,called,callPc,returnPc,callee,long4,long3,long2,long1,short3,short2,short1,vertex,X86Routine.pushWord])
      apply X86Routine.Prefix.step (middle := ⟨long3 s,f,0x2c630⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,called,callPc,returnPc,callee,long4,long3,long2,long1,short3,short2,short1,vertex,X86Routine.pushWord])
      apply X86Routine.Prefix.step (middle := ⟨long4 s,f,0x2c632⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,called,callPc,returnPc,callee,long4,long3,long2,long1,short3,short2,short1,vertex,X86Routine.pushWord])
      apply X86Routine.Prefix.step (middle := called true s f) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,called,callPc,returnPc,callee,long4,long3,long2,long1,short3,short2,short1,vertex,X86Routine.pushWord])
      exact .nil _
  exact path.transfer program [] decoded (by simp)

theorem gate_pc (s : X86Memory.State) : (gate s).pc=callPc (usesDivline s) := by
  unfold gate usesDivline callPc
  split <;> (try split) <;> (try split) <;> (try split) <;> simp_all

theorem gate_preserves (s : X86Memory.State) :
    (gate s).core.memory=s.memory ∧ (gate s).core.regs 1=s.regs 1 ∧ (gate s).core.regs 4=s.regs 4 := by
  unfold gate
  split <;> (try split) <;> (try split) <;> simp [withY,put,write]

def first (s : X86Memory.State) :=
  called (usesDivline (prepared s)) (gate (prepared s)).core (gate (prepared s)).flags

theorem first_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤22 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2c5f0⟩ (first s) := by
  have a := prepare_execution s f
  obtain ⟨n,hn,b⟩ := gate_execution (prepared s) none
  have c := call_execution (usesDivline (prepared s)) (gate (prepared s)).core (gate (prepared s)).flags
  rw [OriginalPathXStep.at_pc _ _ (gate_pc (prepared s))] at c
  refine ⟨8+n+(if usesDivline (prepared s) then 5 else 4),?_,OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join a b) c⟩
  split <;> omega

def saved (s : X86Memory.State) : Memory :=
  store32 (store32 (store32 (store32 (store32 s.memory (s.regs 4-4) (s.regs 3))
    (s.regs 4-8) (s.regs 1)) (s.regs 4-12) (s.regs 2)) (s.regs 4-16) (s.regs 6)) (s.regs 4-20) (s.regs 5)

theorem prepared_memory (s : X86Memory.State) : (prepared s).memory=saved s := by
  simp [prepared,p7,p6,p5,p4,p3,p2,p1,X86Routine.pushWord,put,write,saved,BitVec.sub_eq_add_neg,BitVec.add_assoc]

theorem prepared_regs (s : X86Memory.State) :
    (prepared s).regs 1=s.regs 0 ∧ (prepared s).regs 4=s.regs 4-36 ∧
    (prepared s).regs 2=load32 (prepared s).memory 0x2ba18 := by
  simp [prepared,p7,p6,p5,p4,p3,p2,p1,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]

theorem frame (s : X86Memory.State) (a : Word)
    (safe : ∀ off∈[(4#32),8,12,16,20], Apart a (s.regs 4-off)) :
    load32 (prepared s).memory a=load32 s.memory a := by
  rw [prepared_memory]
  unfold saved
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp))]

/-- Actual point, line/divline pointer, stack and return word sent to the helper. -/
theorem call_inputs (wide : Bool) (s : X86Memory.State) (f : Option Flags) :
    (called wide s f).core.regs 0=(if wide then load32 s.memory (vertex s) else load32 s.memory 0x2ba10) ∧
    (called wide s f).core.regs 2=(if wide then load32 s.memory (vertex s+4) else load32 s.memory 0x2ba14) ∧
    (called wide s f).core.regs 3=(if wide then 0x2ba10 else s.regs 1) ∧
    (called wide s f).core.regs 1=s.regs 1 ∧ (called wide s f).core.regs 4=s.regs 4-4 ∧
    load32 (called wide s f).core.memory (s.regs 4-4)=returnPc wide ∧
    (called wide s f).pc=callee wide := by
  cases wide <;> simp [called,long4,long3,long2,long1,short3,short2,short1,X86Routine.pushWord,put,write,load_store]

/-- The CALL writes one return word; every other separated data word survives. -/
theorem call_frame (wide : Bool) (s : X86Memory.State) (f : Option Flags) (a : Word)
    (safe : Apart a (s.regs 4-(4#32))) :
    load32 (called wide s f).core.memory a=load32 s.memory a := by
  cases wide
  · simpa [called,long4,long3,long2,long1,short3,short2,short1,X86Routine.pushWord,put,write] using
      load_store_apart s.memory (s.regs 4-(4#32)) a (returnPc false) safe
  · simpa [called,long4,long3,long2,long1,short3,short2,short1,X86Routine.pushWord,put,write] using
      load_store_apart s.memory (s.regs 4-(4#32)) a (returnPc true) safe

/-- The full entry has only the five saves and the final CALL write. -/
theorem first_frame (s : X86Memory.State) (a : Word)
    (saves : ∀ off∈[(4#32),8,12,16,20], Apart a (s.regs 4-off))
    (ret : Apart a (s.regs 4-(40#32))) :
    load32 (first s).core.memory a=load32 s.memory a := by
  have sp := (gate_preserves (prepared s)).2.2.trans (prepared_regs s).2.1
  have addr : (gate (prepared s)).core.regs 4-(4#32)=s.regs 4-(40#32) := by
    rw [sp]
    simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  unfold first
  rw [call_frame _ _ _ a (by simpa only [addr] using ret), (gate_preserves (prepared s)).1]
  exact frame s a saves

def reads (line vertex : Word) : List Word := [0x2ba10,0x2ba14,0x2ba18,0x2ba1c,line,vertex,vertex+4]

/-- Memory representation at callback entry, before the five saved-register writes. -/
structure Inputs (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (linePtr vertexPtr : Word) : Prop where
  lineArg : s.regs 0=linePtr
  traceX : load32 s.memory 0x2ba10=trace.x.raw.toBitVec
  traceY : load32 s.memory 0x2ba14=trace.y.raw.toBitVec
  traceDX : load32 s.memory 0x2ba18=trace.dx.raw.toBitVec
  traceDY : load32 s.memory 0x2ba1c=trace.dy.raw.toBitVec
  vertex : load32 s.memory linePtr=vertexPtr
  vertexX : load32 s.memory vertexPtr=line.x.raw.toBitVec
  vertexY : load32 s.memory (vertexPtr+4)=line.y.raw.toBitVec
  safeReads : ∀ a∈reads linePtr vertexPtr, ∀ off∈[(4#32),8,12,16,20], Apart a (s.regs 4-off)

theorem selection_live (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (linePtr vertexPtr : Word) (h : Inputs s trace line linePtr vertexPtr) :
    usesDivline (prepared s)=trace.usesDivlineTest := by
  unfold usesDivline dx dy
  rw [(prepared_regs s).2.2,frame s _ (h.safeReads _ (by simp [reads])),
    frame s _ (h.safeReads _ (by simp [reads])),h.traceDX,h.traceDY]
  simp [Collision.Divline.usesDivlineTest,Int32.lt_iff_toInt_lt,Int32.toInt_toBitVec,or_assoc,Bool.or_assoc]

structure Ready (s : X86Memory.State) (t : X86Control.State) (trace : Collision.Divline)
    (line : Collision.Line) (linePtr : Word) : Prop where
  pointX : t.core.regs 0=(if trace.usesDivlineTest then line.x else trace.x).raw.toBitVec
  pointY : t.core.regs 2=(if trace.usesDivlineTest then line.y else trace.y).raw.toBitVec
  dataArg : t.core.regs 3=(if trace.usesDivlineTest then 0x2ba10 else linePtr)
  lineSaved : t.core.regs 1=linePtr
  stack : t.core.regs 4=s.regs 4-40
  returnWord : load32 t.core.memory (s.regs 4-40)=returnPc trace.usesDivlineTest
  pc : t.pc=callee trace.usesDivlineTest

theorem live (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (linePtr vertexPtr : Word) (h : Inputs s trace line linePtr vertexPtr) :
    Ready s (first s) trace line linePtr := by
  have selected := selection_live s trace line linePtr vertexPtr h
  have mem := (gate_preserves (prepared s)).1
  have savedLine := (gate_preserves (prepared s)).2.1.trans ((prepared_regs s).1.trans h.lineArg)
  have sp := (gate_preserves (prepared s)).2.2.trans (prepared_regs s).2.1
  have keep (a : Word) (ha : a∈reads linePtr vertexPtr) :
      load32 (gate (prepared s)).core.memory a=load32 s.memory a := by
    rw [mem]; exact frame s a (h.safeReads a ha)
  have vp : vertex (gate (prepared s)).core=vertexPtr := by
    unfold vertex
    rw [savedLine,keep _ (by simp [reads]),h.vertex]
  have args := call_inputs (usesDivline (prepared s)) (gate (prepared s)).core (gate (prepared s)).flags
  rw [selected] at args
  have addr : s.regs 4-(36#32)-(4#32)=s.regs 4-(40#32) := by
    simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  unfold first
  rw [selected]
  constructor
  · change (called _ _ _).core.regs 0=_
    rw [args.1,vp,keep _ (by simp [reads]),keep _ (by simp [reads]),h.vertexX,h.traceX]
    split <;> rfl
  · change (called _ _ _).core.regs 2=_
    rw [args.2.1,vp,keep _ (by simp [reads]),keep _ (by simp [reads]),h.vertexY,h.traceY]
    split <;> rfl
  · exact args.2.2.1.trans (by rw [savedLine])
  · exact args.2.2.2.1.trans savedLine
  · have a := args.2.2.2.2.1
    rw [sp] at a
    exact a.trans addr
  · have a := args.2.2.2.2.2.1
    rw [sp] at a
    change load32 _ (s.regs 4-(36#32)-(4#32))=_ at a
    rw [addr] at a
    exact a
  · exact args.2.2.2.2.2.2

end Doom.Proofs.OriginalLineInterceptEntry
