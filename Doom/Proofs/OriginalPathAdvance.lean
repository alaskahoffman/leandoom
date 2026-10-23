import Doom.Proofs.E1M1FiringCellReturn
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalPathAdvance
open Verification X86 X86Memory X86Control BlockSummary
def code : List UInt8 := [0x3b,0x74,0x24,0x14,0x75,0x6,0x3b,0x4c,0x24,0x18,0x74,0x3c,0x8b,0x44,0x24,0x2c,0xc1,0xf8,0x10,0x39,0xc8,0x75,0x16,0x8b,0x44,0x24,0x28,0x8b,0x54,0x24,0x2c,0x8b,0x5c,0x24,0x20,0x1,0xc2,0x1,0xde,0x89,0x54,0x24,0x2c,0xeb,0x15,0x89,0xe8,0xc1,0xf8,0x10,0x39,0xf0,0x75,0xc,0x8b,0x5c,0x24,0x24,0x8b,0x44,0x24,0x1c,0x1,0xdd,0x1,0xc1,0x47,0x83,0xff,0x40,0x7c,0x82]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2cab5≤pc ∧ pc<0x2cafd then X86Routine.decodeAt bytes (pc-0x2cab5) else none
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x2cab5 => some (.control (.cmpMemory 6 ⟨some 4,none,0,20⟩),4)
  | 0x2cab9 => some (.control (.jumpZero false 6),2)
  | 0x2cabb => some (.control (.cmpMemory 1 ⟨some 4,none,0,24⟩),4)
  | 0x2cabf => some (.control (.jumpZero true 60),2)
  | 0x2cac1 => some (.control (.block (.load 0 ⟨some 4,none,0,44⟩)),4)
  | 0x2cac5 => some (.sar 0 16,3)
  | 0x2cac8 => some (.compareRegisters 0 1,2)
  | 0x2caca => some (.control (.jumpZero false 22),2)
  | 0x2cacc => some (.control (.block (.load 0 ⟨some 4,none,0,40⟩)),4)
  | 0x2cad0 => some (.control (.block (.load 2 ⟨some 4,none,0,44⟩)),4)
  | 0x2cad4 => some (.control (.block (.load 3 ⟨some 4,none,0,32⟩)),4)
  | 0x2cad8 => some (.control (.block (.arithmetic (.add 2 0))),2)
  | 0x2cada => some (.control (.block (.arithmetic (.add 6 3))),2)
  | 0x2cadc => some (.control (.block (.store ⟨some 4,none,0,44⟩ 2)),4)
  | 0x2cae0 => some (.jump 21,2)
  | 0x2cae2 => some (.control (.block (.legacy (.mov 0 5))),2)
  | 0x2cae4 => some (.sar 0 16,3)
  | 0x2cae7 => some (.compareRegisters 0 6,2)
  | 0x2cae9 => some (.control (.jumpZero false 12),2)
  | 0x2caeb => some (.control (.block (.load 3 ⟨some 4,none,0,36⟩)),4)
  | 0x2caef => some (.control (.block (.load 0 ⟨some 4,none,0,28⟩)),4)
  | 0x2caf3 => some (.control (.block (.arithmetic (.add 5 3))),2)
  | 0x2caf5 => some (.control (.block (.arithmetic (.add 1 0))),2)
  | 0x2caf7 => some (.addImmediate 7 1,1)
  | 0x2caf8 => some (.compareRegister 7 64,3)
  | 0x2cafb => some (.jumpSigned 3 (-126),2)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def localWord (s : X86Memory.State) (off : Word) := load32 s.memory (s.regs 4+off)
def atEnd (s : X86Memory.State) : Prop := s.regs 6=localWord s 20 ∧ s.regs 1=localWord s 24
instance (s : X86Memory.State) : Decidable (atEnd s) := inferInstanceAs (Decidable (_∧_))
def gate (s : X86Memory.State) : X86Control.State :=
  ⟨s,some (if s.regs 6=localWord s 20 then compare32 (s.regs 1) (localWord s 24)
    else compare32 (s.regs 6) (localWord s 20)),if atEnd s then 0x2cafd else 0x2cac1⟩
def takeX (s : X86Memory.State) : Prop := (localWord s 44).sshiftRight 16=s.regs 1
instance (s : X86Memory.State) : Decidable (takeX s) := inferInstanceAs (Decidable (_=_))
def takeY (s : X86Memory.State) : Prop := (s.regs 5).sshiftRight 16=s.regs 6
instance (s : X86Memory.State) : Decidable (takeY s) := inferInstanceAs (Decidable (_=_))
def x1 (s : X86Memory.State) := put s 0 (localWord s 44)
def x2 (s : X86Memory.State) := put (x1 s) 0 ((localWord s 44).sshiftRight 16)
def xcheck (s : X86Memory.State) : X86Control.State :=
  ⟨x2 s,some (compare32 ((localWord s 44).sshiftRight 16) (s.regs 1)),if takeX s then 0x2cacc else 0x2cae2⟩
def y1 (s : X86Memory.State) := put s 0 (s.regs 5)
def y2 (s : X86Memory.State) := put (y1 s) 0 ((s.regs 5).sshiftRight 16)
def ycheck (s : X86Memory.State) : X86Control.State :=
  ⟨y2 s,some (compare32 ((s.regs 5).sshiftRight 16) (s.regs 6)),if takeY s then 0x2caeb else 0x2caf7⟩
def a1 (s : X86Memory.State) := put s 0 (localWord s 40)
def a2 (s : X86Memory.State) := put (a1 s) 2 (localWord s 44)
def a3 (s : X86Memory.State) := put (a2 s) 3 (localWord s 32)
def a4 (s : X86Memory.State) := put (a3 s) 2 (localWord s 44+localWord s 40)
def a5 (s : X86Memory.State) := put (a4 s) 6 (s.regs 6+localWord s 32)
def a6 (s : X86Memory.State) : X86Memory.State :=
  {a5 s with memory:=store32 s.memory (s.regs 4+44) (localWord s 44+localWord s 40)}
def xadvanced (s : X86Memory.State) : X86Control.State := ⟨a6 s,none,0x2caf7⟩
def b1 (s : X86Memory.State) := put s 3 (localWord s 36)
def b2 (s : X86Memory.State) := put (b1 s) 0 (localWord s 28)
def b3 (s : X86Memory.State) := put (b2 s) 5 (s.regs 5+localWord s 36)
def b4 (s : X86Memory.State) := put (b3 s) 1 (s.regs 1+localWord s 28)
def yadvanced (s : X86Memory.State) : X86Control.State := ⟨b4 s,none,0x2caf7⟩
def incremented (s : X86Memory.State) := put s 7 (s.regs 7+1)
def counted (s : X86Memory.State) : X86Control.State :=
  ⟨incremented s,some (compare32 (s.regs 7+1) 64),
    if (s.regs 7+1).toInt<64 then 0x2ca7f else 0x2cafd⟩

theorem xcheck_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 4 ⟨s,f,0x2cac1⟩ (xcheck s) := by
  have path : X86Routine.Prefix listed [] 4 ⟨s,f,0x2cac1⟩ (xcheck s) := by
    apply X86Routine.Prefix.step (middle := ⟨x1 s,f,0x2cac5⟩) (by simp) (by rfl) (by
      by_cases h : takeX s <;> simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags,BitVec.sub_eq_iff_eq_add,PlayerHeight.cmp_ge_prop,localWord,xcheck,x2,x1,takeX,compare32])
    apply X86Routine.Prefix.step (middle := ⟨x2 s,none,0x2cac8⟩) (by simp) (by rfl) (by
      by_cases h : takeX s <;> simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags,BitVec.sub_eq_iff_eq_add,PlayerHeight.cmp_ge_prop,localWord,xcheck,x2,x1,takeX,compare32])
    apply X86Routine.Prefix.step (middle := ⟨x2 s,some (compare32 ((localWord s 44).sshiftRight 16) (s.regs 1)),0x2caca⟩) (by simp) (by rfl) (by
      by_cases h : takeX s <;> simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags,BitVec.sub_eq_iff_eq_add,PlayerHeight.cmp_ge_prop,localWord,xcheck,x2,x1,takeX,compare32])
    apply X86Routine.Prefix.step (middle := xcheck s) (by simp) (by rfl) (by
      by_cases h : takeX s <;> simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags,BitVec.sub_eq_iff_eq_add,PlayerHeight.cmp_ge_prop,localWord,xcheck,x2,x1,takeX,compare32])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

theorem ycheck_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 4 ⟨s,f,0x2cae2⟩ (ycheck s) := by
  have path : X86Routine.Prefix listed [] 4 ⟨s,f,0x2cae2⟩ (ycheck s) := by
    apply X86Routine.Prefix.step (middle := ⟨y1 s,f,0x2cae4⟩) (by simp) (by rfl) (by
      by_cases h : takeY s <;> simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags,BitVec.sub_eq_iff_eq_add,PlayerHeight.cmp_ge_prop,localWord,ycheck,y2,y1,takeY,compare32])
    apply X86Routine.Prefix.step (middle := ⟨y2 s,none,0x2cae7⟩) (by simp) (by rfl) (by
      by_cases h : takeY s <;> simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags,BitVec.sub_eq_iff_eq_add,PlayerHeight.cmp_ge_prop,localWord,ycheck,y2,y1,takeY,compare32])
    apply X86Routine.Prefix.step (middle := ⟨y2 s,some (compare32 ((s.regs 5).sshiftRight 16) (s.regs 6)),0x2cae9⟩) (by simp) (by rfl) (by
      by_cases h : takeY s <;> simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags,BitVec.sub_eq_iff_eq_add,PlayerHeight.cmp_ge_prop,localWord,ycheck,y2,y1,takeY,compare32])
    apply X86Routine.Prefix.step (middle := ycheck s) (by simp) (by rfl) (by
      by_cases h : takeY s <;> simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags,BitVec.sub_eq_iff_eq_add,PlayerHeight.cmp_ge_prop,localWord,ycheck,y2,y1,takeY,compare32])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

theorem xadvanced_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 7 ⟨s,f,0x2cacc⟩ (xadvanced s) := by
  have path : X86Routine.Prefix listed [] 7 ⟨s,f,0x2cacc⟩ (xadvanced s) := by
    apply X86Routine.Prefix.step (middle := ⟨a1 s,f,0x2cad0⟩) (by simp) (by rfl) (by
      simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags,BitVec.sub_eq_iff_eq_add,PlayerHeight.cmp_ge_prop,localWord,xadvanced,a6,a5,a4,a3,a2,a1])
    apply X86Routine.Prefix.step (middle := ⟨a2 s,f,0x2cad4⟩) (by simp) (by rfl) (by
      simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags,BitVec.sub_eq_iff_eq_add,PlayerHeight.cmp_ge_prop,localWord,xadvanced,a6,a5,a4,a3,a2,a1])
    apply X86Routine.Prefix.step (middle := ⟨a3 s,f,0x2cad8⟩) (by simp) (by rfl) (by
      simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags,BitVec.sub_eq_iff_eq_add,PlayerHeight.cmp_ge_prop,localWord,xadvanced,a6,a5,a4,a3,a2,a1])
    apply X86Routine.Prefix.step (middle := ⟨a4 s,none,0x2cada⟩) (by simp) (by rfl) (by
      simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags,BitVec.sub_eq_iff_eq_add,PlayerHeight.cmp_ge_prop,localWord,xadvanced,a6,a5,a4,a3,a2,a1])
    apply X86Routine.Prefix.step (middle := ⟨a5 s,none,0x2cadc⟩) (by simp) (by rfl) (by
      simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags,BitVec.sub_eq_iff_eq_add,PlayerHeight.cmp_ge_prop,localWord,xadvanced,a6,a5,a4,a3,a2,a1])
    apply X86Routine.Prefix.step (middle := ⟨a6 s,none,0x2cae0⟩) (by simp) (by rfl) (by
      simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags,BitVec.sub_eq_iff_eq_add,PlayerHeight.cmp_ge_prop,localWord,xadvanced,a6,a5,a4,a3,a2,a1])
    apply X86Routine.Prefix.step (middle := xadvanced s) (by simp) (by rfl) (by
      simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags,BitVec.sub_eq_iff_eq_add,PlayerHeight.cmp_ge_prop,localWord,xadvanced,a6,a5,a4,a3,a2,a1])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

theorem yadvanced_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 4 ⟨s,f,0x2caeb⟩ (yadvanced s) := by
  have path : X86Routine.Prefix listed [] 4 ⟨s,f,0x2caeb⟩ (yadvanced s) := by
    apply X86Routine.Prefix.step (middle := ⟨b1 s,f,0x2caef⟩) (by simp) (by rfl) (by
      simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags,BitVec.sub_eq_iff_eq_add,PlayerHeight.cmp_ge_prop,localWord,yadvanced,b4,b3,b2,b1])
    apply X86Routine.Prefix.step (middle := ⟨b2 s,f,0x2caf3⟩) (by simp) (by rfl) (by
      simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags,BitVec.sub_eq_iff_eq_add,PlayerHeight.cmp_ge_prop,localWord,yadvanced,b4,b3,b2,b1])
    apply X86Routine.Prefix.step (middle := ⟨b3 s,none,0x2caf5⟩) (by simp) (by rfl) (by
      simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags,BitVec.sub_eq_iff_eq_add,PlayerHeight.cmp_ge_prop,localWord,yadvanced,b4,b3,b2,b1])
    apply X86Routine.Prefix.step (middle := yadvanced s) (by simp) (by rfl) (by
      simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags,BitVec.sub_eq_iff_eq_add,PlayerHeight.cmp_ge_prop,localWord,yadvanced,b4,b3,b2,b1])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

theorem counted_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 3 ⟨s,f,0x2caf7⟩ (counted s) := by
  have path : X86Routine.Prefix listed [] 3 ⟨s,f,0x2caf7⟩ (counted s) := by
    apply X86Routine.Prefix.step (middle := ⟨incremented s,none,0x2caf8⟩) (by simp) (by rfl) (by
      by_cases h : (s.regs 7+1).toInt<64 <;> simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags,BitVec.sub_eq_iff_eq_add,PlayerHeight.cmp_ge_prop,localWord,counted,incremented,PlayerArmor.cmp_lt])
    apply X86Routine.Prefix.step (middle := ⟨incremented s,some (compare32 (s.regs 7+1) 64),0x2cafb⟩) (by simp) (by rfl) (by
      by_cases h : (s.regs 7+1).toInt<64 <;> simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags,BitVec.sub_eq_iff_eq_add,PlayerHeight.cmp_ge_prop,localWord,counted,incremented,PlayerArmor.cmp_lt])
    apply X86Routine.Prefix.step (middle := counted s) (by simp) (by rfl) (by
      by_cases h : (s.regs 7+1).toInt<64 <;> simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags,BitVec.sub_eq_iff_eq_add,PlayerHeight.cmp_ge_prop,localWord,counted,incremented,PlayerArmor.cmp_lt])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

/-- End-cell equality is tested before either axis; an end cell is not counted
or advanced, even when an intercept happens to match a grid boundary. -/
theorem gate_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n≤4, X86Routine.Prefix program [] n ⟨s,f,0x2cab5⟩ (gate s) := by
  by_cases hx : s.regs 6=localWord s 20
  · have run : X86Routine.Prefix listed [] 4 ⟨s,f,0x2cab5⟩ (gate s) := by
      apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 6) (localWord s 20)),0x2cab9⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.Address.eval,localWord])
      apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 6) (localWord s 20)),0x2cabb⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,hx,compare32])
      apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 1) (localWord s 24)),0x2cabf⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.Address.eval,localWord])
      apply X86Routine.Prefix.step (middle := gate s) (by simp) (by rfl) (by
        by_cases hy : s.regs 1=localWord s 24 <;>
          simp_all [gate,atEnd,X86Routine.execute,X86Control.execute,compare32,BitVec.sub_eq_iff_eq_add])
      exact .nil _
    exact ⟨4,by omega,run.transfer program [] decoded (by simp)⟩
  · have run : X86Routine.Prefix listed [] 2 ⟨s,f,0x2cab5⟩ (gate s) := by
      apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 6) (localWord s 20)),0x2cab9⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.Address.eval,localWord])
      apply X86Routine.Prefix.step (middle := gate s) (by simp) (by rfl) (by
        simp_all [gate,atEnd,X86Routine.execute,X86Control.execute,compare32,BitVec.sub_eq_iff_eq_add])
      exact .nil _
    exact ⟨2,by omega,run.transfer program [] decoded (by simp)⟩

def selected (s : X86Memory.State) : X86Control.State :=
  if takeX s then xadvanced (xcheck s).core
  else if takeY (xcheck s).core then yadvanced (ycheck (xcheck s).core).core
  else ycheck (xcheck s).core

theorem selected_execution (s : X86Memory.State) (f : Option Flags) :
    (∃ n≤12, X86Routine.Prefix program [] n ⟨s,f,0x2cac1⟩ (selected s)) ∧
    (selected s).pc=0x2caf7 := by
  have x := xcheck_execution s f
  by_cases hx : takeX s
  · have a := xadvanced_execution (xcheck s).core (xcheck s).flags
    rw [OriginalPathXStep.at_pc _ _ (show (xcheck s).pc=0x2cacc by simp [xcheck,hx])] at a
    exact ⟨⟨11,by omega,by simpa only [selected,if_pos hx] using OriginalGroupBounds.prefix_join x a⟩,by simp [selected,hx,xadvanced]⟩
  · have y := ycheck_execution (xcheck s).core (xcheck s).flags
    rw [OriginalPathXStep.at_pc _ _ (show (xcheck s).pc=0x2cae2 by simp [xcheck,hx])] at y
    by_cases hy : takeY (xcheck s).core
    · have b := yadvanced_execution (ycheck (xcheck s).core).core (ycheck (xcheck s).core).flags
      rw [OriginalPathXStep.at_pc _ _ (show (ycheck (xcheck s).core).pc=0x2caeb by simp [ycheck,hy])] at b
      exact ⟨⟨12,by omega,by simpa only [selected,if_neg hx,if_pos hy] using
        OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join x y) b⟩,by simp [selected,hx,hy,yadvanced]⟩
    · exact ⟨⟨8,by omega,by simpa only [selected,if_neg hx,if_neg hy] using OriginalGroupBounds.prefix_join x y⟩,
        by simp [selected,hx,hy,ycheck]⟩

def result (s : X86Memory.State) : X86Control.State :=
  if atEnd s then gate s else counted (selected s).core

/-- Exact original branches: endpoint, X priority, Y, stall, then signed loop
count. Counter interpretation is restricted separately to the legal 0..63 range. -/
theorem execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n≤19, X86Routine.Prefix program [] n ⟨s,f,0x2cab5⟩ (result s) := by
  obtain ⟨n,hn,g⟩ := gate_execution s f
  by_cases ended : atEnd s
  · exact ⟨n,by omega,by simpa only [result,if_pos ended] using g⟩
  · obtain ⟨⟨m,hm,a⟩,pc⟩ := selected_execution s (gate s).flags
    have seam : (⟨s,(gate s).flags,0x2cac1⟩ : X86Control.State)=gate s := by simp [gate,ended]
    rw [seam] at a
    have b := counted_execution (selected s).core (selected s).flags
    rw [OriginalPathXStep.at_pc _ _ pc] at b
    exact ⟨n+m+3,by omega,by simpa only [result,if_neg ended] using
      OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join g a) b⟩
end Doom.Proofs.OriginalPathAdvance
