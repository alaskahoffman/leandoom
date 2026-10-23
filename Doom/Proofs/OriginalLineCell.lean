import Doom.Proofs.OriginalLineBounds
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalLineCell
open Verification X86 X86Memory X86Control BlockSummary
def code : List UInt8 := [0xf,0xaf,0xd3,0x1,0xd0,0x8b,0x15,0x0,0xc1,0x2,0x0,0xf,0xbf,0x4,0x42,0x8b,0x15,0xc,0xc1,0x2,0x0,0x1,0xc0,0x1,0xc2,0xeb,0x23,0x6b,0xc0,0x3e,0x8b,0x1d,0x20,0xc1,0x2,0x0,0x1,0xd8,0x8b,0x3d,0x80,0x35,0x1,0x0,0x3b,0x78,0x36,0x74,0xa,0x89,0x78,0x36,0xff,0x14,0x24,0x85,0xc0,0x74,0x10,0x83,0xc2,0x2,0xf,0xbf,0x2,0x83,0xf8,0xff,0x75,0xd5]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2c541≤pc ∧ pc<0x2c587 then X86Routine.decodeAt bytes (pc-0x2c541) else none
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x2c541 => some (.multiplyRegister 2 3,3)
  | 0x2c544 => some (.control (.block (.arithmetic (.add 0 2))),2)
  | 0x2c546 => some (.control (.block (.load 2 ⟨none,none,0,0x2c100⟩)),6)
  | 0x2c54c => some (.loadSignedHalf 0 ⟨some 2,some 0,1,0⟩,4)
  | 0x2c550 => some (.control (.block (.load 2 ⟨none,none,0,0x2c10c⟩)),6)
  | 0x2c556 => some (.control (.block (.arithmetic (.add 0 0))),2)
  | 0x2c558 => some (.control (.block (.arithmetic (.add 2 0))),2)
  | 0x2c55a => some (.jump 35,2)
  | 0x2c55c => some (.multiplyImmediate 0 0 62,3)
  | 0x2c55f => some (.control (.block (.load 3 ⟨none,none,0,0x2c120⟩)),6)
  | 0x2c565 => some (.control (.block (.arithmetic (.add 0 3))),2)
  | 0x2c567 => some (.control (.block (.load 7 ⟨none,none,0,0x13580⟩)),6)
  | 0x2c56d => some (.control (.cmpMemory 7 ⟨some 0,none,0,54⟩),3)
  | 0x2c570 => some (.control (.jumpZero true 10),2)
  | 0x2c572 => some (.control (.block (.store ⟨some 0,none,0,54⟩ 7)),3)
  | 0x2c575 => some (.callMemory ⟨some 4,none,0,0⟩,3)
  | 0x2c578 => some (.control (.testWord 0 0),2)
  | 0x2c57a => some (.control (.jumpZero true 16),2)
  | 0x2c57c => some (.addImmediate 2 2,3)
  | 0x2c57f => some (.control (.block (.legacy (.movsx16 0 2 0))),3)
  | 0x2c582 => some (.compareRegister 0 0xffffffff,3)
  | 0x2c585 => some (.control (.jumpZero false (-43)),2)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def cellIndex (s : X86Memory.State) : Word := s.regs 0+s.regs 2*s.regs 3
def tableBase (s : X86Memory.State) := load32 s.memory 0x2c100
def listBase (s : X86Memory.State) := load32 s.memory 0x2c10c
def offset (s : X86Memory.State) := (load16 s.memory (tableBase s+(cellIndex s <<< 1))).signExtend 32
def l1 (s : X86Memory.State) := put s 2 (s.regs 2*s.regs 3)
def l2 (s : X86Memory.State) := put (l1 s) 0 (cellIndex s)
def l3 (s : X86Memory.State) := put (l2 s) 2 (tableBase s)
def l4 (s : X86Memory.State) := put (l3 s) 0 (offset s)
def l5 (s : X86Memory.State) := put (l4 s) 2 (listBase s)
def l6 (s : X86Memory.State) := put (l5 s) 0 (offset s+offset s)
def l7 (s : X86Memory.State) := put (l6 s) 2 (listBase s+(offset s+offset s))
def lookup (s : X86Memory.State) : X86Control.State := ⟨l7 s,none,0x2c57f⟩

theorem lookup_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 8 ⟨s,f,0x2c541⟩ (lookup s) := by
  have path : X86Routine.Prefix listed [] 8 ⟨s,f,0x2c541⟩ (lookup s) := by
    apply X86Routine.Prefix.step (middle := ⟨l1 s,none,0x2c544⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.add_assoc,lookup,l7,l6,l5,l4,l3,l2,l1,offset,cellIndex,tableBase,listBase])
    apply X86Routine.Prefix.step (middle := ⟨l2 s,none,0x2c546⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.add_assoc,lookup,l7,l6,l5,l4,l3,l2,l1,offset,cellIndex,tableBase,listBase])
    apply X86Routine.Prefix.step (middle := ⟨l3 s,none,0x2c54c⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.add_assoc,lookup,l7,l6,l5,l4,l3,l2,l1,offset,cellIndex,tableBase,listBase])
    apply X86Routine.Prefix.step (middle := ⟨l4 s,none,0x2c550⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.add_assoc,lookup,l7,l6,l5,l4,l3,l2,l1,offset,cellIndex,tableBase,listBase])
    apply X86Routine.Prefix.step (middle := ⟨l5 s,none,0x2c556⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.add_assoc,lookup,l7,l6,l5,l4,l3,l2,l1,offset,cellIndex,tableBase,listBase])
    apply X86Routine.Prefix.step (middle := ⟨l6 s,none,0x2c558⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.add_assoc,lookup,l7,l6,l5,l4,l3,l2,l1,offset,cellIndex,tableBase,listBase])
    apply X86Routine.Prefix.step (middle := ⟨l7 s,none,0x2c55a⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.add_assoc,lookup,l7,l6,l5,l4,l3,l2,l1,offset,cellIndex,tableBase,listBase])
    apply X86Routine.Prefix.step (middle := lookup s) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.add_assoc,lookup,l7,l6,l5,l4,l3,l2,l1,offset,cellIndex,tableBase,listBase])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

def item (s : X86Memory.State) : BitVec 16 := load16 s.memory (s.regs 2)
def itemWord (s : X86Memory.State) := (item s).signExtend 32
def h1 (s : X86Memory.State) := put s 0 (itemWord s)
def header (s : X86Memory.State) : X86Control.State :=
  ⟨h1 s,some (compare32 (itemWord s) 0xffffffff),if itemWord s=(0xffffffff#32) then 0x2c587 else 0x2c55c⟩

theorem header_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 3 ⟨s,f,0x2c57f⟩ (header s) := by
  have path : X86Routine.Prefix listed [] 3 ⟨s,f,0x2c57f⟩ (header s) := by
    apply X86Routine.Prefix.step (middle := ⟨h1 s,f,0x2c582⟩) (by simp) (by rfl) (by
      simp [h1,itemWord,item,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,blockPreservesFlags])
    apply X86Routine.Prefix.step (middle := ⟨h1 s,some (compare32 (itemWord s) 0xffffffff),0x2c585⟩) (by simp) (by rfl) (by
      simp [h1,X86Routine.execute,put,write])
    apply X86Routine.Prefix.step (middle := header s) (by simp) (by rfl) (by
      by_cases h : itemWord s=(0xffffffff#32) <;>
        simp [header,X86Routine.execute,X86Control.execute,cmp32_zero,h])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

def lineBase (s : X86Memory.State) := load32 s.memory 0x2c120
def lineAddress (s : X86Memory.State) := s.regs 0*62+lineBase s
def epoch (s : X86Memory.State) := load32 s.memory 0x13580
def already (s : X86Memory.State) : Prop := epoch s=load32 s.memory (lineAddress s+54)
instance (s : X86Memory.State) : Decidable (already s) := inferInstanceAs (Decidable (_=_))
def d1 (s : X86Memory.State) := put s 0 (s.regs 0*62)
def d2 (s : X86Memory.State) := put (d1 s) 3 (lineBase s)
def d3 (s : X86Memory.State) := put (d2 s) 0 (lineAddress s)
def d4 (s : X86Memory.State) := put (d3 s) 7 (epoch s)
def duplicateFlags (s : X86Memory.State) := some (compare32 (epoch s) (load32 s.memory (lineAddress s+54)))
def duplicate (s : X86Memory.State) : X86Control.State :=
  ⟨d4 s,duplicateFlags s,if already s then 0x2c57c else 0x2c572⟩

theorem duplicate_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 6 ⟨s,f,0x2c55c⟩ (duplicate s) := by
  have path : X86Routine.Prefix listed [] 6 ⟨s,f,0x2c55c⟩ (duplicate s) := by
    apply X86Routine.Prefix.step (middle := ⟨d1 s,none,0x2c55f⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.add_assoc,duplicateFlags,d4,d3,d2,d1,lineBase,lineAddress,epoch])
    apply X86Routine.Prefix.step (middle := ⟨d2 s,none,0x2c565⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.add_assoc,duplicateFlags,d4,d3,d2,d1,lineBase,lineAddress,epoch])
    apply X86Routine.Prefix.step (middle := ⟨d3 s,none,0x2c567⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.add_assoc,duplicateFlags,d4,d3,d2,d1,lineBase,lineAddress,epoch])
    apply X86Routine.Prefix.step (middle := ⟨d4 s,none,0x2c56d⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.add_assoc,duplicateFlags,d4,d3,d2,d1,lineBase,lineAddress,epoch])
    apply X86Routine.Prefix.step (middle := ⟨d4 s,duplicateFlags s,0x2c570⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.add_assoc,duplicateFlags,d4,d3,d2,d1,lineBase,lineAddress,epoch])
    apply X86Routine.Prefix.step (middle := duplicate s) (by simp) (by rfl) (by
      by_cases h : already s <;> simp_all [duplicate,duplicateFlags,already,X86Routine.execute,X86Control.execute,cmp32_zero])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

/-- Stamp before the indirect CALL. The CALL reads its target after the store. -/
def marked (s : X86Memory.State) : X86Memory.State :=
  {s with memory:=store32 s.memory (s.regs 0+(54#32)) (s.regs 7)}
def callback (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨X86Routine.pushWord (marked s) 0x2c578,f,(load32 (marked s).memory (s.regs 4)).toNat⟩

theorem callback_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 2 ⟨s,f,0x2c572⟩ (callback s f) := by
  have path : X86Routine.Prefix listed [] 2 ⟨s,f,0x2c572⟩ (callback s f) := by
    apply X86Routine.Prefix.step (middle := ⟨marked s,f,0x2c575⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.add_assoc,callback,marked,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle := callback s f) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.add_assoc,callback,marked,X86Routine.pushWord])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

def advance (s : X86Memory.State) : X86Control.State := ⟨put s 2 (s.regs 2+2),none,0x2c57f⟩

theorem advance_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 1 ⟨s,f,0x2c57c⟩ (advance s) := by
  have path : X86Routine.Prefix listed [] 1 ⟨s,f,0x2c57c⟩ (advance s) := by
    apply X86Routine.Prefix.step (middle := advance s) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.add_assoc,advance])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

def resumed (s : X86Memory.State) : X86Control.State :=
  ⟨s,some (logical32 (s.regs 0)),if s.regs 0=0 then 0x2c58c else 0x2c57c⟩
theorem resume_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 2 ⟨s,f,0x2c578⟩ (resumed s) := by
  have path : X86Routine.Prefix listed [] 2 ⟨s,f,0x2c578⟩ (resumed s) := by
    apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x2c57a⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute])
    apply X86Routine.Prefix.step (middle := resumed s) (by simp) (by rfl) (by
      by_cases h : s.regs 0=(0#32) <;> simp [resumed,X86Routine.execute,X86Control.execute,logical32,h])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

/-- The terminator is precisely the original signed-short -1. -/
theorem sentinel (v : BitVec 16) : v.signExtend 32=(0xffffffff#32) ↔ v=(0xffff#16) := by
  constructor
  · intro h
    apply BitVec.eq_of_toInt_eq
    have eq := congrArg BitVec.toInt h
    rw [BitVec.toInt_signExtend_of_le (by decide)] at eq
    exact eq
  · intro h
    subst v
    rfl

theorem lookup_observe (s : X86Memory.State) :
    (lookup s).core.regs 2=listBase s+(offset s+offset s) ∧
    (lookup s).core.memory=s.memory ∧ (lookup s).core.regs 4=s.regs 4 ∧
    (lookup s).pc=0x2c57f := by
  simp [lookup,l7,l6,l5,l4,l3,l2,l1,put,write]

theorem header_pc (s : X86Memory.State) :
    (header s).pc=if item s=(0xffff#16) then 0x2c587 else 0x2c55c := by
  simp only [header,itemWord,sentinel]

/-- Arbitrary nonnegative live coordinates have the same row-major word index. -/
theorem natural_bits (v : Int32) (h : 0≤v.toInt) :
    BitVec.ofNat 32 v.toInt.toNat=v.toBitVec := by
  have hi : v.toBitVec.toInt=(v.toBitVec.toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (BitVec.toInt_pos_iff.mp h)
  have eq : v.toInt.toNat=v.toBitVec.toNat := by rw [show v.toInt=v.toBitVec.toInt by rfl,hi]; simp
  simp [eq,BitVec.ofNat_toNat]

theorem live_index (s : X86Memory.State) (x y : Int32) (w : Nat)
    (hx : 0≤x.toInt) (hy : 0≤y.toInt)
    (ex : s.regs 0=x.toBitVec) (ey : s.regs 2=y.toBitVec) (ew : s.regs 3=BitVec.ofNat 32 w) :
    cellIndex s=BitVec.ofNat 32 (Collision.pathCellIndex x y w) := by
  simp only [cellIndex,Collision.pathCellIndex,ex,ey,ew,BitVec.ofNat_add,BitVec.ofNat_mul,
    natural_bits x hx,natural_bits y hy]
  exact BitVec.add_comm _ _

theorem short_nonnegative (n : Nat) (bound : n<32768) :
    (BitVec.ofNat 16 n).signExtend 32=BitVec.ofNat 32 n := by
  have hn : n<2^16 := by omega
  have nat : (BitVec.ofNat 16 n).toNat=n := by simp [Nat.mod_eq_of_lt hn]
  rw [BitVec.signExtend_eq_setWidth_of_msb_false
    (BitVec.msb_eq_false_iff_two_mul_lt.mpr (by rw [nat]; omega))]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth,nat]

/-- Representation at the lookup boundary. The list pointer addresses its leading
zero; no instruction here skips that historically visited linedef. -/
structure Inputs (s : X86Memory.State) (x y : Int32) (w off : Nat) (table lists : Word) : Prop where
  xNonneg : 0≤x.toInt
  yNonneg : 0≤y.toInt
  xReg : s.regs 0=x.toBitVec
  yReg : s.regs 2=y.toBitVec
  widthReg : s.regs 3=BitVec.ofNat 32 w
  tableGlobal : tableBase s=table
  listGlobal : listBase s=lists
  offsetWord : load16 s.memory (table+(BitVec.ofNat 32 (Collision.pathCellIndex x y w) <<< 1))=BitVec.ofNat 16 off
  offsetBound : off<32768

theorem live_lookup (s : X86Memory.State) (x y : Int32) (w off : Nat) (table lists : Word)
    (h : Inputs s x y w off table lists) :
    (lookup s).core.regs 2=lists+BitVec.ofNat 32 (off*2) := by
  rw [(lookup_observe s).1]
  unfold offset
  rw [live_index s x y w h.xNonneg h.yNonneg h.xReg h.yReg h.widthReg,
    h.tableGlobal,h.offsetWord,short_nonnegative off h.offsetBound,h.listGlobal]
  congr 1
  rw [BitVec.ofNat_mul]
  bv_decide

/-- The only write before a new line's callback is its valid-count stamp. -/
theorem callback_observe (s : X86Memory.State) (f : Option Flags)
    (targetSafe : Apart (s.regs 4) (s.regs 0+(54#32)))
    (markSafe : Apart (s.regs 0+(54#32)) (s.regs 4-(4#32))) :
    (callback s f).core.regs 0=s.regs 0 ∧
    (callback s f).core.regs 2=s.regs 2 ∧
    (callback s f).core.regs 4=s.regs 4-(4#32) ∧
    load32 (callback s f).core.memory (s.regs 4-(4#32))=0x2c578 ∧
    load32 (callback s f).core.memory (s.regs 0+(54#32))=s.regs 7 ∧
    (callback s f).pc=(load32 s.memory (s.regs 4)).toNat := by
  simp [callback,marked,X86Routine.pushWord,put,write,load_store,
    load_store_apart _ _ _ _ markSafe,load_store_apart _ _ _ _ targetSafe]

/-- Other words survive the stamp and the real callback return-address push. -/
theorem callback_frame (s : X86Memory.State) (f : Option Flags) (a : Word)
    (stamp : Apart a (s.regs 0+(54#32))) (stack : Apart a (s.regs 4-(4#32))) :
    load32 (callback s f).core.memory a=load32 s.memory a := by
  change load32 (store32 (store32 s.memory (s.regs 0+(54#32)) _) (s.regs 4-(4#32)) _) a=_
  rw [load_store_apart _ _ _ _ stack,load_store_apart _ _ _ _ stamp]

/-- One list item: sentinel, duplicate skip, or the real callback entry. -/
def visit (s : X86Memory.State) : X86Control.State :=
  let h := header s
  if itemWord s=(0xffffffff#32) then h
  else let d := duplicate h.core
       if already h.core then advance d.core else callback d.core d.flags

/-- A duplicate consumes one signed-short entry without changing any memory. -/
theorem skip_observe (s : X86Memory.State) (last : itemWord s≠(0xffffffff#32))
    (seen : already (header s).core) :
    (visit s).core.memory=s.memory ∧
    (visit s).core.regs 2=s.regs 2+2 ∧
    (visit s).pc=0x2c57f := by
  simp only [visit,if_neg last,if_pos seen]
  simp [advance,duplicate,d4,d3,d2,d1,header,h1,put,write]

theorem visit_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤11 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2c57f⟩ (visit s) := by
  have a := header_execution s f
  by_cases last : itemWord s=(0xffffffff#32)
  · exact ⟨3,by omega,by simpa only [visit,if_pos last] using a⟩
  · have hp : (header s).pc=0x2c55c := by simp [header,last]
    have b := duplicate_execution (header s).core (header s).flags
    rw [OriginalPathXStep.at_pc _ _ hp] at b
    have ab := OriginalGroupBounds.prefix_join a b
    by_cases seen : already (header s).core
    · have dp : (duplicate (header s).core).pc=0x2c57c := by simp [duplicate,seen]
      have c := advance_execution (duplicate (header s).core).core (duplicate (header s).core).flags
      rw [OriginalPathXStep.at_pc _ _ dp] at c
      exact ⟨10,by omega,by simpa only [visit,if_neg last,if_pos seen] using OriginalGroupBounds.prefix_join ab c⟩
    · have dp : (duplicate (header s).core).pc=0x2c572 := by simp [duplicate,seen]
      have c := callback_execution (duplicate (header s).core).core (duplicate (header s).core).flags
      rw [OriginalPathXStep.at_pc _ _ dp] at c
      exact ⟨11,by omega,by simpa only [visit,if_neg last,if_neg seen] using OriginalGroupBounds.prefix_join ab c⟩

def first (s : X86Memory.State) := visit (lookup s).core

theorem first_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤19 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2c541⟩ (first s) := by
  have a := lookup_execution s f
  obtain ⟨n,hn,b⟩ := visit_execution (lookup s).core none
  exact ⟨8+n,by omega,OriginalGroupBounds.prefix_join a b⟩

end Doom.Proofs.OriginalLineCell
