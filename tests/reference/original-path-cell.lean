import Doom.Proofs.E1M1PathCell
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
namespace PathCellFixtures

def bounds (x y : Int32) (w h : Nat) (sp : Word := 0x600201) : X86Memory.State :=
  ⟨fun r => if r=0 then x.toBitVec else if r=2 then y.toBitVec else if r=3 then 0x2c5f0
    else if r=4 then sp else if r=7 then 0x12345678 else 0,
   store32 (store32 (store32 (fun _ => 0) 0x2c0fc (BitVec.ofNat 32 w))
     0x2c110 (BitVec.ofNat 32 h)) sp 0x2ca94⟩
example : OriginalLineBounds.Inputs (bounds 16 10 17 11) 16 10 17 11 := by
  constructor <;> try decide
  intro a ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl <;> unfold BlockSummary.Apart <;> decide
example : Collision.pathCellInside 16 10 17 11=true := by decide
example : Collision.pathCellInside 17 10 17 11=false := by decide
example : (OriginalLineBounds.result (bounds 16 10 17 11)).pc=0x2c541 := by decide
example : (OriginalLineBounds.result (bounds 17 10 17 11)).pc=0x2ca94 := by decide
example : (OriginalLineBounds.result (bounds 0 (-1) 17 11)).core.regs 0=(1#32) := by decide
example : (OriginalLineBounds.result (bounds 0 0 0 11)).pc=0x2ca94 := by decide
example : (OriginalLineBounds.result (bounds 0 11 17 11)).pc=0x2ca94 := by decide
example : (OriginalLineBounds.result (bounds (-1) 0 17 11 1)).core.regs 4=(5#32) := by decide
example : (OriginalLineBounds.result (bounds (-1) 0 17 11 1)).core.regs 7=(0x12345678#32) := by decide
example : (OriginalLineBounds.result (bounds (-1) 0 17 11 1)).pc=0x2ca94 := by decide
-- Negative width must reject x=0; treating the encoded word as unsigned is wrong.
example : (OriginalLineBounds.result (bounds 0 0 2147483648 11)).pc=0x2ca94 := by decide

def dispatch (flags ret : Word) : X86Memory.State :=
  ⟨fun r => if r=0 then ret else if r=4 then 0x600200 else if r=6 then 17 else if r=1 then 11 else 0,
   store32 (fun _ => 0) 0x600240 flags⟩
example : (OriginalPathCell.firstVisit (dispatch 3 0)).pc=0x2c520 := by decide
example : (OriginalPathCell.firstVisit (dispatch 2 0)).pc=0x2c5a0 := by decide
example : (OriginalPathCell.firstVisit (dispatch 0 0)).pc=0x2cab5 := by decide
example : (OriginalPathCell.firstVisit (dispatch 0x100 0)).pc=0x2cab5 := by decide
example : (OriginalPathCell.afterLine (dispatch 3 0)).pc=0x2cb0b := by decide
example : (OriginalPathCell.afterLine (dispatch 3 1)).pc=0x2c5a0 := by decide
example : (OriginalPathCell.afterLine (dispatch 1 1)).pc=0x2cab5 := by decide
example : (OriginalPathCell.firstVisit (dispatch 3 0)).core.regs 0=(17#32) := by decide
example : (OriginalPathCell.firstVisit (dispatch 3 0)).core.regs 2=(11#32) := by decide
example : load32 (OriginalPathCell.firstVisit (dispatch 3 0)).core.memory 0x6001fc=(0x2ca94#32) := by decide
end PathCellFixtures
