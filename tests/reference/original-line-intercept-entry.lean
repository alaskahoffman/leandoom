import Doom.Proofs.OriginalLineInterceptEntry
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control OriginalLineInterceptEntry
namespace LineInterceptEntryFixtures
-- Coordinates differ on purpose: wide traces test the wall vertex, short traces
-- test the trace start. Exact ±16-map-unit boundaries are short.
def memory (dx dy : Int32) : Memory :=
  [(0x2ba10,123),(0x2ba14,456),(0x2ba18,dx.toBitVec),(0x2ba1c,dy.toBitVec),
   (0x600200,0x600400),(0x600400,789),(0x600404,987)].foldl
    (fun m (a,v) => store32 m a v) (fun _ => 0)
def fixture (dx dy : Int32) : X86Memory.State :=
  ⟨fun r => if r=0 then 0x600200 else if r=4 then 0x600100 else 42,memory dx dy⟩
def trace (dx dy : Int32) : Collision.Divline := ⟨⟨123⟩,⟨456⟩,⟨dx⟩,⟨dy⟩⟩
def wall : Collision.Line := { (default : Collision.Line) with x:=⟨789⟩,y:=⟨987⟩ }
example : (trace 1048576 (-1048576)).usesDivlineTest=false := by decide
example : (trace (-1048576) 1048576).usesDivlineTest=false := by decide
example : (trace 1048577 0).usesDivlineTest=true := by decide
example : (trace 0 1048577).usesDivlineTest=true := by decide
example : (trace (-1048577) 0).usesDivlineTest=true := by decide
example : (trace 0 (-1048577)).usesDivlineTest=true := by decide
example : (first (fixture 1048576 (-1048576))).pc=0x2c010 := by decide
example : (first (fixture 0 (-1048577))).pc=0x2c1e0 := by decide
example : (first (fixture 0 (-1048577))).core.regs 0=(789#32) := by decide
example : (first (fixture 0 (-1048577))).core.regs 2=(987#32) := by decide
example : (first (fixture 1048576 (-1048576))).core.regs 0=(123#32) := by decide
example : (first (fixture 1048576 (-1048576))).core.regs 2=(456#32) := by decide
example : (first (fixture 0 (-1048577))).core.regs 3=(0x2ba10#32) := by decide
example : (first (fixture 1048576 (-1048576))).core.regs 3=(0x600200#32) := by decide
example : load32 (first (fixture 0 (-1048577))).core.memory 0x6000d8=(0x2c637#32) := by decide
example : load32 (first (fixture 1048576 (-1048576))).core.memory 0x6000d8=(0x2c65f#32) := by decide
example : Inputs (fixture 0 (-1048577)) (trace 0 (-1048577)) wall 0x600200 0x600400 := by
  constructor <;> try decide
  intro a ha off ho
  simp only [reads,List.mem_cons,List.not_mem_nil,or_false] at ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases ho with rfl|rfl|rfl|rfl|rfl <;> unfold BlockSummary.Apart <;> decide
end LineInterceptEntryFixtures
