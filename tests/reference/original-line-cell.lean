import Doom.Proofs.OriginalLineCell
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
namespace LineCellFixtures
example : X86Routine.decodeAt [0x0f,0xbf,0x04,0x42] 0=
    some (.loadSignedHalf 0 ⟨some 2,some 0,1,0⟩,4) := by decide
example : X86Routine.decodeAt [0x0f,0xbf,0x02] 0=
    some (.control (.block (.legacy (.movsx16 0 2 0))),3) := by decide
example : X86Routine.decodeAt [0x0f,0xbf,0x04] 0=none := by decide
example : X86Routine.decodeAt [0x0f,0xbf,0xc0] 0=none := by decide

-- Table entry 4 points to word 100; the list starts with the real leading zero.
def memory (seen : Bool) : Memory :=
  [(0x2c100,0x600400),(0x2c10c,0x600800),(0x600408,100),
   (0x6008c8,0x00070000),(0x6008cc,0xffff),(0x2c120,0x601000),
   (0x13580,42),(0x601036,if seen then 42 else 41),(0x6011e8,41),
   (0x600200,0x2c5f0)].foldl (fun m (a,v) => store32 m a v) (fun _ => 0)
def fixture (seen : Bool) : X86Memory.State :=
  ⟨fun r => if r=0 then 1 else if r=2 then 1 else if r=3 then 3 else if r=4 then 0x600200 else 0,memory seen⟩
example : OriginalLineCell.Inputs (fixture false) 1 1 3 100 0x600400 0x600800 := by
  constructor <;> decide
example : (OriginalLineCell.lookup (fixture false)).core.regs 2=(0x6008c8#32) := by decide
example : (OriginalLineCell.first (fixture false)).pc=0x2c5f0 := by decide
example : (OriginalLineCell.first (fixture false)).core.regs 0=(0x601000#32) := by decide
example : load32 (OriginalLineCell.first (fixture false)).core.memory 0x601036=(42#32) := by decide
example : load32 (OriginalLineCell.first (fixture false)).core.memory 0x6001fc=(0x2c578#32) := by decide
example : (OriginalLineCell.first (fixture true)).pc=0x2c57f := by decide
example : (OriginalLineCell.first (fixture true)).core.regs 2=(0x6008ca#32) := by decide
example : (OriginalLineCell.visit (OriginalLineCell.first (fixture true)).core).core.regs 0=(0x6011b2#32) := by decide
example : (OriginalLineCell.header (put (fixture false) 2 0x6008cc)).pc=0x2c587 := by decide
example : ((0xfffe#16).signExtend 32)=(0xfffffffe#32) := by decide
example : ((0x8000#16).signExtend 32)=(0xffff8000#32) := by decide
example : ((0x7fff#16).signExtend 32)=(32767#32) := by decide

-- The store can alias the indirect-call operand in arbitrary machine memory.
def aliasState : X86Memory.State :=
  ⟨fun r => if r=0 then 0x600200-54 else if r=4 then 0x600200 else if r=7 then 0x2c600 else 0,
   store32 (fun _ => 0) 0x600200 0x2c5f0⟩
example : (OriginalLineCell.callback aliasState none).pc=0x2c600 := by decide
example : (OriginalLineCell.resumed (put (fixture false) 0 0)).pc=0x2c58c := by decide
example : (OriginalLineCell.resumed (put (fixture false) 0 1)).pc=0x2c57c := by decide
end LineCellFixtures
