import Doom.Proofs.OriginalLineFraction
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open OriginalInterceptVector

def trace : Collision.Divline := ⟨⟨0⟩,⟨0⟩,⟨65536⟩,⟨0⟩⟩
def wall : Collision.Divline := ⟨⟨32768⟩,⟨0⟩,⟨0⟩,⟨65536⟩⟩
def memory (sp : Word) : Memory :=
  store32 (store32 (store32 (store32 (store32 (store32 (store32 (store32 (store32
    (fun _ => 0) 0x600201 0) 0x600205 0) 0x600209 65536) 0x60020d 0)
    0x600301 32768) 0x600305 0) 0x600309 0) 0x60030d 65536) sp 0x4f000

def fixture (sp : Word) : X86Memory.State :=
  ⟨fun r => if r=0 then 0x600201 else if r=1 then 111 else if r=2 then 0x600301
    else if r=3 then 333 else if r=4 then sp else if r=5 then 555 else if r=6 then 666 else 777,
    memory sp⟩
example : (Collision.interceptVector trace wall).toOption=some ⟨32768⟩ := by decide
example : (result (fixture 0)).core.regs 0=(32768#32) := by decide
example : (result (fixture 0)).core.regs 4=(4#32) := by decide
example : (result (fixture 0)).core.regs 5=(555#32) := by decide
example : (result (fixture 0)).core.regs 7=(777#32) := by decide
example : (result (fixture 0)).pc=0x4f000 := by decide
example : (result (fixture 0x600103)).core.regs 0=(32768#32) := by decide
example : (result (fixture 0x600103)).core.regs 4=(0x600107#32) := by decide
example : load32 (result (fixture 0)).core.memory (0xffffffe8#32)=(0x2c32e#32) := by decide
example : load32 (result (fixture 0)).core.memory (0x600301#32)=(32768#32) := by decide

def parallel : Collision.Divline := ⟨⟨123⟩,⟨456⟩,⟨65536⟩,⟨0⟩⟩
example : (Collision.interceptVector trace parallel).toOption=some ⟨0⟩ := by decide
example : (Collision.interceptVector ⟨⟨0⟩,⟨0⟩,⟨256⟩,⟨0⟩⟩
    ⟨⟨2147483647⟩,⟨0⟩,⟨0⟩,⟨65536⟩⟩).toOption.map (fun v => v.raw.toBitVec)=some (0x7fffffff#32) := by decide
example : (Collision.interceptVector ⟨⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩⟩
    ⟨⟨33554432⟩,⟨0⟩,⟨0⟩,⟨1073741824⟩⟩).isOk=false := by decide

example : X86Routine.decodeAtWithSubFlags [0x29,0xc7] 0=some (.subRegistersWithFlags 7 0,2) := by decide
example : X86Routine.decodeAtWithSubFlags [0x2b,0xf8] 0=some (.subRegistersWithFlags 7 0,2) := by decide
example : compare32 (0x80000000#32) (1#32)=⟨false,false,true,some false⟩ := by decide
example : compare32 (0#32) (1#32)=⟨false,true,false,some true⟩ := by decide
example : compare32 (42#32) (42#32)=⟨true,false,false,some false⟩ := by decide

def mapLine : Collision.Line := {(default : Collision.Line) with x:=wall.x,y:=wall.y,dx:=wall.dx,dy:=wall.dy}
def callback : X86Memory.State :=
  ⟨fun r => if r=1 then 0x600401 else if r=4 then 0 else (fixture 0).regs r,
    store32 (store32 (store32 (store32 (store32 (store32 (store32 (store32 (store32
      (fun _ => 0) 0x600401 0x600501) 0x600409 0) 0x60040d 65536)
      0x600501 32768) 0x600505 0) 0x2ba10 0) 0x2ba14 0) 0x2ba18 65536) 0x2ba1c 0⟩
example : OriginalLineFraction.Inputs callback trace mapLine 0x600401 0x600501 := by
  constructor <;> try decide
  intro a ha off ho
  simp only [OriginalLineFraction.reads,List.mem_cons,List.not_mem_nil,or_false] at ha ho
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
example : (OriginalLineFraction.result callback).core.regs 0=(32768#32) := by decide
example : (OriginalLineFraction.result callback).pc=0x2c6bb := by decide
example : (OriginalLineFraction.result callback).core.regs 4=(0#32) := by decide
