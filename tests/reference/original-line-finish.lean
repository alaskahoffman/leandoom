import Doom.Proofs.OriginalLineFinish
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open OriginalLineFinish

def fixture (frac active back cur sp : Word) : X86Memory.State :=
  ⟨fun r => if r=0 then frac else if r=1 then 0x600401 else if r=4 then sp else BitVec.ofNat 32 r.val,
   store32 (store32 (store32 (store32 (store32 (store32 (store32 (store32 (store32
    (fun _ => 0) 0x2c024 active) 0x2c028 cur) 0x600433 back)
    (sp+16) 555) (sp+20) 666) (sp+24) 222) (sp+28) 111) (sp+32) 333) (sp+36) 0x4f000⟩

example : (result (fixture 0xffffffff 1 0 0x600801 0xfffffff1)).core.regs 0=(1#32) := by decide
example : load32 (result (fixture 0xffffffff 1 0 0x600801 0xfffffff1)).core.memory 0x2c028=(0x600801#32) := by decide
example : (result (fixture 65535 1 0 0x600801 0xfffffff1)).core.regs 0=(0#32) := by decide
example : load32 (result (fixture 65535 1 0 0x600801 0xfffffff1)).core.memory 0x2c028=(0x600801#32) := by decide
example : (result (fixture 65536 1 0 0x600801 0xfffffff1)).core.regs 0=(1#32) := by decide
example : load32 (result (fixture 65536 1 0 0x600801 0xfffffff1)).core.memory 0x2c028=(0x60080d#32) := by decide
example : load32 (result (fixture 65536 1 0 0x600801 0xfffffff1)).core.memory 0x600801=(65536#32) := by decide
example : load32 (result (fixture 65536 1 0 0x600801 0xfffffff1)).core.memory 0x600805=(1#32) := by decide
example : load32 (result (fixture 65536 1 0 0x600801 0xfffffff1)).core.memory 0x600809=(0x600401#32) := by decide
example : (result (fixture 1 0 0 0xfffffffa 0x600101)).core.regs 0=(1#32) := by decide
example : load32 (result (fixture 1 0 0 0xfffffffa 0x600101)).core.memory 0x2c028=(6#32) := by decide
example : (result (fixture 1 1 0x1234 0x600801 0xfffffff1)).core.regs 4=(25#32) := by decide
example : (result (fixture 1 1 0x1234 0x600801 0xfffffff1)).core.regs 5=(555#32) := by decide
example : (result (fixture 1 1 0x1234 0x600801 0xfffffff1)).pc=0x4f000 := by decide
-- Aliasing the saved EBP deliberately changes the restored register.
example : (result (fixture 123 0 0 0x600111 0x600101)).core.regs 5=(123#32) := by decide
-- The cursor store wins if the record itself aliases the cursor global.
example : load32 (result (fixture 123 0 0 0x2c028 0x600101)).core.memory 0x2c028=(0x2c034#32) := by decide

def hit : Collision.Intercept := ⟨⟨65536⟩,true,17⟩
def path (n : Nat) : Collision.PathResult := ⟨true,⟨⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩⟩,#[],Array.replicate n hit,#[]⟩
example : ((Collision.appendIntercept (path 127) hit).toOption.map fun r => r.collected.size)=some 128 := by decide
example : (Collision.appendIntercept (path 128) hit).isOk=false := by decide

-- Two prior equal-distance hits remain ahead of the newly inserted hit.
def firstHit : Collision.Intercept := ⟨⟨65536⟩,true,7⟩
def secondHit : Collision.Intercept := ⟨⟨65536⟩,true,8⟩
def resolve (h : Collision.Intercept) : Word :=
  if h.id=7 then 0x600501 else if h.id=8 then 0x600601 else 0x600401
def orderedState : X86Memory.State :=
  let s := fixture 65536 0 0 0x600819 0x600101
  {s with memory := store32 (store32 (store32 (store32 (store32 (store32 s.memory
    0x600801 65536) 0x600805 1) 0x600809 0x600501)
    0x60080d 65536) 0x600811 1) 0x600815 0x600601}
example : Encodes (result orderedState).core.memory (0x600801#32) resolve
    (#[firstHit,secondHit].push hit) := by
  apply append_encoded orderedState (0x600801#32) resolve #[firstHit,secondHit] hit
  · decide
  · intro i hi
    have cases : i=0 ∨ i=1 := by simp at hi; omega
    rcases cases with rfl|rfl
    · change RecordAt orderedState.memory (0x600801#32) firstHit (resolve firstHit)
      unfold RecordAt
      decide
    · change RecordAt orderedState.memory (0x60080d#32) secondHit (resolve secondHit)
      unfold RecordAt
      decide
  · decide
  · decide
  · decide
  · decide
  · intro off ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl <;> unfold Apart <;> decide
  · intro i hi off ho w hw
    have cases : i=0 ∨ i=1 := by simp at hi; omega
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho hw
    rcases cases with rfl|rfl <;> rcases ho with rfl|rfl|rfl <;>
      rcases hw with rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
