import Doom.Proofs.OriginalGroupScan
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
open Doom.Verification Doom.Proofs X86 X86Memory X86Control BlockSummary OriginalGroupStep OriginalGroupScan
-- Count-word overlap is an actual counterexample to omitting the frame condition.
def aliasesCount : X86Memory.State :=
  let m : Memory := fun _ => 0
  let m := store32 m 0x2c134 2
  let m := store32 m 0x60012e 0x600900
  let m := store32 m 0x600100 0x600200
  let m := store32 m 0x600104 0x600208
  let m := store32 m 0x600204 1
  let m := store32 m 0x60020c 2
  ⟨fun r => if r=1 then 0x600100 else if r=4 then 0x600800 else if r=5 then 0x600900
    else if r=6 then 0x2c134 else 0,m⟩
example : (load32 aliasesCount.memory 0x2c134).toNat=2 ∧
    (load32 (body aliasesCount).core.memory 0x2c134).toNat=0x600100 := by decide +kernel
example : ¬CountSafe aliasesCount := by
  intro h
  have same : aliasesCount.regs 6=(0x2c134#32) := rfl
  have bad := h.output (0 : Fin 4) (0 : Fin 4)
  exact bad (by rw [same]; rfl)
-- A skipped line still advances the record/index, but does not consume output.
def skipped : X86Memory.State :=
  ⟨fun r => if r=1 then 0x600100 else if r=4 then 0x600800 else if r=5 then 0x600900
    else if r=6 then 0x610000 else 0,store32 (fun _ => 0) 0x2c134 2⟩
example : hit skipped=false ∧ (body skipped).core.regs 6=0x610000 ∧
    (body skipped).core.regs 1=0x60013e ∧ (body skipped).core.regs 7=1 ∧
    (body skipped).pc=0x2e676 ∧ (body (body skipped).core).pc=0x2e6af := by decide +kernel
-- Selected self-edge emits only once; the output capacity is measured in lines.
def selfEdge : X86Memory.State :=
  { skipped with memory := store32 (store32 skipped.memory 0x60012e 0x600900) 0x600132 0x600900 }
example : hit selfEdge=true ∧ (body selfEdge).core.regs 6=0x610004 ∧
    load32 (body selfEdge).core.memory 0x610000=0x600100 := by decide +kernel
-- Empty-count entry terminates without visiting the scan body.
def empty : X86Memory.State := ⟨fun _ => 0,fun _ => 0⟩
example : X86Routine.run program [0x2e6af] 6 ⟨empty,none,0x2e661⟩=some (OriginalGroupLines.entry empty) := by
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path (OriginalGroupLines.entry_execution empty none)
  have path := path.transfer program [0x2e6af] selection_agrees (by
    intro pc hp
    simp only [List.mem_singleton]
    intro eq; subst pc; exact hp (by decide))
  have pc : (OriginalGroupLines.entry empty).pc=0x2e6af := by decide +kernel
  exact path.finish (fuel:=0) (by simp [X86Routine.run,pc]) 6 (by omega)
-- The 43-instruction bound is achieved by a back-side match and both vertices
-- successively raising both maxima (11 instructions per helper).
def worst : X86Memory.State :=
  let m := store32 skipped.memory 0x600132 0x600900
  let m := store32 m 0x600100 0x600200
  let m := store32 m 0x600104 0x600208
  let m := store32 m 0x600200 1
  let m := store32 m 0x600204 1
  let m := store32 m 0x600208 2
  let m := store32 m 0x60020c 2
  {skipped with memory := m}
example : ∃ n, n≤43 ∧ X86Routine.Prefix program [] n ⟨worst,none,0x2e676⟩ (body worst) := iteration_path worst none
example : (body worst).core.regs 6=0x610004 ∧
    load32 (body worst).core.memory 0x600800=2 ∧ load32 (body worst).core.memory 0x60080c=2 := by decide +kernel
