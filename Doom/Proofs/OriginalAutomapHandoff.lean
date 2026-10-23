import Doom.Proofs.OriginalAutomapFrame
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 600000
namespace Doom.Proofs.AutomapStop
open Verification X86 X86Memory X86Control BlockSummary

/-- Complete cache unloading, without assuming the notification's type. -/
theorem handoff_prefix (s : X86Memory.State) (f : Option Flags) (h : UnloadInputs (stopUnload s)) :
    ∃ n, n ≤ 216 ∧ X86Routine.Prefix program [0x39af8] n ⟨s,f,0x24f90⟩
      ⟨stopResponder s,some (logical32 0),0x39aa0⟩ := by
  obtain ⟨n,hn,unload⟩ := unload_execution (stopUnload s) f h
  have path := append_path (append_path (stop_prologue s f) unload) (stop_event_call s)
  have path := path.transfer program [0x39af8] (fun _ _ => rfl) (by
    intro pc hp; simp only [List.mem_singleton]; intro eq; subst pc; exact hp (by decide))
  exact ⟨_,by omega,path⟩

def dosResponderResult (s : X86Memory.State) : X86Control.State :=
  ⟨put (responderStart s).core 2 0,some (compare32 0 1),0x39af8⟩

/-- The stored DOS notification is a keydown, so it takes this branch. -/
theorem dos_responder (s : X86Memory.State) (f : Option Flags)
    (kind : load32 (responderSaved s) (s.regs 0)=0) :
    X86Routine.run program [0x39af8] 10 ⟨s,f,0x39aa0⟩=some (dosResponderResult s) := by
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path (responder_prologue s f)
  have path := path.transfer program [0x39af8] responder_decoded (by
    intro pc hp; simp only [List.mem_singleton]; intro eq; subst pc; exact hp (by decide))
  apply path.finish (fuel := 3) ?_ 10 (by omega)
  have a : program 0x39aaa=some (.control (.block (.legacy (.load 2 0 0))),2) := by decide
  have b : program 0x39aac=some (.compareRegister 2 1,3) := by decide
  have c : program 0x39aaf=some (.control (.jumpZero false 71),2) := by decide
  simp [X86Routine.run,responderStart,dosResponderResult,a,b,c,X86Routine.execute,
    X86Control.execute,X86Block.execute,X86Memory.execute,blockPreservesFlags,X86Block.Address.eval,put,write,kind,compare32]

def handoffWrites (s : X86Memory.State) :=
  [s.regs 4-(4#32),s.regs 4-(8#32),s.regs 4-(12#32)] ++
  unloadWrites (stopUnload s) ++ [0x12c5c,s.regs 4-(12#32)]
theorem handoff_frame (s : X86Memory.State) :
    PlayerHeight.Frame s.memory (stopResponder s).memory (handoffWrites s) :=
  frame_append (frame_append (stopUnload_frame s) (unload_frame (stopUnload s))) (stopResponder_frame s)

def dosWrites (s : X86Memory.State) := handoffWrites s ++ responderWrites (stopResponder s)
theorem saved_frame (s : X86Memory.State) :
    PlayerHeight.Frame s.memory (responderSaved s) (responderWrites s) := by
  intro a safe
  unfold responderSaved
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp [responderWrites]))]

theorem dos_frame (s : X86Memory.State) :
    PlayerHeight.Frame s.memory (dosResponderResult (stopResponder s)).core.memory (dosWrites s) :=
  frame_append (handoff_frame s) (saved_frame (stopResponder s))

theorem dos_execution (s : X86Memory.State) (f : Option Flags)
    (h : UnloadInputs (stopUnload s))
    (kind : load32 s.memory (0x12c98#32)=0)
    (safe : ∀ b, b ∈ dosWrites s → Apart (0x12c98#32) b) :
    X86Routine.run program [0x39af8] 226 ⟨s,f,0x24f90⟩=
      some (dosResponderResult (stopResponder s)) := by
  have kept := dos_frame s (0x12c98#32) safe
  have arg : (stopResponder s).regs 0=(0x12c98#32) := by
    simp [stopResponder,X86Routine.pushWord,write]
  have event : load32 (responderSaved (stopResponder s)) ((stopResponder s).regs 0)=0 := by
    rw [arg]; exact kept.trans kind
  obtain ⟨n,hn,path⟩ := handoff_prefix s f h
  exact path.finish (dos_responder (stopResponder s) (some (logical32 0)) event) 226 (by omega)

end Doom.Proofs.AutomapStop
