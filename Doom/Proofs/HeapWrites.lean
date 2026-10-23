import Doom.Proofs.BlockSummary
namespace Doom.Proofs.HeapWrites
open Verification X86 X86Memory BlockSummary

def apply (ws : List (Word × Word)) (m : Memory) : Memory :=
  ws.foldl (fun m w => store32 m w.1 w.2) m

def Disjoint (ws : List (Word × Word)) : Prop := ws.Pairwise (fun a b => Apart a.1 b.1)

theorem frame (ws : List (Word × Word)) (m : Memory) (a : Word)
    (safe : ∀ w∈ws, Apart a w.1) : load32 (apply ws m) a=load32 m a := by
  induction ws generalizing m with
  | nil => rfl
  | cons w ws ih =>
    exact (ih (store32 m w.1 w.2) (fun p hp => safe p (by simp [hp]))).trans
      (load_store_apart _ _ _ _ (safe w (by simp)))

theorem assigned (ws : List (Word × Word)) (m : Memory) (w : Word × Word)
    (disjoint : Disjoint ws) (member : w∈ws) : load32 (apply ws m) w.1=w.2 := by
  induction ws generalizing m with
  | nil => simp at member
  | cons p ps ih =>
    have h := List.pairwise_cons.mp disjoint
    rcases List.mem_cons.mp member with rfl|member
    · exact (frame ps (store32 m w.1 w.2) w.1 h.1).trans (load_store m w.1 w.2)
    · exact ih (store32 m p.1 p.2) h.2 member

theorem append (a b : List (Word × Word)) (m : Memory) :
    apply (a++b) m=apply b (apply a m) := by simp [apply,List.foldl_append]
end Doom.Proofs.HeapWrites
