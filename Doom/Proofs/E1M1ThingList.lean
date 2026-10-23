import Doom.Proofs.E1M1ThingVisit
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace Doom.Proofs.E1M1ThingList
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ThingVisit (ReadSafe StackSafe Geometry Inputs)
open OriginalThingSecondSide (firstSide lastSide)
abbrev program := E1M1ThingVisit.program

structure Node where
  id : Nat
  pointer : Word
  target : Collision.SolidThing

def head : List Node → Word
  | [] => 0
  | node::_ => node.pointer

def Linked (memory : Memory) : List Node → Prop
  | [] => True
  | node::rest => load32 memory (node.pointer+(44#32))=head rest ∧ Linked memory rest

/-- Static non-aliasing and arithmetic obligations for the whole finite list. -/
structure Layout (sp : Word) (trace : Collision.Divline)
    (resolve : Collision.Intercept → Word) (nodes : List Node) : Prop where
  stack : StackSafe sp
  callback : ReadSafe sp sp
  caller : ReadSafe sp (sp+(4#32))
  nonzero : ∀ node∈nodes, node.pointer≠(0#32)
  pointer : ∀ node∈nodes, ∀ frac, resolve ⟨frac,false,node.id⟩=node.pointer
  reads : ∀ node∈nodes, ∀ a∈E1M1ThingVisit.reads node.pointer, ReadSafe sp a
  link : ∀ node∈nodes, ReadSafe sp (node.pointer+(44#32))
  arithmetic : ∀ node∈nodes, firstSide trace node.target≠lastSide trace node.target →
    ∃ frac, Collision.interceptVector trace (OriginalThingFraction.diagonal trace node.target)=.ok frac

/-- This is supplied once at list entry, then transported through actual writes. -/
structure Image (memory : Memory) (sp : Word) (trace : Collision.Divline)
    (nodes : List Node) (ret : Word) : Prop where
  callback : load32 memory sp=(0x2c720#32)
  caller : load32 memory (sp+(4#32))=ret
  geometry : ∀ node∈nodes, Geometry memory trace node.pointer node.target
  linked : Linked memory nodes

theorem layout_tail (sp : Word) (trace : Collision.Divline) (resolve : Collision.Intercept → Word)
    (node : Node) (rest : List Node) (h : Layout sp trace resolve (node::rest)) :
    Layout sp trace resolve rest := by
  exact ⟨h.stack,h.callback,h.caller,fun n hn => h.nonzero n (by simp [hn]),
    fun n hn => h.pointer n (by simp [hn]),fun n hn => h.reads n (by simp [hn]),
    fun n hn => h.link n (by simp [hn]),fun n hn => h.arithmetic n (by simp [hn])⟩

theorem geometry_transport (before after : Memory) (trace : Collision.Divline) (node : Node)
    (h : Geometry before trace node.pointer node.target)
    (keep : ∀ a∈E1M1ThingVisit.reads node.pointer, load32 after a=load32 before a) :
    Geometry after trace node.pointer node.target := by
  exact ⟨(keep _ (by simp [E1M1ThingVisit.reads])).trans h.x,
    (keep _ (by simp [E1M1ThingVisit.reads])).trans h.y,
    (keep _ (by simp [E1M1ThingVisit.reads])).trans h.dx,
    (keep _ (by simp [E1M1ThingVisit.reads])).trans h.dy,
    (keep _ (by simp [E1M1ThingVisit.reads])).trans h.ox,
    (keep _ (by simp [E1M1ThingVisit.reads])).trans h.oy,
    (keep _ (by simp [E1M1ThingVisit.reads])).trans h.radius⟩

theorem linked_transport (before after : Memory) (nodes : List Node)
    (h : Linked before nodes)
    (keep : ∀ node∈nodes, load32 after (node.pointer+(44#32))=load32 before (node.pointer+(44#32))) :
    Linked after nodes := by
  induction nodes with
  | nil => trivial
  | cons node rest ih =>
    exact ⟨(keep node (by simp)).trans h.1,ih h.2 (fun n hn => keep n (by simp [hn]))⟩

def collect (trace : Collision.Divline) : List Node → Collision.PathResult → Except String Collision.PathResult
  | [], r => .ok r
  | node::rest, r => do
    let next ← E1M1ThingFinish.collect trace node.target node.id r
    collect trace rest next

def run : Nat → X86Control.State → X86Control.State
  | 0, s => s
  | n+1, s => run n (E1M1ThingVisit.result s)

theorem collect_size (trace : Collision.Divline) (target : Collision.SolidThing)
    (id : Nat) (r after : Collision.PathResult) (ok : E1M1ThingFinish.collect trace target id r=.ok after) :
    after.collected.size≤r.collected.size+1 := by
  unfold E1M1ThingFinish.collect at ok
  cases h : Collision.thingIntercept trace target with
  | error e =>
    simp only [h] at ok
    change Except.error e=Except.ok after at ok
    contradiction
  | ok hit =>
    cases hit with
    | none =>
      simp only [h] at ok
      change Except.ok r=Except.ok after at ok
      cases ok; omega
    | some frac =>
      simp only [h] at ok
      change Collision.appendIntercept r ⟨frac,false,id⟩=.ok after at ok
      unfold Collision.appendIntercept at ok
      split at ok
      · contradiction
      · cases ok; simp

/-- All per-visit conditions follow from the initial image and the preserved layout. -/
theorem visit_inputs (s : X86Control.State) (trace : Collision.Divline)
    (resolve : Collision.Intercept → Word) (node : Node) (rest : List Node) (ret : Word)
    (layout : Layout (s.core.regs 4) trace resolve (node::rest))
    (image : Image s.core.memory (s.core.regs 4) trace (node::rest) ret)
    (cursor : s.core.regs 2=node.pointer) : Inputs s trace node.target := by
  refine ⟨image.callback,?_,?_,layout.stack,layout.arithmetic node (by simp)⟩
  · rw [cursor]; exact image.geometry node (by simp)
  · rw [cursor]; exact layout.reads node (by simp)

theorem image_tail (s : X86Control.State) (trace : Collision.Divline)
    (resolve : Collision.Intercept → Word) (node : Node) (rest : List Node) (ret : Word)
    (layout : Layout (s.core.regs 4) trace resolve (node::rest))
    (image : Image s.core.memory (s.core.regs 4) trace (node::rest) ret)
    (cursor : s.core.regs 2=node.pointer) (r : Collision.PathResult)
    (tracked : OriginalLineCollection.Tracks s.core 0x2ba20 resolve r.collected 0)
    (capacity : r.collected.size<128) :
    Image (E1M1ThingVisit.result s).core.memory (s.core.regs 4) trace rest ret ∧
    load32 (E1M1ThingVisit.result s).core.memory (node.pointer+(44#32))=head rest := by
  have h := visit_inputs s trace resolve node rest ret layout image cursor
  have keep (a : Word) (safe : ReadSafe (s.core.regs 4) a) :=
    E1M1ThingVisit.frame s trace node.target h resolve r tracked capacity a safe
  refine ⟨⟨(keep _ layout.callback).trans image.callback,(keep _ layout.caller).trans image.caller,?_,?_⟩,?_⟩
  · intro n hn
    exact geometry_transport _ _ trace n (image.geometry n (by simp [hn]))
      (fun a ha => keep a (layout.reads n (by simp [hn]) a ha))
  · exact linked_transport _ _ rest image.linked.2 (fun n hn => keep _ (layout.link n (by simp [hn])))
  · exact (keep _ (layout.link node (by simp))).trans image.linked.1

/-- Finite list induction. The input supplies raw memory encodings and separation,
not a trace of successful callbacks or any reached-state equality. -/
theorem execution (s : X86Control.State) (trace : Collision.Divline)
    (resolve : Collision.Intercept → Word) (nodes : List Node) (ret : Word)
    (layout : Layout (s.core.regs 4) trace resolve nodes)
    (image : Image s.core.memory (s.core.regs 4) trace nodes ret)
    (cursor : s.core.regs 2=head nodes)
    (pc : s.pc=if head nodes=(0#32) then 0x2c5e2 else 0x2c5d2)
    (r : Collision.PathResult) (tracked : OriginalLineCollection.Tracks s.core 0x2ba20 resolve r.collected 0)
    (capacity : r.collected.size+nodes.length≤128) :
    let out := run nodes.length s
    (∃ n≤230*nodes.length, X86Routine.Prefix program [] n s out) ∧
    out.core.regs 4=s.core.regs 4 ∧ out.core.regs 2=(0#32) ∧ out.pc=0x2c5e2 ∧
    Image out.core.memory (s.core.regs 4) trace [] ret ∧
    (∃ after, collect trace nodes r=.ok after ∧ OriginalLineCollection.Tracks out.core 0x2ba20 resolve after.collected 0) := by
  induction nodes generalizing s r with
  | nil =>
    exact ⟨⟨0,by simp,.nil _⟩,rfl,cursor,by simpa [head,run] using pc,image,r,rfl,tracked⟩
  | cons node rest ih =>
    have nonzero := layout.nonzero node (by simp)
    have cursor' : s.core.regs 2=node.pointer := cursor
    have pc' : s.pc=0x2c5d2 := by simpa [head,nonzero] using pc
    have room : r.collected.size<128 := by simp only [List.length_cons] at capacity; omega
    have h := visit_inputs s trace resolve node rest ret layout image cursor'
    have pointer (frac : Fixed) : resolve ⟨frac,false,node.id⟩=s.core.regs 2 := (layout.pointer node (by simp) frac).trans cursor'.symm
    obtain ⟨⟨n,hn,one⟩,sp,next,pcNext,after,produced,encoded⟩ :=
      E1M1ThingVisit.execution s trace node.target h pc' resolve node.id r pointer tracked room
    obtain ⟨imageNext,link⟩ := image_tail s trace resolve node rest ret layout image cursor' r tracked room
    have cursorNext : (E1M1ThingVisit.result s).core.regs 2=head rest := by rw [cursor'] at next; exact next.trans link
    have space : after.collected.size+rest.length≤128 := by
      have size := collect_size trace node.target node.id r after produced
      simp only [List.length_cons] at capacity
      omega
    obtain ⟨⟨m,hm,tail⟩,spOut,zero,pcOut,imageOut,final,production,collection⟩ :=
      ih (E1M1ThingVisit.result s) (by rw [sp]; exact layout_tail _ _ _ _ _ layout)
        (by rw [sp]; exact imageNext) cursorNext (by rw [cursorNext] at pcNext; exact pcNext) after encoded space
    refine ⟨⟨n+m,by simp only [List.length_cons]; omega,OriginalGroupBounds.prefix_join one tail⟩,
      spOut.trans sp,zero,pcOut,?_,final,?_,collection⟩
    · rw [sp] at imageOut; exact imageOut
    · simp only [collect,produced]
      exact production
end Doom.Proofs.E1M1ThingList
