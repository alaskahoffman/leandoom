import Doom.Proofs.E1M1AimCallFrame
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimRetryData
open Verification X86 X86Memory X86Control BlockSummary
open E1M1CellWalkInvariant (Context Cell)
open E1M1ScanGeometry (linePointer)
attribute [local irreducible] load32 store32

/-- Setup write protection depends on stack addresses, not the old contents. -/
theorem safe (s t : X86Memory.State) (a : Word) (stack : t.regs 4=s.regs 4)
    (h : E1M1PathMapQuery.Safe s a) : E1M1PathMapQuery.Safe t a := by
  rcases h with ⟨saves,setup,later⟩
  constructor
  · simpa only [OriginalAimQuery.saveWrites,stack] using saves
  · simpa only [OriginalAimSetup.writes,E1M1PathMapQuery.withStack,write,ite_true,stack] using setup
  · simpa only [E1M1PathMapSetup.Safe,OriginalPathInit.writes,
      E1M1PathMapQuery.withStack,write,ite_true,stack] using later

def mapReads (base : Word) (words : Array Nat) : List Word :=
  [(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120] ++
    (List.range words.size).map (fun i => base+BitVec.ofNat 32 (2*i))

/-- Recover the complete blockmap input, including its 16-bit encoded words,
from 32-bit word preservation and the restored stack. -/
theorem map (s t : X86Memory.State) (base lines : Word) (words : Array Nat) (w h : Nat)
    (stack : t.regs 4=s.regs 4)
    (before : E1M1PathMapQuery.MapInputs s base lines words w h)
    (kept : ∀ a∈mapReads base words, load32 t.memory a=load32 s.memory a) :
    E1M1PathMapQuery.MapInputs t base lines words w h := by
  have globals (a : Word) (member : a∈[(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120]) :=
    kept a (List.mem_append_left _ member)
  refine ⟨(globals _ (by simp)).trans before.width,(globals _ (by simp)).trans before.height,
    before.widthBound,before.heightBound,(globals _ (by simp)).trans before.table,
    (globals _ (by simp)).trans before.lists,(globals _ (by simp)).trans before.lines,
    fun a ha => safe s t a stack (before.globalsSafe a ha),?_,
    fun i hi => safe s t _ stack (before.imageSafe i hi)⟩
  intro i v hv
  obtain ⟨hi,_⟩ := Array.getElem?_eq_some_iff.mp hv
  have word := kept (base+BitVec.ofNat 32 (2*i)) (by
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩)
  have half := congrArg (fun v : Word => v.extractLsb' 0 16) word
  rw [SectorDispatch.load_half,SectorDispatch.load_half] at half
  exact half.trans (before.image i v hv)

def cellReads (q : Context) (c : Cell) : List Word :=
  (List.finRange c.cell.ids.length).flatMap (fun i =>
    E1M1ScanMemory.lineReads (linePointer q.lines c.cell.ids[i.val]) (c.data i.val).v (c.data i.val).w ++
      [linePointer q.lines c.cell.ids[i.val]+50]) ++
  c.nodes.flatMap (fun node => [node.pointer+12,node.pointer+16,node.pointer+64,node.pointer+44]) ++
  [0x2c0f8,E1M1CellObjectSelection.address q.links c.x c.y q.width]

/-- Rebuild line encodings, actor bounds, object links and the selected block
head from an explicit finite read set. The trace/epoch are not payload fields. -/
theorem payload (m n : Memory) (q : Context) (c : Cell)
    (before : E1M1QueryImages.Payload m q c)
    (kept : ∀ a∈cellReads q c, load32 n a=load32 m a) :
    E1M1QueryImages.Payload n q c := by
  have line (i : Fin c.cell.ids.length) (a : Word)
      (member : a∈E1M1ScanMemory.lineReads (linePointer q.lines c.cell.ids[i.val])
        (c.data i.val).v (c.data i.val).w ++ [linePointer q.lines c.cell.ids[i.val]+50]) :=
    kept a (by simp only [cellReads,List.mem_append]; exact Or.inl (Or.inl
      (List.mem_flatMap.mpr ⟨i,by simp,member⟩)))
  have object (node : E1M1ThingList.Node) (member : node∈c.nodes) (a : Word)
      (field : a∈[node.pointer+12,node.pointer+16,node.pointer+64,node.pointer+44]) :=
    kept a (by simp only [cellReads,List.mem_append]; exact Or.inl (Or.inr
      (List.mem_flatMap.mpr ⟨node,member,field⟩)))
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro i
    exact E1M1NextCallbackMemory.line_words _ _ _ _ _ _ (before.encoded i)
      (fun a ha => line i a (List.mem_append_left _ ha))
  · intro i
    rw [line i _ (List.mem_append_right _ (by simp))]
    exact before.back i
  · intro node member
    rw [object node member _ (by simp),object node member _ (by simp),object node member _ (by simp)]
    exact before.objects node member
  · exact E1M1ThingList.linked_transport _ _ _ before.linked
      (fun node member => object node member _ (by simp))
  · exact (kept _ (by simp [cellReads])).trans before.selection.global
  · exact (kept _ (by simp [cellReads])).trans before.selection.selected

/-- Payload setup guards can be reused at the restored query stack. -/
theorem payload_safe (s t : X86Memory.State) (q : Context) (c : Cell)
    (stack : t.regs 4=s.regs 4) (h : E1M1AimPreRayMemory.PayloadSafe s q c) :
    E1M1AimPreRayMemory.PayloadSafe t q c :=
  ⟨fun i a ha => safe s t a stack (h.lines i a ha),
    fun i => safe s t _ stack (h.back i),
    fun node hn off ho => safe s t _ stack (h.objects node hn off ho),
    fun node hn => safe s t _ stack (h.links node hn),
    safe s t _ stack h.global,safe s t _ stack h.selected⟩
end Doom.Proofs.E1M1AimRetryData
