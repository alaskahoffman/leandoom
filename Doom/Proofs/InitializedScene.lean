import Doom.Proofs.InitializedAddress
import Doom.Proofs.InitializedE1M1
import Doom.Proofs.E1M1AimMapEntry
import Doom.Proofs.E1M1QueryImages

set_option maxRecDepth 32768
namespace Doom.Proofs.InitializedScene
open Verification X86Memory Collision
open InitializedAddress (Read Encodes)
open E1M1CellWalkInvariant (Context Cell)

/-- Captured placements and raw BLOCKMAP words, not desired scene contracts.
Pointers are indexed by production identity (player zero, map index + one). -/
structure Input where
  base : Word
  lines : Word
  links : Word
  words : Array Nat
  pointers : Array Word

def mapReads (d : Input) : List Read :=
  [.scalar 0x2c0fc 36,.scalar 0x2c110 23,.pointer 0x2c100 (d.base+8),
   .pointer 0x2c10c d.base,.pointer 0x2c120 d.lines] ++
  List.ofFn (fun i : Fin d.words.size =>
    .short (d.base+BitVec.ofNat 32 (2*i.val)) (BitVec.ofNat 16 d.words[i.val]))

def lineData (m : Memory) (d : Input) (world : Scene) (id : Nat)
    (fraction : Nat → Fixed) : E1M1ScanContracts.LineData :=
  let p := E1M1ScanGeometry.linePointer d.lines id
  ⟨world.lines[id]!,load32 m p,load32 m (p+4),fraction id⟩

def node (d : Input) (world : Scene) (id : Nat) : E1M1ThingList.Node :=
  ⟨id,d.pointers[id]!,world.things[id]!⟩

/-- Raw iterator visits include the leading zero. Actor order is precisely the
production blocklink order; it is not sorted or recovered from thinker indices. -/
def cell (m : Memory) (d : Input) (world : Scene) (index : Nat)
    (fraction : Nat → Fixed) : Cell :=
  let ids := 0 :: world.grid.cells[index]!.toList
  ⟨Int32.ofNat (index%36),Int32.ofNat (index/36),
    ⟨d.words[4+index]!,ids⟩,
    (fun i => lineData m d world ids[i]! fraction),
    world.links[index]!.toList.map (node d world)⟩

def context (d : Input) (world : Scene) (sp epoch : Word) (trace : Divline) : Context :=
  ⟨sp,d.base,d.lines,epoch,d.words,36,23,d.links,(fun id => d.pointers[id]!),trace,world⟩

def lineReads (p : Word) (data : E1M1ScanContracts.LineData) : List Read :=
  [.pointer p data.v,.pointer (p+4) data.w,
   .scalar data.v data.line.x.raw.toBitVec,
   .scalar (data.v+4) data.line.y.raw.toBitVec,
   .scalar data.w (data.line.x+data.line.dx).raw.toBitVec,
   .scalar (data.w+4) (data.line.y+data.line.dy).raw.toBitVec,
   .scalar (p+8) data.line.dx.raw.toBitVec,.scalar (p+12) data.line.dy.raw.toBitVec]

def nodeReads : List E1M1ThingList.Node → List Read
  | [] => []
  | n::rest => [.scalar (n.pointer+12) n.target.x.raw.toBitVec,
      .scalar (n.pointer+16) n.target.y.raw.toBitVec,
      .scalar (n.pointer+64) n.target.radius.raw.toBitVec,
      .pointer (n.pointer+44) (E1M1ThingList.head rest)] ++ nodeReads rest

def cellReads (m : Memory) (d : Input) (c : Cell) : List Read :=
  (List.ofFn fun i : Fin c.cell.ids.length =>
    let p := E1M1ScanGeometry.linePointer d.lines c.cell.ids[i.val]
    lineReads p (c.data i.val) ++ [.pointer (p+50) (load32 m (p+50))]).flatten ++
  nodeReads c.nodes ++
  [.pointer 0x2c0f8 d.links,
   .pointer (E1M1CellObjectSelection.address d.links c.x c.y 36) (E1M1ThingList.head c.nodes)]

def cellCheck (raw m : Memory) (base extent : Nat) (d : Input) (world : Scene)
    (index : Nat) (fraction : Nat → Fixed) : Bool :=
  let c := cell m d world index fraction
  decide (c.cell.Valid d.words ∧ Collision.pathCellIndex c.x c.y 36=index ∧
    Collision.pathCellInside c.x c.y 36 23=true ∧
    (∀ i : Fin c.cell.ids.length,
      (load32 m (E1M1ScanGeometry.linePointer d.lines c.cell.ids[i.val]+50)=0 ↔
       (c.data i.val).line.back.isNone=true)) ∧
    (∀ id∈world.links[index]!.toList, id<world.things.size ∧ id<d.pointers.size ∧ d.pointers[id]!≠0)) &&
  InitializedAddress.check raw m base extent (cellReads m d c)

def sceneCheck (raw m : Memory) (base extent : Nat) (world : Scene) (d : Input) : Bool :=
  InitializedE1M1.shapeCheck world &&
  decide (world.lines.size=475 ∧ d.words.size=3461 ∧ d.pointers.size=world.things.size) &&
  InitializedAddress.check raw m base extent (mapReads d) &&
  (List.range 828).all (fun i => cellCheck raw m base extent d world i (fun _ => Fixed.ofInt 0))

theorem map_values (raw m : Memory) (base extent : Nat) (d : Input)
    (checked : InitializedAddress.check raw m base extent (mapReads d)=true) :
    E1M1AimMapEntry.Values m d.base d.lines d.words := by
  have reads := InitializedAddress.encodes raw m base extent (mapReads d) checked
  refine ⟨reads (.scalar 0x2c0fc 36) (by simp [mapReads]),
    reads (.scalar 0x2c110 23) (by simp [mapReads]),
    reads (.pointer 0x2c100 (d.base+8)) (by simp [mapReads]),
    reads (.pointer 0x2c10c d.base) (by simp [mapReads]),
    reads (.pointer 0x2c120 d.lines) (by simp [mapReads]),?_⟩
  intro i value hv
  obtain ⟨hi,eq⟩ := Array.getElem?_eq_some_iff.mp hv
  have h := reads (.short (d.base+BitVec.ofNat 32 (2*i)) (BitVec.ofNat 16 d.words[i]))
    (List.mem_append_right _ (List.mem_ofFn.mpr ⟨⟨i,hi⟩,rfl⟩))
  simpa only [Encodes,eq] using h

theorem line_words (m : Memory) (p : Word) (data : E1M1ScanContracts.LineData)
    (reads : ∀ r∈lineReads p data, Encodes m r) :
    E1M1ScanMemory.LineWords m data.line p data.v data.w := by
  exact ⟨reads (.pointer p data.v) (by simp [lineReads]),
    reads (.pointer (p+4) data.w) (by simp [lineReads]),
    reads (.scalar data.v data.line.x.raw.toBitVec) (by simp [lineReads]),
    reads (.scalar (data.v+4) data.line.y.raw.toBitVec) (by simp [lineReads]),
    reads (.scalar data.w (data.line.x+data.line.dx).raw.toBitVec) (by simp [lineReads]),
    reads (.scalar (data.w+4) (data.line.y+data.line.dy).raw.toBitVec) (by simp [lineReads]),
    reads (.scalar (p+8) data.line.dx.raw.toBitVec) (by simp [lineReads]),
    reads (.scalar (p+12) data.line.dy.raw.toBitVec) (by simp [lineReads])⟩

theorem node_words (m : Memory) (nodes : List E1M1ThingList.Node)
    (reads : ∀ r∈nodeReads nodes, Encodes m r) :
    (∀ n∈nodes, (load32 m (n.pointer+12),load32 m (n.pointer+16),load32 m (n.pointer+64))=
      (n.target.x.raw.toBitVec,n.target.y.raw.toBitVec,n.target.radius.raw.toBitVec)) ∧
    E1M1ThingList.Linked m nodes := by
  induction nodes with
  | nil => simp [E1M1ThingList.Linked]
  | cons n rest ih =>
    have tail := ih (fun r hr => reads r (by simp only [nodeReads,List.mem_append]; exact Or.inr hr))
    refine ⟨?_,reads (.pointer (n.pointer+44) (E1M1ThingList.head rest)) (by simp [nodeReads]),tail.2⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl|hr
    · exact Prod.ext (reads (.scalar (x.pointer+12) x.target.x.raw.toBitVec) (by simp [nodeReads]))
        (Prod.ext (reads (.scalar (x.pointer+16) x.target.y.raw.toBitVec) (by simp [nodeReads]))
          (reads (.scalar (x.pointer+64) x.target.radius.raw.toBitVec) (by simp [nodeReads])))
    · exact tail.1 x hr

theorem cell_payload (raw m : Memory) (base extent : Nat) (d : Input) (world : Scene)
    (index : Nat) (fraction : Nat → Fixed) (sp epoch : Word) (trace : Divline)
    (checked : cellCheck raw m base extent d world index fraction=true) :
    E1M1QueryImages.Payload m (context d world sp epoch trace) (cell m d world index fraction) := by
  let c := cell m d world index fraction
  simp only [cellCheck,Bool.and_eq_true] at checked
  have h := checked
  have facts := of_decide_eq_true h.1
  have reads := InitializedAddress.encodes raw m base extent (cellReads m d c) h.2
  have nr := node_words m c.nodes (fun r hr => reads r (by
    simp only [cellReads,List.mem_append]; exact Or.inl (Or.inr hr)))
  refine ⟨?_,facts.2.2.2.1,nr.1,nr.2,?_,?_⟩
  · intro i
    apply line_words
    intro r hr
    apply reads r
    simp only [cellReads,List.mem_append]
    exact Or.inl (Or.inl (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,
      List.mem_append_left _ hr⟩))
  · exact reads (.pointer 0x2c0f8 d.links) (by simp [cellReads])
  · exact reads (.pointer (E1M1CellObjectSelection.address d.links c.x c.y 36)
      (E1M1ThingList.head c.nodes)) (by simp [cellReads])

/-- Construction uses actual scene lookups; bounded IDs justify those lookups,
not a decidable equality assumed between two independently supplied scenes. -/
theorem cell_scene_lines (raw m : Memory) (base extent : Nat) (d : Input) (world : Scene)
    (index : Nat) (fraction : Nat → Fixed) (sp epoch : Word) (trace : Divline)
    (size : world.lines.size=475) (cells : world.grid.cells.size=828) (hi : index<828)
    (checked : cellCheck raw m base extent d world index fraction=true) :
    E1M1CellLineSource.SceneLines (context d world sp epoch trace) (cell m d world index fraction) := by
  simp only [cellCheck,Bool.and_eq_true] at checked
  have facts := of_decide_eq_true checked.1
  have hc : index<world.grid.cells.size := by omega
  constructor
  · change world.grid.cells[Collision.pathCellIndex _ _ 36]?=some _
    rw [facts.2.1]
    simp [cell,Array.getElem?_eq_getElem hc,getElem!_pos world.grid.cells index hc]
  · intro i
    have bound := (facts.1.2.2.2.1 i).1
    have hi' : i.val < (0 :: world.grid.cells[index]!.toList).length := i.isLt
    have hb : (0 :: world.grid.cells[index]!.toList)[i.val]!<world.lines.size := by
      simpa only [cell,getElem!_pos (0 :: world.grid.cells[index]!.toList) i.val hi',size] using bound
    change world.lines[(0 :: world.grid.cells[index]!.toList)[i.val]'hi']? =
      some world.lines[(0 :: world.grid.cells[index]!.toList)[i.val]!]!
    rw [←getElem!_pos (0 :: world.grid.cells[index]!.toList) i.val hi']
    exact Array.getElem?_eq_some_getElem! world.lines _ hb

/-- The remaining route-independent Static fields: exact raw-list selection,
ordered production actor identities, actual target lookups and nonnull resolvers. -/
theorem cell_sources (raw m : Memory) (base extent : Nat) (d : Input) (world : Scene)
    (index : Nat) (fraction : Nat → Fixed)
    (words : d.words.size=3461) (links : world.links.size=828) (hi : index<828)
    (checked : cellCheck raw m base extent d world index fraction=true) :
    let c := cell m d world index fraction
    d.words[4+Collision.pathCellIndex c.x c.y 36]?=some c.cell.offset ∧
    world.links[Collision.pathCellIndex c.x c.y 36]?=some (c.nodes.map E1M1ThingList.Node.id).toArray ∧
    (∀ n∈c.nodes, world.things[n.id]?=some n.target ∧ n.pointer=d.pointers[n.id]! ∧ n.pointer≠0) := by
  simp only [cellCheck,Bool.and_eq_true] at checked
  have facts := of_decide_eq_true checked.1
  have hw : 4+index<d.words.size := by omega
  have hl : index<world.links.size := by omega
  dsimp only
  rw [facts.2.1]
  refine ⟨Array.getElem?_eq_some_getElem! d.words _ hw,?_,?_⟩
  · have ids : (E1M1ThingList.Node.id ∘ node d world) = id := rfl
    simpa only [cell,List.map_map,ids,List.map_id,Array.toArray_toList] using
      (Array.getElem?_eq_some_getElem! world.links index hl)
  · intro n hn
    obtain ⟨id,member,rfl⟩ := List.mem_map.mp hn
    have bound := facts.2.2.2.2 id member
    exact ⟨Array.getElem?_eq_some_getElem! world.things id bound.1,rfl,bound.2.2⟩

/-- Fractions, stack, trace and epoch are not checked future query outcomes.
The same initial data works for arbitrary choices of these route parameters. -/
theorem fraction_check (raw m : Memory) (base extent : Nat) (d : Input) (world : Scene)
    (index : Nat) (f g : Nat → Fixed) :
    cellCheck raw m base extent d world index f = cellCheck raw m base extent d world index g := by
  rfl

theorem scene_sound (raw m : Memory) (base extent : Nat) (world : Scene) (d : Input)
    (checked : sceneCheck raw m base extent world d=true) :
    E1M1QuerySource.supported world=true ∧
    E1M1AimMapEntry.Values m d.base d.lines d.words ∧
    (∀ index<828, ∀ fraction sp epoch trace,
      E1M1CellLineSource.SceneLines (context d world sp epoch trace) (cell m d world index fraction) ∧
      E1M1QueryImages.Payload m (context d world sp epoch trace) (cell m d world index fraction) ∧
      (cell m d world index fraction).cell.Valid d.words ∧
      Collision.pathCellInside (cell m d world index fraction).x (cell m d world index fraction).y 36 23=true ∧
      (∀ r∈cellReads m d (cell m d world index fraction),
        InitializedAddress.Address base extent r ∧
        InitializedAddress.Observed raw m base extent r ∧ Encodes m r)) := by
  simp only [sceneCheck,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨shape,sizes⟩,maps⟩,allCells⟩ := checked
  have sizes := of_decide_eq_true sizes
  have shapeFacts := of_decide_eq_true shape
  refine ⟨InitializedE1M1.supported_of_check world shape,map_values raw m base extent d maps,?_⟩
  intro index hi fraction sp epoch trace
  have hc := List.all_eq_true.mp allCells index (List.mem_range.mpr hi)
  rw [fraction_check raw m base extent d world index _ fraction] at hc
  have hc' := hc
  simp only [cellCheck,Bool.and_eq_true] at hc'
  have facts := of_decide_eq_true hc'.1
  exact ⟨cell_scene_lines raw m base extent d world index fraction sp epoch trace sizes.1 shapeFacts.2.2.2.1 hi hc,
    cell_payload raw m base extent d world index fraction sp epoch trace hc,
    facts.1,facts.2.2.1,InitializedAddress.sound raw m base extent _ hc'.2⟩

def startCheck (lumps : Array Lump) (raw m : Memory) (base extent : Nat) (d : Input) : Bool :=
  match Engine.start lumps true false with
  | .error _ => false
  | .ok (_,state,_) => match InitializedE1M1.aimingScene state with
    | .error _ => false
    | .ok world => sceneCheck raw m base extent world d

/-- Success and the actual production projection are obtained by inspecting the
initializer, not assumed. Only finite data/provenance checks are premises. -/
theorem started_scene (lumps : Array Lump) (raw m : Memory) (base extent : Nat) (d : Input)
    (checked : startCheck lumps raw m base extent d=true) :
    ∃ ctx state events world,
      Engine.start lumps true false=.ok (ctx,state,events) ∧
      InitializedE1M1.aimingScene state=.ok world ∧
      E1M1QuerySource.supported world=true ∧
      E1M1AimMapEntry.Values m d.base d.lines d.words ∧
      (∀ index<828, ∀ fraction sp epoch trace,
        E1M1CellLineSource.SceneLines (context d world sp epoch trace) (cell m d world index fraction) ∧
        E1M1QueryImages.Payload m (context d world sp epoch trace) (cell m d world index fraction)) := by
  cases hs : Engine.start lumps true false with
  | error e => simp [startCheck,hs] at checked
  | ok result =>
    rcases result with ⟨ctx,state,events⟩
    cases hw : InitializedE1M1.aimingScene state with
    | error e => simp [startCheck,hs,hw] at checked
    | ok world =>
      have hc : sceneCheck raw m base extent world d=true := by
        simpa only [startCheck,hs,hw] using checked
      obtain ⟨supported,maps,cells⟩ := scene_sound raw m base extent world d hc
      exact ⟨ctx,state,events,world,rfl,hw,supported,maps,fun i hi f sp epoch trace =>
        ⟨(cells i hi f sp epoch trace).1,(cells i hi f sp epoch trace).2.1⟩⟩

end Doom.Proofs.InitializedScene
