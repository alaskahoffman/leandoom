import Doom.Proofs.E1M1FiringGeometry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
namespace Doom.Proofs.E1M1ScanMemory
open Verification X86 X86Memory X86Control BlockSummary
open E1M1PathMapQuery (withStack)

def scan (s : X86Memory.State) := E1M1PathMapCaller.scan (E1M1PathMapSetup.grid s).core
def firstScan (gun : Fire.Gun) (s : X86Memory.State) :=
  E1M1PathMapCaller.scan (E1M1PathGridSetup.firstGrid gun s).core

theorem caller_frame (s : X86Memory.State) (a : Word) (safe : E1M1PathMapCaller.Safe s a) :
    load32 (E1M1PathMapCaller.scan s).core.memory a=load32 s.memory a := by
  change load32 (OriginalLineCell.lookup _).core.memory a=_
  rw [(OriginalLineCell.lookup_observe _).2.1]
  exact (E1M1PathMapBounds.result_frame _ a (E1M1PathMapCaller.safe_at_call s a safe)).trans
    (E1M1PathMapCaller.call_frame s a safe.1)

/-- Initialization may change the word. Only subsequent stack writes are
excluded, so this applies to the freshly written trace, flags and visit epoch. -/
theorem initialized_frame (s : X86Memory.State) (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs s ox oy sx sy ex ey) (a : Word)
    (safe : E1M1PathMapSetup.StackSafe (s.regs 4-(60#32)) a) :
    load32 (scan s).core.memory a=load32 (OriginalPathInit.result s).core.memory a := by
  have sp := E1M1PathMapSetup.grid_stack s ox oy sx sy ex ey geometry
  have caller : E1M1PathMapCaller.Safe (E1M1PathMapSetup.grid s).core a := by
    unfold E1M1PathMapCaller.Safe
    rw [sp]
    exact ⟨by simpa [BitVec.sub_eq_add_neg] using safe (-4) (by simp [E1M1PathMapSetup.offsets]),
      by simpa [BitVec.sub_eq_add_neg] using safe (-8) (by simp [E1M1PathMapSetup.offsets]),
      by simpa [BitVec.sub_eq_add_neg] using safe (-12) (by simp [E1M1PathMapSetup.offsets])⟩
  exact (caller_frame _ a caller).trans (E1M1PathMapSetup.after_frame _ a (by
    rw [(OriginalPathInit.ready s ox oy sx sy ex ey geometry).stack]; exact safe))

theorem traversal_frame (s : X86Memory.State) (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs s ox oy sx sy ex ey) (a : Word)
    (safe : E1M1PathMapSetup.Safe s a) :
    load32 (scan s).core.memory a=load32 s.memory a :=
  (initialized_frame s ox oy sx sy ex ey geometry a safe.2).trans (OriginalPathInit.frame15 s a safe.1)

theorem firing_frame (gun : Fire.Gun) (s : X86Memory.State) (actor : Word)
    (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (geometry : E1M1FiringGeometry.Inputs gun s actor thing angle ox oy) (a : Word)
    (safe : E1M1PathMapFiring.Safe gun s a) :
    load32 (firstScan gun s).core.memory a=load32 s.memory a := by
  have qs := E1M1PathMapFiring.query_safe gun s a safe
  have geo := E1M1AimGeometry.path_inputs _ thing angle _ ox oy
    (E1M1FiringGeometry.query_geometry gun s actor thing angle ox oy geometry)
  exact (traversal_frame _ ox oy _ _ _ _ geo a (E1M1PathMapQuery.traversal_safe _ a qs)).trans
    ((E1M1PathMapQuery.traversal_frame _ a qs).trans (E1M1PathMapFiring.query_frame gun s a safe))

/-- The loaded line/vertex representation, independent of callback registers
and scratch storage. Its coordinates use the production wrapping endpoint sum. -/
structure LineWords (memory : Memory) (line : Collision.Line) (p v w : Word) : Prop where
  vertex1 : load32 memory p=v
  vertex2 : load32 memory (p+4)=w
  x1 : load32 memory v=line.x.raw.toBitVec
  y1 : load32 memory (v+4)=line.y.raw.toBitVec
  x2 : load32 memory w=(line.x+line.dx).raw.toBitVec
  y2 : load32 memory (w+4)=(line.y+line.dy).raw.toBitVec
  dx : load32 memory (p+8)=line.dx.raw.toBitVec
  dy : load32 memory (p+12)=line.dy.raw.toBitVec

def lineReads (p v w : Word) : List Word := [p,p+4,v,v+4,w,w+4,p+8,p+12]

theorem firing_line (gun : Fire.Gun) (s : X86Memory.State) (actor : Word)
    (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (geometry : E1M1FiringGeometry.Inputs gun s actor thing angle ox oy)
    (line : Collision.Line) (p v w : Word) (encoded : LineWords s.memory line p v w)
    (safe : ∀ a∈lineReads p v w, E1M1PathMapFiring.Safe gun s a) :
    LineWords (firstScan gun s).core.memory line p v w := by
  have keep (a : Word) (ha : a∈lineReads p v w) :=
    firing_frame gun s actor thing angle ox oy geometry a (safe a ha)
  exact ⟨(keep _ (by simp [lineReads])).trans encoded.vertex1,
    (keep _ (by simp [lineReads])).trans encoded.vertex2,
    (keep _ (by simp [lineReads])).trans encoded.x1,
    (keep _ (by simp [lineReads])).trans encoded.y1,
    (keep _ (by simp [lineReads])).trans encoded.x2,
    (keep _ (by simp [lineReads])).trans encoded.y2,
    (keep _ (by simp [lineReads])).trans encoded.dx,
    (keep _ (by simp [lineReads])).trans encoded.dy⟩

/-- Unlike the full frame contract, this stops before traversal initialization.
It can protect the old epoch, which initialization intentionally increments. -/
structure BeforeInit (gun : Fire.Gun) (s : X86Memory.State) (a : Word) : Prop where
  beforeFlash : ∀ b∈E1M1DischargeSetters.beforeFlashWrites gun s, Apart a b
  flash : ∀ b∈E1M1FlashInstall.writes (E1M1DischargeSetters.flashCall gun s).core, Apart a b
  aim : Apart a (s.regs 4-(4#32))
  slope : ∀ b∈E1M1PathMapFiring.slopeWrites (E1M1DischargeSetters.aimCall gun s).core, Apart a b
  saves : ∀ b∈OriginalAimQuery.saveWrites (withStack s (s.regs 4-(24#32))), Apart a b
  setup : ∀ b∈(OriginalAimSetup.writes (withStack s (s.regs 4-(40#32)))).toList, Apart a b

theorem before_init_frame (gun : Fire.Gun) (s : X86Memory.State) (a : Word) (safe : BeforeInit gun s a) :
    load32 (E1M1AimSetup.firstTraversal gun s).core.memory a=load32 s.memory a := by
  have flashed := (E1M1FlashInstall.memory_frame gun _ a safe.flash).trans
    (E1M1DischargeSetters.before_flash_frame gun s a safe.beforeFlash)
  have aim : load32 (E1M1DischargeSetters.aimCall gun s).core.memory a=load32 s.memory a := by
    change load32 (store32 (E1M1DischargeSetters.flashed gun s).core.memory
      ((E1M1DischargeSetters.flashed gun s).core.regs 4-(4#32)) _) a=_
    rw [E1M1PathMapFiring.flashed_stack,load_store_apart _ _ _ _ safe.aim]
    exact flashed
  have query := (E1M1PathMapFiring.slope_frame _ (E1M1DischargeSetters.aimCall gun s).flags a safe.slope).trans aim
  have saves : ∀ b∈OriginalAimQuery.saveWrites (E1M1BulletAim.firstQuery gun s).core, Apart a b := by
    simpa only [OriginalAimQuery.saveWrites,E1M1PathMapFiring.query_stack,withStack,write,ite_true] using safe.saves
  have sp : (OriginalAimQuery.ray (E1M1BulletAim.firstQuery gun s).core).core.regs 4=s.regs 4-(40#32) := by
    rw [E1M1PathMapQuery.ray_stack,E1M1PathMapFiring.query_stack]
    simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have setup : ∀ b∈(OriginalAimSetup.writes (OriginalAimQuery.ray (E1M1BulletAim.firstQuery gun s).core).core).toList,
      Apart a b := by
    simpa only [OriginalAimSetup.writes,sp,withStack,write,ite_true] using safe.setup
  exact (OriginalAimSetup.frame9 _ a setup).trans ((OriginalAimQuery.saved_frame _ a saves).trans query)

theorem firing_stack (gun : Fire.Gun) (s : X86Memory.State) :
    (E1M1AimSetup.firstTraversal gun s).core.regs 4=s.regs 4-(52#32) := by
  change (E1M1PathMapQuery.traversal (E1M1BulletAim.firstQuery gun s).core).core.regs 4=_
  rw [E1M1PathMapQuery.traversal_stack,E1M1PathMapFiring.query_stack]
  simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]

theorem firing_initialized_frame (gun : Fire.Gun) (s : X86Memory.State) (actor : Word)
    (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (geometry : E1M1FiringGeometry.Inputs gun s actor thing angle ox oy) (a : Word)
    (safe : E1M1PathMapSetup.StackSafe (s.regs 4-(112#32)) a) :
    load32 (firstScan gun s).core.memory a=load32 (E1M1PathInit.firstPath gun s).core.memory a := by
  apply initialized_frame _ ox oy thing.x thing.y (thing.attackEndpoint angle (Fixed.ofInt 1024)).1
    (thing.attackEndpoint angle (Fixed.ofInt 1024)).2
  · exact E1M1AimGeometry.path_inputs _ thing angle _ ox oy
      (E1M1FiringGeometry.query_geometry gun s actor thing angle ox oy geometry)
  · rw [firing_stack]
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe

/-- The trace used by line tests is the initialized production path, including
its original block-boundary nudges, not the unadjusted shooter coordinates. -/
theorem firing_trace (gun : Fire.Gun) (s : X86Memory.State) (actor : Word)
    (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (geometry : E1M1FiringGeometry.Inputs gun s actor thing angle ox oy)
    (safe : ∀ a∈[(0x2ba10#32),0x2ba14,0x2ba18,0x2ba1c],
      E1M1PathMapSetup.StackSafe (s.regs 4-(112#32)) a) :
    let trace := (Collision.pathStart ox oy thing.x thing.y (thing.attackEndpoint angle (Fixed.ofInt 1024)).1
      (thing.attackEndpoint angle (Fixed.ofInt 1024)).2).trace
    (load32 (firstScan gun s).core.memory 0x2ba10,load32 (firstScan gun s).core.memory 0x2ba14,
      load32 (firstScan gun s).core.memory 0x2ba18,load32 (firstScan gun s).core.memory 0x2ba1c)=
      (trace.x.raw.toBitVec,trace.y.raw.toBitVec,trace.dx.raw.toBitVec,trace.dy.raw.toBitVec) := by
  have keep (a : Word) (ha : a∈[(0x2ba10#32),0x2ba14,0x2ba18,0x2ba1c]) :=
    firing_initialized_frame gun s actor thing angle ox oy geometry a (safe a ha)
  rw [keep _ (by simp),keep _ (by simp),keep _ (by simp),keep _ (by simp)]
  exact (OriginalPathInit.ready _ ox oy _ _ _ _ (E1M1AimGeometry.path_inputs _ thing angle _ ox oy
    (E1M1FiringGeometry.query_geometry gun s actor thing angle ox oy geometry))).trace

theorem firing_epoch (gun : Fire.Gun) (s : X86Memory.State) (actor : Word)
    (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (geometry : E1M1FiringGeometry.Inputs gun s actor thing angle ox oy)
    (before : BeforeInit gun s (0x13580#32))
    (after : E1M1PathMapSetup.StackSafe (s.regs 4-(112#32)) (0x13580#32)) :
    load32 (firstScan gun s).core.memory 0x13580=load32 s.memory 0x13580+(1#32) := by
  apply (firing_initialized_frame gun s actor thing angle ox oy geometry _ after).trans
  have ready := OriginalPathInit.ready _ ox oy _ _ _ _ (E1M1AimGeometry.path_inputs _ thing angle _ ox oy
    (E1M1FiringGeometry.query_geometry gun s actor thing angle ox oy geometry))
  exact (congrArg (fun v => v.2.2) ready.globals).trans
    (congrArg (fun v : Word => v+1) (before_init_frame gun s _ before))

/-- A scan-header duplicate check compares the current epoch to the selected
linedef's stamp; selecting an index does not mutate either word. -/
theorem seen_iff (s : X86Memory.State) (i : Nat) :
    OriginalLineCell.already (OriginalLineCell.header (OriginalLineInvariant.atIndex s i)).core ↔
    load32 s.memory 0x13580=load32 s.memory (OriginalLineDispatch.pointer (OriginalLineInvariant.atIndex s i)+54) := by
  rfl

/-- Initial membership is read from DOS stamps, including wraparound of the
32-bit epoch. This does not assume every line is fresh on query entry. -/
theorem firing_seen (gun : Fire.Gun) (s : X86Memory.State) (actor : Word)
    (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (geometry : E1M1FiringGeometry.Inputs gun s actor thing angle ox oy)
    (before : BeforeInit gun s (0x13580#32))
    (after : E1M1PathMapSetup.StackSafe (s.regs 4-(112#32)) (0x13580#32))
    (lines : Word) (c : E1M1PathMap.Cell)
    (items : E1M1PathMapLookup.ScanWords (firstScan gun s).core lines c) (i : Fin c.ids.length)
    (safe : E1M1PathMapFiring.Safe gun s (E1M1PathMap.resolve lines ⟨(Fixed.ofInt 0),true,c.ids[i.val]⟩+54)) :
    OriginalLineCell.already (OriginalLineCell.header
      (OriginalLineInvariant.atIndex (firstScan gun s).core i.val)).core ↔
    load32 s.memory 0x13580+(1#32)=
      load32 s.memory (E1M1PathMap.resolve lines ⟨(Fixed.ofInt 0),true,c.ids[i.val]⟩+54) := by
  rw [seen_iff,items.pointers i (Fixed.ofInt 0),firing_epoch gun s actor thing angle ox oy geometry before after,
    firing_frame gun s actor thing angle ox oy geometry _ safe]
end Doom.Proofs.E1M1ScanMemory
