import Doom.Proofs.OriginalSideCleanup
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimSideCleanup
open Verification X86 X86Memory X86Control BlockSummary
open E1M1AimSideLoop E1M1AimSideStack
open E1M1NoiseAllocation (Region)

/-- Explicit owned/no-coalescing branch data; not an allocation/reachability claim. -/
structure Heap (l : LayoutData) where
  user : Word
  previous : Word
  following : Word

def header (l : LayoutData) := l.raw-24
def reads (l : LayoutData) (h : Heap l) : List Word :=
  [header l+12,header l+4,header l+20,header l+16,h.previous+4,h.following+4,h.user]
def links (l : LayoutData) (h : Heap l) : List Word :=
  [header l+20,header l+16,h.previous+4,h.following+4]
def stores (l : LayoutData) (h : Heap l) : List Word :=
  [h.user,header l+4,header l+8,header l+12]
structure Image (l : LayoutData) (h : Heap l) (m : Memory) : Prop where
  valid : load32 m (header l+12)=0x1d4a11
  owner : load32 m (header l+4)=h.user
  owned : 256<h.user.toNat
  cached : load32 m h.user=l.raw
  prev : load32 m (header l+20)=h.previous
  next : load32 m (header l+16)=h.following
  prevBusy : load32 m (h.previous+4)≠0
  nextBusy : load32 m (h.following+4)≠0

/-- All frames are static address/region conditions. In particular the owner
slot cannot alias output or upper saved stack. Metadata reads survive the loop;
link/busy reads additionally survive the four real deallocation stores. -/
structure Placement (l : LayoutData) (layout : Layout l) (h : Heap l) : Prop where
  readRegions : ∀ p∈reads l h, ∃ r : Region, r.Contains p ∧ Protected l layout r
  writeRegions : ∀ w∈stores l h, ∃ r : Region,
    r.Contains w ∧ r.Disjoint layout.stack ∧ r.Disjoint (upperRegion l) ∧
    r.Disjoint (region l.output (18*648)) ∧
    (∀ p∈links l h, ∃ q : Region, q.Contains p ∧ q.Disjoint r)

theorem stack_contains (l : LayoutData) (layout : Layout l) (off : Nat) (bound : off≤44) :
    layout.stack.Contains (l.sp-BitVec.ofNat 32 off) := by
  have reserve := layout.reserve
  have := l.sp.isLt
  simp only [Region.Contains,BitVec.toNat_sub,BitVec.toNat_ofNat]
  omega

theorem saved_frame (s : X86Memory.State) (p : Word)
    (safe : ∀ off∈([4,8,12,16] : List Nat), Apart p (s.regs 4-BitVec.ofNat 32 off)) :
    load32 (OriginalSideCleanup.saved s).memory p=load32 s.memory p := by
  have mem : (OriginalSideCleanup.saved s).memory=
    store32 (store32 (store32 (store32 s.memory (s.regs 4-4) 0x2e4e6)
      (s.regs 4-8) (s.regs 3)) (s.regs 4-12) (s.regs 1)) (s.regs 4-16) (s.regs 2) := by
    simp [OriginalSideCleanup.saved,X86Routine.pushWord,put,write,BitVec.sub_sub]
  rw [mem]
  change load32 (store32 (store32 (store32 (store32 s.memory (s.regs 4-(4#32)) 0x2e4e6) (s.regs 4-(8#32)) (s.regs 3)) (s.regs 4-(12#32)) (s.regs 1)) (s.regs 4-(16#32)) (s.regs 2)) p=load32 s.memory p
  rw [load_store_apart _ _ _ _ (safe 16 (by simp)),
    load_store_apart _ _ _ _ (safe 12 (by simp)),load_store_apart _ _ _ _ (safe 8 (by simp)),
    load_store_apart _ _ _ _ (safe 4 (by simp))]

theorem metadata (l : LayoutData) (layout : Layout l) (h : Heap l)
    (s : X86Memory.State) (f : Option Flags) (initial : Incoming l s)
    (placement : Placement l layout h) (p : Word) (read : p∈reads l h) :
    load32 (OriginalSideCleanup.saved (states s f 648).core).memory p=load32 s.memory p := by
  obtain ⟨r,contains,safe⟩ := placement.readRegions p read
  apply (saved_frame _ p ?_).trans
  · exact region_preserved l layout s f initial r safe p contains 648 (by decide)
  · intro off member
    rw [(states_invariant l layout s f initial 648 (by decide)).1.registers.stack]
    apply Region.apart contains _ safe.stack
    apply stack_contains
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    omega

theorem cache_owned (l : LayoutData) (layout : Layout l) (h : Heap l)
    (s : X86Memory.State) (f : Option Flags) (initial : Incoming l s)
    (placement : Placement l layout h) (image : Image l h s.memory) :
    load32 (states s f 648).core.memory h.user=l.raw := by
  obtain ⟨r,contains,safe⟩ := placement.readRegions h.user (by simp [reads])
  exact (region_preserved l layout s f initial r safe h.user contains 648 (by decide)).trans image.cached

theorem links_apart (l : LayoutData) (layout : Layout l) (h : Heap l)
    (placement : Placement l layout h) (p w : Word)
    (read : p∈links l h) (store : w∈stores l h) : Apart p w := by
  obtain ⟨r,contains,_,_,_,safe⟩ := placement.writeRegions w store
  obtain ⟨q,hq,disjoint⟩ := safe p read
  exact Region.apart hq contains disjoint

/-- Derive the exact post-push/post-store branch conditions from ONE incoming
heap image. No Ready condition on a reached machine is an input. -/
theorem cleanup_ready (l : LayoutData) (layout : Layout l) (h : Heap l)
    (s : X86Memory.State) (f : Option Flags) (initial : Incoming l s)
    (upper : UpperStack l layout) (placement : Placement l layout h)
    (image : Image l h s.memory) (raw : load32 s.memory (l.sp+4)=l.raw) :
    OriginalSideCleanup.Ready (states s f 648).core := by
  have sp := (states_invariant l layout s f initial 648 (by decide)).1.registers.stack
  have rr := saved_raw_pointer l layout s f initial upper raw
  have read := metadata l layout h s f initial placement
  generalize ht : (states s f 648).core=t at *
  have block : OriginalSideCleanup.block t=header l :=
    congrArg (fun x : Word => x-24) rr
  have owner : OriginalSideCleanup.owner t=h.user := by
    rw [OriginalSideCleanup.owner,block]
    exact (read _ (by simp [reads])).trans image.owner
  have first (p : Word) (hp : p∈links l h) :
      load32 (OriginalSideCleanup.firstMemory t) p=load32 s.memory p := by
    unfold OriginalSideCleanup.firstMemory
    rw [block,owner]
    rw [load_store_apart _ _ _ _ (links_apart l layout h placement p _ hp (by simp [stores])),
      load_store_apart _ _ _ _ (links_apart l layout h placement p _ hp (by simp [stores])),
      load_store_apart _ _ _ _ (links_apart l layout h placement p _ hp (by simp [stores]))]
    exact read p (by simp only [links,List.mem_cons,List.not_mem_nil,or_false] at hp; rcases hp with rfl|rfl|rfl|rfl <;> simp [reads])
  have clear (p : Word) (hp : p∈links l h) :
      load32 (OriginalSideCleanup.cleared t) p=load32 s.memory p := by
    rw [OriginalSideCleanup.cleared,block,
      load_store_apart _ _ _ _ (links_apart l layout h placement p _ hp (by simp [stores]))]
    exact first p hp
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [block]; exact (read _ (by simp [reads])).trans image.valid
  · rw [owner]; exact image.owned
  · have prev : OriginalSideCleanup.prev t=h.previous := by
      rw [OriginalSideCleanup.prev,block,first _ (by simp [links])]; exact image.prev
    rw [prev,clear _ (by simp [links])]; exact image.prevBusy
  · have next : OriginalSideCleanup.next t=h.following := by
      rw [OriginalSideCleanup.next,block,clear _ (by simp [links])]; exact image.next
    rw [next,clear _ (by simp [links])]; exact image.nextBusy
  · intro w hw
    have hw' : w.1∈stores l h := by
      simp only [OriginalSideCleanup.writes,block,owner,List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl|rfl|rfl <;> simp [stores]
    obtain ⟨r,contains,disjoint,_,_,_⟩ := placement.writeRegions w.1 hw'
    rw [sp]
    exact Region.apart (stack_contains l layout 4 (by decide)) contains (by
      rcases disjoint with a|b; exact Or.inr a; exact Or.inl b)

def program : X86ByteRoutine.Program := fun pc =>
  match E1M1AimSideLookup.iterationProgram pc with
  | some op => some op
  | none => X86ByteRoutine.liftProgram OriginalSideCleanup.program pc

theorem loop_agreement (pc : Nat) (valid : E1M1AimSideLookup.iterationProgram pc≠none) :
    program pc=E1M1AimSideLookup.iterationProgram pc := by
  unfold program
  cases h : E1M1AimSideLookup.iterationProgram pc <;> simp_all

/-- Embeds only the executed selected listing, whose every instruction is
kernel-decoded from the authenticated full byte ranges. -/
theorem lift_cleanup (n : Nat) (s t : X86Control.State)
    (path : X86Routine.Prefix OriginalSideCleanup.program [] n s t) :
    X86ByteRoutine.Prefix program [] n s t := by
  induction path with
  | nil => exact .nil _
  | @step n s middle last op len active dec exe rest ih =>
    have inside : (0x2e4dd≤s.pc ∧ s.pc<0x2e4f0) ∨ (0x39600≤s.pc ∧ s.pc<0x39690) := by
      by_cases a : 0x2e4dd≤s.pc ∧ s.pc<0x2e4f0
      · exact Or.inl a
      · by_cases b : 0x39600≤s.pc ∧ s.pc<0x39690
        · exact Or.inr b
        · simp [OriginalSideCleanup.program,OriginalSideCleanup.bytesProgram,a,b] at dec
    have empty : E1M1AimSideLookup.iterationProgram s.pc=none := by
      simp [E1M1AimSideLookup.iterationProgram,E1M1AimSideLookup.joined,
        E1M1AimTextureSearch.joined,OriginalTextureSearch.program,OriginalTextureSearch.bytesProgram,
        OriginalTextureComparator.joined,OriginalTextureComparator.combine,
        OriginalTextureIteration.program,OriginalTextureIteration.bytesProgram,
        OriginalTextureFold.bytesProgram,OriginalTextureTable.program,OriginalTextureTable.bytesProgram,
        X86ByteRoutine.liftProgram,
        show ¬(s.pc<0x2e47e ∨ (0x2e4af≤s.pc ∧ s.pc<0x2e4dd)) by omega,
        show ¬(0x2e47e≤s.pc ∧ s.pc<0x2e4af) by omega,
        show ¬(0x346f0≤s.pc ∧ s.pc<0x34700) by omega,
        show ¬(0x34750≤s.pc ∧ s.pc<0x34773) by omega,
        show ¬(0x4198c≤s.pc ∧ s.pc<0x41999) by omega,
        show ¬(0x419b5≤s.pc ∧ s.pc<0x419ce) by omega,
        show ¬(0x41999≤s.pc ∧ s.pc<0x419b5) by omega,
        show ¬(0x34700≤s.pc ∧ s.pc<0x34722) by omega,
        show ¬(0x3473c≤s.pc ∧ s.pc<0x34741) by omega,
        show ¬(0x34722≤s.pc ∧ s.pc<0x3473c) by omega,
        show ¬(0x34741≤s.pc ∧ s.pc<0x34747) by omega]
    exact .step (op:=.base op) (length:=len) (middle:=middle) (by simp)
      (by simp [program,empty,X86ByteRoutine.liftProgram,dec]) exe ih

theorem execution (l : LayoutData) (layout : Layout l) (h : Heap l) (s : X86Memory.State)
    (f : Option Flags) (initial : Incoming l s) (upper : UpperStack l layout)
    (placement : Placement l layout h) (image : Image l h s.memory)
    (raw : load32 s.memory (l.sp+4)=l.raw) :
    ∃ k≤648*(3*(202*2147483647+30)+36)+40,
      X86ByteRoutine.Prefix program [] k ⟨s,f,0x2e46a⟩
        (OriginalSideCleanup.result (states s f 648).core) := by
  obtain ⟨n,hn,path⟩ := loop_path l layout s f initial 648 (by decide)
  have ready := cleanup_ready l layout h s f initial upper placement image raw
  obtain ⟨m,hm,cleanup⟩ := OriginalSideCleanup.execution _ (states s f 648).flags ready
  have seam : (⟨(states s f 648).core,(states s f 648).flags,0x2e4dd⟩ : X86Control.State)=states s f 648 := by
    rw [←show (states s f 648).pc=0x2e4dd from (E1M1AimSideLoop.execution l layout s f initial).2.1]
  rw [seam] at cleanup
  exact ⟨n+m,by omega,(path.transfer program [] loop_agreement (by simp)).trans (lift_cleanup m _ _ cleanup)⟩
def savedRegisters : List (Reg × Word) := [(5,8),(7,12),(6,16),(2,20),(1,24),(3,28)]

theorem result_properties (t : X86Memory.State) (ready : OriginalSideCleanup.Ready t) :
    (OriginalSideCleanup.result t).core.memory=OriginalSideCleanup.cleared t ∧
    (OriginalSideCleanup.result t).pc=(load32 (OriginalSideCleanup.cleared t) (t.regs 4+32)).toNat ∧
    (OriginalSideCleanup.result t).core.regs 4=t.regs 4+36 ∧
    (∀ r off, (r,off)∈savedRegisters → (OriginalSideCleanup.result t).core.regs r=
      load32 (OriginalSideCleanup.cleared t) (t.regs 4+off)) := by
  have ret := OriginalSideCleanup.return_properties t ready
  refine ⟨?_,?_,?_,?_⟩
  · simp [OriginalSideCleanup.result,OriginalSideCleanup.tail,OriginalSideCleanup.restored,
      OriginalSideCleanup.popCore,put,ret.2.2]
  · simp [OriginalSideCleanup.result,OriginalSideCleanup.tail,ret.2.1,ret.2.2]
  · simp [OriginalSideCleanup.result,OriginalSideCleanup.tail,OriginalSideCleanup.restored,put,write,ret.2.1]
  · intro r off member
    simp only [savedRegisters,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with eq|eq|eq|eq|eq|eq <;> cases eq <;>
      simp [OriginalSideCleanup.result,OriginalSideCleanup.tail,OriginalSideCleanup.restored,
        OriginalSideCleanup.popCore,put,write,ret.2.1,ret.2.2,BitVec.add_assoc]

theorem clear_frame (l : LayoutData) (layout : Layout l) (h : Heap l)
    (s : X86Memory.State) (f : Option Flags) (initial : Incoming l s)
    (upper : UpperStack l layout) (placement : Placement l layout h)
    (image : Image l h s.memory) (raw : load32 s.memory (l.sp+4)=l.raw)
    (p : Word) (safeStack : ∀ off∈([4,8,12,16] : List Nat), Apart p (l.sp-BitVec.ofNat 32 off))
    (safeWrites : ∀ w∈stores l h, Apart p w) :
    load32 (OriginalSideCleanup.cleared (states s f 648).core) p=
      load32 (states s f 648).core.memory p := by
  have sp := (states_invariant l layout s f initial 648 (by decide)).1.registers.stack
  have rr := saved_raw_pointer l layout s f initial upper raw
  have read := metadata l layout h s f initial placement (header l+4) (by simp [reads])
  generalize ht : (states s f 648).core=t at *
  have block : OriginalSideCleanup.block t=header l := congrArg (fun x : Word => x-24) rr
  have owner : OriginalSideCleanup.owner t=h.user := by
    rw [OriginalSideCleanup.owner,block]; exact read.trans image.owner
  rw [OriginalSideCleanup.cleared,OriginalSideCleanup.firstMemory,block,owner,
    load_store_apart _ _ _ _ (safeWrites _ (by simp [stores])),
    load_store_apart _ _ _ _ (safeWrites _ (by simp [stores])),
    load_store_apart _ _ _ _ (safeWrites _ (by simp [stores])),
    load_store_apart _ _ _ _ (safeWrites _ (by simp [stores]))]
  exact saved_frame t p (by simpa only [sp] using safeStack)

/-- The exact original caller return, six restored registers and every emitted
sector pointer survive deallocation. Ownership is still an incoming condition. -/
theorem observations (l : LayoutData) (layout : Layout l) (h : Heap l) (s : X86Memory.State)
    (f : Option Flags) (initial : Incoming l s) (upper : UpperStack l layout)
    (placement : Placement l layout h) (image : Image l h s.memory)
    (raw : load32 s.memory (l.sp+4)=l.raw) :
    let t := OriginalSideCleanup.result (states s f 648).core
    Outputs l 648 t.core.memory ∧ t.pc=(load32 s.memory (l.sp+32)).toNat ∧
      t.core.regs 4=l.sp+36 ∧
      (∀ r off, (r,off)∈savedRegisters → t.core.regs r=load32 s.memory (l.sp+off)) := by
  have ready := cleanup_ready l layout h s f initial upper placement image raw
  have props := result_properties _ ready
  have sp := (states_invariant l layout s f initial 648 (by decide)).1.registers.stack
  have saved (off : Nat) (low : 4≤off) (high : off+4≤36) :
      load32 (OriginalSideCleanup.cleared (states s f 648).core) (l.sp+BitVec.ofNat 32 off)=
        load32 s.memory (l.sp+BitVec.ofNat 32 off) := by
    apply (clear_frame l layout h s f initial upper placement image raw _ ?_ ?_).trans
    · exact upper_preserved l layout s f initial upper off low high
    · intro n hn
      apply Region.apart (upper_contains l layout upper off low high) _ upper.protection.stack
      apply stack_contains
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hn; omega
    · intro w hw
      obtain ⟨r,contains,_,sep,_,_⟩ := placement.writeRegions w hw
      apply Region.apart (upper_contains l layout upper off low high) contains
      rcases sep with a|b; exact Or.inr a; exact Or.inl b
  refine ⟨?_,?_,?_,?_⟩
  · intro row bound
    rw [props.1]
    have contains := region_field l.output (18*648) (18*row.val+14) layout.outputBound (by have := row.isLt; omega)
    have address : l.output+BitVec.ofNat 32 (18*row.val+14)=cursor l.output 18 row.val+14 := by
      simp [cursor,BitVec.ofNat_add,BitVec.add_assoc]
    rw [address] at contains
    rw [clear_frame l layout h s f initial upper placement image raw _ ?_ ?_]
    · exact (E1M1AimSideLoop.execution l layout s f initial).2.2.1 row bound
    · intro n hn
      apply Region.apart contains _ layout.outputStack
      apply stack_contains
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hn; omega
    · intro w hw
      obtain ⟨r,has,_,_,sep,_⟩ := placement.writeRegions w hw
      apply Region.apart contains has
      rcases sep with a|b; exact Or.inr a; exact Or.inl b
  · rw [props.2.1,sp]
    exact congrArg BitVec.toNat (saved 32 (by decide) (by decide))
  · exact props.2.2.1.trans (congrArg (fun v : Word => v+36) sp)
  · intro r off member
    rw [props.2.2.2 r off member,sp]
    simp only [savedRegisters,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with eq|eq|eq|eq|eq|eq <;> cases eq <;> exact saved _ (by decide) (by decide)
end Doom.Proofs.E1M1AimSideCleanup
