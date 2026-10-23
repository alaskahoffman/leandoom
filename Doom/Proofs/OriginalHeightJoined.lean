import Doom.Proofs.OriginalHeightControl

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000
namespace Doom.Proofs.PlayerHeight
open Verification X86 X86Memory X86Control BlockSummary

/-- Bounded execution without an artificial block-boundary stop. -/
def Reaches (budget : Nat) (s t : X86Control.State) : Prop :=
  ∃ n, n ≤ budget ∧ X86Routine.Prefix program [] n s t

theorem reaches_of_run {exits budget s t}
    (h : X86Routine.run program exits budget s = some t) : Reaches budget s t := by
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path h
  exact ⟨n,hn,path.transfer program [] (fun _ _ => rfl) (by simp)⟩

theorem prefix_trans {n m s u t}
    (h : X86Routine.Prefix program [] n s u) (k : X86Routine.Prefix program [] m u t) :
    X86Routine.Prefix program [] (n+m) s t := by
  induction h with
  | nil => simpa using k
  | step active decoded executed rest ih =>
    simpa only [Nat.succ_add] using X86Routine.Prefix.step active decoded executed (ih k)

theorem Reaches.trans {n m s u t} (h : Reaches n s u) (k : Reaches m u t) : Reaches (n+m) s t := by
  obtain ⟨a,ha,pa⟩ := h
  obtain ⟨b,hb,pb⟩ := k
  exact ⟨a+b,by omega,prefix_trans pa pb⟩

def viewWrites (p : Word) : List Word := [p+(16#32),p+(20#32),p+(24#32),p+(28#32)]

def contextReads (p obj a : Word) : Prop :=
  a ∈ [p,p+(4#32),p+(196#32),obj+(20#32),obj+(60#32),obj+(72#32),obj+(76#32),184192,184208,0x13584] ∨
  ∃ i : Fin 10240, a = 0x5a84 + BitVec.ofNat 32 (i.val*4)

structure Context (p obj : Word) (body : Motion) (time : Int32)
    (ground live : Bool) (m : Memory) : Prop where
  pointer : load32 m p = obj
  z : load32 m (obj+(20#32)) = body.z.raw.toBitVec
  ceiling : load32 m (obj+(60#32)) = body.ceilingz.raw.toBitVec
  momx : load32 m (obj+(72#32)) = body.momx.raw.toBitVec
  momy : load32 m (obj+(76#32)) = body.momy.raw.toBitVec
  tic : load32 m 184192 = time.toBitVec
  grounded : (load32 m (184208#32) != (0#32)) = ground
  noMomentum : ((m (p+(196#32)) &&& (4#8)) != (0#8)) = body.noMomentum
  alive : (load32 m (p+(4#32)) == (0#32)) = live
  tables : ThrustTables m

structure Words (p : Word) (m : Memory) (v : ViewState) : Prop where
  height : load32 m (p+(20#32)) = v.height.raw.toBitVec
  delta : load32 m (p+(24#32)) = v.delta.raw.toBitVec
  bob : load32 m (p+(28#32)) = v.bob.raw.toBitVec

def Safe (p obj : Word) : Prop :=
  ∀ a, contextReads p obj a → ∀ b, b ∈ viewWrites p → Apart a b

theorem context_transport {p obj body time ground live m m'}
    (h : Context p obj body time ground live m)
    (keep : ∀ a, contextReads p obj a → load32 m' a = load32 m a) :
    Context p obj body time ground live m' := by
  have byteKeep : m' (p+(196#32)) = m (p+(196#32)) := by
    have eq := congrArg (fun v : Word => v.extractLsb' 0 8) (keep (p+(196#32)) (by simp [contextReads]))
    simpa only [load_byte] using eq
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [keep _ (by simp [contextReads])]; exact h.pointer
  · rw [keep _ (by simp [contextReads])]; exact h.z
  · rw [keep _ (by simp [contextReads])]; exact h.ceiling
  · rw [keep _ (by simp [contextReads])]; exact h.momx
  · rw [keep _ (by simp [contextReads])]; exact h.momy
  · rw [keep _ (by simp [contextReads])]; exact h.tic
  · rw [keep _ (by simp [contextReads])]; exact h.grounded
  · rw [byteKeep]; exact h.noMomentum
  · rw [keep _ (by simp [contextReads])]; exact h.alive
  · rw [keep _ (by simp [contextReads])]; exact h.tables.cosinePointer
  · intro i; rw [keep _ (Or.inr ⟨i,rfl⟩)]; exact h.tables.entries i

theorem Frame.context {p obj body time ground live m m' writes}
    (h : Context p obj body time ground live m) (safe : Safe p obj)
    (frame : Frame m m' writes) (sub : ∀ b, b ∈ writes → b ∈ viewWrites p) :
    Context p obj body time ground live m' :=
  context_transport h (fun a ha => frame a (fun b hb => safe a ha b (sub b hb)))

/-- A read of another player-field slot survives every write in the given list. -/
theorem Frame.slot {p m m'} (js : List (Fin 8)) (i : Fin 8) (apart : i ∉ js)
    (frame : Frame m m' (js.map (fun j => p + BitVec.ofNat 32 (4*j.val)))) :
    load32 m' (p + BitVec.ofNat 32 (4*i.val)) = load32 m (p + BitVec.ofNat 32 (4*i.val)) := by
  apply frame
  intro b hb
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hb
  exact slots_apart p i j (by intro he; subst j; exact apart hj)

theorem Frame.widen {m m' small big} (h : Frame m m' small)
    (sub : ∀ b, b ∈ small → b ∈ big) : Frame m m' big :=
  fun a ha => h a (fun b hb => ha b (sub b hb))

structure Post (p obj sp : Word) (body : Motion) (time : Int32)
    (ground live : Bool) (v : ViewState) (s : X86Control.State) : Prop where
  player : s.core.regs 1 = p
  stack : s.core.regs 4 = sp
  context : Context p obj body time ground live s.core.memory
  words : Words p s.core.memory v

theorem amplitude_segment (s : X86Memory.State) (f : Option Flags) (obj : Word)
    (body : Motion) (time : Int32) (ground live : Bool) (v : ViewState)
    (ctx : Context (s.regs 0) obj body time ground live s.memory)
    (words : Words (s.regs 0) s.memory v) (safe : Safe (s.regs 0) obj) :
    ∃ t, Reaches 20 ⟨s,f,6⟩ t ∧ t.pc = 64 ∧
      Post (s.regs 0) obj (s.regs 4) body time ground live
        {v with bob := ViewState.bobAmplitude body.momx body.momy} t ∧
      Frame s.memory t.core.memory (viewWrites (s.regs 0)) := by
  have obs := amplitude_execution s f
  obtain ⟨t,ht,ho⟩ := Option.map_eq_some_iff.mp obs
  simp only [Prod.mk.injEq] at ho
  obtain ⟨pc,bob,player,stack⟩ := ho
  have frame : Frame s.memory t.core.memory [s.regs 0+(28#32)] := by
    intro a ha
    have h := amplitude_frame s f a ha
    simpa only [ht,Option.map_some,Option.some.injEq] using h
  have result : amplitudeWord (bobSum s) = (ViewState.bobAmplitude body.momx body.momy).raw.toBitVec := by
    simp only [bobSum,ctx.pointer,ctx.momx,ctx.momy,amplitude_runtime]
  refine ⟨t,reaches_of_run ht,pc,⟨player,stack,frame.context ctx safe (by simp [viewWrites]),?_⟩,
    frame.widen (by simp [viewWrites])⟩
  constructor
  · exact (frame.slot [7] 5 (by decide)).trans words.height
  · exact (frame.slot [7] 6 (by decide)).trans words.delta
  · exact bob.trans result

theorem recovery_segment (s : X86Memory.State) (f : Option Flags)
    (p obj sp : Word) (body : Motion) (time : Int32) (ground live : Bool) (v : ViewState)
    (post : Post p obj sp body time ground live v ⟨s,f,177⟩)
    (safe : Safe p obj) (active : s.regs 5 = 0) :
    ∃ t, Reaches 30 ⟨s,f,177⟩ t ∧ t.pc = 263 ∧
      t.core.regs 0 = s.regs 0 ∧ Post p obj sp body time ground live v.recoverHeight t ∧
      Frame s.memory t.core.memory (viewWrites p) := by
  have obs := recovery_execution s f active
  obtain ⟨t,ht,ho⟩ := Option.map_eq_some_iff.mp obs
  simp only [Prod.mk.injEq] at ho
  obtain ⟨pc,height,delta,offset,player,stack⟩ := ho
  have pp : s.regs 1 = p := post.player
  have frame : Frame s.memory t.core.memory [p+(20#32),p+(24#32)] := by
    intro a ha
    have h := recovery_frame s f active a (by simpa only [pp] using ha)
    simpa only [ht,Option.map_some,Option.some.injEq] using h
  rw [pp,post.words.height,post.words.delta,recover_runtime] at height delta
  refine ⟨t,reaches_of_run ht,pc,offset,⟨player.trans pp,stack.trans post.stack,
    frame.context post.context safe (by simp [viewWrites]),?_⟩,frame.widen (by simp [viewWrites])⟩
  constructor
  · simpa only [pp] using height
  · simpa only [pp] using delta
  · exact (frame.slot [5,6] 7 (by decide)).trans post.words.bob

theorem ceiling_segment (s : X86Memory.State) (f : Option Flags)
    (p obj sp : Word) (body : Motion) (time : Int32) (ground live : Bool) (v : ViewState)
    (offset : Fixed) (post : Post p obj sp body time ground live v ⟨s,f,263⟩)
    (safe : Safe p obj) (eaxOffset : s.regs 0 = offset.raw.toBitVec) :
    ∃ t, Reaches 12 ⟨s,f,263⟩ t ∧ t.pc = 295 ∧
      Post p obj sp body time ground live v t ∧
      load32 t.core.memory (p+(16#32)) = (ViewState.clampZ body v.height offset).raw.toBitVec ∧
      Frame s.memory t.core.memory (viewWrites p) := by
  have pp : s.regs 1 = p := post.player
  have ptr : viewObject s = obj := by simpa only [viewObject,pp] using post.context.pointer
  have apart : Apart (viewObject s+(60#32)) (s.regs 1+(16#32)) := by
    rw [ptr,pp]; exact safe _ (by simp [contextReads]) _ (by simp [viewWrites])
  have obs := ceiling_execution s f apart
  obtain ⟨t,ht,ho⟩ := Option.map_eq_some_iff.mp obs
  simp only [Prod.mk.injEq] at ho
  obtain ⟨pc,z,player,stack⟩ := ho
  have frame : Frame s.memory t.core.memory [p+(16#32)] := by
    intro a ha
    have h := ceiling_frame s f a (by simpa only [pp] using ha)
    simpa only [ht,Option.map_some,Option.some.injEq] using h
  have result : clampWord (viewCandidate s) (viewCeiling s) =
      (ViewState.clampZ body v.height offset).raw.toBitVec := by
    simp only [viewCandidate,viewCeiling,ptr,pp,post.context.z,post.context.ceiling,
      post.words.height,eaxOffset]
    change clampWord (body.z+v.height+offset).raw.toBitVec
      (body.ceilingz-Fixed.ofInt 4).raw.toBitVec = _
    rw [clamp_runtime]; rfl
  refine ⟨t,reaches_of_run ht,pc,⟨player.trans pp,stack.trans post.stack,
    frame.context post.context safe (by simp [viewWrites]),?_⟩,?_,frame.widen (by simp [viewWrites])⟩
  · exact ⟨(frame.slot [4] 5 (by decide)).trans post.words.height,
      (frame.slot [4] 6 (by decide)).trans post.words.delta,
      (frame.slot [4] 7 (by decide)).trans post.words.bob⟩
  · simpa only [pp,result] using z

theorem offset_segment (s : X86Memory.State) (f : Option Flags)
    (p obj sp : Word) (body : Motion) (time : Int32) (ground live : Bool) (v : ViewState)
    (post : Post p obj sp body time ground live v ⟨s,f,130⟩) :
    ∃ t, Reaches 10 ⟨s,f,130⟩ t ∧ t.pc = 170 ∧
      Post p obj sp body time ground live v t ∧
      t.core.regs 0 = (ViewState.bobOffset v.bob time).raw.toBitVec ∧ t.core.memory = s.memory := by
  have obs := offset_execution s f
  obtain ⟨t,ht,ho⟩ := Option.map_eq_some_iff.mp obs
  simp only [Prod.mk.injEq] at ho
  obtain ⟨pc,offset,player,stack,mem⟩ := ho
  have result := offset_runtime s v.bob time post.context.tic
    (by rw [show s.regs 1 = p from post.player]; exact post.words.bob) post.context.tables
  refine ⟨t,reaches_of_run ht,pc,⟨player.trans post.player,stack.trans post.stack,?_,?_⟩,
    offset.trans result,mem⟩
  · simpa only [mem] using post.context
  · simpa only [mem] using post.words

theorem at_pc (t : X86Control.State) {pc : Nat} (h : t.pc = pc) : ⟨t.core,t.flags,pc⟩ = t := by rw [←h]

theorem Frame.trans {a b c writes} (h : Frame a b writes) (k : Frame b c writes) : Frame a c writes :=
  fun addr safe => (k addr safe).trans (h addr safe)

theorem airborne_segment (s : X86Memory.State) (f : Option Flags)
    (p obj sp : Word) (body : Motion) (time : Int32) (ground live : Bool) (v : ViewState)
    (post : Post p obj sp body time ground live v ⟨s,f,82⟩) (safe : Safe p obj) :
    ∃ t, Reaches 17 ⟨s,f,82⟩ t ∧ t.pc = 295 ∧
      Post p obj sp body time ground live v t ∧
      load32 t.core.memory (p+(16#32)) = (body.z+v.height).raw.toBitVec ∧
      Frame s.memory t.core.memory (viewWrites p) := by
  have pp : s.regs 1 = p := post.player
  obtain ⟨u,hu,ho⟩ := Option.map_eq_some_iff.mp (early_execution s f)
  simp only [Prod.mk.injEq] at ho
  obtain ⟨pcu,pu,su⟩ := ho
  have fr1 : Frame s.memory u.core.memory [p+(16#32)] := by
    intro a ha
    have eq := early_frame s f a (by rw [pp]; exact ha _ (by simp))
    simpa only [hu,Option.map_some,Option.some.injEq] using eq
  have ctx := fr1.context post.context safe (by simp [viewWrites])
  have words : Words p u.core.memory v :=
    ⟨(fr1.slot [4] 5 (by decide)).trans post.words.height,
     (fr1.slot [4] 6 (by decide)).trans post.words.delta,
     (fr1.slot [4] 7 (by decide)).trans post.words.bob⟩
  have up : u.core.regs 1 = p := pu.trans pp
  obtain ⟨t,ht,ho⟩ := Option.map_eq_some_iff.mp (airborne_tail u.core u.flags 0)
  simp only [Prod.mk.injEq] at ho
  obtain ⟨pc,z,pt,st⟩ := ho
  have fr2 : Frame u.core.memory t.core.memory [p+(16#32)] := by
    intro a ha
    have eq := airborne_frame u.core u.flags a (by rw [up]; exact ha _ (by simp))
    simpa only [ht,Option.map_some,Option.some.injEq] using eq
  have path2 : Reaches 6 u t := by simpa only [at_pc u pcu] using reaches_of_run ht
  refine ⟨t,(reaches_of_run hu).trans path2,pc,⟨pt.trans up,st.trans (su.trans post.stack),
    fr2.context ctx safe (by simp [viewWrites]),?_⟩,?_,
    (fr1.widen (by simp [viewWrites])).trans (fr2.widen (by simp [viewWrites]))⟩
  · exact ⟨(fr2.slot [4] 5 (by decide)).trans words.height,
      (fr2.slot [4] 6 (by decide)).trans words.delta,
      (fr2.slot [4] 7 (by decide)).trans words.bob⟩
  · simpa only [up,ctx.pointer,ctx.z,words.height,fixed_add_raw,Int32.toBitVec_add] using z

theorem Reaches.weaken {n m s t} (h : Reaches n s t) (bound : n ≤ m) : Reaches m s t := by
  obtain ⟨k,hk,path⟩ := h; exact ⟨k,by omega,path⟩

theorem Post.repc {p obj sp body time ground live v s}
    (h : Post p obj sp body time ground live v s) (pc : Nat) :
    Post p obj sp body time ground live v ⟨s.core,s.flags,pc⟩ :=
  ⟨h.player,h.stack,h.context,h.words⟩

theorem live_segment (s : X86Memory.State) (f : Option Flags)
    (p obj sp : Word) (body : Motion) (time : Int32) (ground live : Bool) (v : ViewState)
    (post : Post p obj sp body time ground live v ⟨s,f,170⟩) (safe : Safe p obj) :
    ∃ t, Reaches 33 ⟨s,f,170⟩ t ∧ t.pc = 263 ∧
      Post p obj sp body time ground live (if live then v.recoverHeight else v) t ∧
      t.core.regs 0 = s.regs 0 ∧ Frame s.memory t.core.memory (viewWrites p) := by
  let l := liveEnd s
  have path : Reaches 3 ⟨s,f,170⟩ l := reaches_of_run (live_execution s f)
  have pp : s.regs 1 = p := post.player
  have lp : Post p obj sp body time ground live v l := by
    refine ⟨?_,?_,post.context,post.words⟩
    · simpa [l,liveEnd,put,write] using pp
    · simpa [l,liveEnd,put,write] using post.stack
  have ax : l.core.regs 0 = s.regs 0 := by simp [l,liveEnd,put,write]
  have mem : l.core.memory = s.memory := rfl
  by_cases hz : load32 s.memory (p+(4#32)) = (0#32)
  · have hl : live = true := by have h := post.context.alive; simpa only [hz,BEq.rfl] using h.symm
    have pc : l.pc = 177 := by simp [l,liveEnd,pp,hz]
    have active : l.core.regs 5 = 0 := by simp [l,liveEnd,put,write,pp,hz]
    obtain ⟨t,ht,pt,axr,postt,frame⟩ := recovery_segment l.core l.flags p obj sp body time ground live v
      (lp.repc 177) safe active
    rw [at_pc l pc] at ht
    exact ⟨t,path.trans ht,pt,by simpa only [hl,↓reduceIte] using postt,
      axr.trans ax,by simpa only [mem] using frame⟩
  · have hl : live = false := by
      apply post.context.alive.symm.trans
      apply Bool.eq_false_iff.mpr
      intro he; exact hz (eq_of_beq he)
    have pc : l.pc = 263 := by simp [l,liveEnd,pp,hz]
    exact ⟨l,path.weaken (by decide),pc,by simpa only [hl,Bool.false_eq_true,↓reduceIte] using lp,
      ax,fun _ _ => rfl⟩

theorem ground_segment (s : X86Memory.State) (f : Option Flags)
    (p obj sp : Word) (body : Motion) (time : Int32) (ground live : Bool) (v : ViewState)
    (post : Post p obj sp body time ground live v ⟨s,f,130⟩) (safe : Safe p obj) :
    ∃ t, Reaches 55 ⟨s,f,130⟩ t ∧ t.pc = 295 ∧
      Post p obj sp body time ground live (if live then v.recoverHeight else v) t ∧
      load32 t.core.memory (p+(16#32)) =
        (ViewState.clampZ body (if live then v.recoverHeight else v).height
          (ViewState.bobOffset v.bob time)).raw.toBitVec ∧
      Frame s.memory t.core.memory (viewWrites p) := by
  obtain ⟨o,po,pco,posto,ao,mo⟩ := offset_segment s f p obj sp body time ground live v post
  obtain ⟨r,pr,pcr,postr,ar,fr⟩ := live_segment o.core o.flags p obj sp body time ground live v
    (posto.repc 170) safe
  obtain ⟨t,pt,pct,postt,zt,ft⟩ := ceiling_segment r.core r.flags p obj sp body time ground live
    (if live then v.recoverHeight else v) (ViewState.bobOffset v.bob time)
    (postr.repc 263) safe (ar.trans ao)
  rw [at_pc o pco] at pr
  rw [at_pc r pcr] at pt
  exact ⟨t,(po.trans pr).trans pt,pct,postt,zt,by simpa only [mo] using fr.trans ft⟩

@[simp] theorem guard_core (s : X86Memory.State) : (guardEnd s).core = s := by
  unfold guardEnd; split <;> rfl

theorem guard_pc (s : X86Memory.State) (p obj : Word) (body : Motion) (time : Int32)
    (ground live : Bool) (pp : s.regs 1 = p) (ctx : Context p obj body time ground live s.memory) :
    (guardEnd s).pc = if body.noMomentum || !ground then 82 else 130 := by
  have nm : noMomentumWord s = body.noMomentum := by
    simpa only [noMomentumWord,pp] using ctx.noMomentum
  by_cases hz : load32 s.memory (184208#32) = (0#32)
  · have gr : ground = false := by simpa only [hz,bne,BEq.rfl,Bool.not_true] using ctx.grounded.symm
    cases hn : body.noMomentum <;> simp [guardEnd,nm,gr,hz,hn]
  · have eqfalse : (load32 s.memory (184208#32) == (0#32)) = false :=
      Bool.eq_false_iff.mpr (fun h => hz (eq_of_beq h))
    have gr : ground = true := by simpa only [bne,eqfalse,Bool.not_false] using ctx.grounded.symm
    cases hn : body.noMomentum <;> simp [guardEnd,nm,gr,hz,hn]

theorem calcHeight_shape (v : ViewState) (body : Motion) (time : Int32) (ground live : Bool) :
    v.calcHeight body time ground live =
      let w := {v with bob := ViewState.bobAmplitude body.momx body.momy}
      if body.noMomentum || !ground then {w with z := body.z+v.height}
      else
        let r := if live then w.recoverHeight else w
        {r with z := ViewState.clampZ body r.height (ViewState.bobOffset w.bob time)} := by
  cases hn : body.noMomentum <;> cases ground <;> cases live <;>
    simp [ViewState.calcHeight,hn]

theorem Post.withZ {p obj sp body time ground live v s}
    (h : Post p obj sp body time ground live v s) (z : Fixed) :
    Post p obj sp body time ground live {v with z} s :=
  ⟨h.player,h.stack,h.context,⟨h.words.height,h.words.delta,h.words.bob⟩⟩

/-- Every body path joins the original arithmetic blocks, deriving their entry
contracts from a single initial context. No intermediate-state premises. -/
theorem body_segment (s : X86Memory.State) (f : Option Flags) (obj : Word)
    (body : Motion) (time : Int32) (ground live : Bool) (v : ViewState)
    (ctx : Context (s.regs 0) obj body time ground live s.memory)
    (words : Words (s.regs 0) s.memory v) (safe : Safe (s.regs 0) obj) :
    ∃ t, Reaches 79 ⟨s,f,6⟩ t ∧ t.pc = 295 ∧
      Post (s.regs 0) obj (s.regs 4) body time ground live (v.calcHeight body time ground live) t ∧
      load32 t.core.memory (s.regs 0+(16#32)) = (v.calcHeight body time ground live).z.raw.toBitVec ∧
      Frame s.memory t.core.memory (viewWrites (s.regs 0)) := by
  let w := {v with bob := ViewState.bobAmplitude body.momx body.momy}
  obtain ⟨a,pa,pca,posta,fa⟩ := amplitude_segment s f obj body time ground live v ctx words safe
  let g := guardEnd a.core
  have pg : Reaches 4 a g := by
    simpa only [at_pc a pca] using reaches_of_run (guard_execution a.core a.flags)
  have postg : Post (s.regs 0) obj (s.regs 4) body time ground live w g := by
    exact ⟨by simpa only [g,guard_core] using posta.player,
      by simpa only [g,guard_core] using posta.stack,
      by simpa only [g,guard_core] using posta.context,
      by simpa only [g,guard_core] using posta.words⟩
  have pcg := guard_pc a.core (s.regs 0) obj body time ground live posta.player posta.context
  have mg : g.core.memory = a.core.memory := by simp only [g,guard_core]
  by_cases air : (body.noMomentum || !ground) = true
  · have pc : g.pc = 82 := by simpa only [air,Bool.false_eq_true,↓reduceIte] using pcg
    obtain ⟨t,pt,pct,postt,zt,ft⟩ := airborne_segment g.core g.flags (s.regs 0) obj (s.regs 4)
      body time ground live w (postg.repc 82) safe
    rw [at_pc g pc] at pt
    refine ⟨t,((pa.trans pg).trans pt).weaken (by decide),pct,?_,?_,
      fa.trans (by simpa only [mg] using ft)⟩
    · simpa only [calcHeight_shape,air,Bool.false_eq_true,↓reduceIte] using postt.withZ _
    · simpa only [calcHeight_shape,air,Bool.false_eq_true,↓reduceIte] using zt
  · have pc : g.pc = 130 := by simpa only [air,Bool.false_eq_true,↓reduceIte] using pcg
    obtain ⟨t,pt,pct,postt,zt,ft⟩ := ground_segment g.core g.flags (s.regs 0) obj (s.regs 4)
      body time ground live w (postg.repc 130) safe
    rw [at_pc g pc] at pt
    refine ⟨t,(pa.trans pg).trans pt,pct,?_,?_,fa.trans (by simpa only [mg] using ft)⟩
    · simpa only [calcHeight_shape,air,Bool.false_eq_true,↓reduceIte] using postt.withZ _
    · simpa only [calcHeight_shape,air,Bool.false_eq_true,↓reduceIte] using zt

end Doom.Proofs.PlayerHeight
