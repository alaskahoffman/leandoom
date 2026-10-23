import Doom.Proofs.E1M1AimDiskRead
import Doom.Verification.X86VgaRoutine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimActiveIcon
open Verification X86 X86Memory X86Control X86VgaRoutine
abbrev VState := X86VgaRoutine.State
abbrev VOp := X86VgaRoutine.Op
def program : X86VgaRoutine.Program := fun pc =>
  if 0x1adb0≤pc ∧ pc<0x1aea0 then
    X86VgaRoutine.decodeAt E1M1AimReadPrologue.beginReadBytes (pc-0x1adb0)
  else none
def listed : X86VgaRoutine.Program
  | 0x1adc0 => some (.immediate 2 0x3c4,5)
  | 0x1adc5 => some (.byteImmediate 0 2,2)
  | 0x1adc7 => some (.output,1)
  | 0x1adc8 => some (.immediate 2 0x3c5,5)
  | 0x1adcd => some (.byteImmediate 0 0xf,2)
  | 0x1adcf => some (.output,1)
  | 0x1add0 => some (.immediate 2 0x3ce,5)
  | 0x1add5 => some (.byteImmediate 0 5,2)
  | 0x1add7 => some (.output,1)
  | 0x1add8 => some (.immediate 2 0x3cf,5)
  | 0x1addd => some (.sub 0 0,2)
  | 0x1addf => some (.input,1)
  | 0x1ade0 => some (.orByte 0 1,2)
  | 0x1ade2 => some (.xor 3 3,2)
  | 0x1ade4 => some (.output,1)
  | 0x1ade5 => some (.loadWord 0 0x290f8,5)
  | 0x1adea => some (.immediate 2 0xaf9c8,5)
  | 0x1adef => some (.add 0 0x39cc,5)
  | 0x1adf4 => some (.loadByte 1 ⟨some 0,none,0,0⟩,2)
  | 0x1adf6 => some (.storeByte ⟨some 2,none,0,0⟩ 1,2)
  | 0x1adf8 => some (.loadByte 1 ⟨some 0,none,0,1⟩,3)
  | 0x1adfb => some (.storeByte ⟨some 2,none,0,1⟩ 1,3)
  | 0x1adfe => some (.loadByte 1 ⟨some 0,none,0,2⟩,3)
  | 0x1ae01 => some (.storeByte ⟨some 2,none,0,2⟩ 1,3)
  | 0x1ae04 => some (.loadByte 1 ⟨some 0,none,0,3⟩,3)
  | 0x1ae07 => some (.storeByte ⟨some 2,none,0,3⟩ 1,3)
  | 0x1ae0a => some (.loadByte 1 ⟨some 0,none,0,80⟩,3)
  | 0x1ae0d => some (.storeByte ⟨some 2,none,0,80⟩ 1,3)
  | 0x1ae10 => some (.loadByte 1 ⟨some 0,none,0,81⟩,3)
  | 0x1ae13 => some (.add 0 0x50,3)
  | 0x1ae16 => some (.storeByte ⟨some 2,none,0,81⟩ 1,3)
  | 0x1ae19 => some (.add 2 0x50,3)
  | 0x1ae1c => some (.loadByte 1 ⟨some 0,none,0,2⟩,3)
  | 0x1ae1f => some (.add 3 2,3)
  | 0x1ae22 => some (.storeByte ⟨some 2,none,0,2⟩ 1,3)
  | 0x1ae25 => some (.add 2 0x50,3)
  | 0x1ae28 => some (.loadByte 1 ⟨some 0,none,0,3⟩,3)
  | 0x1ae2b => some (.add 0 0x50,3)
  | 0x1ae2e => some (.storeByte ⟨some 2,none,0,-77⟩ 1,3)
  | 0x1ae31 => some (.compare 3 0x10,3)
  | 0x1ae34 => some (.less (-66),2)
  | 0x1ae36 => some (.immediate 2 0xaf9cc,5)
  | 0x1ae3b => some (.loadWord 0 0x290f8,5)
  | 0x1ae40 => some (.xor 3 3,2)
  | 0x1ae42 => some (.add 0 0x39cc,5)
  | 0x1ae47 => some (.loadByte 1 ⟨some 2,none,0,0⟩,2)
  | 0x1ae49 => some (.storeByte ⟨some 0,none,0,0⟩ 1,2)
  | 0x1ae4b => some (.loadByte 1 ⟨some 2,none,0,1⟩,3)
  | 0x1ae4e => some (.storeByte ⟨some 0,none,0,1⟩ 1,3)
  | 0x1ae51 => some (.loadByte 1 ⟨some 2,none,0,2⟩,3)
  | 0x1ae54 => some (.storeByte ⟨some 0,none,0,2⟩ 1,3)
  | 0x1ae57 => some (.loadByte 1 ⟨some 2,none,0,3⟩,3)
  | 0x1ae5a => some (.storeByte ⟨some 0,none,0,3⟩ 1,3)
  | 0x1ae5d => some (.loadByte 1 ⟨some 2,none,0,80⟩,3)
  | 0x1ae60 => some (.storeByte ⟨some 0,none,0,80⟩ 1,3)
  | 0x1ae63 => some (.loadByte 1 ⟨some 2,none,0,81⟩,3)
  | 0x1ae66 => some (.add 2 0x50,3)
  | 0x1ae69 => some (.storeByte ⟨some 0,none,0,81⟩ 1,3)
  | 0x1ae6c => some (.add 0 0x50,3)
  | 0x1ae6f => some (.loadByte 1 ⟨some 2,none,0,2⟩,3)
  | 0x1ae72 => some (.add 3 2,3)
  | 0x1ae75 => some (.storeByte ⟨some 0,none,0,2⟩ 1,3)
  | 0x1ae78 => some (.add 0 0x50,3)
  | 0x1ae7b => some (.loadByte 1 ⟨some 2,none,0,3⟩,3)
  | 0x1ae7e => some (.add 2 0x50,3)
  | 0x1ae81 => some (.storeByte ⟨some 0,none,0,-77⟩ 1,3)
  | 0x1ae84 => some (.compare 3 0x10,3)
  | 0x1ae87 => some (.less (-66),2)
  | 0x1ae89 => some (.immediate 2 0x3ce,5)
  | 0x1ae8e => some (.byteImmediate 0 5,2)
  | 0x1ae90 => some (.output,1)
  | 0x1ae91 => some (.immediate 2 0x3cf,5)
  | 0x1ae96 => some (.sub 0 0,2)
  | 0x1ae98 => some (.input,1)
  | 0x1ae99 => some (.andByte 0 0xfe,2)
  | 0x1ae9b => some (.output,1)
  | 0x1ae9c => some (.pop 2,1)
  | 0x1ae9d => some (.pop 1,1)
  | 0x1ae9e => some (.pop 3,1)
  | 0x1ae9f => some (.ret,1)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide +kernel

/-- Candidate next state; the execution proof must still discharge success.
Fallback is NOT an execution step and cannot manufacture a Prefix. -/
def next (env : Environment) (op : VOp) (length : Nat) (s : VState) : VState :=
  (X86VgaRoutine.execute env op {s with cpu:={s.cpu with pc:=s.cpu.pc+length}}).getD s
def admitted (s : X86Control.State) (d : Device) (trace : List Observation) : VState :=
  ⟨s,d,trace,true,true⟩
def head (env : Environment) (s : VState) : VState :=
  let t1 := next env (.immediate 2 0x3c4) 5 s
  let t2 := next env (.byteImmediate 0 2) 2 t1
  let t3 := next env (.output) 1 t2
  let t4 := next env (.immediate 2 0x3c5) 5 t3
  let t5 := next env (.byteImmediate 0 0xf) 2 t4
  let t6 := next env (.output) 1 t5
  let t7 := next env (.immediate 2 0x3ce) 5 t6
  let t8 := next env (.byteImmediate 0 5) 2 t7
  let t9 := next env (.output) 1 t8
  let t10 := next env (.immediate 2 0x3cf) 5 t9
  let t11 := next env (.sub 0 0) 2 t10
  let t12 := next env (.input) 1 t11
  let t13 := next env (.orByte 0 1) 2 t12
  let t14 := next env (.xor 3 3) 2 t13
  let t15 := next env (.output) 1 t14
  let t16 := next env (.loadWord 0 0x290f8) 5 t15
  let t17 := next env (.immediate 2 0xaf9c8) 5 t16
  let t18 := next env (.add 0 0x39cc) 5 t17
  t18
theorem head_execution (env : Environment) (s : X86Memory.State) (f : Option Flags)
    (d : Device) (trace : List Observation) :
    X86VgaRoutine.Prefix env program 18 (admitted ⟨s,f,0x1adc0⟩ d trace)
      (head env (admitted ⟨s,f,0x1adc0⟩ d trace)) := by
  have path : X86VgaRoutine.Prefix env listed 18 (admitted ⟨s,f,0x1adc0⟩ d trace)
      (head env (admitted ⟨s,f,0x1adc0⟩ d trace)) := by
    refine .step rfl rfl ?_
    refine .step rfl rfl ?_
    refine .step rfl rfl ?_
    refine .step rfl rfl ?_
    refine .step rfl rfl ?_
    refine .step rfl rfl ?_
    refine .step rfl rfl ?_
    refine .step rfl rfl ?_
    refine .step rfl rfl ?_
    refine .step rfl rfl ?_
    refine .step rfl rfl ?_
    refine .step rfl rfl ?_
    refine .step rfl rfl ?_
    refine .step rfl rfl ?_
    refine .step rfl rfl ?_
    refine .step rfl rfl ?_
    refine .step rfl rfl ?_
    refine .step rfl rfl ?_
    exact .nil _
  exact path.transfer _ decoded

/-- Unguarded candidate for an individual instruction, not a machine step.
Every use below separately proves the real decoder and admission checks. -/
def candidate (env : Environment) (op : VOp) (length : Nat) (s : VState) : VState :=
  let t := {s with cpu:={s.cpu with pc:=s.cpu.pc+length}}
  match op with
  | .byteImmediate r v => {t with cpu:={t.cpu with core:=putByte t.cpu.core r v}}
  | .input =>
      let response := touch env (.input (port t)) t
      {response.1 with cpu:={t.cpu with core:=putByte t.cpu.core 0 response.2}}
  | .output => (touch env (.output (port t) (readByte t.cpu.core.regs 0)) t).1
  | .loadByte r a =>
      let response := touch env (.read (a.eval t.cpu.core.regs)) t
      {response.1 with cpu:={t.cpu with core:=putByte t.cpu.core r response.2}}
  | .storeByte a r => (touch env (.write (a.eval t.cpu.core.regs) (readByte t.cpu.core.regs r)) t).1
  | _ => {t with cpu:=(X86Routine.execute (oldOp op) t.cpu).getD t.cpu}
def ordinary : VOp → Bool | .less _ => false | _ => true

theorem candidate_step (env : Environment) (op : VOp) (len : Nat) (s : VState)
    (ord : ordinary op=true) (g : X86VgaRoutine.guard op s=true) :
    X86VgaRoutine.execute env op {s with cpu:={s.cpu with pc:=s.cpu.pc+len}}=
      some (candidate env op len s) := by
  have gg : X86VgaRoutine.guard op {s with cpu:={s.cpu with pc:=s.cpu.pc+len}}=true := by
    cases op <;> exact g
  unfold X86VgaRoutine.execute
  rw [gg]
  cases op <;> try rfl
  case less => cases ord

def CopySafe (s : VState) : Prop :=
  s.apertureMapped=true ∧ ∀ r∈([0,2] : List Reg), ∀ off∈([0,1,2,3,80,81,82,83] : List Word),
    aperture (s.cpu.core.regs r+off)=true

def copyBody (env : Environment) (s : VState) : VState :=
  let t1 := candidate env (.loadByte 1 ⟨some 0,none,0,0⟩) 2 s
  let t2 := candidate env (.storeByte ⟨some 2,none,0,0⟩ 1) 2 t1
  let t3 := candidate env (.loadByte 1 ⟨some 0,none,0,1⟩) 3 t2
  let t4 := candidate env (.storeByte ⟨some 2,none,0,1⟩ 1) 3 t3
  let t5 := candidate env (.loadByte 1 ⟨some 0,none,0,2⟩) 3 t4
  let t6 := candidate env (.storeByte ⟨some 2,none,0,2⟩ 1) 3 t5
  let t7 := candidate env (.loadByte 1 ⟨some 0,none,0,3⟩) 3 t6
  let t8 := candidate env (.storeByte ⟨some 2,none,0,3⟩ 1) 3 t7
  let t9 := candidate env (.loadByte 1 ⟨some 0,none,0,80⟩) 3 t8
  let t10 := candidate env (.storeByte ⟨some 2,none,0,80⟩ 1) 3 t9
  let t11 := candidate env (.loadByte 1 ⟨some 0,none,0,81⟩) 3 t10
  let t12 := candidate env (.add 0 0x50) 3 t11
  let t13 := candidate env (.storeByte ⟨some 2,none,0,81⟩ 1) 3 t12
  let t14 := candidate env (.add 2 0x50) 3 t13
  let t15 := candidate env (.loadByte 1 ⟨some 0,none,0,2⟩) 3 t14
  let t16 := candidate env (.add 3 2) 3 t15
  let t17 := candidate env (.storeByte ⟨some 2,none,0,2⟩ 1) 3 t16
  let t18 := candidate env (.add 2 0x50) 3 t17
  let t19 := candidate env (.loadByte 1 ⟨some 0,none,0,3⟩) 3 t18
  let t20 := candidate env (.add 0 0x50) 3 t19
  let t21 := candidate env (.storeByte ⟨some 2,none,0,-77⟩ 1) 3 t20
  let t22 := candidate env (.compare 3 0x10) 3 t21
  t22
theorem copy_body_execution (env : Environment) (s : VState)
    (pc : s.cpu.pc=0x1adf4) (safe : CopySafe s) :
    X86VgaRoutine.Prefix env program 22 s (copyBody env s) := by
  have path : X86VgaRoutine.Prefix env listed 22 s (copyBody env s) := by
    let t1 := candidate env (.loadByte 1 ⟨some 0,none,0,0⟩) 2 s
    let t2 := candidate env (.storeByte ⟨some 2,none,0,0⟩ 1) 2 t1
    let t3 := candidate env (.loadByte 1 ⟨some 0,none,0,1⟩) 3 t2
    let t4 := candidate env (.storeByte ⟨some 2,none,0,1⟩ 1) 3 t3
    let t5 := candidate env (.loadByte 1 ⟨some 0,none,0,2⟩) 3 t4
    let t6 := candidate env (.storeByte ⟨some 2,none,0,2⟩ 1) 3 t5
    let t7 := candidate env (.loadByte 1 ⟨some 0,none,0,3⟩) 3 t6
    let t8 := candidate env (.storeByte ⟨some 2,none,0,3⟩ 1) 3 t7
    let t9 := candidate env (.loadByte 1 ⟨some 0,none,0,80⟩) 3 t8
    let t10 := candidate env (.storeByte ⟨some 2,none,0,80⟩ 1) 3 t9
    let t11 := candidate env (.loadByte 1 ⟨some 0,none,0,81⟩) 3 t10
    let t12 := candidate env (.add 0 0x50) 3 t11
    let t13 := candidate env (.storeByte ⟨some 2,none,0,81⟩ 1) 3 t12
    let t14 := candidate env (.add 2 0x50) 3 t13
    let t15 := candidate env (.loadByte 1 ⟨some 0,none,0,2⟩) 3 t14
    let t16 := candidate env (.add 3 2) 3 t15
    let t17 := candidate env (.storeByte ⟨some 2,none,0,2⟩ 1) 3 t16
    let t18 := candidate env (.add 2 0x50) 3 t17
    let t19 := candidate env (.loadByte 1 ⟨some 0,none,0,3⟩) 3 t18
    let t20 := candidate env (.add 0 0x50) 3 t19
    let t21 := candidate env (.storeByte ⟨some 2,none,0,-77⟩ 1) 3 t20
    let t22 := candidate env (.compare 3 0x10) 3 t21
    refine .step (middle:=t1) ?_ (candidate_step env (.loadByte 1 ⟨some 0,none,0,0⟩) 2 s rfl ?_) ?_
    · rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 0+0+0))=true
      have h := safe.2 0 (by decide) 0 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t2) ?_ (candidate_step env (.storeByte ⟨some 2,none,0,0⟩ 1) 2 t1 rfl ?_) ?_
    · change listed (s.cpu.pc+2)=_; rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 2+0+0))=true
      have h := safe.2 2 (by decide) 0 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t3) ?_ (candidate_step env (.loadByte 1 ⟨some 0,none,0,1⟩) 3 t2 rfl ?_) ?_
    · change listed (s.cpu.pc+4)=_; rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 0+0+1))=true
      have h := safe.2 0 (by decide) 1 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t4) ?_ (candidate_step env (.storeByte ⟨some 2,none,0,1⟩ 1) 3 t3 rfl ?_) ?_
    · change listed (s.cpu.pc+7)=_; rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 2+0+1))=true
      have h := safe.2 2 (by decide) 1 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t5) ?_ (candidate_step env (.loadByte 1 ⟨some 0,none,0,2⟩) 3 t4 rfl ?_) ?_
    · change listed (s.cpu.pc+10)=_; rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 0+0+2))=true
      have h := safe.2 0 (by decide) 2 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t6) ?_ (candidate_step env (.storeByte ⟨some 2,none,0,2⟩ 1) 3 t5 rfl ?_) ?_
    · change listed (s.cpu.pc+13)=_; rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 2+0+2))=true
      have h := safe.2 2 (by decide) 2 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t7) ?_ (candidate_step env (.loadByte 1 ⟨some 0,none,0,3⟩) 3 t6 rfl ?_) ?_
    · change listed (s.cpu.pc+16)=_; rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 0+0+3))=true
      have h := safe.2 0 (by decide) 3 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t8) ?_ (candidate_step env (.storeByte ⟨some 2,none,0,3⟩ 1) 3 t7 rfl ?_) ?_
    · change listed (s.cpu.pc+19)=_; rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 2+0+3))=true
      have h := safe.2 2 (by decide) 3 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t9) ?_ (candidate_step env (.loadByte 1 ⟨some 0,none,0,80⟩) 3 t8 rfl ?_) ?_
    · change listed (s.cpu.pc+22)=_; rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 0+0+80))=true
      have h := safe.2 0 (by decide) 80 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t10) ?_ (candidate_step env (.storeByte ⟨some 2,none,0,80⟩ 1) 3 t9 rfl ?_) ?_
    · change listed (s.cpu.pc+25)=_; rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 2+0+80))=true
      have h := safe.2 2 (by decide) 80 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t11) ?_ (candidate_step env (.loadByte 1 ⟨some 0,none,0,81⟩) 3 t10 rfl ?_) ?_
    · change listed (s.cpu.pc+28)=_; rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 0+0+81))=true
      have h := safe.2 0 (by decide) 81 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t12) ?_ (candidate_step env (.add 0 0x50) 3 t11 rfl ?_) ?_
    · change listed (s.cpu.pc+31)=_; rw [pc]; rfl
    · rfl
    refine .step (middle:=t13) ?_ (candidate_step env (.storeByte ⟨some 2,none,0,81⟩ 1) 3 t12 rfl ?_) ?_
    · change listed (s.cpu.pc+34)=_; rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 2+0+81))=true
      have h := safe.2 2 (by decide) 81 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t14) ?_ (candidate_step env (.add 2 0x50) 3 t13 rfl ?_) ?_
    · change listed (s.cpu.pc+37)=_; rw [pc]; rfl
    · rfl
    refine .step (middle:=t15) ?_ (candidate_step env (.loadByte 1 ⟨some 0,none,0,2⟩) 3 t14 rfl ?_) ?_
    · change listed (s.cpu.pc+40)=_; rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 0+80+0+2))=true
      have h := safe.2 0 (by decide) 82 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t16) ?_ (candidate_step env (.add 3 2) 3 t15 rfl ?_) ?_
    · change listed (s.cpu.pc+43)=_; rw [pc]; rfl
    · rfl
    refine .step (middle:=t17) ?_ (candidate_step env (.storeByte ⟨some 2,none,0,2⟩ 1) 3 t16 rfl ?_) ?_
    · change listed (s.cpu.pc+46)=_; rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 2+80+0+2))=true
      have h := safe.2 2 (by decide) 82 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t18) ?_ (candidate_step env (.add 2 0x50) 3 t17 rfl ?_) ?_
    · change listed (s.cpu.pc+49)=_; rw [pc]; rfl
    · rfl
    refine .step (middle:=t19) ?_ (candidate_step env (.loadByte 1 ⟨some 0,none,0,3⟩) 3 t18 rfl ?_) ?_
    · change listed (s.cpu.pc+52)=_; rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 0+80+0+3))=true
      have h := safe.2 0 (by decide) 83 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t20) ?_ (candidate_step env (.add 0 0x50) 3 t19 rfl ?_) ?_
    · change listed (s.cpu.pc+55)=_; rw [pc]; rfl
    · rfl
    refine .step (middle:=t21) ?_ (candidate_step env (.storeByte ⟨some 2,none,0,-77⟩ 1) 3 t20 rfl ?_) ?_
    · change listed (s.cpu.pc+58)=_; rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 2+80+80+0+-77))=true
      have h := safe.2 2 (by decide) 83 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t22) ?_ (candidate_step env (.compare 3 0x10) 3 t21 rfl ?_) ?_
    · change listed (s.cpu.pc+61)=_; rw [pc]; rfl
    · rfl
    exact .nil _
  exact path.transfer _ decoded
theorem copy_body_registers (env : Environment) (s : VState) :
    (copyBody env s).cpu.pc=s.cpu.pc+64 ∧
    (copyBody env s).cpu.core.regs 0=s.cpu.core.regs 0+160 ∧
    (copyBody env s).cpu.core.regs 2=s.cpu.core.regs 2+160 ∧
    (copyBody env s).cpu.core.regs 3=s.cpu.core.regs 3+2 ∧
    (∀ r, r≠0 → r≠1 → r≠2 → r≠3 → (copyBody env s).cpu.core.regs r=s.cpu.core.regs r) ∧
    (copyBody env s).apertureMapped=s.apertureMapped ∧
    (copyBody env s).ioAllowed=s.ioAllowed ∧
    (copyBody env s).cpu.flags=some (compare32 (s.cpu.core.regs 3+2) 16) := by
  refine ⟨rfl,?_,?_,rfl,?_,rfl,rfl,rfl⟩
  · change s.cpu.core.regs 0+80+80=s.cpu.core.regs 0+160
    simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd]
  · change s.cpu.core.regs 2+80+80=s.cpu.core.regs 2+160
    simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd]
  · intro r h0 h1 h2 h3
    have n0 : r.val≠0 := fun h => h0 (Fin.ext h)
    have n1 : r.val≠1 := fun h => h1 (Fin.ext h)
    have n2 : r.val≠2 := fun h => h2 (Fin.ext h)
    have n3 : r.val≠3 := fun h => h3 (Fin.ext h)
    have hr : r.val=4 ∨ r.val=5 ∨ r.val=6 ∨ r.val=7 := by have := r.isLt; omega
    rcases hr with h | h | h | h
    · have : r=4 := Fin.ext h; subst r; rfl
    · have : r=5 := Fin.ext h; subst r; rfl
    · have : r=6 := Fin.ext h; subst r; rfl
    · have : r=7 := Fin.ext h; subst r; rfl
def copyBackBody (env : Environment) (s : VState) : VState :=
  let t1 := candidate env (.loadByte 1 ⟨some 2,none,0,0⟩) 2 s
  let t2 := candidate env (.storeByte ⟨some 0,none,0,0⟩ 1) 2 t1
  let t3 := candidate env (.loadByte 1 ⟨some 2,none,0,1⟩) 3 t2
  let t4 := candidate env (.storeByte ⟨some 0,none,0,1⟩ 1) 3 t3
  let t5 := candidate env (.loadByte 1 ⟨some 2,none,0,2⟩) 3 t4
  let t6 := candidate env (.storeByte ⟨some 0,none,0,2⟩ 1) 3 t5
  let t7 := candidate env (.loadByte 1 ⟨some 2,none,0,3⟩) 3 t6
  let t8 := candidate env (.storeByte ⟨some 0,none,0,3⟩ 1) 3 t7
  let t9 := candidate env (.loadByte 1 ⟨some 2,none,0,80⟩) 3 t8
  let t10 := candidate env (.storeByte ⟨some 0,none,0,80⟩ 1) 3 t9
  let t11 := candidate env (.loadByte 1 ⟨some 2,none,0,81⟩) 3 t10
  let t12 := candidate env (.add 2 0x50) 3 t11
  let t13 := candidate env (.storeByte ⟨some 0,none,0,81⟩ 1) 3 t12
  let t14 := candidate env (.add 0 0x50) 3 t13
  let t15 := candidate env (.loadByte 1 ⟨some 2,none,0,2⟩) 3 t14
  let t16 := candidate env (.add 3 2) 3 t15
  let t17 := candidate env (.storeByte ⟨some 0,none,0,2⟩ 1) 3 t16
  let t18 := candidate env (.add 0 0x50) 3 t17
  let t19 := candidate env (.loadByte 1 ⟨some 2,none,0,3⟩) 3 t18
  let t20 := candidate env (.add 2 0x50) 3 t19
  let t21 := candidate env (.storeByte ⟨some 0,none,0,-77⟩ 1) 3 t20
  let t22 := candidate env (.compare 3 0x10) 3 t21
  t22
theorem copy_back_body_execution (env : Environment) (s : VState)
    (pc : s.cpu.pc=0x1ae47) (safe : CopySafe s) :
    X86VgaRoutine.Prefix env program 22 s (copyBackBody env s) := by
  have path : X86VgaRoutine.Prefix env listed 22 s (copyBackBody env s) := by
    let t1 := candidate env (.loadByte 1 ⟨some 2,none,0,0⟩) 2 s
    let t2 := candidate env (.storeByte ⟨some 0,none,0,0⟩ 1) 2 t1
    let t3 := candidate env (.loadByte 1 ⟨some 2,none,0,1⟩) 3 t2
    let t4 := candidate env (.storeByte ⟨some 0,none,0,1⟩ 1) 3 t3
    let t5 := candidate env (.loadByte 1 ⟨some 2,none,0,2⟩) 3 t4
    let t6 := candidate env (.storeByte ⟨some 0,none,0,2⟩ 1) 3 t5
    let t7 := candidate env (.loadByte 1 ⟨some 2,none,0,3⟩) 3 t6
    let t8 := candidate env (.storeByte ⟨some 0,none,0,3⟩ 1) 3 t7
    let t9 := candidate env (.loadByte 1 ⟨some 2,none,0,80⟩) 3 t8
    let t10 := candidate env (.storeByte ⟨some 0,none,0,80⟩ 1) 3 t9
    let t11 := candidate env (.loadByte 1 ⟨some 2,none,0,81⟩) 3 t10
    let t12 := candidate env (.add 2 0x50) 3 t11
    let t13 := candidate env (.storeByte ⟨some 0,none,0,81⟩ 1) 3 t12
    let t14 := candidate env (.add 0 0x50) 3 t13
    let t15 := candidate env (.loadByte 1 ⟨some 2,none,0,2⟩) 3 t14
    let t16 := candidate env (.add 3 2) 3 t15
    let t17 := candidate env (.storeByte ⟨some 0,none,0,2⟩ 1) 3 t16
    let t18 := candidate env (.add 0 0x50) 3 t17
    let t19 := candidate env (.loadByte 1 ⟨some 2,none,0,3⟩) 3 t18
    let t20 := candidate env (.add 2 0x50) 3 t19
    let t21 := candidate env (.storeByte ⟨some 0,none,0,-77⟩ 1) 3 t20
    let t22 := candidate env (.compare 3 0x10) 3 t21
    refine .step (middle:=t1) ?_ (candidate_step env (.loadByte 1 ⟨some 2,none,0,0⟩) 2 s rfl ?_) ?_
    · rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 2+0+0))=true
      have h := safe.2 2 (by decide) 0 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t2) ?_ (candidate_step env (.storeByte ⟨some 0,none,0,0⟩ 1) 2 t1 rfl ?_) ?_
    · change listed (s.cpu.pc+2)=_; rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 0+0+0))=true
      have h := safe.2 0 (by decide) 0 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t3) ?_ (candidate_step env (.loadByte 1 ⟨some 2,none,0,1⟩) 3 t2 rfl ?_) ?_
    · change listed (s.cpu.pc+4)=_; rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 2+0+1))=true
      have h := safe.2 2 (by decide) 1 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t4) ?_ (candidate_step env (.storeByte ⟨some 0,none,0,1⟩ 1) 3 t3 rfl ?_) ?_
    · change listed (s.cpu.pc+7)=_; rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 0+0+1))=true
      have h := safe.2 0 (by decide) 1 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t5) ?_ (candidate_step env (.loadByte 1 ⟨some 2,none,0,2⟩) 3 t4 rfl ?_) ?_
    · change listed (s.cpu.pc+10)=_; rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 2+0+2))=true
      have h := safe.2 2 (by decide) 2 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t6) ?_ (candidate_step env (.storeByte ⟨some 0,none,0,2⟩ 1) 3 t5 rfl ?_) ?_
    · change listed (s.cpu.pc+13)=_; rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 0+0+2))=true
      have h := safe.2 0 (by decide) 2 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t7) ?_ (candidate_step env (.loadByte 1 ⟨some 2,none,0,3⟩) 3 t6 rfl ?_) ?_
    · change listed (s.cpu.pc+16)=_; rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 2+0+3))=true
      have h := safe.2 2 (by decide) 3 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t8) ?_ (candidate_step env (.storeByte ⟨some 0,none,0,3⟩ 1) 3 t7 rfl ?_) ?_
    · change listed (s.cpu.pc+19)=_; rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 0+0+3))=true
      have h := safe.2 0 (by decide) 3 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t9) ?_ (candidate_step env (.loadByte 1 ⟨some 2,none,0,80⟩) 3 t8 rfl ?_) ?_
    · change listed (s.cpu.pc+22)=_; rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 2+0+80))=true
      have h := safe.2 2 (by decide) 80 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t10) ?_ (candidate_step env (.storeByte ⟨some 0,none,0,80⟩ 1) 3 t9 rfl ?_) ?_
    · change listed (s.cpu.pc+25)=_; rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 0+0+80))=true
      have h := safe.2 0 (by decide) 80 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t11) ?_ (candidate_step env (.loadByte 1 ⟨some 2,none,0,81⟩) 3 t10 rfl ?_) ?_
    · change listed (s.cpu.pc+28)=_; rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 2+0+81))=true
      have h := safe.2 2 (by decide) 81 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t12) ?_ (candidate_step env (.add 2 0x50) 3 t11 rfl ?_) ?_
    · change listed (s.cpu.pc+31)=_; rw [pc]; rfl
    · rfl
    refine .step (middle:=t13) ?_ (candidate_step env (.storeByte ⟨some 0,none,0,81⟩ 1) 3 t12 rfl ?_) ?_
    · change listed (s.cpu.pc+34)=_; rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 0+0+81))=true
      have h := safe.2 0 (by decide) 81 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t14) ?_ (candidate_step env (.add 0 0x50) 3 t13 rfl ?_) ?_
    · change listed (s.cpu.pc+37)=_; rw [pc]; rfl
    · rfl
    refine .step (middle:=t15) ?_ (candidate_step env (.loadByte 1 ⟨some 2,none,0,2⟩) 3 t14 rfl ?_) ?_
    · change listed (s.cpu.pc+40)=_; rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 2+80+0+2))=true
      have h := safe.2 2 (by decide) 82 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t16) ?_ (candidate_step env (.add 3 2) 3 t15 rfl ?_) ?_
    · change listed (s.cpu.pc+43)=_; rw [pc]; rfl
    · rfl
    refine .step (middle:=t17) ?_ (candidate_step env (.storeByte ⟨some 0,none,0,2⟩ 1) 3 t16 rfl ?_) ?_
    · change listed (s.cpu.pc+46)=_; rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 0+80+0+2))=true
      have h := safe.2 0 (by decide) 82 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t18) ?_ (candidate_step env (.add 0 0x50) 3 t17 rfl ?_) ?_
    · change listed (s.cpu.pc+49)=_; rw [pc]; rfl
    · rfl
    refine .step (middle:=t19) ?_ (candidate_step env (.loadByte 1 ⟨some 2,none,0,3⟩) 3 t18 rfl ?_) ?_
    · change listed (s.cpu.pc+52)=_; rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 2+80+0+3))=true
      have h := safe.2 2 (by decide) 83 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t20) ?_ (candidate_step env (.add 2 0x50) 3 t19 rfl ?_) ?_
    · change listed (s.cpu.pc+55)=_; rw [pc]; rfl
    · rfl
    refine .step (middle:=t21) ?_ (candidate_step env (.storeByte ⟨some 0,none,0,-77⟩ 1) 3 t20 rfl ?_) ?_
    · change listed (s.cpu.pc+58)=_; rw [pc]; rfl
    · change (s.apertureMapped && aperture (s.cpu.core.regs 0+80+80+0+-77))=true
      have h := safe.2 0 (by decide) 83 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.reduceNeg,BitVec.add_zero] at h ⊢
      rw [safe.1,h]; rfl
    refine .step (middle:=t22) ?_ (candidate_step env (.compare 3 0x10) 3 t21 rfl ?_) ?_
    · change listed (s.cpu.pc+61)=_; rw [pc]; rfl
    · rfl
    exact .nil _
  exact path.transfer _ decoded
theorem copy_back_body_registers (env : Environment) (s : VState) :
    (copyBackBody env s).cpu.pc=s.cpu.pc+64 ∧
    (copyBackBody env s).cpu.core.regs 0=s.cpu.core.regs 0+160 ∧
    (copyBackBody env s).cpu.core.regs 2=s.cpu.core.regs 2+160 ∧
    (copyBackBody env s).cpu.core.regs 3=s.cpu.core.regs 3+2 ∧
    (∀ r, r≠0 → r≠1 → r≠2 → r≠3 → (copyBackBody env s).cpu.core.regs r=s.cpu.core.regs r) ∧
    (copyBackBody env s).apertureMapped=s.apertureMapped ∧
    (copyBackBody env s).ioAllowed=s.ioAllowed ∧
    (copyBackBody env s).cpu.flags=some (compare32 (s.cpu.core.regs 3+2) 16) := by
  refine ⟨rfl,?_,?_,rfl,?_,rfl,rfl,rfl⟩
  · change s.cpu.core.regs 0+80+80=s.cpu.core.regs 0+160
    simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd]
  · change s.cpu.core.regs 2+80+80=s.cpu.core.regs 2+160
    simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd]
  · intro r h0 h1 h2 h3
    have n0 : r.val≠0 := fun h => h0 (Fin.ext h)
    have n1 : r.val≠1 := fun h => h1 (Fin.ext h)
    have n2 : r.val≠2 := fun h => h2 (Fin.ext h)
    have n3 : r.val≠3 := fun h => h3 (Fin.ext h)
    have hr : r.val=4 ∨ r.val=5 ∨ r.val=6 ∨ r.val=7 := by have := r.isLt; omega
    rcases hr with h | h | h | h
    · have : r=4 := Fin.ext h; subst r; rfl
    · have : r=5 := Fin.ext h; subst r; rfl
    · have : r=6 := Fin.ext h; subst r; rfl
    · have : r=7 := Fin.ext h; subst r; rfl

def loopPC (back : Bool) : Nat := if back then 0x1ae47 else 0x1adf4
def body (env : Environment) (back : Bool) (s : VState) :=
  if back then copyBackBody env s else copyBody env s
theorem body_execution (env : Environment) (back : Bool) (s : VState)
    (pc : s.cpu.pc=loopPC back) (safe : CopySafe s) :
    X86VgaRoutine.Prefix env program 22 s (body env back s) := by
  cases back
  · exact copy_body_execution env s pc safe
  · exact copy_back_body_execution env s pc safe

theorem body_registers (env : Environment) (back : Bool) (s : VState) :
    (body env back s).cpu.pc=s.cpu.pc+64 ∧
    (body env back s).cpu.core.regs 0=s.cpu.core.regs 0+160 ∧
    (body env back s).cpu.core.regs 2=s.cpu.core.regs 2+160 ∧
    (body env back s).cpu.core.regs 3=s.cpu.core.regs 3+2 ∧
    (∀ r, r≠0 → r≠1 → r≠2 → r≠3 → (body env back s).cpu.core.regs r=s.cpu.core.regs r) ∧
    (body env back s).apertureMapped=s.apertureMapped ∧
    (body env back s).ioAllowed=s.ioAllowed ∧
    (body env back s).cpu.flags=some (compare32 (s.cpu.core.regs 3+2) 16) := by
  cases back
  · exact copy_body_registers env s
  · exact copy_back_body_registers env s

def latched (back : Bool) (k : Nat) (s : VState) : VState :=
  {s with cpu:={s.cpu with pc:=if k+1<8 then loopPC back else loopPC back+66}}
theorem latch_execution (env : Environment) (back : Bool) (s : VState) (k : Fin 8)
    (pc : s.cpu.pc=loopPC back+64)
    (flags : s.cpu.flags=some (compare32 (BitVec.ofNat 32 (2*k.val)+2) 16)) :
    X86VgaRoutine.Prefix env program 1 s (latched back k.val s) := by
  have finite : ∀ j : Fin 8,
      ((compare32 (BitVec.ofNat 32 (2*j.val)+2) 16).sign !=
       (compare32 (BitVec.ofNat 32 (2*j.val)+2) 16).overflow) = decide (j.val+1<8) := by decide +kernel
  have hd : program s.cpu.pc=some (.less (-66),2) := by
    rw [pc]; cases back <;> decide +kernel
  refine .step hd ?_ (.nil _)
  change (Option.map (fun c : X86Control.State => {s with cpu:=c}) (do
    let f ← s.cpu.flags
    if f.sign != f.overflow then
      if ((s.cpu.pc+2 : Nat) : Int)-66 < 0 ∨ ((s.cpu.pc+2 : Nat) : Int)-66 ≥ 4294967296 then none
      else some {s.cpu with pc:=(((s.cpu.pc+2 : Nat) : Int)-66).toNat}
    else some {s.cpu with pc:=s.cpu.pc+2})) = some (latched back k.val s)
  rw [flags]
  simp only [bind,Bind.bind,Option.bind]
  rw [finite k,pc]
  cases back <;> by_cases h : k.val+1<8 <;>
    simp only [loopPC,latched,h,decide_true,decide_false,↓reduceIte] <;> rfl

/-- Static incoming address footprint, not a reached-state or helper-success
assumption. Both source and destination must lie in the admitted device window. -/
def LoopSafe (s : VState) : Prop := s.apertureMapped=true ∧
  ∀ r∈([0,2] : List Reg), ∀ k<8,
  ∀ off∈([0,1,2,3,80,81,82,83] : List Word),
    aperture (s.cpu.core.regs r+BitVec.ofNat 32 (160*k)+off)=true

theorem copy_loop_progress (env : Environment) (back : Bool) (s : VState)
    (pc : s.cpu.pc=loopPC back) (counter : s.cpu.core.regs 3=0)
    (safe : LoopSafe s) (n : Nat) (bound : n≤8) :
    ∃ t, X86VgaRoutine.Prefix env program (23*n) s t ∧
      t.cpu.pc=(if n<8 then loopPC back else loopPC back+66) ∧
      t.cpu.core.regs 0=s.cpu.core.regs 0+BitVec.ofNat 32 (160*n) ∧
      t.cpu.core.regs 2=s.cpu.core.regs 2+BitVec.ofNat 32 (160*n) ∧
      t.cpu.core.regs 3=BitVec.ofNat 32 (2*n) ∧
      (∀ r, r≠0 → r≠1 → r≠2 → r≠3 → t.cpu.core.regs r=s.cpu.core.regs r) ∧
      t.apertureMapped=true ∧ t.ioAllowed=s.ioAllowed := by
  induction n with
  | zero =>
    exact ⟨s,.nil _,by simpa using pc,by simp,by simp,by simpa using counter,
      by intros; rfl,safe.1,rfl⟩
  | succ n ih =>
    have small : n<8 := by omega
    obtain ⟨t,path,tpc,t0,t2,t3,kept,mapped,io⟩ := ih (by omega)
    have atPC : t.cpu.pc=loopPC back := by simpa only [if_pos small] using tpc
    have cs : CopySafe t := by
      refine ⟨mapped,?_⟩
      intro r hr off ho
      have rr : r=0 ∨ r=2 := by simpa using hr
      rcases rr with rfl | rfl
      · rw [t0]; exact safe.2 0 (by decide) n small off ho
      · rw [t2]; exact safe.2 2 (by decide) n small off ho
    have bp := body_execution env back t atPC cs
    obtain ⟨bpc,b0,b2,b3,bkept,bmapped,bio,bflags⟩ := body_registers env back t
    have lp := latch_execution env back (body env back t) ⟨n,small⟩
      (bpc.trans (congrArg (·+64) atPC)) (by rw [bflags,t3])
    let u := latched back n (body env back t)
    have outpath : X86VgaRoutine.Prefix env program (23*(n+1)) s u := by
      have composed := path.trans (bp.trans lp)
      simpa only [Nat.mul_add,Nat.mul_one] using composed
    refine ⟨u,outpath,rfl,?_,?_,?_,?_,?_,?_⟩
    · change (body env back t).cpu.core.regs 0=_
      rw [b0,t0]
      simp only [Nat.mul_add,Nat.mul_one,BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc]
    · change (body env back t).cpu.core.regs 2=_
      rw [b2,t2]
      simp only [Nat.mul_add,Nat.mul_one,BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc]
    · change (body env back t).cpu.core.regs 3=_
      rw [b3,t3]
      simp only [Nat.mul_add,Nat.mul_one,BitVec.ofNat_add,BitVec.ofNat_eq_ofNat]
    · intro r h0 h1 h2 h3
      exact (bkept r h0 h1 h2 h3).trans (kept r h0 h1 h2 h3)
    · exact bmapped.trans mapped
    · exact bio.trans io

theorem copy_loop_execution (env : Environment) (back : Bool) (s : VState)
    (pc : s.cpu.pc=loopPC back) (counter : s.cpu.core.regs 3=0) (safe : LoopSafe s) :
    ∃ t, X86VgaRoutine.Prefix env program 184 s t ∧
      t.cpu.pc=loopPC back+66 ∧
      t.cpu.core.regs 0=s.cpu.core.regs 0+1280 ∧
      t.cpu.core.regs 2=s.cpu.core.regs 2+1280 ∧
      t.cpu.core.regs 3=16 ∧
      (∀ r, r≠0 → r≠1 → r≠2 → r≠3 → t.cpu.core.regs r=s.cpu.core.regs r) ∧
      t.apertureMapped=true ∧ t.ioAllowed=s.ioAllowed := by
  exact copy_loop_progress env back s pc counter safe 8 (by decide)

def StackRam (s : VState) : Prop := ∀ off∈([0,4,8,12] : List Word),
  ramWord (s.cpu.core.regs 4+off)=true
def tail (env : Environment) (s : VState) : VState :=
  let t1 := candidate env (.immediate 2 0x3ce) 5 s
  let t2 := candidate env (.byteImmediate 0 5) 2 t1
  let t3 := candidate env (.output) 1 t2
  let t4 := candidate env (.immediate 2 0x3cf) 5 t3
  let t5 := candidate env (.sub 0 0) 2 t4
  let t6 := candidate env (.input) 1 t5
  let t7 := candidate env (.andByte 0 0xfe) 2 t6
  let t8 := candidate env (.output) 1 t7
  let t9 := candidate env (.pop 2) 1 t8
  let t10 := candidate env (.pop 1) 1 t9
  let t11 := candidate env (.pop 3) 1 t10
  let t12 := candidate env (.ret) 1 t11
  t12
theorem tail_execution (env : Environment) (s : VState)
    (pc : s.cpu.pc=0x1ae89) (io : s.ioAllowed=true) (stack : StackRam s) :
    X86VgaRoutine.Prefix env program 12 s (tail env s) := by
  have path : X86VgaRoutine.Prefix env listed 12 s (tail env s) := by
    let t1 := candidate env (.immediate 2 0x3ce) 5 s
    let t2 := candidate env (.byteImmediate 0 5) 2 t1
    let t3 := candidate env (.output) 1 t2
    let t4 := candidate env (.immediate 2 0x3cf) 5 t3
    let t5 := candidate env (.sub 0 0) 2 t4
    let t6 := candidate env (.input) 1 t5
    let t7 := candidate env (.andByte 0 0xfe) 2 t6
    let t8 := candidate env (.output) 1 t7
    let t9 := candidate env (.pop 2) 1 t8
    let t10 := candidate env (.pop 1) 1 t9
    let t11 := candidate env (.pop 3) 1 t10
    let t12 := candidate env (.ret) 1 t11
    refine .step (middle:=t1) ?_ (candidate_step env (.immediate 2 0x3ce) 5 s rfl ?_) ?_
    · rw [pc]; rfl
    · rfl
    refine .step (middle:=t2) ?_ (candidate_step env (.byteImmediate 0 5) 2 t1 rfl ?_) ?_
    · change listed (s.cpu.pc+5)=_; rw [pc]; rfl
    · rfl
    refine .step (middle:=t3) ?_ (candidate_step env (.output) 1 t2 rfl ?_) ?_
    · change listed (s.cpu.pc+7)=_; rw [pc]; rfl
    · change (s.ioAllowed && true)=true; rw [io]; rfl
    refine .step (middle:=t4) ?_ (candidate_step env (.immediate 2 0x3cf) 5 t3 rfl ?_) ?_
    · change listed (s.cpu.pc+8)=_; rw [pc]; rfl
    · rfl
    refine .step (middle:=t5) ?_ (candidate_step env (.sub 0 0) 2 t4 rfl ?_) ?_
    · change listed (s.cpu.pc+13)=_; rw [pc]; rfl
    · rfl
    refine .step (middle:=t6) ?_ (candidate_step env (.input) 1 t5 rfl ?_) ?_
    · change listed (s.cpu.pc+15)=_; rw [pc]; rfl
    · change (s.ioAllowed && true)=true; rw [io]; rfl
    refine .step (middle:=t7) ?_ (candidate_step env (.andByte 0 0xfe) 2 t6 rfl ?_) ?_
    · change listed (s.cpu.pc+16)=_; rw [pc]; rfl
    · rfl
    refine .step (middle:=t8) ?_ (candidate_step env (.output) 1 t7 rfl ?_) ?_
    · change listed (s.cpu.pc+18)=_; rw [pc]; rfl
    · change (s.ioAllowed && true)=true; rw [io]; rfl
    refine .step (middle:=t9) ?_ (candidate_step env (.pop 2) 1 t8 rfl ?_) ?_
    · change listed (s.cpu.pc+19)=_; rw [pc]; rfl
    · change ramWord (s.cpu.core.regs 4)=true
      have h := stack 0 (by decide)
      simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero] using h
    refine .step (middle:=t10) ?_ (candidate_step env (.pop 1) 1 t9 rfl ?_) ?_
    · change listed (s.cpu.pc+20)=_; rw [pc]; rfl
    · change ramWord (s.cpu.core.regs 4+4)=true
      have h := stack 4 (by decide)
      simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero] using h
    refine .step (middle:=t11) ?_ (candidate_step env (.pop 3) 1 t10 rfl ?_) ?_
    · change listed (s.cpu.pc+21)=_; rw [pc]; rfl
    · change ramWord (s.cpu.core.regs 4+4+4)=true
      have h := stack 8 (by decide)
      simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero] using h
    refine .step (middle:=t12) ?_ (candidate_step env (.ret) 1 t11 rfl ?_) ?_
    · change listed (s.cpu.pc+22)=_; rw [pc]; rfl
    · change ramWord (s.cpu.core.regs 4+4+4+4)=true
      have h := stack 12 (by decide)
      simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero] using h
    exact .nil _
  exact path.transfer _ decoded
theorem tail_registers (env : Environment) (s : VState) :
    (tail env s).cpu.pc=(load32 s.cpu.core.memory (s.cpu.core.regs 4+12)).toNat ∧
    (tail env s).cpu.core.regs 1=load32 s.cpu.core.memory (s.cpu.core.regs 4+4) ∧
    (tail env s).cpu.core.regs 2=load32 s.cpu.core.memory (s.cpu.core.regs 4) ∧
    (tail env s).cpu.core.regs 3=load32 s.cpu.core.memory (s.cpu.core.regs 4+8) ∧
    (tail env s).cpu.core.regs 4=s.cpu.core.regs 4+16 ∧
    (tail env s).cpu.core.regs 5=s.cpu.core.regs 5 ∧
    (tail env s).cpu.core.regs 6=s.cpu.core.regs 6 ∧
    (tail env s).cpu.core.regs 7=s.cpu.core.regs 7 := by
  refine ⟨?_,rfl,rfl,?_,?_,rfl,rfl,rfl⟩
  · change (load32 s.cpu.core.memory (s.cpu.core.regs 4+4+4+4)).toNat=_
    simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd]
  · change load32 s.cpu.core.memory (s.cpu.core.regs 4+4+4)=_
    simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd]
  · change s.cpu.core.regs 4+4+4+4+4=_
    simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd]
def middle (env : Environment) (s : VState) : VState :=
  let t1 := candidate env (.immediate 2 0xaf9cc) 5 s
  let t2 := candidate env (.loadWord 0 0x290f8) 5 t1
  let t3 := candidate env (.xor 3 3) 2 t2
  let t4 := candidate env (.add 0 0x39cc) 5 t3
  t4
theorem middle_execution (env : Environment) (s : VState) (pc : s.cpu.pc=0x1ae36) :
    X86VgaRoutine.Prefix env program 4 s (middle env s) := by
  have path : X86VgaRoutine.Prefix env listed 4 s (middle env s) := by
    refine .step (op:=.immediate 2 0xaf9cc) (length:=5) ?_ rfl ?_
    · rw [pc]; rfl
    refine .step (op:=.loadWord 0 0x290f8) (length:=5) ?_ rfl ?_
    · change listed (s.cpu.pc+5)=_; rw [pc]; rfl
    refine .step (op:=.xor 3 3) (length:=2) ?_ rfl ?_
    · change listed (s.cpu.pc+10)=_; rw [pc]; rfl
    refine .step (op:=.add 0 0x39cc) (length:=5) ?_ rfl ?_
    · change listed (s.cpu.pc+12)=_; rw [pc]; rfl
    exact .nil _
  exact path.transfer _ decoded
theorem middle_registers (env : Environment) (s : VState) :
    (middle env s).cpu.pc=s.cpu.pc+17 ∧
    (middle env s).cpu.core.regs 0=load32 s.cpu.core.memory 0x290f8+0x39cc ∧
    (middle env s).cpu.core.regs 2=0xaf9cc ∧
    (middle env s).cpu.core.regs 3=0 ∧
    (∀ r, r≠0 → r≠1 → r≠2 → r≠3 → (middle env s).cpu.core.regs r=s.cpu.core.regs r) ∧
    (middle env s).apertureMapped=s.apertureMapped ∧
    (middle env s).ioAllowed=s.ioAllowed := by
  refine ⟨rfl,?_,rfl,?_,?_,rfl,rfl⟩
  · change load32 s.cpu.core.memory ((0#32)+(0#32 <<< 0)+(0x290f8#32))+(0x39cc#32)=_
    rw [BitVec.zero_shiftLeft,BitVec.zero_add,BitVec.zero_add]
    rfl
  · change s.cpu.core.regs 3 ^^^ s.cpu.core.regs 3=0; exact BitVec.xor_self
  · intro r h0 h1 h2 h3
    have n0 : r.val≠0 := fun h => h0 (Fin.ext h)
    have n1 : r.val≠1 := fun h => h1 (Fin.ext h)
    have n2 : r.val≠2 := fun h => h2 (Fin.ext h)
    have n3 : r.val≠3 := fun h => h3 (Fin.ext h)
    have hr : r.val=4 ∨ r.val=5 ∨ r.val=6 ∨ r.val=7 := by have := r.isLt; omega
    rcases hr with h | h | h | h
    · have : r=4 := Fin.ext h; subst r; rfl
    · have : r=5 := Fin.ext h; subst r; rfl
    · have : r=6 := Fin.ext h; subst r; rfl
    · have : r=7 := Fin.ext h; subst r; rfl
end Doom.Proofs.E1M1AimActiveIcon
