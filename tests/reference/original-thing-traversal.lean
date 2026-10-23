import Doom.Proofs.E1M1ThingTraversal
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
namespace ThingTraversalFixture
deriving instance DecidableEq for Collision.Divline
deriving instance DecidableEq for Collision.Intercept
deriving instance DecidableEq for Collision.PathResult
deriving instance DecidableEq for Except
-- Synthetic diagnostic layout: unaligned SP=1 deliberately wraps stack writes.
-- Three linked nodes: hit, same-side rejection, equal-fraction hit.
def trace : Collision.Divline := ⟨⟨0⟩,⟨0⟩,⟨65536⟩,⟨131072⟩⟩
def target (x y : Int32) : Collision.SolidThing := {x:=⟨x⟩,y:=⟨y⟩,radius:=⟨65536⟩}
def nodes : List E1M1ThingList.Node :=
  [⟨0,0x700401,target 65536 131072⟩,⟨1,0x700801,target 196608 131072⟩,⟨2,0x700c01,target 65536 131072⟩]
def machine : X86Control.State :=
  ⟨⟨fun r => if r=2 then 0x700401 else if r=4 then 1 else 0,
    ([(1,0x2c720),(5,0x2cab1),(0x2ba10,0),(0x2ba14,0),(0x2ba18,65536),(0x2ba1c,131072),
      (0x2c028,0x2ba2c),(0x2ba20,99),(0x2ba24,1),(0x2ba28,0x1234),
      (0x70040d,65536),(0x700411,131072),(0x700441,65536),(0x70042d,0x700801),
      (0x70080d,196608),(0x700811,131072),(0x700841,65536),(0x70082d,0x700c01),
      (0x700c0d,65536),(0x700c11,131072),(0x700c41,65536),(0x700c2d,0)] : List (Word × Word)).foldl
      (fun m (a,v) => store32 m a v) (fun _ => 0)⟩,none,0x2c5d2⟩
def before : Collision.PathResult := {trace:=trace,collected:=#[⟨⟨99⟩,true,7⟩]}
def after : Collision.PathResult := {before with collected:=before.collected++#[⟨⟨65536⟩,false,0⟩,⟨⟨65536⟩,false,2⟩]}

theorem ordered_collection : E1M1ThingList.collect trace nodes before=.ok after := by decide +kernel

theorem full_return : let out := E1M1ThingTraversal.result machine nodes.length
    out.pc=0x2cab1 ∧ out.core.regs 0=1 ∧ out.core.regs 4=9 ∧ out.core.regs 2=0 ∧
    load32 out.core.memory 1=0x2c720 ∧ load32 out.core.memory 5=0x2cab1 ∧
    load32 out.core.memory 0x2c028=0x2ba44 ∧
    load32 out.core.memory 0x2ba20=99 ∧ load32 out.core.memory 0x2ba24=1 ∧ load32 out.core.memory 0x2ba28=0x1234 ∧
    load32 out.core.memory 0x2ba2c=65536 ∧ load32 out.core.memory 0x2ba30=0 ∧ load32 out.core.memory 0x2ba34=0x700401 ∧
    load32 out.core.memory 0x2ba38=65536 ∧ load32 out.core.memory 0x2ba3c=0 ∧ load32 out.core.memory 0x2ba40=0x700c01 := by decide +kernel

theorem empty_return : let s : X86Control.State := ⟨put machine.core 2 0,none,0x2c5e2⟩
    let out := E1M1ThingTraversal.result s 0
    out.pc=0x2cab1 ∧ out.core.regs 0=1 ∧ out.core.regs 4=9 ∧ load32 out.core.memory 0x2c028=0x2ba2c := by decide +kernel

theorem scene_loop : E1M1ThingTraversal.objectCell trace (nodes.map E1M1ThingList.Node.target).toArray #[0,1,2] before=.ok after := by decide +kernel
example : E1M1ThingTraversal.objectCell trace #[] #[0] before=.error "path: invalid actor link" := by decide +kernel
example : E1M1ThingList.collect trace nodes {before with collected:=Array.replicate 128 ⟨⟨99⟩,true,7⟩}=
    .error "path: intercept overflow profile is unverified" := by decide +kernel
#print axioms full_return
end ThingTraversalFixture
