import Doom.Proofs.E1M1FiringThings
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
namespace FiringThingsFixture
deriving instance DecidableEq for Collision.Divline
deriving instance DecidableEq for Collision.Intercept
deriving instance DecidableEq for Collision.PathResult
deriving instance DecidableEq for Except
-- Diagnostic scene: row-major cell (0,1) has deliberately non-sorted IDs.
-- Two equal-fraction hits precede a same-side rejection.
def trace : Collision.Divline := ⟨⟨0⟩,⟨0⟩,⟨65536⟩,⟨131072⟩⟩
def target (x y : Int32) : Collision.SolidThing := {x:=⟨x⟩,y:=⟨y⟩,radius:=⟨65536⟩}
def world : Collision.Scene :=
  {grid:={origin:=⟨0,0⟩,width:=2,height:=2,cells:=#[#[],#[],#[],#[]]},lines:=#[],
   things:=#[target 65536 131072,target 196608 131072,target 65536 131072],
   links:=#[#[1],#[],#[2,0,1],#[0]]}
def before : Collision.PathResult := {trace:=trace,collected:=#[⟨⟨99⟩,true,7⟩]}
def after : Collision.PathResult :=
  {before with collected:=before.collected++#[⟨⟨65536⟩,false,2⟩,⟨⟨65536⟩,false,0⟩]}

theorem selected_order : E1M1FiringThings.sceneCell trace world 0 1 before=.ok after := by decide +kernel
example : E1M1FiringThings.sceneCell trace world 1 0 before=.ok before := by decide +kernel
example : E1M1FiringThings.sceneCell trace {world with grid:={world.grid with width:=1}} 0 1 before=.ok before := by decide +kernel
example : E1M1FiringThings.sceneCell trace {world with links:=#[]} 0 1 before=.error "path: missing thing cell" := by decide +kernel
example : E1M1FiringThings.sceneCell trace {world with links:=#[#[],#[],#[99],#[]]} 0 1 before=.error "path: invalid actor link" := by decide +kernel
-- A two-hit list fits exactly with 126 old records; the next hit would overflow.
example : (E1M1FiringThings.sceneCell trace world 0 1 {before with collected:=Array.replicate 126 ⟨⟨99⟩,true,7⟩}).isOk=true := by decide +kernel
example : E1M1FiringThings.sceneCell trace world 0 1 {before with collected:=Array.replicate 127 ⟨⟨99⟩,true,7⟩}=
    .error "path: intercept overflow profile is unverified" := by decide +kernel
#print axioms selected_order
end FiringThingsFixture
