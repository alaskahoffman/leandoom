import Doom.Proofs.InitializedScene
open Doom Doom.Proofs.InitializedScene Doom.Verification.X86Memory
#check map_values
#check cell_payload
#check cell_scene_lines
#check scene_sound
#check started_scene
#check cell_sources
-- Truncated witness cannot be accepted as a whole scene.
example : sceneCheck (fun _ => 0) (fun _ => 0) 0x100000 0x200000
    ({ grid := { origin := ⟨0,0⟩, width := 0, height := 0, cells := #[] },
       lines := #[], links := #[] } : Collision.Scene) ⟨0,0,0,#[],#[]⟩ = false := by decide +kernel
