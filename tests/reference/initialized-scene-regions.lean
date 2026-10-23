import Doom.Proofs.InitializedSceneRegions
open Doom Doom.Proofs.InitializedSceneRegions
example : storageCheck ⟨0x80000,0x90000⟩ 0x240000 6924 = true := by decide +kernel
example : storageCheck ⟨0x80000,0x90000⟩ 0x80004 8 = false := by decide +kernel
example : storageCheck ⟨0x80000,0x90000⟩ 0x2c020 8 = false := by decide +kernel
example : storageCheck ⟨0x80000,0x90000⟩ 0xfffffffc 8 = false := by decide +kernel
#check cell_safe
#check map_inputs
