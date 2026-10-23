import Lake
open Lake DSL System

package «lean-doom» where
  version := v!"0.6.0"

lean_lib Doom

-- Pinned, unmodified core from the HITrees paper's Lean development.
lean_lib HITrees where
  srcDir := "vendor/hitrees/src"

@[default_target]
lean_exe «lean-doom» where
  root := `Main

lean_exe «doom-tests» where
  root := `Tests

lean_exe «fidelity-probe» where
  root := `FidelityProbe

lean_exe «motion-probe» where
  root := `MotionProbe

lean_exe «collision-probe» where
  root := `CollisionProbe

lean_exe «pickup-probe» where
  root := `PickupProbe

lean_exe «fuzz-probe» where
  root := `FuzzProbe

lean_exe «status-probe» where
  root := `StatusProbe

lean_exe «lights-probe» where
  root := `LightsProbe

lean_exe «doors-probe» where
  root := `DoorsProbe

lean_exe «movers-probe» where
  root := `MoversProbe

lean_exe «level-probe» where
  root := `LevelProbe

lean_exe «imp-probe» where
  root := `ImpProbe

lean_exe «blast-probe» where
  root := `BlastProbe

lean_exe «death-probe» where
  root := `DeathProbe

target sdlShim pkg : FilePath := do
  let flags ← IO.Process.output { cmd := "pkg-config", args := #["--cflags", "sdl2"] }
  if flags.exitCode != 0 then
    error "SDL2 development files missing: install SDL2 and pkg-config to build the viewer"
  let includeDir ← getLeanIncludeDir
  let src ← inputTextFile (pkg.dir / "native" / "sdl.c")
  let args := flags.stdout.trimAscii.toString.splitOn " " |>.filter (!·.isEmpty) |>.toArray
  buildO (pkg.buildDir / "native" / "sdl.o") src
    #["-I", includeDir.toString] (#["-O2", "-std=c11", "-Wall", "-Wextra", "-Werror"] ++ args)

lean_exe «lean-doom-viewer» where
  root := `Viewer
  -- AppKit must run on the OS main thread; Lean's default runner spawns a worker.
  moreLeancArgs := #["-Dlean_run_main=doom_run_on_main"]
  moreLinkObjs := #[sdlShim]
  moreLinkArgs := #["-lSDL2"] ++
    (match get_config? sdlLibDir with
     | some dir => #[s!"-L{dir}", s!"-Wl,-rpath,{dir}"]
     | none => #[])

lean_exe «platform-tests» where
  root := `PlatformTests
  moreLeancArgs := #["-Dlean_run_main=doom_run_on_main"]
  moreLinkObjs := #[sdlShim]
  moreLinkArgs := #["-lSDL2"] ++
    (match get_config? sdlLibDir with
     | some dir => #[s!"-L{dir}", s!"-Wl,-rpath,{dir}"]
     | none => #[])

lean_exe «audio-probe» where
  root := `AudioProbe

lean_exe «weapon-probe» where
  root := `WeaponProbe

lean_exe «demo-probe» where
  root := `DemoProbe

lean_exe «trace-probe» where
  root := `TraceProbe

lean_exe «render-probe» where
  root := `RenderProbe

lean_exe «impact-probe» where
  root := `ImpactProbe

lean_exe «player-damage-probe» where
  root := `PlayerDamageProbe

lean_exe «monster-motion-probe» where
  root := `MonsterMotionProbe

lean_exe «live-render-probe» where
  root := `LiveRenderProbe

lean_exe «dos-memory-probe» where
  root := `DosMemoryProbe

lean_exe «dos-startup-probe» where
  root := `DosStartupProbe

lean_exe «initialized-e1m1-probe» where
  root := `InitializedE1M1Probe

lean_exe «initialized-scene-probe» where
  root := `InitializedSceneProbe
