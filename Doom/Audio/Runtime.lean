import Doom.Combat
import Doom.Audio.Music
namespace Doom.Audio

structure Playback where
  initial : Music.Player
  music : Music.Player
  deriving Inhabited

private def musicName (map : String) : Except String String := do
  if map.startsWith "E" then return "D_" ++ map
  let names := #["RUNNIN","STALKS","COUNTD","BETWEE","DOOM","THE_DA","SHAWN","DDTBLU","IN_CIT","DEAD","STLKS2","THEDA2","DOOM2","DDTBL2","RUNNI2","DEAD2","STLKS3","ROMERO","SHAWN2","MESSAG","COUNT2","DDTBL3","AMPIE","THEDA3","ADRIAN","MESSG2","ROMER2","TENSE","SHAWN3","OPENIN","EVIL","ULTIMA"]
  let some n := (map.drop 3).toString.toNat? | throw "music: invalid map name"
  let some name := names[n-1]? | throw "music: unknown map music"
  return "D_" ++ name

def Playback.load (lumps : Array Lump) (map : String) : Except String (Playback × Sfx.State) := do
  let name ← musicName map
  let some i := findLump lumps name | throw s!"music: missing {name}"
  let score ← (Score.parse lumps[i]!.bytes).mapError (name ++ ": " ++ ·)
  let some i := findLump lumps "GENMIDI" | throw "music: missing GENMIDI"
  let bank ← Music.instruments lumps[i]!.bytes
  let music := Music.Player.start bank score
  let effects ← Sfx.load lumps
  return (⟨music,music⟩,{ bank := effects, map8 := map.endsWith "8" || map == "MAP08" })

/-- One 35-Hz gameplay interval produces exactly 1260 stereo frames. All sample
creation/mixing stays in Lean; platform code only queues these signed PCM bytes. -/
def Playback.render (playback : Playback) (state : Simulation) : Except String (ByteArray × Playback × Simulation) := do
  let (music,player) ← playback.music.render framesPerTic
  let mut state := state
  let mut pcm := ByteArray.emptyWithCapacity (framesPerTic*4)
  let mut effects ← match state.audio with
    | none => throw "audio: playback not enabled"
    | some effects => effects.update state.soundListener state.soundPosition
  for frame in music do
    let ((l,r),next) := effects.sample
    effects := next
    pcm := put16 (put16 pcm (max (-32768) (min 32767 (frame.1+l)))) (max (-32768) (min 32767 (frame.2+r)))
  state := { state with audio := some effects }
  return (pcm,{ playback with music := player },state)

end Doom.Audio
