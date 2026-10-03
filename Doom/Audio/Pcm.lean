import Doom.Wad
namespace Doom.Audio
open Binary

def sampleRate : Nat := 44100
def framesPerTic : Nat := 1260

structure Sample where
  rate : Nat
  data : ByteArray
  deriving Inhabited

/-- Digital DMX (format 3). Match the reference's >48-sample gate and skip
16 leading/trailing padding bytes. Reject zero-rate and truncated input. -/
def Sample.parse (bytes : ByteArray) : Parse Sample := do
  require ((← u16 bytes 0) == 3) "DMX: expected digital sound format 3"
  let rate ← u16 bytes 2; let count ← u32 bytes 4
  require (rate > 0) "DMX: zero sample rate"
  require (count > 48) "DMX: sample too short"
  checkRange bytes 8 count
  return ⟨rate,bytes.extract 24 (8+count-16)⟩

def put16 (out : ByteArray) (n : Int) : ByteArray :=
  let n := (Int16.ofInt n).toUInt16
  (out.push n.toUInt8).push (n >>> 8).toUInt8

def put32 (out : ByteArray) (n : Nat) : ByteArray :=
  ((out.push n.toUInt8).push (n >>> 8).toUInt8 |>.push (n >>> 16).toUInt8).push (n >>> 24).toUInt8

def wav (pcm : ByteArray) : ByteArray := Id.run do
  let mut out := "RIFF".toUTF8
  out := put32 out (36+pcm.size) ++ "WAVEfmt ".toUTF8
  out := put32 out 16
  out := put16 (put16 out 1) 2
  out := put32 (put32 out sampleRate) (sampleRate*4)
  out := put16 (put16 out 4) 16
  return put32 (out ++ "data".toUTF8) pcm.size ++ pcm

end Doom.Audio
