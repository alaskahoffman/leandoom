import Doom.Render

namespace Doom

def keyDown (keys : UInt32) (bit : UInt32) : Bool := keys &&& bit != 0

/-- Free camera for renderer inspection: deliberately has no gameplay collision or gravity. -/
def Camera.move (camera : Camera) (keys : UInt32) (elapsed : Float) : Camera := Id.run do
  let dt := max 0.0 (min 0.05 elapsed)
  let direction := fun positive negative =>
    (if keyDown keys positive then 1.0 else 0.0) - (if keyDown keys negative then 1.0 else 0.0)
  let angle := camera.angle.turn (direction 32 64 * dt * 1.8)
  let speed := if keyDown keys 512 then 400.0 else 160.0
  let forward := direction 2 4
  let strafe := direction 16 8
  let norm := if forward != 0 && strafe != 0 then 0.7071067811865476 else 1.0
  let sin := angle.radians.sin
  let cos := angle.radians.cos
  let clamp := fun v => Fixed.ofFloat (max (-32767.0) (min 32767.0 v))
  return {
    x := clamp (camera.x.toFloat + (forward * cos + strafe * sin) * norm * speed * dt)
    y := clamp (camera.y.toFloat + (forward * sin - strafe * cos) * norm * speed * dt)
    z := clamp (camera.z.toFloat + direction 128 256 * speed * dt)
    angle := angle
  }

end Doom
