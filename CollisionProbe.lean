import Doom.WorldPhysics
import Doom.SectorChange
import Doom.ActorFlags
import Doom.Use
import Doom.Hitscan
import Doom.Scrolling
import Doom.App

open Doom Doom.Collision

private def number (s : String) : Except String Int := do
  let some n := s.toInt? | throw "invalid integer"
  if n < -2147483648 || n > 2147483647 then throw "integer outside int32"
  return n

private def raw (s : String) : Except String Fixed := do return ⟨Int32.ofInt (← number s)⟩

private def index (s : String) : Except String Nat := do
  let n ← number s
  if n < 0 then throw "negative index"
  return n.toNat

private def initial : Scene := {
  grid := { origin := ⟨0, 0⟩, width := 1, height := 1, cells := #[#[]] }
  lines := #[], links := #[#[]]
  sectors := #[⟨⟨0⟩, Fixed.ofInt 128⟩, ⟨⟨0⟩, Fixed.ofInt 128⟩]
  sectorLinks := #[#[], #[]] }

private def arrayText (ids : Array Nat) : String :=
  ids.foldl (fun s n => s ++ s!" {n}") (toString ids.size)

private def showResult (r : PositionResult) : String :=
  s!"{if r.clear then 1 else 0} {r.floor.raw.toInt} {r.ceiling.raw.toInt} {r.dropoff.raw.toInt} {r.ceilingLine.map Int.ofNat |>.getD (-1)} {arrayText r.specials} | {arrayText r.visitedThings} | {arrayText r.visitedLines}"

private def stepScene (scene : Scene) (p : List String) : Except String (String × Scene) := do
  match p with
  | ["reset"] => return ("reset", initial)
  | ["missilething",id,kind,z,height,flags] =>
    let id ← index id; let kind ← index kind; let flags ← index flags
    let thing := { scene.things[id]! with
      kind, z := ← raw z, height := ← raw height,
      solid := flags &&& 2 != 0, shootable := flags &&& 4 != 0 }
    return ("missilething",{ scene with things := scene.things.set! id thing })
  | ["missilequery",x,y,z,source,kind,roll] =>
    let source ← number source
    let missile : MissileQuery := {
      z := ← raw z, height := Fixed.ofInt 8,
      source := if source < 0 then none else some source.toNat,
      sourceKind := ← index kind, kinds := scene.things.map (·.kind) }
    let (_,result) ← scene.checkPositionWithEffects {
      x := ← raw x,y := ← raw y,radius := Fixed.ofInt 6,
      player := false, missile := some missile } ⟨⟨0⟩,Fixed.ofInt 128⟩
    let roll ← index roll
    let amount := if result.missileHit.isSome then 3*(roll%8+1) else 0
    return (showResult result ++ s!" | {result.missileHit.map Int.ofNat |>.getD (-1)} {amount}",scene)
  | ["grid", ox, oy, w, h] =>
    let ox ← number ox; let oy ← number oy
    let w ← index w; let h ← index h
    if w == 0 || h == 0 || w > 8 || h > 8 then throw "invalid fixture grid"
    let grid : Blockmap := { origin := ⟨ox, oy⟩, width := w, height := h, cells := Array.replicate (w*h) #[] }
    return ("grid", { scene with grid, links := Array.replicate (w*h) #[] })
  | ["line", x, y, x2, y2, ff, fc, bf, bc, flags] =>
    let flags ← index flags
    let front : Heights := ⟨← raw ff, ← raw fc⟩
    let backHeights : Heights := ⟨← raw bf, ← raw bc⟩
    let back := if flags &&& 1 != 0 then some backHeights else none
    let line ← Line.make (← raw x) (← raw y) (← raw x2) (← raw y2) front back
      (flags &&& 2 != 0) (flags &&& 4 != 0)
    let line := { line with twoSided := back.isSome && flags &&& 16 == 0, blockMonsters := flags &&& 8 != 0 }
    return (s!"line {scene.lines.size}", { scene with lines := scene.lines.push line })
  | "cell" :: c :: ids =>
    let c ← index c
    if c ≥ scene.grid.cells.size then throw "invalid cell"
    let ids ← ids.toArray.mapM index
    return ("cell", { scene with grid := { scene.grid with cells := scene.grid.cells.set! c ids } })
  | ["thing", x, y, r, solid] =>
    let thing : SolidThing := { x := ← raw x, y := ← raw y, radius := ← raw r, solid := (← index solid) != 0 }
    return (s!"thing {scene.things.size}", { scene with things := scene.things.push thing })
  | "link" :: c :: ids =>
    let c ← index c
    if c ≥ scene.links.size then throw "invalid cell"
    let ids ← ids.toArray.mapM index
    return ("link", { scene with links := scene.links.set! c ids })
  | ["query", x, y, radius, floor, ceiling, self, noclip] =>
    let self ← number self
    let query : Query := { x := ← raw x, y := ← raw y, radius := ← raw radius
                           self := if self < 0 then none else some self.toNat
                           noClip := (← index noclip) != 0 }
    let r ← scene.checkPosition query ⟨← raw floor, ← raw ceiling⟩
    return (showResult r, scene)
  | ["point", id, x, y] =>
    let some line := scene.lines[← index id]? | throw "invalid line"
    return (if line.pointSide (← raw x) (← raw y) then "1" else "0", scene)
  | ["box", id, top, bottom, left, right] =>
    let some line := scene.lines[← index id]? | throw "invalid line"
    let side := line.boxSide ⟨← raw top, ← raw bottom, ← raw left, ← raw right⟩
    return (match side with | none => "-1" | some false => "0" | some true => "1", scene)
  | ["coord", value, origin] =>
    return (toString (blockCoordinate (← raw value) (← raw origin)), scene)
  | _ => throw s!"invalid collision command: {p}"

private structure Fixture where
  sky : Array (Bool × Bool) := Array.replicate 64 (false,false)
  noBlood : Array Bool := Array.replicate 64 false
  scene : Scene := initial
  scrollSpecials : Array Nat := #[]
  scrollFronts : Array Nat := #[]
  scrollOffsets : Array Fixed := #[]
  scrollers : Array Nat := #[]
  split : Fixed := ⟨0⟩
  effect : Nat := 0
  effectX : Fixed := ⟨0⟩
  effectY : Fixed := ⟨0⟩
  motion : Motion := {}
  view : ViewState := {}

private def showScene (scene : Scene) : String := Id.run do
  let mut s := s!"{scene.things.size}"
  for t in scene.things do
    s := s ++ s!" {t.x.raw.toInt} {t.y.raw.toInt} {t.z.raw.toInt} {t.height.raw.toInt} {t.floor.raw.toInt} {t.ceiling.raw.toInt} {t.sector}"
  for lists in #[scene.sectorLinks, scene.links] do
    s := s ++ s!" | {lists.size}"
    for ids in lists do s := s ++ " / " ++ arrayText ids
  return s

private def showPath (p : PathResult) : String := Id.run do
  let t := p.trace
  let mut s := s!"{if p.completed then 1 else 0} {t.x.raw.toInt} {t.y.raw.toInt} {t.dx.raw.toInt} {t.dy.raw.toInt} | {p.blocks.size}"
  for (kind, x, y) in p.blocks do s := s ++ s!" {if kind then 1 else 0} {x.toInt} {y.toInt}"
  for hits in #[p.collected, p.visited] do
    s := s ++ s!" | {hits.size}"
    for hit in hits do s := s ++ s!" {if hit.isLine then 1 else 0} {hit.id} {hit.frac.raw.toInt}"
  return s

private def showCollection (scene : Scene) : Except String String := do
  let some player := scene.pickupPlayer | throw "no pickup player"
  let s := player.state
  let bitmask (a : Array Bool) := (a.zipIdx).foldl (fun n (b, i) => n + if b then 2^i else 0) (0 : Nat)
  let mut text := s!"{s.health} {s.bodyHealth} {s.armor} {s.armorType} {s.readyWeapon.val} {s.pendingWeapon.val} {s.bonus} {s.items} {if s.backpack then 1 else 0} {if s.shadow then 1 else 0}"
  for n in s.ammo.toArray ++ s.maxAmmo.toArray do text := text ++ s!" {n}"
  text := text ++ s!" {bitmask s.weapons.toArray} {bitmask s.cards.toArray}"
  for n in s.powers.toArray do text := text ++ s!" {n}"
  text := text ++ s!" {s.message} | {scene.things.size}"
  for t in scene.things do text := text ++ s!" {if t.removed then 1 else 0}"
  text := text ++ s!" | {scene.pickupEvents.size}"
  for e in scene.pickupEvents do
    let sound := match e.sound with | none => 0 | some .item => 1 | some .weapon => 2 | some .power => 3
    text := text ++ s!" {e.item} {if e.removed then 1 else 0} {sound} {e.message}"
  return text

private def step (state : Fixture) (p : List String) : Except String (String × Fixture) := do
  let scene := state.scene
  let sectorAt : SectorAt := fun x _ => pure (if x.raw < state.split.raw then 0 else 1)
  match p with
  | ["reset"] => return ("reset", {})
  | ["shootmeta",id,shoot,blood,z,height] =>
    let id ← index id
    let some thing := scene.things[id]? | throw "invalid actor"
    let thing := { thing with shootable := (← index shoot) != 0, z := ← raw z, height := ← raw height }
    return ("shootmeta",{ state with scene := { scene with things := scene.things.set! id thing }, noBlood := state.noBlood.set! id ((← index blood) != 0) })
  | ["skyline",id,front,back] =>
    return ("skyline",{ state with sky := state.sky.set! (← index id) ((← index front) != 0,(← index back) != 0) })
  | ["aim",id,angle,distance] =>
    let result ← scene.aimLineAttack (← index id) ⟨(Int32.ofInt (← number angle)).toUInt32⟩ (← raw distance)
    return (s!"{result.slope.raw.toInt} {result.target.map Int.ofNat |>.getD (-1)} | " ++ showPath result.path,state)
  | ["bulletslope",id,angle] =>
    let result ← scene.bulletSlope (← index id) ⟨(Int32.ofInt (← number angle)).toUInt32⟩
    return (s!"{result.raw.toInt}",state)
  | ["shoot",id,angle,distance,slope,damage] =>
    let result ← scene.lineAttack (← index id) ⟨(Int32.ofInt (← number angle)).toUInt32⟩ (← raw distance) (← raw slope)
      (Int32.ofInt (← number damage)) (fun id => state.sky[id]!) (fun id => state.noBlood[id]!)
    let text := result.events.foldl (fun text event => text ++ match event with
      | .special id => s!" s {id} 0 0 0"
      | .puff x y z => s!" p {x.raw.toInt} {y.raw.toInt} {z.raw.toInt} 0"
      | .blood x y z damage => s!" b {x.raw.toInt} {y.raw.toInt} {z.raw.toInt} {damage}"
      | .damage id damage => s!" d {id} {damage} 0 0") ""
    return (text ++ " | " ++ showPath result.path,state)
  | ["use",x,y,angle] =>
    let result ← scene.useLines (← raw x) (← raw y) ⟨(Int32.ofInt (← number angle)).toUInt32⟩
    let action := match result.action with
      | .nothing => "0 -1 -1"
      | .blocked => "1 -1 -1"
      | .special id back => s!"2 {id} {if back then 1 else 0}"
    return (action ++ " | " ++ showPath result.path,state)
  | ["scrollreset"] => return ("scrollreset", { state with scrollSpecials := #[], scrollFronts := #[], scrollOffsets := #[], scrollers := #[] })
  | ["scrollside",offset] => return ("scrollside",{ state with scrollOffsets := state.scrollOffsets.push (← raw offset) })
  | ["scrollline",special,front] =>
    let front ← index front
    if front ≥ state.scrollOffsets.size then throw "invalid scrolling side"
    return ("scrollline",{ state with scrollSpecials := state.scrollSpecials.push (← index special), scrollFronts := state.scrollFronts.push front })
  | ["scrollspecial",id,special] =>
    let id ← index id
    if id ≥ state.scrollSpecials.size then throw "invalid scrolling line"
    return ("scrollspecial",{ state with scrollSpecials := state.scrollSpecials.set! id (← index special) })
  | ["scrollspawn"] | ["scrolltick"] =>
    do
      let op := p.head!
      let state ← if op == "scrollspawn" then do
        pure { state with scrollers := ← Scrolling.spawn state.scrollSpecials }
      else do
        pure { state with scrollOffsets := ← Scrolling.tick state.scrollers state.scrollSpecials state.scrollFronts state.scrollOffsets }
      let text := state.scrollOffsets.foldl (fun text x => text ++ s!" {x.raw.toInt}")
        (arrayText state.scrollers ++ s!" | {state.scrollOffsets.size}")
      return (text,state)
  | ["bounds",top,bottom,left,right,ox,oy,w,h] =>
    let grid : Blockmap := { origin := ⟨← number ox, ← number oy⟩, width := ← index w, height := ← index h, cells := #[] }
    let bounds := sectorBlocks ⟨← raw top, ← raw bottom, ← raw left, ← raw right⟩ grid
    return (s!"{bounds.left} {bounds.right} {bounds.bottom} {bounds.top}",state)
  | ["actormeta",editor] =>
    let text := match actorFlags (← index editor) with
      | none => "none"
      | some a => s!"{a.health} {if a.shootable then 1 else 0} {if a.noBlockmap then 1 else 0} {if a.noSector then 1 else 0}"
    return (text,state)
  | ["sectoractor",id,health,shoot,drop] =>
    let id ← index id
    let some thing := scene.things[id]? | throw "invalid actor"
    let thing := { thing with health := Int32.ofInt (← number health), shootable := (← index shoot) != 0, dropped := (← index drop) != 0 }
    return ("sectoractor",{ state with scene := { scene with things := scene.things.set! id thing } })
  | ["change",left,right,bottom,top,player] =>
    let player ← number player
    let bounds : SectorBlocks := ⟨← number left, ← number right, ← number bottom, ← number top⟩
    let result ← scene.changeSectorNoCrush bounds sectorAt (if player < 0 then none else some player.toNat)
    let scene := result.scene
    let events := result.events.map (fun e => match e with | .gib id => id*2 | .remove id => id*2+1)
    let mut text := s!"{if result.blocked then 1 else 0} | " ++ arrayText result.visited ++ " | " ++ arrayText events ++ s!" | {scene.things.size}"
    for t in scene.things do
      text := text ++ s!" {t.health} {if t.solid then 1 else 0} {if t.shootable then 1 else 0} {if t.dropped || t.pickup.any (·.dropped) then 1 else 0} {if t.gibbed then 1 else 0} {t.radius.raw.toInt} {if t.removed then 1 else 0}"
    return (text ++ " | " ++ showScene scene,{ state with scene })
  | ["height",z,height,floor,ceiling,newFloor,newCeiling,clear] =>
    let thing : SolidThing := {
      x := ⟨0⟩, y := ⟨0⟩, radius := ⟨0⟩,
      z := ← raw z, height := ← raw height, floor := ← raw floor, ceiling := ← raw ceiling }
    let clear ← index clear
    if clear > 1 then throw "invalid query reply"
    let (thing,fits) := thing.clipHeight (← raw newFloor) (← raw newCeiling)
    return (s!"{if fits then 1 else 0} {thing.z.raw.toInt} {thing.floor.raw.toInt} {thing.ceiling.raw.toInt} 1 {clear}",state)
  | ["clip",id,player] =>
    let player ← index player
    if player > 1 then throw "invalid player flag"
    let result ← scene.heightClip (← index id) sectorAt (player == 1)
    return (s!"{if result.fits then 1 else 0} | " ++ showResult result.position ++ " | " ++ showScene result.scene,
      { state with scene := result.scene })
  | ["collector", id, health, skill, commercial, enabled] =>
    let id ← index id
    let some thing := scene.things[id]? | throw "invalid actor"
    let skill ← index skill
    if h : skill < 5 then
      let health := Int32.ofInt (← number health)
      let player : PickupPlayer := {
        actor := id, state := { health, bodyHealth := health },
        profile := { skill := ⟨skill, h⟩, commercial := (← index commercial) != 0 } }
      return ("collector", { state with scene := { scene with
        pickupPlayer := some player, pickupEvents := #[],
        things := scene.things.set! id { thing with canPickup := (← index enabled) != 0 } } })
    else throw "invalid skill"
  | ["item", id, sprite, z, dropped, counted] =>
    let id ← index id
    let some thing := scene.things[id]? | throw "invalid actor"
    let sprite ← index sprite
    if h : sprite < 36 then
      let z ← raw z
      let item : Pickup.Item := {
        sprite := ⟨sprite, h⟩, z,
        dropped := (← index dropped) != 0, countItem := (← index counted) != 0 }
      return ("item", { state with scene := { scene with things := scene.things.set! id { thing with z, pickup := some item } } })
    else throw "invalid sprite"
  | ["collection"] => return (← showCollection scene, state)
  | ["physical", id, angle, mz, frame, cheat, nogravity, vh, vd] =>
    let some t := scene.things[← index id]? | throw "invalid actor"
    let frame ← index frame
    if h : frame < 5 then
      let motion := t.motion {
        angle := ⟨(Int32.ofInt (← number angle)).toUInt32⟩,
        momz := ← raw mz, frame := ⟨frame, h⟩, noMomentum := (← index cheat) != 0,
        noGravity := (← index nogravity) != 0 }
      return ("physical", { state with motion, view := { height := ← raw vh, delta := ← raw vd } })
    else throw "invalid player frame"
  | ["worldxy", id, forward, side, turn, time] | ["worldtick", id, forward, side, turn, time] =>
    let op := p.head!
    let id ← index id
    let f ← number forward; let s ← number side; let a ← number turn
    if f < -128 || f > 127 || s < -128 || s > 127 || a < -32768 || a > 32767 then
      throw "integer outside ticcmd fields"
    if state.effect != 0 then throw "physics fixture requires recording-only specials"
    let cmd : Ticcmd := { forwardMove := Int8.ofInt f, sideMove := Int8.ofInt s, angleTurn := Int16.ofInt a }
    let time := Int32.ofInt (← number time)
    let cross : Scene → Crossing → Except String Scene := fun current _ => pure current
    let result ← if op == "worldxy" then
      scene.advancePlayerXY id state.motion cmd sectorAt cross
    else scene.playerPhysics id state.motion state.view cmd time sectorAt cross
    let v := if op == "worldxy" then state.view else result.view
    let b := result.body
    let mut text := showScene result.scene ++ s!" | {b.momx.raw.toInt} {b.momy.raw.toInt} {b.momz.raw.toInt} {b.angle.raw.toNat} {b.frame.val} {v.height.raw.toInt} {v.delta.raw.toInt} {v.z.raw.toInt} {v.bob.raw.toInt} {if result.landing then 1 else 0} | {result.attempts.size}"
    for a in result.attempts do
      text := text ++ s!" {a.x.raw.toInt} {a.y.raw.toInt} {if a.accepted then 1 else 0} {if a.floatOK then 1 else 0}"
    text := text ++ s!" | {result.slides.size} | {result.crossings.size}"
    for e in result.crossings do
      text := text ++ s!" {e.line} {if e.oldSide then 1 else 0} {e.x.raw.toInt} {e.y.raw.toInt} {e.sector}"
    return (text, { state with scene := result.scene, motion := b, view := v })
  | ["world", lf, lc, rf, rc, split] =>
    let scene := { scene with sectors := #[⟨← raw lf, ← raw lc⟩, ⟨← raw rf, ← raw rc⟩] }
    return ("world", { state with scene, split := ← raw split })
  | ["body", id, z, height, floor, ceiling, flags] =>
    let id ← index id; let flags ← index flags
    let some t := scene.things[id]? | throw "invalid actor"
    let moveFlags : MoveFlags := {
      noClip := flags &&& 1 != 0, teleport := flags &&& 2 != 0
      dropoff := flags &&& 4 != 0, floating := flags &&& 8 != 0
      noSector := flags &&& 16 != 0, noBlockmap := flags &&& 32 != 0 }
    let t := { t with
      z := ← raw z, height := ← raw height, floor := ← raw floor
      ceiling := ← raw ceiling, moveFlags }
    return ("body", { state with scene := { scene with things := scene.things.set! id t } })
  | ["place", id] =>
    let scene ← scene.linkThing (← index id) sectorAt
    return ("placed | " ++ showScene scene, { state with scene })
  | ["effect", mode, x, y] =>
    let effect ← index mode
    if effect > 2 then throw "invalid effect"
    return ("effect", { state with effect, effectX := ← raw x, effectY := ← raw y })
  | ["try", id, x, y] =>
    let result ← scene.tryMove (← index id) (← raw x) (← raw y) sectorAt fun current event => do
      let t := current.things[event.actor]!
      if !t.moveFlags.noSector && current.sectorLinks[t.sector]![0]? != some event.actor then
        throw "callback fired before sector relinking"
      if state.effect == 1 then
        return { current with lines := current.lines.map fun l => { l with special := false } }
      if state.effect == 2 then
        let current ← current.unlinkThing event.actor
        let moved := { t with x := state.effectX, y := state.effectY }
        let current := { current with things := current.things.set! event.actor moved }
        return ← current.linkThing event.actor sectorAt
      return current
    let events := result.crossings.foldl (fun s e =>
      s ++ s!" {e.line} {if e.oldSide then 1 else 0} {e.x.raw.toInt} {e.y.raw.toInt} {e.sector}")
      (toString result.crossings.size)
    return (s!"{if result.decision.accepted then 1 else 0} {if result.decision.floatOK then 1 else 0} | " ++
      showResult result.position ++ " | " ++ showScene result.scene ++ " | " ++ events,
      { state with scene := result.scene })
  | ["divside", x, y, ox, oy, dx, dy] =>
    let line : Divline := ⟨← raw ox, ← raw oy, ← raw dx, ← raw dy⟩
    return (if line.pointSide (← raw x) (← raw y) then "1" else "0", state)
  | ["intercept", x, y, dx, dy, x2, y2, dx2, dy2] =>
    let a : Divline := ⟨← raw x, ← raw y, ← raw dx, ← raw dy⟩
    let b : Divline := ⟨← raw x2, ← raw y2, ← raw dx2, ← raw dy2⟩
    return (toString (← interceptVector a b).raw.toInt, state)
  | ["path", x, y, x2, y2, flags, stop] =>
    let stop ← number stop
    let result ← scene.pathTraverse (← raw x) (← raw y) (← raw x2) (← raw y2) (← index flags)
      fun _ n => Int.ofNat n != stop
    return (showPath result, state)
  | ["momentum", id, x, y] =>
    let id ← index id
    let some thing := scene.things[id]? | throw "invalid actor"
    let thing := { thing with momx := ← raw x, momy := ← raw y }
    return ("momentum", { state with scene := { scene with things := scene.things.set! id thing } })
  | ["hit", line, id, x, y] =>
    let some line := scene.lines[← index line]? | throw "invalid line"
    let some thing := scene.things[← index id]? | throw "invalid actor"
    let (x, y) ← line.hitSlide thing.x thing.y (← raw x) (← raw y)
    return (s!"{x.raw.toInt} {y.raw.toInt}", state)
  | ["slide", id] =>
    let id ← index id
    if state.effect != 0 then throw "slide fixture requires recording-only specials"
    let result ← scene.slideMove id sectorAt fun current _ => pure current
    let thing := result.scene.things[id]!
    let mut s := showScene result.scene ++ s!" | {thing.momx.raw.toInt} {thing.momy.raw.toInt} | {result.attempts.size}"
    for a in result.attempts do
      s := s ++ s!" {a.x.raw.toInt} {a.y.raw.toInt} {if a.accepted then 1 else 0} {if a.floatOK then 1 else 0}"
    s := s ++ s!" | {result.paths.size}"
    for path in result.paths do s := s ++ " / " ++ showPath path
    s := s ++ s!" | {result.crossings.size}"
    for e in result.crossings do
      s := s ++ s!" {e.line} {if e.oldSide then 1 else 0} {e.x.raw.toInt} {e.y.raw.toInt} {e.sector}"
    return (s, { state with scene := result.scene })
  | _ =>
    let (text, scene) ← stepScene scene p
    return (text, { state with scene })

def main (args : List String) : IO Unit := do
  if let ["--map-lines", path, mapName, x, y, radius] := args then
    let wad ← checked (Wad.parse (← IO.FS.readBinFile path))
    let map ← checked (Doom.Map.load wad.lumps mapName)
    let scene ← checked (Scene.fromMap map)
    let x ← checked (raw x); let y ← checked (raw y); let radius ← checked (raw radius)
    let sectorId ← checked (map.sectorAt x y)
    let some sector := map.sectors[sectorId]? | throw (IO.userError "invalid destination sector")
    let result ← checked (scene.checkPosition { x, y, radius }
      ⟨Fixed.ofInt sector.floor, Fixed.ofInt sector.ceiling⟩)
    IO.println (showResult result)
    return
  let [path] := args | throw (IO.userError "usage: collision-probe input.txt")
  let input ← IO.FS.readFile path
  let out ← IO.getStdout
  let mut scene : Fixture := {}
  let mut n := 0
  for line in input.splitOn "\n" do
    n := n + 1
    if line.trimAscii.isEmpty then continue
    match step scene ((line.splitOn " ").filter (!·.isEmpty)) with
    | .ok (text, next) => scene := next; out.putStrLn text
    | .error text => throw (IO.userError s!"line {n}: {text}")
