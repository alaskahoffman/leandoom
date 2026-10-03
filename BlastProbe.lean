import Doom.Radius
open Doom Doom.Collision

private def portal (v : Array Int) : Except String Bool := do
  let f := fun i => Fixed.ofInt v[i]!
  let axis := v[14]!
  let vertices : Array Vertex := if axis == 0 then #[⟨64,-128⟩,⟨64,128⟩] else #[⟨-128,64⟩,⟨128,64⟩]
  let origin := vertices[0]!
  let delta : Vertex := if axis == 0 then ⟨0,256⟩ else ⟨256,0⟩
  let sectors : Array Sector := #[⟨v[8]!,v[9]!,"","",0,0,0⟩,⟨v[10]!,v[11]!,"","",0,0,0⟩]
  let map : Map := {
    name := "fixture", things := #[], vertices,
    lines := #[⟨0,1,v[12]!.toNat,0,0,0,1⟩],
    sides := #[⟨0,0,"","","",0⟩,⟨0,0,"","","",1⟩], sectors,
    segs := #[⟨0,1,0,0,0,0⟩,⟨1,0,0,0,1,0⟩],
    subsectors := #[⟨1,0⟩,⟨1,1⟩],
    nodes := #[⟨origin,delta,default,default,.subsector 0,.subsector 1⟩],
    reject := ByteArray.mk #[UInt8.ofNat v[13]!.toNat],
    blockmap := ⟨⟨0,0⟩,1,1,#[#[]],true⟩ }
  let a : SolidThing := {x := f 0,y := f 1,z := f 2,height := f 3,radius := f 3,sector := 0}
  let b : SolidThing := {x := f 4,y := f 5,z := f 6,height := f 7,radius := f 7,sector := 1}
  Sight.check map a b

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: blast-probe commands")
  let out ← IO.getStdout
  for line in (← IO.FS.readFile path).splitOn "\n" do
    let parts := (line.splitOn " ").filter (!·.isEmpty)
    if parts.isEmpty then continue
    let op := parts.head!
    let v := (parts.tail.map (fun s => s.toInt!.toInt32)).toArray
    let f := fun i => (⟨v[i]!⟩ : Fixed)
    let result : Except String String := do
      if op == "side" then return toString (Sight.side ⟨f 2,f 3,f 4,f 5⟩ (f 0) (f 1))
      if op == "portal" then return if (← portal (v.map Int32.toInt)) then "1" else "0"
      if op == "blast" then
        let mut actors := #[]
        let mut links := Array.replicate 16 (#[] : Array Nat)
        for i in [:32] do
          let cell := i%16
          let actor : SolidThing := {
            x := f 0 + Fixed.ofInt (Int.ofNat ((cell%4)*128+60+i%2)),
            y := f 1 + Fixed.ofInt (Int.ofNat ((cell/4)*128+60)),
            radius := Fixed.ofInt (Int.ofNat ((i%4)*8)), shootable := i%5 != 0, sector := i }
          actors := actors.push actor
          links := links.set! cell (#[i] ++ links[cell]!)
        let scene : Scene := {
          grid := ⟨⟨v[0]!.toInt/65536,v[1]!.toInt/65536⟩,4,4,Array.replicate 16 #[],true⟩,
          lines := #[], things := actors, links }
        let spot : SolidThing := {x := f 2,y := f 3,radius := ⟨0⟩}
        let hits ← scene.radiusAttack spot v[4]!
          (fun id => if id%7 == 0 then 16 else 3001)
          (fun target _ => pure (target.sector % 3 != 0))
        return "hits" ++ String.join (hits.toList.map fun (id,n) => s!" {id}:{n}")
      if op == "falloff" then
        let a : SolidThing := {x := f 0,y := f 1,radius := ⟨0⟩}
        let b : SolidThing := {x := f 2,y := f 3,radius := f 4,shootable := v[5]! &&& 4 != 0}
        let amount ← radiusDamage a b v[7]! v[6]!.toInt.toNat
        return s!"{if v[8]! == 0 then 0 else amount} {if amount > 0 then 1 else 0}"
      throw "invalid blast command"
    match result with
    | .ok value => out.putStrLn value
    | .error e => throw (IO.userError e)
