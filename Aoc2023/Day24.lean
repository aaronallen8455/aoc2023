import Aoc2023.Common

import Std.Data.List.Basic
import Std.Data.HashMap
import Std.Data.RBMap

namespace D24

structure Pt where
  x : Int
  y : Int
  z : Int
  deriving Repr

instance : ToString Pt where
  toString := reprStr

instance : Inhabited Pt where
  default := {x:=0,y:=0,z:=0}

def parse (i : String) : Option (Pt × Pt) :=
  match (String.dropRightWhile · (·==',')) <$> i.words with
    | [x, y, z, _, vx, vy, vz] =>
      some ({ x:= x.toInt!, y := y.toInt!, z:= z.toInt!}, {x:= vx.toInt!, y:= vy.toInt!, z:= vz.toInt!})
    | _ => none

def slopeXY (p : Pt × Pt) : Int × Int :=
  let nX := p.1.x + p.2.x
  let nY := p.1.y + p.2.y
  if p.1.x < nX then
    (nY - p.1.y, nX - p.1.x)
  else
    (p.1.y - nY, p.1.x - nX)

-- x component = 1
-- gives y per unit of x
def unitizeSlp (s : Int × Int) : Float :=
  -- no input has 0 components
  -- if s.2 == 0 then none else
  Float.ofInt s.1 / Float.ofInt s.2

def yInter (s : Float) (p : Pt) : Float :=
  s.neg * Float.ofInt p.x + Float.ofInt p.y

def inter (a : Pt × Pt) (b : Pt × Pt) : Option (Float × Float) :=
  let as := unitizeSlp $ slopeXY a
  let aY := yInter as a.1
  let bs := unitizeSlp $ slopeXY b
  let bY := yInter bs b.1
  if as == bs then none else
    let x := (bY - aY) / (as - bs)
    (x, x * as + aY)

def notInPast (a : Pt × Pt) (p : Float × Float) : Bool :=
  if (Float.ofInt a.1.x) == p.1 then true else
  if (Float.ofInt a.1.x) < p.1  then a.2.x > 0 else
  a.2.x < 0

def inRange (a : Pt × Pt) (b : Pt × Pt) : Bool :=
  match inter a b with
    | none => false
    | some i => notInPast a i && notInPast b i
        && i.1 ≥ 200000000000000 && i.1 ≤ 400000000000000
        && i.2 ≥ 200000000000000 && i.2 ≤ 400000000000000

-- make x component = 1
def normVec (v : Pt) : Float × Float × Float :=
  (1, Float.ofInt v.y / Float.ofInt v.x, Float.ofInt v.z / Float.ofInt v.x)

def scale (p : Pt) (n : Int) : Pt :=
  {x := p.x * n, y := p.y * n, z := p.z * n}

def addPt (a : Pt) (b : Pt) : Pt :=
  {x := a.x + b.x, y := a.y + b.y, z := a.z + b.z}

def err (a : Pt × Pt) (b : Pt × Pt) : Option Float := do
  let (_, y) ← inter a b
  let (_, yy) ← inter
    -- segfaults if z field is not assigned...
    ({a.1 with x := a.1.z, z := a.1.x}, {a.2 with x := a.2.z, z := a.2.x})
    ({b.1 with x := b.1.z, z := b.1.x}, {b.2 with x := b.2.z, z := b.2.x})
  pure $ y - yy

def mkLine (a : Pt) (b : Pt) : (Pt × Pt) :=
  (a, {x := b.x - a.x, y := b.y - a.y, z := b.z - a.z})

partial
def search2 (lp : Pt) (r : Pt × Pt) (pol : Bool) (rv : Pt) (rp : Pt) (ps : List (Pt × Pt)) (pprev : Float) (prev : Float) : Float × Pt :=
  let ln := mkLine lp rp
  let e := (List.sum (ps.filterMap (err ln))) / Float.ofNat ps.length
  if dbgTraceVal e == 0 then (0, rp)
  else if e == pprev then (min e prev, rp)
  else if e ≥ prev then
    let v := if pol then r.2 else scale r.2 (-1)
    search2 lp r (not pol) v (addPt v rp) ps prev e
  else
    let v := scale rv 2
    search2 lp r pol v (addPt v rp) ps prev e

partial
def search1 (l : Pt × Pt) (pol : Bool) (lv : Pt) (lp : Pt) (r : Pt × Pt) (rp : Pt) (ps : List (Pt × Pt)) (pprev : Float) (prev : Float) : Option (Pt × Pt) :=
  let (e, nrp) := search2 lp r false r.2 rp ps 0 0
  if e == 0 then mkLine lp nrp
  else if e == pprev then none
  else if e ≥ prev then
    let v := if pol then l.1 else scale r.1 (-1)
    search1 l (not pol) v (addPt v lp) r nrp ps prev e
  else
    let v := scale lv 2
    search1 l pol v (addPt v lp) r nrp ps prev e

def inter3D (a : Pt × Pt) (b : Pt × Pt) : Option (Float × Float × Float) := do
  let (x, y) ← inter a b
  let (z, yy) ← inter
    -- segfaults if z field is not assigned...
    ({a.1 with x := a.1.z, z := a.1.x}, {a.2 with x := a.2.z, z := a.2.x})
    ({b.1 with x := b.1.z, z := b.1.x}, {b.2 with x := b.2.z, z := b.2.x})
  guard $ y == yy
  pure (x, y, z)

#eval inter3D ({x:=-1,y:=-2,z:=-3},{x:=1,y:=2,z:=3}) ({x:=-2,y:=2,z:=-5},{x:=2,y:=-2,z:=5})

def solve (inp : String) (p : Part) : String :=
  let lns := inp.lines.filterMap parse
  if p == .Part1 then
    let r := lns.mapWithPrefixSuffix λ _ x suf =>
      (suf.filter (inRange x)).length
    toString r.sum
  else
    match lns with
      | a :: b :: rest =>
        let r := search1 a false a.2 a.1 b b.1 rest 0 0
        toString r
      | _ => "no"
    --let r := lns.mapWithPrefixSuffix λ _ x suf =>
      --(suf.filterMap (inter3D x))
    --toString r.join--$ inp.lines.map parse


-- pos = x + vx * t, y + vy * t, z + vz * t
-- could collect the position of each thing at various points in time and do a
-- massive search for the combination across all of them that results in
-- a straight line. Given that we're dealing with gigantic numbers, this
-- sort of iteration seems doomed to be extremely slow.
-- has to be a better way than guess and check.
-- there must be some math trick
-- if two of the lines have the same velocity vector than that should
-- constrain the possibilities to a plane.
-- perhaps then find the intersection with that plane for all other lines
-- and hope to god that it forms a straight path.
-- need to first test for the existence of such a plane.
-- normalize all vectors and check for dupes. can be going in opposite directions.
-- there don't appear to be any parallel vectors which is appalling because
-- the sample set had them.
-- Perhaps can make due with finding two lines that intersect. If they
-- intersect is it then possible to specify a plane that contains both
-- lines? Seems like yes. Is it feasible to search of intersections of
-- lines in 3d space?
-- It seems complicated to find line intersections but what if it is first
-- narrowed to lines that intersect ristricted to two dimensions.
-- If they intersect when viewed from the X-Y perspective, then we find the
-- intersection from the Y-Z perspective and if they have the same Y component
-- then that must be an intersection? Need to also check the X-Z perspective?
-- Apparently there are no lines that intersect and therefore no way to
-- restrict to a plane. Do I have to brute force this bitch?
--
--
-- taking the X-Y intersections between each one and the others, find one point
-- for each one that together lie on the same line. doesnt work.
--
-- There are a handful of pairs where the slopes of the lines are the same
-- from one perspective. This means that the correct location can be found
-- by moving so that those lines overlap. No, if the lines overlap then it's
-- impossible to hit both.
--
-- Find a line that passes through 3 of the stone lines.
-- A line between two stones can simply be their starting points, or better,
-- the point on the second line one nano later.
-- Can test if lines are getter closer to intersecting by the size of the gap
-- between the y components in interceps from the two perspectives.
-- Can use this to do a binary search to find where it aligns...
-- It's important that the master line crosses each at integer positions
--
-- Draw a line between any two points on 2 of the lines and test and amount
-- of error with the 3rd line. Adjust the two points using binary search to
-- minimize error until points are found that form a line between all three.
--
-- To generalize, what if two points are selected from any of the two lines
-- check error with all other paths and adjust the two points to minimize the
-- total error across all of them. Should eventually find the lines that
-- intersects everything.
