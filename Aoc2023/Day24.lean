import Aoc2023.Common

import Std.Data.List.Basic
import Std.Data.HashMap
import Std.Data.RBMap
import Lean.Data.HashSet

namespace D24

structure Pt where
  x : Int
  y : Int
  z : Int
  deriving Repr, BEq

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
  let (x, y) ← inter a b
  let (_, yy) ← inter
    -- segfaults if z field is not assigned...
    ({a.1 with x := a.1.z, z := a.1.x}, {a.2 with x := a.2.z, z := a.2.x})
    ({b.1 with x := b.1.z, z := b.1.x}, {b.2 with x := b.2.z, z := b.2.x})
  let (xx, _) ← inter
    -- segfaults if z field is not assigned...
    ({a.1 with y := a.1.z, z := a.1.y}, {a.2 with y := a.2.z, z := a.2.y})
    ({b.1 with y := b.1.z, z := b.1.y}, {b.2 with y := b.2.z, z := b.2.y})
  pure $ Float.abs (y - yy) + Float.abs (x - xx)

def mkLine (a : Pt) (b : Pt) : (Pt × Pt) :=
  (a, {x := b.x - a.x, y := b.y - a.y, z := b.z - a.z})

def dist (a : Pt × Pt) (b : Pt × Pt) : Option Float := do
  let (x, _) ← inter a b
  let diffXA := x - Float.ofInt a.1.x
  let ma := diffXA / Float.ofInt a.2.x
  let aZ := ma * Float.ofInt a.2.z + Float.ofInt a.1.z
  let diffXB := x - Float.ofInt b.1.x
  let mb := diffXB / Float.ofInt b.2.x
  let bZ := mb * Float.ofInt b.2.z + Float.ofInt b.1.z
  (aZ - bZ).abs

partial
def search2 (lp : Pt) (r : Pt × Pt) (rv : Pt) (rp : Pt) (ps : List (Pt × Pt)) (prev : Float) : Float × Pt :=
  let ln := mkLine lp rp
  let e := (List.sum (ps.filterMap (dist ln))) / Float.ofNat ps.length
  if e == 0 then (0, rp)
  -- else if e == pprev then (min e prev, rp)
  else if e ≥ prev then
    if rv == r.2 then dbgTrace (toString e) λ _ => (min e prev, rp) else
    let v := r.2
    if v == rv then
      search2 lp r v (addPt v rp) ps prev
      else search2 lp r v (addPt v $ addPt (scale rv (-1)) rp) ps prev
  else
    let v := scale rv 2
    search2 lp r v (addPt v rp) ps e

partial
def search1 (l : Pt × Pt) (lv : Pt) (lp : Pt) (r : Pt × Pt) (ps : List (Pt × Pt)) (prev : Float) : Option (Pt × Pt) :=
  let (e, nrp) := search2 lp r r.2 r.1 ps 99999999999999999999999
  if e == 0 then mkLine lp nrp
  else if e ≥ prev then
    --if lv == l.2 then none else
    let v := l.2
    if v == lv then
      search1 l v (addPt v lp) r ps prev
      else
      search1 l v (addPt v $ addPt (scale lv (-1)) lp) r ps prev
  else
    let v := scale lv 2
    search1 l v (addPt v lp) r ps e

def inter3D (a : Pt × Pt) (b : Pt × Pt) : Option (Float × Float × Float) := do
  let (x, y) ← inter a b
  let (z, yy) ← inter
    -- segfaults if z field is not assigned...
    ({a.1 with x := a.1.z, z := a.1.x}, {a.2 with x := a.2.z, z := a.2.x})
    ({b.1 with x := b.1.z, z := b.1.x}, {b.2 with x := b.2.z, z := b.2.x})
  guard $ y == yy
  pure (x, y, z)

def viable (can : Pt × Pt) (l : Pt × Pt) : Bool := flip Option.getD false $ do
  let i ← inter can l
  notInPast l i -- && notInPast can i

def findCycle (s : Int) (ln : Int × Int) : Id (Lean.HashSet Int) := do
  let mut seen := Lean.HashSet.empty
  let mut i := 0
  repeat
    let v := ln.1 * i + ln.2 - s * i -- (ln.1 - s) * i + ln.2
    -- will then have two things of the form
    -- (ln.1 - s) * i + ln.2
    -- need to find if there is some value of i1 and i2 that make them equal
    -- and what that value is.
    -- (ln1.1 - s) * i1 + ln1.2 = (ln2.1 - s) * i2 + ln2.2
    -- i1 = ((ln2.1 - s) * i2 + ln2.2 - ln1.2) / (ln1.1 - s)
    if seen.contains v then break
    seen := seen.insert v
    i := i + 1
  seen

partial
def interCs (a : Int × Int) (b : Int × Int) : Option (Int × Int) :=
  let newM := lcmInt a.1 b.1
  let g := a.1.natAbs.gcd b.1.natAbs
  if (b.2 - a.2).mod g == 0
  then
    let rec go x :=
      if x.mod a.1 == 0
      then some (newM, x + a.2)
      else go (x + b.1)
    dbgTrace (toString (a.1, b.1 + b.2 - a.2)) λ _ => go (b.1 + b.2 - a.2)
  else none

def checkSlope (s : Int) (lns : List (Int × Int)) : Option Int :=
  let go | (accM, accC), (m, c) => interCs (accM, accC) (m - s, c)
  Prod.snd <$> lns.foldlM go (1, 0)

#eval checkSlope (-3) [(-2, 19), (-1, 18), (-2, 20), (-1, 12), (1, 20)]

def solve (inp : String) (p : Part) : String :=
  let lns := inp.lines.filterMap parse
  if p == .Part1 then
    let r := lns.mapWithPrefixSuffix λ _ x suf =>
      (suf.filter (inRange x)).length
    toString r.sum
  else
    let lnss := (lns.toArray.qsort (·.1.x < ·.1.x)).toList
    match lnss, lnss.reverse with
      | a :: rest, b :: rest2 =>
        --let r := search1 a a.2 a.1 b (rest.take 20) 99999999999999999999999
        --toString r
        let lp := addPt (scale a.2 1200732622000) a.1
        let rp := addPt (scale b.2 1) b.1
        --let lp := addPt (scale a.2 999999000000000000000) a.1
        --let rp := addPt (scale b.2 10000000000) b.1
        let ln := mkLine lp rp
        let rr := rest.filter (viable ln)
        toString rr.length
        --let rr := (List.sum (rest.filterMap (dist ln))) / Float.ofNat rest.length
        --toString rr
      | _, _ => "no"
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
--
-- Maybe try to progressively find a line where the XY intersection with all other lines
-- are within the future trajectory of that object. Could maybe be useful to narrow down
-- to ranges that are at least somewhat possible.
