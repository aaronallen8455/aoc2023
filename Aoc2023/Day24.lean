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

-- instead of finding the intersection of the two sets, find one that contains both sets
-- so that the slope can be minimal. There will need to be another step that checks that there
-- is a velocity that allows each intersection to occur at the right time.

def extendedGcd (a : Int) (b : Int) : Id (Int × Int × Int) := do
    --Returns:
        --gcd: The greatest common divisor of a and b.
        --s, t: Coefficients such that s*a + t*b = gcd
  let mut old_r := a
  let mut r := b
  let mut old_s := 1
  let mut s := 0
  let mut old_t := 0
  let mut t := 1
  while r ≠ 0 do
    let quotient := old_r.div r
    let pr := r
    r := old_r - quotient * r
    old_r := pr
    let ps := s
    s := old_s - quotient * s
    old_s := ps
    let pt := t
    t := old_t - quotient * t
    old_t := pt
  (old_r, old_s, old_t)

def combinePhasedRotations (a_period : Int) (a_phase : Int) (b_period : Int) (b_phase : Int) : Option (Int × Int) := do
    --Returns: combined_period, combined_phase
    --The combined rotation is at its reference point if and only if both a and b
    --are at their reference points.
  let (gcd, s, _t) := extendedGcd a_period b_period
  let phase_difference := a_phase - b_phase
  let pd_mult := phase_difference.div gcd
  let pd_remainder := phase_difference.mod gcd
  guard $ pd_remainder == 0
  let combined_period := a_period / gcd * b_period
  let combined_phase := (a_phase - s * pd_mult * a_period) % combined_period
  (combined_period, combined_phase)

def lcmOffset (a : Int) (b : Int) (d : Int) : Option Int := do
    --"""Where the arrows first align, where green starts shifted by advantage"""
  let (period, phase) ← combinePhasedRotations a 0 b (-d % b)
  pure $ -phase % period

partial
def interCs (a : Int × Int) (b : Int × Int) : Option (Int × Int) := do
  let newM := lcmInt a.1 b.1
  let lcm ← lcmOffset a.1 b.1 (b.2 - a.2)
  some (newM, lcm + a.2)

def checkSlope (s : Int) (lns : List (Int × Int)) : Option Int :=
  let go | (accM, accC), (m, c) => interCs (accM, accC) (m - s, c)
  Prod.snd <$> lns.foldlM go (1, 0)

#eval checkSlope (1) [(1, 13), (-1, 19), (-2, 25), (-2, 31), (-5, 19)]
#eval checkSlope (2) [(-2, 30), (-2, 22), (-4, 34), (-1, 28), (-3, 15)]

def searchC (lns : List (Int × Int)) : List (Int × Int) :=
  ((List.replicate 100000 ()).enum.map λ (n, _) => Int.ofNat n - 50000).filterMap
    (λ s => (s, ·) <$> checkSlope s lns)

def solve (inp : String) (p : Part) : String :=
  let lns := inp.lines.filterMap parse
  if p == .Part1 then
    let r := lns.mapWithPrefixSuffix λ _ x suf =>
      (suf.filter (inRange x)).length
    toString r.sum
  else
    let ys := searchC $ lns.map λ (p, v) => (v.y, p.y)
    let xs := searchC $ lns.map λ (p, v) => (v.x, p.x)
    let zs := searchC $ lns.map λ (p, v) => (v.z, p.z)
    (toString ∘ List.sum) $ (ys ++ xs ++ zs).map Prod.snd

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
