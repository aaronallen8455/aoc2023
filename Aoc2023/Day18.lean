import Aoc2023.Common

import Std.Data.HashMap

namespace D18

inductive Dir where
  | U
  | D
  | L
  | R

structure Instr where
  dir : Dir
  dist : Nat
  color : String

def parse (i : String) : Instr :=
  match i.words with
    | [d, r, c] =>
      let dir := match d with
        | "U" => .U
        | "D" => .D
        | "L" => .L
        | "R" => .R
        | _ => .U
      { dir := dir, dist := r.toNat!, color := c }
    | _ => { dir := .U, dist := panic! "no", color := panic! "no" }

def pts (i : List Instr) : List (Int × Int) :=
  let mv x p := match x.dir with
    | .U => (p.1 - x.dist, p.2)
    | .D => (p.1 + x.dist, p.2)
    | .L => (p.1, p.2 - x.dist)
    | .R => (p.1, p.2 + x.dist)
  let go acc x := match acc with
    | [] => panic! "nooo"
    | p::ps => mv x p :: p :: ps
  i.foldl go [(0,0)]

def fromHex (i : String) : Nat :=
  let go acc x := match x.toNat - 87 with
    | 0 => x.toString.toNat! + acc * 16
    | r => r + acc * 16
  i.toList.foldl go 0

def parse2 (i : String) : Instr :=
  match i.words with
    | [_, _, c] =>
      let dist := fromHex $ (c.drop 2).dropRight 2
      let dir := match (c.dropRight 1).back with
        | '0' => .R
        | '1' => .D
        | '2' => .L
        | '3' => .U
        | _ => .R
      {dir := dir, dist := dist, color := "boo"}
    | _ => { dir := .U, dist := panic! "no", color := panic! "no" }

partial
def scan (ri : Int) (ranges : List (Int × Int)) (inp : Int × List Int) (acc : Int) : (Int × List (Int × Int) × Int) :=
  let rowCount := inp.1 - ri - 1
  let pts := inp.2
  let rec pairUp
      | a::b::r => (a,b) :: pairUp r
      | [] => []
      | _ => panic! "nfw"
  let rec fPts : List (Int × Int) → List Int → Int × List (Int × Int)
      | r :: rrs, p1 :: p2 :: rest =>
        if r.1 == p1 && r.2 == p2 -- close
        then
          let n := fPts rrs rest
          (n.1 + r.2 - r.1 + 1, n.2)
        else
        if r.1 == p1 -- lower up
        then
          let n := fPts ((p2, r.2) :: rrs) rest
          (n.1 + p2 - r.1, n.2)
        else
        if r.1 == p2 -- lower down
        then
          let n := fPts ((p2, r.2) :: rrs) rest
          (n.1 + r.1 - p1 + 1, (p1, r.1) :: n.2)
        else
        if r.2 == p1 -- upper up
        then
          let n := fPts rrs rest
          (n.1 + p2 - r.1 + 1, (r.1, p2) :: n.2)
        else
        if r.2 == p2 -- upper down
        then
          let n:= fPts rrs rest
          (n.1 + r.2 - r.1 + 1, (r.1, p1) :: n.2)
        else
        if r.2 < p1 -- below
        then
          let n := fPts rrs (p1::p2::rest)
          (n.1 + r.2 - r.1 + 1, r :: n.2)
        else
        if r.1 < p1 && r.2 > p2 -- split
        then
          let n := fPts ((p2, r.2) :: rrs) rest
          (n.1 + p2 - r.1, (r.1, p1) :: n.2)
        else
        if r.1 > p2 -- above
        then
          let n := fPts (r :: rrs) rest
          (n.1 + p2 - p1 + 1, (p1, p2) :: n.2)
        else
        dbgTrace (toString (r.1, r.2, p1, p2, inp.2, ranges)) λ _ => panic! "shite"
      | rrs, [] => (rrs.foldl (λ acc x => acc + x.2 - x.1 + 1) 0, rrs)
      | [], points =>
        let rr := pairUp points
        (rr.foldl (λ acc x => acc + x.2 - x.1 + 1) 0, rr)
      | _, _ => panic! "noway"
  let (rAcc, newRng) := fPts ranges pts
  let rec combine : List (Int × Int) → StateT Int Id (List (Int × Int))
      | r1 :: r2 :: rrs =>
        if r1.2 == r2.1 then do
          modify (· + 1)
          combine $ (r1.1, r2.2) :: rrs
        else (r1 :: ·) <$> combine (r2 :: rrs)
      | [x] => pure [x]
      | [] => pure []
  let newAcc := ranges.foldl (λ acc x => acc + (x.2 - x.1 + 1) * rowCount) acc
  let newerRng : List (Int × Int) × Int := StateT.run (combine newRng) 0
  (inp.1, newerRng.1, newAcc + rAcc - newerRng.2)

def solve (inp : String) (p : Part) : String :=
  let lns := (if p == .Part1 then parse else parse2) <$> inp.lines
  let pp := (λ (a,b) => (a, [b])) <$> pts lns
  let m := Std.HashMap.mapVal (λ _ b => b.toArray.qsortOrd.deduplicateSorted.toList)
        $ Std.HashMap.ofListWith pp (·++·)
  let ml := Array.toList $ m.toArray.qsort (λ x y => x.1 < y.1)
  let r := ml.foldl (λ (a,b,c) x => scan a b x c) (0, [], 0)
  toString r.2.2
