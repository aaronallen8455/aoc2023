import Aoc2023.Common

import Std.Data.PairingHeap
import Std.Data.HashMap

namespace D17

inductive Dir where
  | U
  | D
  | L
  | R
  deriving BEq, Hashable

structure S where
  dist : Nat
  dir : Dir
  r : Int
  c : Int
  heat : Nat
  deriving BEq, Hashable

instance : ToString S where
  toString s := toString (s.dist, s.r, s.c, s.heat)

def move (s : S) : S :=
  let rr := match s.dir with
    | .U => s.r - 1
    | .D => s.r + 1
    | .L | .R => s.r
  let cc := match s.dir with
    | .L => s.c - 1
    | .R => s.c + 1
    | .U | .D => s.c
  {s with r := rr, c := cc, dist := s.dist + 1}

def branch (p : Part) (s : S) : List S := List.map move $
  let turnLeft :=
      { s with
        dist := 0
      , dir := match s.dir with
        | .U => .L
        | .D => .R
        | .L => .D
        | .R => .U
      }
  let turnRight :=
      { s with
        dist := 0
      , dir := match s.dir with
        | .U => .R
        | .D => .L
        | .L => .U
        | .R => .D
      }
  match p with
    | .Part1 =>
        if s.dist == 3 then
          [ turnLeft, turnRight ]
        else
          [ turnLeft, turnRight, s ]
    | .Part2 =>
        if s.dist < 4 then [s] else
        if s.dist == 10
        then [turnLeft, turnRight]
        else [s, turnLeft, turnRight]

def applyHeat (a : Array (Array Nat)) (s : S) : Option S :=
  match a.idx s.r >>= (·.idx s.c) with
    | none => none
    | some x => some {s with heat := s.heat + x}

def path (p : Part) (a : Array (Array Nat)) : Id Nat := do
  let mut fringe : Std.PairingHeap S (λ a b => a.heat < b.heat)
    := Std.PairingHeap.insert {dist := 0, dir := .D, r := 0, c := 0, heat := 0} $
      Std.PairingHeap.singleton
      {dist := 0, dir := .R, r := 0, c := 0, heat := 0}
  let mut visited : Std.HashMap (Int × Int × Dir × Nat) S := Std.HashMap.empty
  let endR := a.size - 1
  let endC := a[0]!.size - 1
  repeat
    match fringe.deleteMin with
    | none => return 0
    | some (s, nf) => do
      if s.c == endC && s.r == endR then
        return s.heat

      match visited.find? ⟨s.r, s.c, s.dir, s.dist⟩ with
        | none => visited := visited.insert ⟨s.r, s.c, s.dir, s.dist⟩ s
        | some hh =>
          if hh.heat ≤ s.heat
          then
            fringe := nf
            continue
          else
            visited := visited.insert ⟨s.r, s.c, s.dir, s.dist⟩ s

      let ns := List.filterMap (applyHeat a) $ branch p s
      fringe := ns.foldr (Std.PairingHeap.insert) nf
  0

def solve (inp : String) (p : Part) : String :=
  let a := List.toArray $
          (List.toArray ∘ List.map (String.toNat! ∘ Char.toString) ∘ String.toList)
          <$> inp.lines
  toString $ path p a
