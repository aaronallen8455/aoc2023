import Aoc2023.Common

import Std.Data.List.Basic

namespace D11

def space (p : Part)
          (g : Nat → Nat × Nat → Nat × Nat)
          (xs : List (List (Option (Nat × Nat))))
          : List (List (Option (Nat × Nat))) :=
  let f s x :=
    if x.all Option.isNone
    then (x, s + if p == .Part1 then 1 else 999999)
    else (x.map (Option.map (g s)), s)
  (List.mapAccumL f 0 xs).1

def dist (p : Nat × Nat) (q : Nat × Nat) : Nat :=
  p.1.max q.1 - p.1.min q.1 + p.2.max q.2 - p.2.min q.2

def dists : List (Nat × Nat) → Nat
  | [] => 0
  | x :: xs => (dist x <$> xs).sum + dists xs

def solve (inp : String) (p : Part) : String :=
  let grid := List.enum $ (List.enum ∘ String.toList) <$> inp.lines
  let gals := grid.map λ (r, x) => x.map λ pp =>
    match Prod.snd pp with
      | '#' => some (r, pp.1)
      | _ => none
  let gs := space p (λ n (r, c) => (r + n, c)) gals
  let gs2 := space p (λ n (r, c) => (r, c + n)) gs.transpose
  let gs3 := (gs2.map λ xs => xs.filterMap id).join
  toString $ dists gs3
