import Aoc2023.Common

import Std.Data.HashMap

namespace D12

def parse (i : String) : Array Char × List Nat :=
  match i.words with
    | [a, b] => (a.toList.toArray, (b.split (· == ',')).map String.toNat!)
    | _ => panic! "no"

partial
def groupAt (n : Nat) (l : Nat) (a : Array Char) : Bool :=
  if l == 0 then
    match a.get? n with
      | some '#' => false
      | _ => true
    else
    match a.get? n with
      | some '#' | some '?' => groupAt (n + 1) (l - 1) a
      | _ => false

partial
def combos (n : Nat) (a : Array Char) : List Nat → StateM (Std.HashMap (Nat × Nat) Nat) Nat
  | [] => match a.get? n with
          | some '#' => pure 0
          | some _ => combos (n + 1) a []
          | none => pure 1
  | x :: xs => do
  if n ≥ a.size then return 0
  let dp ← get
  match dp.find? (n, xs.length) with
    | some r => pure r
    | none =>
      let r1 ←
        if groupAt n x a
        then combos (n + x + 1) a xs
        else pure 0
      let r2 ←
        if a.get? n == some '#' then pure 0
        else combos (n + 1) a (x :: xs)
      let r3 := r1 + r2
      modify (λ s => s.insert (n, xs.length) r3)
      pure r3

def expand (p : Array Char × List Nat) : Array Char × List Nat :=
  ( (List.intercalate ['?'] (List.replicate 5 p.1.toList)).toArray
  , List.join $ List.replicate 5 p.2)

def solve (inp : String) (p : Part) : String :=
  let lns := ((if p == .Part1 then id else expand) ∘ parse) <$> inp.lines
  let rs : List Nat :=
    (λ (a, xs) => StateT.run' (combos 0 a xs) Std.HashMap.empty) <$> lns
  toString rs.sum
