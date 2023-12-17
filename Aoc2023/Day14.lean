import Aoc2023.Common

import Std.Data.List.Basic
import Std.Data.HashMap

namespace D14

def roll : List Char → List Char
  | [] => []
  | 'O' :: xs => 'O' :: roll xs
  | '.' :: 'O' :: xs => 'O' :: '.' :: roll xs
  | '.' :: xs => '.' :: roll xs
  | '#' :: xs => '#' :: roll xs
  | _ => panic! "no"

def spin (i : List (List Char)) : List (List Char) :=
  let n := til (·==·) roll <$> i
  let w := List.transpose $ til (·==·) roll <$> n.transpose
  let s := (List.reverse ∘ til (·==·) roll ∘ List.reverse) <$> w
  let e := List.transpose $ (List.reverse ∘ til (·==·) roll ∘ List.reverse) <$> s.transpose
  e

instance : Hashable (List (List Char)) where
  hash x := hash $ List.toString <$> x

partial
def cycle (i : List (List Char)) : List (List Char) :=
  let rec go (n : Nat) hm ii :=
    if n == 1000000000 then ii else
      match hm.find? ii with
      | some nn =>
        let sz := n - nn
        let rem := 1000000000 - n
        let m := rem.div sz
        go (n + m * sz) Std.HashMap.empty ii
      | none =>
        let hm2 := hm.insert ii n
        go (n+1) hm2 (spin ii)
  go 0 Std.HashMap.empty i

def solve (inp : String) (p : Part) : String :=
  let lns := (String.toList <$> inp.lines).transpose
  let rolled :=
    if p == .Part1 then
      til (·==·) roll <$> lns
    else
      cycle lns
  let scores := List.map (λ (x, y) => x * y) $
    (List.enumFrom 1 ∘ List.reverse) $
    (List.length ∘ List.filter (· == 'O')) <$> rolled.transpose
  toString scores.sum
