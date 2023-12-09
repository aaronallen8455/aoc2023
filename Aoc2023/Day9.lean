import Aoc2023.Common

namespace D9

def next (i : List Int) : Int :=
  let f acc x :=
    let rec go
      | [], _ => []
      | d :: r, x =>
        (x - d) :: go r (x - d)
    go (0 :: acc) x
  (i.foldl f []).sum

def solve (inp : String) (p : Part) : String :=
  let xs := (List.map String.toInt! ∘ String.words) <$> inp.lines
  if p == .Part1 then
    toString (next <$> xs).sum
  else
    toString ((next ∘ List.reverse) <$> xs).sum
