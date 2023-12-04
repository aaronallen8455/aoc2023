import Aoc2023.Common

import Std.Data.HashMap

namespace D3

def adjSym (m : Std.HashMap (Int × Int) Char) (i : (Int × Int)) : Bool :=
  let f c := c ≠ '.' && not c.isDigit
  (m.find? (i.1 - 1, i.2)).elim False f
  || (m.find? (i.1 - 1, i.2 - 1)).elim False f
  || (m.find? (i.1 - 1, i.2 + 1)).elim False f
  || (m.find? (i.1, i.2 - 1)).elim False f
  || (m.find? (i.1, i.2 + 1)).elim False f
  || (m.find? (i.1 + 1, i.2)).elim False f
  || (m.find? (i.1 + 1, i.2 - 1)).elim False f
  || (m.find? (i.1 + 1, i.2 + 1)).elim False f

def adjStar (m : Std.HashMap (Int × Int) Char) (i : (Int × Int)) : List (Int × Int) :=
  let f t c := if c == '*' then [t] else []
  (m.find? (i.1 - 1, i.2)).elim [] (f (i.1 - 1, i.2))
  ++ (m.find? (i.1 - 1, i.2 - 1)).elim [] (f (i.1 - 1, i.2 - 1))
  ++ (m.find? (i.1 - 1, i.2 + 1)).elim [] (f (i.1 - 1, i.2 + 1))
  ++ (m.find? (i.1, i.2 - 1)).elim [] (f (i.1, i.2 - 1))
  ++ (m.find? (i.1, i.2 + 1)).elim [] (f (i.1, i.2 + 1))
  ++ (m.find? (i.1 + 1, i.2)).elim [] (f (i.1 + 1, i.2))
  ++ (m.find? (i.1 + 1, i.2 - 1)).elim [] (f (i.1 + 1, i.2 - 1))
  ++ (m.find? (i.1 + 1, i.2 + 1)).elim [] (f (i.1 + 1, i.2 + 1))

def solve (inp : String) (p : Part) : String :=
  let ls :=
    inp.lines.enum.bind $ λ (r, l) =>
      (λ (c, x) => ((r, c), x)) <$> l.toList.enum
  let m : Std.HashMap (Int × Int) Char := Std.HashMap.ofList ls
  if p == .Part1
  then
    let nums := Functor.map (String.toNat! ∘ String.mk ∘ Functor.map Prod.snd)
              $ List.filter (λ ns => ns.any λ (i, _) => adjSym m i)
              $ List.groupBy (λ ((_, c1), _) ((_, c2), _) => c2 == c1 + 1)
              $ ls.filter $ λ (_, x) => x.isDigit
    toString $ Nat.sum nums
  else
    let gears : Std.HashMap (Int × Int) (List Nat)
             := Std.HashMap.filter (λ _ x => x.length == 2)
              $ List.foldr (λ x acc => Std.HashMap.mergeWith (λ _ a b => a ++ b) x acc) Std.HashMap.empty
              $ List.map (λ xs => Std.HashMap.ofList xs)
              $ List.map (λ ns => ns.bind λ (i, _) =>
                (adjStar m i).map λ i =>
                  (i, [String.toNat! $ String.mk (Prod.snd <$> ns)]))
              $ List.groupBy (λ ((_, c1), _) ((_, c2), _) => c2 == c1 + 1)
              $ ls.filter $ λ (_, x) => x.isDigit
    let rats := Nat.sum
              $ (List.prod ∘ Prod.snd) <$> gears.toList
    toString rats
