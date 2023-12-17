import Aoc2023.Common

namespace D15

def harsh (n : Nat) (c : Char) : Nat :=
  let asc := c.toNat
  let n2 := n + asc
  let n3 := n2 * 17
  n3.mod 256

def repl (l : String) (f : Nat) : List (String × Nat) → Option (List (String × Nat))
  | [] => none
  | (ll, ff) :: xs =>
    if ll == l
    then some $ (l, f) :: xs
    else List.cons (ll, ff) <$> repl l f xs

def step (a : Array (List (String × Nat))) (i : String × String)  : Array (List (String × Nat)) :=
  let bx := i.1.toList.foldl harsh 0
  a.modify bx $ λ xs =>
    match i.2.toList with
      | ['-'] => xs.filter (·.fst ≠ i.1)
      | ['=', fs] =>
        let f := fs.toString.toNat!
        (repl i.1 f xs).getD ((i.1, f) :: xs)
      | _ => panic! "no"

def foc (bi : Nat) (l : List (String × Nat)) : Nat :=
  ((l.reverse.enumFrom 1).map (λ (i, (_, f)) => i * f * (bi + 1))).sum

def parseCmd (i : String) : String × String :=
  (i.takeWhile Char.isAlpha, i.dropWhile Char.isAlpha)

def solve (inp : String) (p : Part) : String :=
  let cmds := inp.split (· == ',')
  if p == .Part1 then
    let rs := (λ s => s.toList.foldl harsh 0) <$> cmds
    toString rs.sum
  else
    let cmds := parseCmd <$> cmds
    let r := cmds.foldl step (List.replicate 256 []).toArray
    let r := r.mapIdx (λ bi => foc bi)
    toString r.toList.sum
