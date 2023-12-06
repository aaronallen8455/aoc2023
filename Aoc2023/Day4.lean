import Aoc2023.Common

import Std.Data.HashMap

namespace D4

def parseCard (i : String) : (List Nat × List Nat) :=
  match i.split (· == ':') with
    | [_, c] =>
    match c.split (· == '|') with
      | [a, b] =>
        let numList x := String.toNat! <$> x.trim.words
        (numList a, numList b)
      | _ => panic! "nooo"
    | _ => panic! "shite"

def numMatch (c : (List Nat × List Nat)) : Nat :=
  let win := Std.HashMap.ofList $ (λ x => (x, ())) <$> c.1
  List.length $ c.2.filter win.contains

def scoreCard (c : (List Nat × List Nat)) : Nat :=
  let num := numMatch c
  if num == 0
  then 0
  else 2 ^ (num - 1)

def cardCount (cs : List (List Nat × List Nat)) : Nat :=
  let ms := cs.map numMatch
  let f x acc := (Nat.sum (acc.take x) + 1) :: acc
  Nat.sum $ ms.foldr f []

def solve (inp : String) (p : Part) : String :=
  let cards := parseCard <$> inp.lines
  if p == .Part1
  then
    let scores := scoreCard <$> cards
    toString $ Nat.sum scores
  else
    toString $ cardCount cards
