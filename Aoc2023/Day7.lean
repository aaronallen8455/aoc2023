import Aoc2023.Common

import Std.Data.HashMap

namespace D7

def parseHand (i : String) : List Char × Nat :=
  match i.words with
    | [c, b] => (c.toList, b.toNat!)
    | _ => panic! "no"

def cardRank (p : Part) : Char → Nat
  | 'A' => 14
  | 'K' => 13
  | 'Q' => 12
  | 'J' => if p == .Part1 then 11 else 0
  | 'T' => 10
  | '9' => 9
  | '8' => 8
  | '7' => 7
  | '6' => 6
  | '5' => 5
  | '4' => 4
  | '3' => 3
  | '2' => 2
  | _ => panic! "c"

def counts (p : Part) (cs : List Char) : Std.HashMap Nat Nat :=
  Std.HashMap.ofListWith ((λ c => (cardRank p c, 1)) <$> cs) (· + ·)

def handRank (p : Part) (cs : List Char) : List Nat :=
  let m := counts p cs
  let r := cardRank p <$> cs
  let numJ := m.findD 0 0
  let m := m.erase 0
  let els := match (Array.map Prod.snd m.toArray).qsortOrd.toList.reverse with
    | f :: rest => (f + numJ) :: rest
    | [] => [5]
  match els with
    | [5] => 10 :: r
    | [4, 1] => 9 :: r
    | [3, 2] => 8 :: r
    | [3, 1, 1] => 7 :: r
    | [2, 2, 1] => 6 :: r
    | [2, 1, 1, 1] => 5 :: r
    | _ => 4 :: r

def solve (inp : String) (p : Part) : String :=
  let hands := parseHand <$> inp.lines
  let sorted :=
      hands.toArray.qsort (λ a b => handRank p a.1 < handRank p b.1)
  let e := sorted.toList.enumFrom 1
  let scores := (λ (r, (_, b)) => r * b) <$> e
  toString $ Nat.sum $ scores
