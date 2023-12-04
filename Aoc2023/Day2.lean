import Aoc2023.Common

import Std.Data.HashMap

namespace D2

def parseLn (i : String) : List (String × Nat) :=
  match i.split (· == ':') with
    | [_, ps] =>
        (ps.split (· == ';')).bind $ λ p =>
        (p.split (· == ',')).bind $ λ b =>
        match b.trim.words with
          | [n, l] => [(l, n.toNat!)]
          | _ => []
    | _ => panic! "no"

def aggr (i : List (String × Nat)) : Std.HashMap String Nat :=
  Std.HashMap.ofListWith i max

def check : Nat × Std.HashMap String Nat → Bool
  | (_, m) =>
  (m.find? "red").elim True (λ x => x <= 12)
  && (m.find? "green").elim True (λ x => x <= 13)
  && (m.find? "blue").elim True (λ x => x <= 14)

def power (m : Std.HashMap String Nat) : Nat :=
  m.fold (λ a _ b => a * b) 1

def solve (inp : String) (p : Part) : String :=
  let lns := (aggr ∘ parseLn) <$> inp.lines
  if p == .Part1
  then toString ∘ Nat.sum $ (Nat.succ ∘ Prod.fst) <$> lns.enum.filter check
  else toString ∘ Nat.sum $ power <$> lns
