import Aoc2023.Common

import Std.Data.List.Basic

namespace D13

def matchMod1 (a : List Char) (b : List Char) : Bool :=
  let rec go h
    | (x :: xs), (y :: ys) =>
      if x == y
      then go h xs ys
      else
        if h then false
        else go true xs ys
    | [], [] => true
    | _, _ => panic! "no"
  go false a b

def findRefl2 (i : List (List Char)) : Option Nat :=
  let rec go one res n
    | _, some _, [] => if one then res else none
    | a :: acc, none, r :: rs =>
      if a == r then
        go false (some n) (n+1) (r::a::acc) (some acc) rs
        <|> go false none (n+1) (r::a::acc) none rs
      else
        if matchMod1 a r then
          go true (some n) (n + 1) (r::a::acc) (some acc) rs
          <|> go false none (n+1) (r::a::acc) none rs
        else
          go false none (n+1) (r::a::acc) none rs
    | acc, some (s :: ss), r :: rs =>
      if s == r then
        go one res (n+1) (r::acc) (some ss) rs
      else
        if one then none else
        if matchMod1 s r then
          go true res (n+1) (r::acc) (some ss) rs
        else none
    | _, none, [] => none
    | [], none, r :: rs =>
        go one none (n+1) [r] none rs
    | _, some [], _ => if one then res else none

  go false none 0 [] none i

def findRefl (i : List String) : Option Nat :=
  let rec go res n
    | _, some _, [] => res
    | a :: acc, none, r :: rs =>
      if a == r then
        go (some n) (n+1) (r::a::acc) (some acc) rs
      else
        go none (n+1) (r::a::acc) none rs
    | acc, some (s :: ss), r :: rs =>
      if s == r then
        go res (n+1) (r::acc) (some ss) rs
      else
        go none (n+1) (r::acc) none rs
    | _, none, [] => none
    | [], none, r :: rs =>
        go none (n+1) [r] none rs
    | _, some [], _ => res

  go none 0 [] none i

def solve (inp : String) (p : Part) : String :=
  let lns :=
    List.filter (λ x => x ≠ [""])
    $ List.groupBy (λ a b => not a.isEmpty && not b.isEmpty) inp.lines
  if p == .Part1 then
    let res := (λ x => ((· * 100) <$> findRefl x) <|> findRefl (List.toString <$> (String.toList <$> x).transpose))
                <$> lns
    toString (res.filterMap id).sum
  else
    let lns := List.map String.toList <$> lns
    let res := (λ x => ((· * 100) <$> findRefl2 x) <|> findRefl2 (x.transpose))
                <$> lns
    toString (res.filterMap id).sum
