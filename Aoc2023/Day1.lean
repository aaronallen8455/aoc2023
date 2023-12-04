import Aoc2023.Common

import Std.Data.String

namespace D1

def doLine (s : String) : Nat :=
  let first := s.find Char.isDigit
  let last := Option.get! (s.revFind Char.isDigit)
  String.toNat! $ String.mk [s.get first, s.get last]

def doLine2 (s : String) : Nat :=
  let parse : List Char → Option (Nat × List Char)
    | 'o'::'n'::'e'::rest | '1'::rest => (1, rest)
    | 't'::'w'::'o'::rest | '2'::rest => (2, rest)
    | 't'::'h'::'r'::'e'::'e'::rest | '3'::rest => (3, rest)
    | 'f'::'o'::'u'::'r'::rest | '4'::rest => (4, rest)
    | 'f'::'i'::'v'::'e'::rest | '5'::rest => (5, rest)
    | 's'::'i'::'x'::rest | '6'::rest => (6, rest)
    | 's'::'e'::'v'::'e'::'n'::rest | '7'::rest => (7, rest)
    | 'e'::'i'::'g'::'h'::'t'::rest | '8'::rest => (8, rest)
    | 'n'::'i'::'n'::'e'::rest | '9'::rest => (9, rest)
    | _ => none
  let rec e (i : List Char) (l : Nat) : Nat :=
    match i with
      | [] => l
      | _ :: rest => if let some (d, _) := parse i then
                e rest d
              else e rest l
  let rec h (i : List Char) : Nat :=
    if let some (d, r) := parse i then
      d * 10 + e r d
    else match i with
      | [] => 0
      | _ :: rest => h rest
  h s.toList

def solve (inp : String) (p : Part) : String :=
  let f := if p == .Part1 then doLine else doLine2
  let lns := Functor.map f inp.lines
  toString $ Nat.sum lns
