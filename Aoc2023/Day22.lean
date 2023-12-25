import Aoc2023.Common

import Std.Data.HashMap
import Lean.Data.HashSet

namespace D22

structure Pt where
  x : Nat
  y : Nat
  z : Nat

instance : ToString Pt where
  toString p := toString (p.x, p.y, p.z)

structure Block where
  e1 : Pt
  e2 : Pt
  supports : Lean.HashSet Nat
  supportedBy : Lean.HashSet Nat

instance : ToString Block where
  toString b := toString (b.supports.toList, b.supportedBy.toList, b.e1, b.e2)

def parsePt (i : String) : Pt :=
  match i.split (·==',') with
    | [x,y,z] => {x := x.toNat!, y := y.toNat!, z := z.toNat!}
    | _ => {x := panic! "no", y := 0, z := 0}

def parse (i : String) : Option Block :=
  match i.split (·=='~') with
    | [a, b] => some {e1 := parsePt a, e2 := parsePt b, supports := .empty, supportedBy := .empty}
    | _ => none

def rngOv (a : Nat × Nat) (b : Nat × Nat) : Bool :=
  let (a1, a2) := (min a.1 a.2, max a.1 a.2)
  let (b1, b2) := (min b.1 b.2, max b.1 b.2)
  (a1 ≤ b1 && b1 ≤ a2)
  || (b1 ≤ a1 && a1 ≤ b2)
  || (a1 ≤ b2 && b2 ≤ a2)
  || (b1 ≤ a2 && a2 ≤ b2)

#eval rngOv (1,1) (0,2)

def overlap (a : Block) (b : Block) : Bool :=
  rngOv (a.e1.x, a.e2.x) (b.e1.x, b.e2.x)
  &&
  rngOv (a.e1.y, a.e2.y) (b.e1.y, b.e2.y)

#eval overlap {e1:={x:=0,y:=1,z:=2}, e2:={x:=2,y:=1,z:=2}, supports:= Lean.HashSet.empty, supportedBy:= Lean.HashSet.empty}
              {e1:={x:=1,y:=1,z:=2}, e2:={x:=1,y:=1,z:=3}, supports:= .empty, supportedBy:= .empty}

abbrev Blocks := Std.HashMap Nat Block

def maxZ (bs : List (Nat × Block)) : List (Nat × Block) :=
  let mz (b : Block) := max b.e1.z b.e2.z
  bs.foldl (λ acc x => match acc.head? with
    | none => [x]
    | some b => match compare (mz b.2) (mz x.2) with
        | .eq => x :: acc
        | .lt => [x]
        | .gt => acc
  ) []

def stack (bot : Block) (top : Block) : Block :=
  let mz := max bot.e1.z bot.e2.z
  if top.e1.z ≤ top.e2.z then
    {top with e1 := {top.e1 with z := mz + 1}
            , e2 := {top.e2 with z := top.e2.z - top.e1.z + mz + 1}
    }
  else
    {top with e2 := {top.e2 with z := mz + 1}
            , e1 := {top.e1 with z := top.e1.z - top.e2.z + mz + 1}
    }

def settle (bsl : List (Nat × Block)) : Blocks :=
  let f (bs : Blocks) ib :=
    let ob := maxZ $ (bs.filter (λ _ x => overlap x ib.2)).toList
    let b :=
      match ob.head? with
        | none => stack {e1:={x:=0,y:=0,z:=0},e2:={x:=0,y:=0,z:=0},supports:=.empty,supportedBy:=.empty}
                    ib.2
        | some xz => stack xz.2 $
          { ib.2 with supportedBy := Lean.HashSet.empty.insertMany $ ob.map Prod.fst}
    (ob.foldl (λ acc x => acc.insert x.1 {x.2 with supports := x.2.supports.insert ib.1})
      bs).insert ib.1 b
  bsl.foldl f .empty

def cands (bs : Blocks) : Blocks :=
  bs.filter (λ l b =>
    b.supports.toList.all (λ x =>
      match bs.find? x with
        | none => false
        | some bx => not (bx.supportedBy.erase l).isEmpty
    )
  )

def unSupported (bs : Blocks) (sup : Lean.HashSet Nat) (n : Nat) : Bool :=
  if sup.contains n then true else
  match bs.find? n with
  | none => panic! "screw you"
  | some b =>
      not b.supportedBy.isEmpty &&
        b.supportedBy.toList.all sup.contains

partial
def depends (bs : Blocks) (sup : Lean.HashSet Nat) (ns : List Nat) : Lean.HashSet Nat :=
  if ns.isEmpty then sup else
  let getem n :=
    match bs.find? n with
      | none => panic! "sanic"
      | some b =>
          b.supports.toList.filter (unSupported bs sup)
  let fringe := ns.bind getem
  depends bs (sup.insertMany fringe) fringe

def chain (bs : Blocks) : Nat :=
  bs.fold (λ acc l _ => (depends bs (Lean.HashSet.empty.insert l) [l]).size - 1 + acc) 0

def solve (inp : String) (p : Part) : String :=
  let lns := List.filterMap parse inp.lines
  let sorted := (lns.toArray.qsort (λ a b => min a.e1.z a.e2.z < min b.e1.z b.e2.z)).toList.enum
  let settled := settle sorted
  if p == .Part1 then
    let r := cands settled
    toString r.size
  else
    toString $ chain settled
