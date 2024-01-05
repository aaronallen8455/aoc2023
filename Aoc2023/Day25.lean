import Aoc2023.Common

import Std.Data.HashMap
import Std.Data.RBMap
import Lean.Data.HashSet

namespace D25

def Graph := Std.HashMap String (Std.RBSet String compare)

def mkGraph (ls : List (String × List String)) : Graph :=
  let ls' := ls.map λ x => (Prod.map id (Std.RBSet.ofList · compare) x)
                        :: (x.2.map λ y => (y, Std.RBSet.single x.1))
  Std.HashMap.ofListWith ls'.join Std.RBSet.union

structure Edge where
  ptA : String
  ptB : String
  deriving BEq, Ord, Repr

def Edge.canon (e : Edge) : Edge :=
  if e.ptA < e.ptB then e else { ptA := e.ptB, ptB := e.ptA }

def Edge.compare (a : Edge) (b : Edge) : Ordering :=
  Ord.compare a.canon b.canon

def pathEdges (i : List String) : List Edge :=
  i.zipWith Edge.mk (i.drop 1)

def shortestPath (g : Graph) (banned : Std.RBSet Edge Edge.compare) (a : String) (b : String)
    : Id (Option (List Edge)) := do
  let mut visitedA : Std.RBSet String compare := .empty
  let mut fringeA : List (List String) := [[a]]
  let mut visitedB : Std.RBSet String compare := .empty
  let mut fringeB : List (List String) := [[b]]
  while (not fringeA.isEmpty) && (not fringeB.isEmpty) do
    let mut newFringeA : List (List String) := []
    let mut newFringeB : List (List String) := []
    for x in fringeA do
      let s := x.head!
      let ns := ((g.findD s .empty).sdiff visitedA)
      for n in ns do
        if banned.contains (Edge.mk s n) then continue
        if visitedB.contains n then
          let rest := (fringeB.find? λ zz => zz.head! == n).getD []
          return some $ pathEdges $ x.reverse ++ rest
        visitedA := visitedA.insert n
        newFringeA := (n :: x) :: newFringeA
    fringeA := newFringeA

    for x in fringeB do
      let s := x.head!
      let ns := ((g.findD s .empty).sdiff visitedB)
      for n in ns do
        if banned.contains (Edge.mk s n) then continue
        if visitedA.contains n then
          let rest := (fringeA.find? λ zz => zz.head! == n).getD []
          return some $ pathEdges $ rest.reverse ++ x
        visitedB := visitedB.insert n
        newFringeB := (n :: x) :: newFringeB
    fringeB := newFringeB
  none

-- Returns true if two nodes have at least 4 non-overlapping paths between them and therefore must
-- belong to the same group.
def stronglyConnected (g : Graph) (a : String) (b : String) : Bool := flip Option.getD false $ do
  let p1 ← (Std.RBSet.ofList · _) <$> shortestPath g .empty a b
  let p2 ← (Std.RBSet.ofList · _) <$> shortestPath g p1 a b
  let banned1 := p1.union p2
  let p3 ← (Std.RBSet.ofList · _) <$> shortestPath g banned1 a b
  let _p4 ← shortestPath g (banned1.union p3) a b
  true

def allConnected (g : Graph) : Std.RBSet Edge Edge.compare :=
  let rec go
    | [] => Std.RBSet.empty
    | n :: rest => dbgTrace (toString n) λ _ =>
      let r := (rest.filter (stronglyConnected g n)).map (Edge.mk n)
      (Std.RBSet.ofList r Edge.compare).union $ go rest
  go (g.toList.map Prod.fst)

def parseEdge (i : String) : String × List String :=
  match i.words with
    | n :: edges => (n.dropRight 1, edges)
    | _ => panic! "nooo"

def solve (inp : String) (p : Part) : String :=
  let g := mkGraph $ parseEdge <$> inp.lines
  let allCon := (g.toList.map Prod.fst).filter (stronglyConnected g "qsf")
  toString $ allCon.length * (g.size - allCon.length)
