import Aoc2023.Common

import Lean.Data.HashSet
import Std.Data.HashMap

namespace D23

--inductive Dir where
  --| U
  --| D
  --| L
  --| R

abbrev Map := Array (Array Char)

def ltP (a : Int × Int) (b : Int × Int) : Bool :=
  match compare a.1 b.1 with
    | .lt => true
    | .gt => false
    | .eq => a.2 < b.2

def explore (p : Part) (m : Map) : Id Nat := do
  let mut steps := 0
  let mut fringe : List ((Int × Int) × Lean.HashSet (Int × Int)) :=
    [((0, 1), Lean.HashSet.empty.insert (0, 1))]
  let mut res := 0
  let mut shared := Lean.HashSet.empty
  repeat
    if steps.mod 200 == 0 then
      let s := fringe.foldl (λ acc x =>
          if acc.isEmpty then x.2 else acc.intersect x.2
        ) Lean.HashSet.empty
      fringe :=
        fringe.map λ (p, v) => (p, Lean.HashSet.empty.insertMany $ v.toList.filter (not ∘ s.contains))
      --fringe := (fringe.toArray.qsort (λ a b => LT.lt a.1 b.1)).toList
        --(fringe.map (λ (p, v) => (p, v.toArray.qsort ltP))).toArray.sortAndDeduplicate
      shared := dbgTrace (toString $ fringe.map Prod.fst) λ _ => shared.insertMany s
    let mut newFringe := []
    repeat
      match fringe with
      | [] =>
        if newFringe.isEmpty then return res
        else
          fringe := newFringe --dbgTrace (toString res) λ _ => newFringe
          steps := steps + 1
          break
      | ((r, c), v) :: rest =>
        fringe := rest
        if r == m.size - 1 && c == (m.getD 1 Array.empty).size - 2
        then
          res := steps
          continue
        let cands := match p with
          | .Part1 =>
            match m.idx r >>= (·.idx c) with
            | some '.' => [(r+1,c),(r-1,c),(r,c+1),(r,c-1)]
            | some '>' => [(r, c+1)]
            | some '<' => [(r, c-1)]
            | some '^' => [(r-1, c)]
            | some 'v' => [(r+1, c)]
            | _ => []
          | .Part2 =>
            match m.idx r >>= (·.idx c) with
            | some _ => [(r+1,c),(r-1,c),(r,c+1),(r,c-1)]
            | _ => []
        let new := cands.filterMap λ (rr, cc) =>
          match m.idx rr >>= (·.idx cc) with
            | none => none
            | some '#' => none
            | _ => if not $ v.contains (rr, cc) || shared.contains (rr, cc) then
                    some ((rr, cc), v.insert (rr, cc)) else none
        newFringe := new ++ newFringe
  res

abbrev Graph := Std.HashMap (Int × Int) (Std.HashMap (Int × Int) Nat)

def neighbors (m : Map) (p : Int × Int) : List (Int × Int) :=
  [(p.1+1,p.2),(p.1-1,p.2),(p.1,p.2-1),(p.1,p.2+1)].filter λ (r, c) =>
    match m.idx r >>= (·.idx c) with
      | none => false
      | some '#' => false
      | some _ => true

def isNode (m : Map) (p : Int × Int) : Bool :=
  (neighbors m p).length > 2
  || p.1 == 0 || p.1 == m.size - 1

partial
def walk (m : Map) (p : Int × Int) (s : Nat) (prev : Int × Int) : Option (Nat × (Int × Int)) :=
  if isNode m p then
    (s, p)
  else
    match (neighbors m p).filter (· ≠ prev) with
    | [] => none
    | nxt :: _ => walk m nxt (s + 1) p

partial
def mkGraph (m : Map) (n : Int × Int) : StateM Graph Unit := do
  let ns := neighbors m n
  for p in ns do
    match walk m p 1 n with
      | none => pure ()
      | some (s, nxt) =>
        let g ← get
        let cur := g.find! n
        match cur.find? nxt with
          | none => modify (·.insert n (cur.insert nxt s))
          | some ss => modify (·.insert n (cur.insert nxt $ max s ss))
        match g.find? nxt with
        | some x =>
          let nx := match x.find? n with
              | none => x.insert n s
              | some ss => x.insert n (max s ss)
          modify (·.insert nxt nx)
        | none =>
          modify (·.insert nxt $ Std.HashMap.empty.insert n s)
          mkGraph m nxt

def exploreGraph (m : Map) (g : Graph) : Id Nat := do
  let mut fringe : List ((Int × Int) × Lean.HashSet (Int × Int) × Nat) :=
    [((0, 1), Lean.HashSet.empty.insert (0, 1), 0)]
  let mut res := 0
  repeat
    match fringe with
    | [] => break
    | (nc, v, s) :: rest =>
      fringe := rest
      if nc.1 == m.size - 1
      then
        res := max res s
        continue
      let cands := g.find! nc
      let new := cands.toList.filterMap λ (newN, d) =>
        if v.contains newN then none else
          some (newN, v.insert newN, s + d)
      fringe := new ++ fringe
  res

def solve (inp : String) (p : Part) : String :=
  let map := List.toArray $ (List.toArray ∘ String.toList) <$> inp.lines
  if p == .Part1 then
    toString $ explore p map
  else
    let g := StateT.run (mkGraph map (0,1)) $ Std.HashMap.empty.insert (0,1) Std.HashMap.empty
    toString $ exploreGraph map g.2
