import Aoc2023.Common

import Lean.Data.HashSet

namespace D21

abbrev Map := Array (Array Char)

def step (m : Map) (ls : Lean.HashSet (Int × Int)) : Id (Lean.HashSet (Int × Int)) := do
  let mut r := Lean.HashSet.empty
  for (row, c) in ls do
    for (nr, nc) in [(row-1,c),(row+1,c),(row,c-1),(row,c+1)] do
      match m.idx nr >>= (·.idx nc) with
        | some '.' | some 'S' => r := r.insert (nr, nc)
        | _ => pure ()
  r

def rep (m : Map) (h : Lean.HashSet (Int × Int)) : Nat → Nat
  | Nat.zero => h.size
  | Nat.succ x =>
      rep m (step m h) x

-- does change based on the edge point selected?
-- Yes, corners are always 259
-- mid point is always 194
-- 7558 is the saturation point
def toSaturate (m : Map) (p : Int × Int) : Id Nat := do
  let mut t := 1
  let mut s := Lean.HashSet.empty.insert p
  repeat
    s := step m s
    if s.size == 7558 then return t
    t := t + 1
  1

-- number of maps to traverse: 202299
#eval (26501365 - 66) / 131
-- number of steps leftover: 130
#eval (26501365 - 66 : Nat).mod 131

-- the 4 points are 5698 each
-- adjacent to

-- the 4 behind the points are 161 + 130

#eval 130 + 131 - 194

def armLen : Nat := (26501365 - 66) / 131
def prim : Nat := (armLen + 1).pow 2 * 7623
def sec : Nat := armLen.pow 2 * 7558
def diag1SE : Nat := (armLen + 1) * 968
def diag2SE : Nat := armLen * 6643
def diag1SW : Nat := (armLen + 1) * 978
def diag2SW : Nat := armLen * 6619
def diag1NW : Nat := (armLen + 1) * 964
def diag2NW : Nat := armLen * 6637
def diag1NE : Nat := (armLen + 1) * 984
def diag2NE : Nat := armLen * 6624
def caps : Nat := 5698 + 5704 + 5709 + 5703

def solve (inp : String) (p : Part) : String :=
  let a := List.toArray $ (List.toArray ∘ String.toList) <$> inp.lines
  let sR := (a.findIdx? (λ x => x.contains 'S')).get!
  let sC := ((a.get! sR).findIdx? (· == 'S')).get!
  --toString $ rep a (Lean.HashSet.empty.insert (sR, sC)) 131
  --toString $ toSaturate a (130,65)
  -- toString $ rep a (Lean.HashSet.empty.insert (65, 130)) 130
  -- toString $ rep a (Lean.HashSet.empty.insert (130, 0)) (130 - 66)
  -- toString $ rep a (Lean.HashSet.empty.insert (130, 0)) (130 + 131 - 66)
  --toString $ rep a (Lean.HashSet.empty.insert (0, 0)) (130 + 131 - 66)
  -- toString $ rep a (Lean.HashSet.empty.insert (65, 130)) (131 + 130) --194
  if p == .Part1 then
    toString $ rep a (Lean.HashSet.empty.insert (sR, sC)) 64
  else
    toString $ prim + sec + diag1SE + diag2SE + diag1SW + diag2SW + diag1NE + diag2NE + diag1NW + diag2NW + caps

-- The map has clear paths going in all 4 directions
-- Determine how many maps can be traversed and the remaining steps once entering that map
-- find the number of cells reachable upon entry of that last map
-- do this for all 4 extremities
-- now need to find the values along the diagonals
--
-- Is there a number of steps at which arrival at any grid will result in
-- full saturation of that grid?
-- beyond that, simply find the number starting from the edge of that grid
-- given that that edge is the closest to the start so that it is the fastest
-- path to that point.
