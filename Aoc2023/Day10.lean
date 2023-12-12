import Aoc2023.Common

import Std.Data.HashMap

namespace D10

inductive Dir
  | N
  | S
  | E
  | W
  deriving BEq

def nxt (p : Nat × Nat) : Char → Dir → Dir × (Nat × Nat)
  | '|', .S => (.S, (p.1 + 1, p.2))
  | '|', .N => (.N, (p.1 - 1, p.2))
  | '-', .W => (.W, (p.1, p.2 - 1))
  | '-', .E => (.E, (p.1, p.2 + 1))
  | '7', .E => (.S, (p.1 + 1, p.2))
  | '7', .N => (.W, (p.1, p.2 - 1))
  | 'L', .S => (.E, (p.1, p.2 + 1))
  | 'L', .W => (.N, (p.1 - 1, p.2))
  | 'J', .E => (.N, (p.1 - 1, p.2))
  | 'J', .S => (.W, (p.1, p.2 - 1))
  | 'F', .N => (.E, (p.1, p.2 + 1))
  | 'F', .W => (.S, (p.1 + 1, p.2))
  | _, _ => (.S, panic! "no!")

inductive Cell
  | In
  | Out
  | Pipe (c : Char) (d : Dir)
  deriving BEq

def findPipe (p : Nat × Nat) (g : Array (Array Char)) : Id (Array (Array (Option Cell))) := do
  let mut cells := g.map (λ h => h.map (λ _ => none))
  let mut pp := (p.1 + 1, p.2)
  cells := cells.modify pp.1 (λ a => a.set! pp.2 (Cell.Pipe (g[pp.1]![pp.2]!) .S))
  let mut dir := Dir.S
  while g[pp.1]![pp.2]! ≠ 'S' do
    let r := nxt pp (g[pp.1]![pp.2]!) dir
    dir := r.1
    pp := r.2
    cells := cells.modify pp.1 (λ a => a.set! pp.2 (Cell.Pipe (g[pp.1]![pp.2]!) dir))
  cells

partial
def isIn (p : Nat × Nat) (a : Array (Array (Option Cell))) : Bool :=
  if a[p.1]![p.2]!.isSome
  then false else
  let rec go n pp :=
    match a.get? pp.1 >>= (λ a => a.get? pp.2) with
      | some (some (.Pipe 'L' _)) => go (n + 2) (pp.1+1, pp.2+1)
      | some (some (.Pipe '7' _)) => go (n + 2) (pp.1+1, pp.2+1)
      | some (some (.Pipe _ _)) => go (n + 1) (pp.1+1, pp.2+1)
      | some _ => go n (pp.1+1, pp.2+1)
      | none => Nat.mod n 2 == 1
  go 0 p

def numIn (a : Array (Array (Option Cell))) : Nat :=
  let rR := a.size
  let cR := a[0]!.size
  List.foldl
    (λ acc r =>
      List.foldl
        (λ acc c => if isIn (r, c) a then acc + 1 else acc)
        acc
        (List.range cR)
    )
    0
    (List.range rR)

def dist (p : Nat × Nat) (g : Array (Array Char)) : Id Nat := do
  let mut d := 0
  let mut pp := (p.1 + 1, p.2)
  let mut dir := Dir.S
  while g[pp.1]![pp.2]! ≠ 'S' do
    let r := nxt pp (g[pp.1]![pp.2]!) dir
    dir := r.1
    pp := r.2
    d := d + 1
  d + 1

def solve (inp : String) (p : Part) : String :=
  let grid := List.toArray $ (List.toArray ∘ String.toList) <$> inp.lines
  let sPos := grid.map (λ a => a.findIdx? (· == 'S'))
  let rx := (sPos.findIdx? Option.isSome).get!
  let cx := (sPos.find? Option.isSome).get!.get!
  if p == .Part1 then
    let d : Nat := dist (rx, cx) grid
    toString (d / 2)
  else
    let pipes := findPipe (rx, cx) grid
    toString $ numIn pipes
