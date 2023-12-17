import Aoc2023.Common

namespace D16

inductive Dir where
  | Up
  | Down
  | Left
  | Right
  deriving BEq

inductive R where
  | Fwd
  | Bck

inductive S where
  | H
  | V

inductive Cell where
  | Refl (r : R)
  | Split (s : S)
  | Empty

instance : Inhabited Cell where
  default := .Empty

def parseCell : Char → Cell
  | '.' => .Empty
  | '-' => .Split .H
  | '|' => .Split .V
  | '/' => .Refl .Fwd
  | '\\' => .Refl .Bck
  | _ => panic! "fo"

partial
def step (r : Nat) (c : Nat) (d : Dir) (a : Array (Array (Cell × List Dir)))
    : Array (Array (Cell × List Dir)) :=
  match a.get? r >>= (Array.get? · c) with
    | none => a
    | some (cell, ds) =>
      let (rr, cc) := match d with
        | .Up => (r - 1, c)
        | .Down => (r + 1, c)
        | .Left => (r, c - 1)
        | .Right => (r, c + 1)
      let aa := a.modify r (·.set! c (cell, d :: ds))
      if ds.contains d then a else
      match cell with
        | .Empty => step rr cc d aa
        | .Split s => match s, d with
          | .V, .Up | .V, .Down | .H, .Left | .H, .Right =>
            step rr cc d aa
          | .V, .Left | .V, .Right =>
            let aaa := step (r - 1) c .Up aa
            step (r + 1) c .Down aaa
          | .H, .Up | .H, .Down =>
            let aaa := step r (c - 1) .Left aa
            step r (c + 1) .Right aaa
        | .Refl .Fwd => match d with
          | .Up => step r (c + 1) .Right aa
          | .Down =>
              if c == 0 then aa else
              step r (c - 1) .Left aa
          | .Left => step (r + 1) c .Down aa
          | .Right =>
              if r == 0 then aa else
              step (r - 1) c .Up aa
        | .Refl .Bck => match d with
          | .Up =>
              if c == 0 then aa else
              step r (c - 1) .Left aa
          | .Down => step r (c + 1) .Right aa
          | .Left =>
              if r == 0 then aa else
              step (r - 1) c .Up aa
          | .Right => step (r + 1) c .Down aa

def starts (a : Array (Array α)) : List ((Nat × Nat) × Dir) :=
  let tr := (λ c => ((0, c), .Down)) <$> List.range (a[0]!.size)
  let lc := (λ r => ((r, 0), .Right)) <$> List.range a.size
  let br := (λ c => ((a.size - 1, c), .Up)) <$> List.range (a[0]!.size)
  let rc := (λ r => ((r, a[0]!.size - 1), .Left)) <$> List.range a.size
  tr ++ lc ++ br ++ rc

def solve (inp : String) (p : Part) : String :=
  let a := List.toArray $ (List.toArray ∘ List.map (λ c => (parseCell c, [])) ∘ String.toList) <$> inp.lines
  let ss := if p == .Part1 then [((0, 0), .Right)] else starts a
  let count i := ((i.map (λ x => x.map (if ·.2.length > 0 then 1 else 0))).map (·.toList.sum)).toList.sum
  let rs := ss.map λ ((r,c),d) => count (step r c d a)
  let r := rs.maximum?.getD 0
  toString r
