import Aoc2023.Common

import Std.Data.HashMap

namespace D8

def parseLn (i : String) : String × (String × String) :=
  match i.words with
  | [n, _, l, r] => (n, ((l.drop 1).dropRight 1, r.dropRight 1))
  | _ => panic! "no"

def nav (start : String) (m : Std.HashMap String (String × String)) (d : List Char) : Id Nat := do
  let mut n := 0
  let mut dir := d
  let mut loc := start
  while true do
    if loc.takeRight 1 == "Z" then break
    let (l, r) := m.findD loc ("", "")
    match dir with
    | [] => dir := d
    | c :: dr => do
      dir := dr
      n := n + 1
      match c with
      | 'L' => loc := l
      | 'R' => loc := r
      | _ => pure ()
  pure n

--def trace (start : String) (m : Std.HashMap String (String × String)) (d : List Char) : Id (List String) := do
  --let mut n := 0
  --let mut dir := d
  --let mut loc := start
  --let mut res := []
  --let mut zs := 0
  --while true do
    --if zs > 3 then break
    --let (l, r) := m.findD loc ("", "")
    --match dir with
    --| [] => dir := d
    --| c :: dr => do
      --if loc.takeRight 1 == "Z" then zs := zs + 1
      --res := loc :: res
      --dir := dr
      --n := n + 1
      --match c with
      --| 'L' => loc := l
      --| 'R' => loc := r
      --| _ => pure ()
  --pure res

-- [JTA, QXA, NBA, BLA, TSA, AAA]

partial
def lcm (a : Nat) (b : Nat) : Nat :=
  let rec go x y :=
    match compare x y with
    | .eq => x
    | .lt => go (x + a) y
    | .gt => go x (y + b)
  go a b

#eval [(1:Nat),2,3].minimum?

def solve (inp : String) (p : Part) : String :=
  let lns := inp.lines
  let dir := lns.head!.toList
  let map := Std.HashMap.ofList $ parseLn <$> lns.drop 2
  if p == .Part1 then
    toString $ nav "AAA" map dir
  else
    let starts := List.filter (λ x => x.takeRight 1 == "A") $ List.map Prod.fst $ map.toList
    let rs : List Nat := (λ s => nav s map dir) <$> starts
    let r := rs.foldr lcm (rs.minimum?.getD 1)
    toString r
