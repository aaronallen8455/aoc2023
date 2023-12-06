import Aoc2023.Common

namespace D5

structure Range where
  rs : Int
  re : Int
  deriving BEq, Ord, Repr

instance : ToString Range where
  toString := reprStr

def validRange (r : Range) : Bool :=
  r.re ≥ r.rs

def intersect (r1 : Range) (r2 : Range) : List Range × List Range :=
  match compare r1.rs r2.rs, compare r1.rs r2.re, compare r1.re r2.rs, compare r1.re r2.re with
    | .lt, _, .gt, .lt | .lt, _, .eq, _ | .lt, _, _, .eq =>
      ([{rs := r2.rs, re := r1.re}]
      , [{rs := r1.rs, re := r2.rs - 1} ]
      )
    | .gt, .lt, .gt, .lt | .eq, _, _, .eq | .eq, _, _, .lt | .gt, _, _, .eq =>
      ([r1]
      ,[]
      )
    | .gt, .lt, _, .gt | .eq, _, _, .gt | _, .eq, _, .gt =>
      ([{rs := r1.rs, re := r2.re}]
      ,[{rs := r2.re + 1, re := r1.re}]
      )
    | .lt, _, _, .gt =>
      ([r2]
      ,[{rs := r1.rs, re := r2.rs - 1}, {rs := r2.re + 1, re := r1.re}]
      )
    | _, _, _, _ => ([],[r1])

def applyMap (r : Range) (s : Range) (o : Int) : List Range × List Range :=
  let (g, b) := intersect r s
  ((λ x => {rs := x.rs + o, re := x.re + o}) <$> g, b)

def applyMaps (r : Range) (ms : List (Range × Int)) : List Range :=
  let f t1 t2 : List Range × List Range :=
    let blah := (applyMap · t1.1 t1.2) <$> t2.2
    ((Prod.fst <$> blah).join ++ t2.1, (Prod.snd <$> blah).join.filter validRange)
  let foo := List.foldr f ([], [r]) ms
  (foo.1 ++ foo.2)

def toFun (i : String) : Int → Option Int :=
  match i.words.map String.toInt! with
  | [a, b, c] => λ x =>
    if x ≥ b && x < b + c
    then x + (a - b)
    else none
  | _ => panic! "no"

def toMap (i : String) : Range × Int :=
  match i.words.map String.toInt! with
  | [a, b, c] => ({rs := b, re := b + c - 1}, a - b)
  | _ => ({rs := 0, re := 0}, panic! "no")

def seedRngs : List Int → List Range
  | s :: z :: rest => {rs := s, re := s + z - 1} :: seedRngs rest
  | [] => []
  | _ => []

def solve (inp : String) (p : Part) : String :=
  let lns := List.filter (· ≠ [""])
          $ inp.lines.groupBy (λ a b => a ≠ "" && b ≠ "")
  let seeds := String.toInt! <$> (lns.head!.head!.drop 7).words
  let cats := List.drop 1 <$> lns.drop 1
  if p == .Part1 then
    let funz := (List.foldr (λ a b x => a x <|> b x) (λ x => some x) ∘ List.map toFun) <$> cats
    let funn := List.foldr (· >=> ·) some funz
    toString $ List.minimum? $ List.map Option.get! $ funn <$> seeds
  else
    let cats2 := List.map toMap <$> cats
    match cats2 with
      | [a, b, c, d, e, f, g] =>
          let funz r := (applyMaps r a).bind $ λ r =>
                        (applyMaps r b).bind $ λ r =>
                        (applyMaps r c).bind $ λ r =>
                        (applyMaps r d).bind $ λ r =>
                        (applyMaps r e).bind $ λ r =>
                        (applyMaps r f).bind $ λ r =>
                        (applyMaps r g)
          let what := (List.minimum? ∘ List.map Range.rs ∘ funz) <$> seedRngs seeds
          toString (List.minimum? $ Option.get! <$> what)

      | _ => panic! ""
