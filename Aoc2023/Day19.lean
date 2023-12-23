import Aoc2023.Common

import Std.Data.HashMap

namespace D19

structure part where
  x : Nat
  m : Nat
  a : Nat
  s : Nat

inductive Field where
  | x
  | m
  | a
  | s

inductive Pred where
  | LT (g : Field) (n : Nat)
  | GT (g : Field) (n : Nat)
  | End

inductive Result where
  | R
  | A
  deriving BEq

inductive Action where
  | Res (r : Result)
  | To (t : String)

structure Rule where
  pred : Pred
  action : Action

structure Box where
  name : String
  rules : List Rule

abbrev Boxes := Std.HashMap String Box

def parsePred (i : String) : Pred :=
  match i.split (· == '<') with
    | [l, r] =>
      let g := match l with
        | "x" => .x
        | "m" => .m
        | "a" => .a
        | "s" => .s
        | _ => .x
      .LT g r.toNat!
    | _ => match i.split (· == '>') with
        | [l, r] =>
          let g := match l with
            | "x" => .x
            | "m" => .m
            | "a" => .a
            | "s" => .s
            | _ => .x
          .GT g r.toNat!
        | _ => .End

def parseAction (i : String) : Action :=
  match i with
    | "A" => .Res .A
    | "R" => .Res .R
    | _ => .To i

def parseRule (i : String) : Rule :=
  match i.split (· == ':') with
    | [p, a] => {pred := parsePred p, action := parseAction a}
    | [a] => {pred := .End, action := parseAction a}
    | _ => {pred := .End, action := .To $ panic! "F"}

def parseBox (i : String) : Box :=
  match i.split (·=='{') with
    | [n, r] =>
      let rs := parseRule <$> (r.dropRight 1).split (·==',')
      {name := n, rules := rs}
    | _ => {name := panic! "fff", rules := []}

def checkPred (p : part) (pred : Pred) : Bool :=
  let g (f : Field) : part → Nat := match f with
    | .x => part.x
    | .m => part.m
    | .a => part.a
    | .s => part.s
  match pred with
    | .LT f v => g f p < v
    | .GT f v => g f p > v
    | .End => true

instance : Inhabited Result where
  default := .R

mutual
  partial
  def doBox (bs : Boxes) (n : String) (p : part) : Result :=
    let b := (bs.find? n).getD {name := panic! "foo", rules := []}
    let mr : Option Result := (b.rules.foldl (λ acc x => acc <|> doRule bs p x) none)
    mr.get!

  partial
  def doAction (bs : Boxes) (p : part) (a : Action) : Result :=
    match a with
      | .Res r => r
      | .To x => doBox bs x p

  partial
  def doRule (bs : Boxes) (p : part) (r : Rule) : Option Result :=
    if checkPred p r.pred then
      doAction bs p r.action
    else none
end

instance : Min (Nat × Nat) where
  min a b := match compare a.1 b.1 with
    | .lt => a
    | .gt => b
    | .eq => if a.2 ≤ b.2 then a else b

instance : Max (Nat × Nat) where
  max a b := match compare a.1 b.1 with
    | .lt => b
    | .gt => a
    | .eq => if a.2 ≥ b.2 then a else b

namespace P2
  structure Rng where
    x : Nat × Nat
    m : Nat × Nat
    a : Nat × Nat
    s : Nat × Nat

  instance : ToString Rng where
    toString x := toString (x.x, x.m, x.a, x.s)

  def checkPred (p : Rng) (pred : Pred) : Option (Rng × Option Rng) :=
    match pred with
      | .GT .x v =>
        if p.x.2 ≤ v then none else
          some ( { p with x := (max p.x.1 (v + 1), p.x.2)}
               , if v < p.x.1 then none else
                 some { p with x := (p.x.1, v)}
               )
      | .GT .m v =>
        if p.m.2 ≤ v then none else
          some ( { p with m := (max p.m.1 $ v + 1, p.m.2)}
               , if v < p.m.1 then none else
                 some { p with m := (p.m.1, v)}
               )
      | .GT .a v =>
        if p.a.2 ≤ v then none else
          some ( { p with a := (max p.a.1 $ v + 1, p.a.2)}
               , if v < p.a.1 then none else
                 some { p with a := (p.a.1, v)}
               )
      | .GT .s v =>
        if p.s.2 ≤ v then none else
          some ( { p with s := (max p.s.1 $ v + 1, p.s.2)}
               , if v < p.s.1 then none else
                 some { p with s := (p.s.1, v)}
               )

      | .LT .x v =>
        if p.x.1 ≥ v then none else
          some ( { p with x := (p.x.1, min p.x.2 $ v-1)}
               , if v > p.x.2 then none else
                 some { p with x := (v, p.x.2)}
               )
      | .LT .m v =>
        if p.m.1 ≥ v then none else
          some ( { p with m := (p.m.1, min p.m.2 $ v-1)}
               , if v > p.m.2 then none else
                 some { p with m := (v, p.m.2)}
               )
      | .LT .a v =>
        if p.a.1 ≥ v then none else
          some ( { p with a := (p.a.1, min p.a.2 $ v-1)}
               , if v > p.a.2 then none else
                 some { p with a := (v, p.a.2)}
               )
      | .LT .s v =>
        if p.s.1 ≥ v then none else
          some ( { p with s := (p.s.1, min p.s.2 $ v-1)}
               , if v > p.s.2 then none else
                 some { p with s := (v, p.s.2)}
               )

      | .End => some (p, none)

  mutual
    partial
    def doBox (bs : Boxes) (n : String) (p : Rng) : List Rng :=
      let b := (bs.find? n).getD {name := panic! "foo", rules := []}
      Prod.snd $
        b.rules.foldl (λ (pp, acc) x =>
          match pp with
            | none => (none, acc)
            | some p =>
                let (rs, n) := doRule bs p x
                (n, rs ++ acc)

        ) (some p, [])

    partial
    def doAction (bs : Boxes) (p : Rng) (a : Action) : List Rng :=
      match a with
        | .Res r =>
            if r == .A then [p]
            else []
        | .To x => doBox bs x p

    partial
    def doRule (bs : Boxes) (p : Rng) (r : Rule) : List Rng × Option Rng :=
      match checkPred p r.pred with
        | none => ([], none)
        | some (pp, n) => (doAction bs pp r.action, n)
  end

  -- sort first
  def inter (a : Nat × Nat) (b : Nat × Nat) : Option (Nat × Nat) :=
    if a.2 < b.1 then none
    else
    if b.1 ≥ a.1 && b.2 ≤ a.2 then b
    else if b.1 ≤ a.2 then (b.1, a.2)
      else panic! "nope"

  def trunc (r : Nat × Nat) (c : Nat × Nat) : List (Nat × Nat) :=
    if r.1 ≥ c.1 && r.2 ≤ c.2 then [] else
    if r.1 ≥ c.1 then [(c.2 + 1, r.2)] else
    if r.2 ≤ c.2 then [(r.1, c.1 - 1)] else
    [(r.1, c.1 - 1), (c.2 + 1, r.2)]

  def cut (a : Rng) (b : Rng) : List Rng :=
    match inter (min a.x b.x) (max a.x b.x),
          inter (min a.m b.m) (max a.m b.m),
          inter (min a.a b.a) (max a.a b.a),
          inter (min a.s b.s) (max a.s b.s) with
      | some x, some m, some a, some s =>
        (λ nx => {b with x := nx}) <$> trunc b.x x ++
        (λ nm => {b with m := nm}) <$> trunc b.m m ++
        (λ na => {b with a := na}) <$> trunc b.a a ++
        (λ ns => {b with s := ns}) <$> trunc b.s s
      | _,_,_,_ => [b]

  partial
  def cuts : List Rng → List Rng
    | a :: rest => a :: cuts (rest.bind (cut a))
    | [] => []

  --def union (a : Nat × Nat) (b : Nat × Nat) : Option (Nat × Nat) :=
    --if a.2 < b.1 || b.2 < a.1 then none
    --else (min a.1 b.1, max a.2 b.2)
  ---- If no ranges overlap then return both unchanged
  ---- only if all four overlap do we need to change
  ---- can combine in this case
  --def react (a : Rng) (b : Rng) : Option Rng :=
    --match union a.x b.x, union a.m b.m, union a.a b.a, union a.s b.s with
      --| some x, some m, some a, some s => some {x := x, m := m, a := a, s := s}
      --| _,_,_,_ => none

  --partial
  --def combine (l : List Rng) : List Rng :=
    --let rec go
      --| a :: b :: rest =>
        --match react a b with
          --| none => a :: go (b :: rest)
          --| some x => go (x :: rest)
      --| [x] => [x]
      --| [] => []
    --go $ (l.toArray.qsort (λ a b => a.x.1 < b.x.1)).toList

  def total (p : Rng) : Nat :=
    (p.x.2 - p.x.1 + 1) * (p.m.2 - p.m.1 + 1) * (p.a.2 - p.a.1 + 1) * (p.s.2 - p.s.1 + 1)

end P2

def parsePart (i : String) : part :=
  match i.split (· == ',') with
    | [a, b, c, d] =>
      { x := (a.drop 3).toNat!
      , m := (b.drop 2).toNat!
      , a := (c.drop 2).toNat!
      , s := ((d.drop 2).dropRight 1).toNat!
      }
    | _ => {x := panic! "no", m := 1, a := 1, s := 1}

    -- 206016000000000
    -- 167409079868000

def solve (inp : String) (p : Part) : String :=
  let lns := inp.lines
  let (top, bottom) := lns.span (· ≠ "")
  let boxes := Std.HashMap.ofList $ (λ x => (x.name, x)) <$> (parseBox <$> top)
  if p == .Part1 then
    let parts := parsePart <$> bottom.drop 1
    let toN p := p.x + p.m + p.a + p.s
    let rs := (λ p => (doBox boxes "in" p, toN p)) <$> parts
    let acc := rs.map (λ (r, s) => if r == .A then s else 0)
    toString acc.sum
  else
    let r := P2.cuts $
        P2.doBox boxes "in" {x := (1, 4000), m := (1, 4000), a := (1, 4000), s := (1, 4000)}
    toString (r.map P2.total).sum
