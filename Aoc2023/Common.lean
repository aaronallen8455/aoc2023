import Lean.Data.HashSet

inductive Part
  | Part1
  | Part2
  deriving Repr, Ord, BEq

def String.lines (s : String) : List String := s.split (· == '\n')

def String.words (s : String) : List String :=
  (s.split Char.isWhitespace).filter (· ≠ "")

def List.prod [Mul α] [OfNat α 1] (xs : List α) : α := xs.foldr (· * ·) 1

def List.sum [Add α] [OfNat α 0] (xs : List α) : α := xs.foldr (· + ·) 0

--def List.transpose (xs : List (List α)) : List (List α) :=
  --let n := (xs.head?.getD []).length
  --List.foldr (λ x acc => List.zipWith (·::·) x acc)
    --(List.replicate n []) xs

def List.mapAccumL (f : σ → α → β × σ) (s : σ) : List α → List β × σ
  | [] => ([], s)
  | x :: xs =>
    let (b, ss) := f s x
    let (xss, sss) := List.mapAccumL f ss xs
    (b :: xss, sss)

partial
def til (p : α → α → Bool) (f : α → α) (x : α) : α :=
  let fx := f x
  if p x fx then fx
  else til p f (f x)

def Array.idx (a : Array α) (i : Int) : Option α :=
  if i < 0 then none else a.get? i.toNat

#eval #[1,2].idx (-1)

partial
def lcm (a : Nat) (b : Nat) : Nat :=
  let rec go x y :=
    match compare x y with
    | .eq => x
    | .lt => go (x + a) y
    | .gt => go x (y + b)
  go a b

partial
def lcmInt (a : Int) (b : Int) : Int :=
  if a == 0 || b == 0 then 0 else
  Int.natAbs $ a.div (Nat.gcd a.natAbs b.natAbs) * b
  --let isNeg := a * b < 0
  --let rec go x y :=
    --match compare x y with
    --| .eq => x
    --| .lt => go (x + if isNeg then Int.ofNat a.natAbs else a) y
    --| .gt => go x (y + if isNeg then Int.ofNat b.natAbs else b)
  --if isNeg
  --then go (Int.ofNat a.natAbs) (Int.ofNat b.natAbs)
  --else go a b

def Lean.HashSet.intersect [BEq α] [Hashable α] (a : Lean.HashSet α) (b : Lean.HashSet α) : Lean.HashSet α :=
  Lean.HashSet.empty.insertMany $ a.toList.filter b.contains

def Lean.HashSet.ofList [BEq α] [Hashable α] (xs : List α) : Lean.HashSet α :=
  Lean.HashSet.empty.insertMany xs

instance [Ord α] [Ord β] : Ord (α × β) where
  compare a b := match compare a.1 b.1 with
    | .lt => .lt
    | .gt => .gt
    | .eq => compare a.2 b.2

def floorDiv (a : Int) (b : Int) : Int :=
  if a.mod b == 0 then a / b else
  if a < 0 || b < 0 then a / b - 1 else
  a / b

--instance [Ord α] [Ord β] : LT (α × β) where
  --lt a b := match compare a b with
    --| .lt => True
    --| _ => False
