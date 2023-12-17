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
