inductive Part
  | Part1
  | Part2
  deriving Repr, Ord, BEq

def String.lines (s : String) : List String := s.split (· == '\n')

def String.words (s : String) : List String := s.split Char.isWhitespace

def List.prod [Mul α] [OfNat α 1] (xs : List α) : α := xs.foldr (· * ·) 1
