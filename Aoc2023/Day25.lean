import Aoc2023.Common

import Std.Data.HashMap
import Std.Data.RBMap
import Lean.Data.HashSet

namespace D25

def Graph := Std.HashMap String (Std.RBSet String compare)

def mkGraph (ls : List (String × List String)) : Graph :=
  let ls' := ls.map λ x => (Prod.map id (Std.RBSet.ofList · compare) x)
                        :: (x.2.map λ y => (y, Std.RBSet.single x.1))
  Std.HashMap.ofListWith ls'.join Std.RBSet.union

--def findPaths (g : Graph) (a : String) (b : String) : Id (List (Lean.HashSet String)) := do
  --let mut r := []
  --let mut fringe
  --r

#check Std.RBMap.erase

def formGroup (g : Graph) : Option Nat := do
  let (m, ml) ← g.toList.head?
  let es := Std.RBMap.ofList (ml.toList.map (·, 1)) compare
  let mut fringe : List (Std.RBSet String compare × Std.RBMap String Nat compare) :=
    [(Std.RBSet.single m, es)]
  repeat do
    let mut newFringe := []
    for (visited, edges) in fringe do
      for (e, _) in edges do
        --let ws ← g.find? e
        let wires ← (Std.RBSet.sdiff · visited) <$> g.find? e
        let ws := Std.RBMap.ofList (wires.toList.map (·, 1)) compare
        let newEdges := (edges.mergeWith (λ _ => (·+·)) ws).erase e
        if newEdges.size == 0 then continue
        let newVisited := visited.insert e
        if newEdges.size == 3 && newEdges.all (λ _ x => x == 1)
          then return newVisited.size
        -- use new edges instead?
        if newFringe.any λ (v, _) => v == newVisited then continue
        newFringe := (newVisited, newEdges) :: newFringe
    fringe := newFringe
    if fringe.isEmpty then break
  some 0

def progress (f : Std.RBMap String Nat compare) : List (List String) :=
  let rec go rem
    | (name, count) :: rest =>
      if rem == 0 then [name :: rest.map Prod.fst]
      else
        if rem - count < 0 then
          (go rem rest).map (name :: ·)
        else
          (go rem rest).map (name :: ·) ++
          go (rem - count) rest
    | [] => []
  go 3 f.toList

def formGroup' (g : Graph) : Option Nat := do
  let (m, _ml) ← g.toList.head?
  let es := Std.RBMap.single m 1
  let mut fringe : List (Std.RBMap String Nat compare × Std.RBMap String Nat compare) :=
    [(es, es)]
  let mut i := 1
  repeat do
    let mut dedup : Std.RBSet String compare := .empty -- why can't this be in the loop?
    let mut newFringe := []
    -- prev could just be the last node added since that's the only difference
    for (prev, edges) in fringe do
      -- If an edge has > 3 inputs then there's no way those wires could be part of the solution
      -- so go ahead and expand them in every new fringe entry.
      -- seems to be very uncommon
      -- Might be a worthwhile optimization to consolidate the common visited nodes so that
      -- check equality of visited sets is faster. Also much less on the heap.
      -- Doesn't seem to help much
      -- Only three edges need to remain unfolded when doing a step.
      -- This will make the search a bit faster but will not cut down on the proliferation of candidates
      -- Rather than tracking all visited nodes, can track the previous nodes only. Use the new edges
      -- as the means of deduplication.
      -- Optimizations to try
      -- - Only track previous nodes, not all visited - doesn't work
      -- - turn the set of new edges into a string which can then be used to dedupe in log time
      -- - prioritize fewest number of out edges
      -- - Expand more than 1 node at a time
      for (e, _) in edges do
        let wires ← (Std.RBSet.filter · (λ s => not (prev.contains s)))
            <$> g.find? e -- slower than using a sdiff
        let ws := Std.RBMap.ofList (wires.toList.map (·, 1)) compare
        let newEdges := (edges.mergeWith (λ _ => (·+·)) ws).erase e
        if newEdges.size == 0 then continue
        if newEdges.valuesList.sum == 3
          then return i
        let key := String.join newEdges.keysList
        if dedup.contains key then continue
        dedup := dedup.insert key
        newFringe := dbgTrace (toString newFringe.length) λ _ => (prev.insert e 1, newEdges) :: newFringe
    i := dbgTraceVal $ i + 1
    fringe := newFringe
    if fringe.isEmpty then break
  some 0

-- Is there a viable approach where all possible groups are formed and then identify the two groups
-- that are connected by three wires only. That is more or less what I'm doing...
-- Maybe the path enumeration approach works... Once you have all the paths, there will be three
-- suffixes that can occur. So find common suffixes and determine if there are 3 suffixes that occur.
-- As the paths are enumerated, can keep track of common suffixes and if there are more than 3 found
-- than that choice of points can be discarded.
-- This is wrong because if all paths are enumerated then it won't have common suffixes.
-- Would need to find the shortest path between the two points
-- Could find all the shortest paths from one node to every other node but that also wouldn't
-- provide enough info.

--partial
--def step
      --(g : Graph)
      --(visited : Std.RBSet String compare)
      --(fringe : Std.RBSet String compare)
      --(cands : Std.RBSet String compare)
      --: Option Nat := dbgTrace (toString fringe.toList) λ _ =>
  --if cands.size == 3 && fringe.isEmpty && cands.size + visited.size ≠ g.size
    --then dbgTrace (toString visited.toList) λ _ => some visited.size
  --else if fringe.isEmpty then
    --cands.foldr (λ x acc =>
      --step g (visited.insert x) (fringe.insert x) (cands.erase (compare x)) <|> acc
    --) none
  --else do
  --let mut edges : Std.RBMap String Nat compare := .empty
  --for x in fringe do
    --let fuck := match g.find? x with
      --| none => panic! "fuck you"
      --| some f => f
    --let ws := (g.find! x).sdiff visited
    --let wires := Std.RBMap.ofList (ws.toList.map (·, 1)) compare
    --edges := edges.mergeWith (λ _ => (·+·))  wires
  --let edgeCands := edges.filter (λ _ => (· == 1))
  --let newCands := edgeCands.foldl (λ x _ => Std.RBSet.insert · x)
                  --(cands.filter (not ∘ edges.contains))
  --let newEdges := Std.RBSet.ofList (edges.filter (λ x _ => not $ newCands.contains x)).keysList compare
  --let newVisited := visited.mergeWith (λ a _ => a) (newEdges.sdiff newCands)
  --step g newVisited newEdges newCands

--def search (g : Graph) : Option Nat := do
  --let (m, _) ← g.toList.head?
  --step g (Std.RBSet.single m) (Std.RBSet.single m) .empty

def parseEdge (i : String) : String × List String :=
  match i.words with
    | n :: edges => (n.dropRight 1, edges)
    | _ => panic! "nooo"

def solve (inp : String) (p : Part) : String :=
  let g := mkGraph $ parseEdge <$> inp.lines
  let r := formGroup' g
  --toString $ g.toList.map λ (n,m) => (n, m.toList)
  toString $ r.get! * (g.size - r.get!)

-- super naive: try every combo of disconnecting wires until the correct one is found
-- better? pick two modules and suppose they are put of different groups. Find every possible
-- path between the two and then find the three wires where one of those three occurs in
-- every path but never more than one.
--
-- take the intersection of the wires from every path. This is garuanteed to not contain the
-- target wires.
-- Remove those from each path.
-- of the remaining wires in the first path, iterate selecting a wire and supposing it is
-- one of the targets. For another path which does not contain that wire, select one of
-- those wires and suppose it is a target. Select a third wire from another path that not
-- have either of the two targets. Check if every path has exclusively one of the targets,
-- otherwise select a different wire at which ever step.
-- At each step, take the union of all wires that appear at that group of paths and don't
-- select the next wire if it is in that group.
-- If no combo is found, select a different pair of modules
--
-- If there is one node that has three wires, then could make that a group of size one.
-- if there are more than 3, add one of the connect modules wires and check again if there
-- are exactly three, otherwise repeat the process. Can DP with the group of modules.
