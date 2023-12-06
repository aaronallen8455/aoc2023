import Aoc2023.Common

namespace D6

def calcWins (i : Nat × Nat) : UInt64 :=
  let t := Nat.toFloat i.1
  let w := Nat.toFloat i.2
  let ubr := (-t - Float.sqrt (t^2 - 4 * w)) / (-2)
  let ub := Float.floor ubr
  let u := if ubr == ub then Float.toUInt64 ub - 1 else Float.toUInt64 ub
  let lbr := (-t + Float.sqrt (t^2 - 4 * w)) / (-2)
  let lb := Float.ceil lbr
  let l := if lbr == lb then Float.toUInt64 lb + 1 else Float.toUInt64 lb
  u - l + 1

def solve (inp : String) (p : Part) : String :=
  match String.words <$> inp.lines with
    | [_ :: times, _ :: dists] =>
      if p == .Part1 then
        let cs := List.zip (times.map String.toNat!) (dists.map String.toNat!)
        toString $ (List.map calcWins cs).prod
      else
        let t := String.toNat! $ String.join times
        let w := String.toNat! $ String.join dists
        toString $ calcWins (t, w)
    | _ => panic! "death"
