import Aoc2023.Common

import Std.Data.HashMap

namespace D20

inductive Pulse where
  | High
  | Low
  deriving BEq

instance : ToString Pulse where
  toString
    | .High => "h"
    | .Low => "l"

inductive Ty where
  | Flip (isOn : Bool)
  | Conj (ins : Std.HashMap String Pulse)
  | Broad

instance : ToString Ty where
  toString
    | .Flip _ => "flip"
    | .Conj c => toString c.toList
    | .Broad => "b"

structure Mod where
  name : String
  ty : Ty
  out : List String

def parseMod (i : String) : Mod :=
  match i.words with
    | nt :: _ :: outs =>
      let o := (String.dropRightWhile · (·==',')) <$> outs
      let t := match nt.take 1 with
        | "%" => .Flip false
        | "&" => .Conj Std.HashMap.empty
        | "b" => .Broad
        | _ => .Flip (panic "f")
      let n := nt.dropWhile (not ∘ Char.isAlpha)
      { ty := t
      , out := o
      , name := n
      }
    | _ => {ty := .Flip false, out := panic! "no", name := panic! ""}

abbrev Mods := Std.HashMap String Mod

#check StateM

def genPulses (p : Pulse) (iN : String) (mn : String) : StateM Mods (List (String × Pulse)) := do
  let mm ← (Std.HashMap.find? · mn) <$> get
  match mm with
    | none => pure []
    | some m =>
      match p, m.ty with
        | .High, .Flip _ => pure []
        | .Low, .Flip isOn =>
          let po := if isOn then .Low else .High
          modify (Std.HashMap.insert · mn {m with ty := .Flip (not isOn)})
          pure ((·, po) <$> m.out)
        | _, .Conj c =>
          let cc := c.insert iN p
          let po := if cc.toList.all (·.snd == .High) then .Low else .High
          modify (Std.HashMap.insert · mn {m with ty := .Conj cc})
          pure ((·, po) <$> m.out)
        | _, .Broad =>
          pure ((·, p) <$> m.out)

partial
def doPulses (t : Nat) (hC : Nat) (lC : Nat) (rx : Nat) : List (String × String × Pulse) → StateM Mods (Nat × Nat × Nat)
  | (s, r, p) :: rest => do
    let np ← genPulses p s r
    let pp := np.partition (·.snd == .High)
    let nHC := pp.1.length
    let nLC := pp.2.length
    let nq := rest ++ ((r, ·) <$> np)
    -- lt 3739
    -- vz 4093
    -- bq 3889
    -- qh 3821
    -- get the LCM of these

    if r == "ft" && s == "lt" && p == .High then
      dbgTrace (toString t) $ λ _ => pure ()
    let nrx := if r == "rx" && p == .Low then rx + 1 else rx
    doPulses t (hC + nHC) (lC + nLC) nrx nq
  | [] => pure (hC, lC, rx)
#eval 3820 * 3
def initMods : StateM Mods Unit := do
  let mods ← get
  for (_, m) in mods.toList do
    for o in m.out do
      let mods ← get
      match mods.find? o with
        | none => pure ()
        | some mr =>
            match mr.ty with
              | .Conj c =>
                let cc := c.insert m.name .Low
                modify (·.insert o {mr with ty := .Conj cc})
              | _ => pure ()

def solve (inp : String) (p : Part) : String :=
  let mo := Std.HashMap.ofList $
        ((λ x => (x.name, x)) ∘ parseMod) <$> inp.lines
  let pgm : StateM Mods (Nat × Nat) := do
        initMods
        let mut t := 0
        let mut hC := 0
        let mut lC := 0
        while t < 1000 do
          let (h, l, _) ← doPulses t hC (lC + 1) 0 [("button", "broadcaster", .Low)]
          hC := h
          lC := l
          t := t + 1
        pure (hC, lC)
  let pgm2 : StateM Mods Nat := do
        initMods
        let mut hC := 0
        let mut lC := 0
        let mut t := 0
        repeat
          let (h, l, rx) ← doPulses t hC (lC + 1) 0 [("button", "broadcaster", .Low)]
          hC := h
          lC := l
          t := t + 1
          if rx > 0 then return t
        pure 0

  if p == .Part1 then
    let (hC, lC) := StateT.run' pgm mo
    toString $ hC * lC
  else
    let t := StateT.run' pgm2 mo
    toString t
