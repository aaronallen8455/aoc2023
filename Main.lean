import Aoc2023.Day1
import Aoc2023.Day2
import Aoc2023.Day3
import Aoc2023.Day4
import Aoc2023.Day5
import Aoc2023.Day6
import Aoc2023.Day7
import Aoc2023.Day8
import Std.Data.String

def main (args : List String) : IO Unit :=
  match args with
    | [day, part] => do
      let fileName := s!"input/{day}"
      let content ← IO.FS.readFile fileName
      let stdout ← IO.getStdout
      let part := match part with
            | "1" => Part.Part1
            | _ => Part.Part2
      let f := match day with
            | "1" => D1.solve
            | "2" => D2.solve
            | "3" => D3.solve
            | "4" => D4.solve
            | "5" => D5.solve
            | "6" => D6.solve
            | "7" => D7.solve
            | "8" => D8.solve
            | _ => λ _ _ => ""
      IO.FS.Stream.putStr stdout $ f content part

    | _ => pure ()
