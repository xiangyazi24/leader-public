import Leader.L3.Primitive.TapSelection

/-!
# Executable cross-check of the selected primitive taps

`main` prints, for each width `t` given on the command line (default `18..64`), the mask
`tapSelectedMask t` of the compiled tap table (`Params.tapTable`, first odd mask passing
`passesTests`) and its one-positions `j` (`b_j = 1`, coefficient of `X^j`).  Used to compare the
Lean table with `research/method-review/l3-prime/compiler/primitive-taps.mjs` ('mask' order).
No proof content.
-/

namespace L3.TapEval

def onePositions (t m : Nat) : List Nat :=
  (List.range t).filter (fun j => Nat.testBit m j)

def report (t : Nat) : String :=
  let m := L3.tapSelectedMask t
  s!"{t}\t{m}\t{",".intercalate ((onePositions t m).map toString)}"

end L3.TapEval

def main (args : List String) : IO Unit := do
  let ts : List Nat :=
    if args.isEmpty then (List.range 47).map (· + 18) else args.filterMap String.toNat?
  for t in ts do
    IO.println (L3.TapEval.report t)
    (← IO.getStdout).flush
