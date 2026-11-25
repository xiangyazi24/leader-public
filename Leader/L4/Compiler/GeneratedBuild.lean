import Leader.L4.Compiler.StagesLoad
import Leader.L4.Compiler.StagesClock
import Leader.L4.Compiler.StagesView
import Leader.L4.Compiler.StagesEdit
import Leader.L4.Compiler.StagesOut
import Leader.L4.Compiler.Literal

/-! Static assembly of the accepted stages at their literal register
addresses. This file has no dependence on a radix, bank, or evaluator. -/
namespace L4.Compiler.Native

/-- Shared clock and view program, including the final NEED bit. -/
def buildPrefix : List Code :=
  stageConst ++ stageSide 7 0 0 2 ++ stageSide 36 1 0 2 ++ stageSide 65 2 0 2 ++
    stageSucc 94 58 1 2 4 ++
    stageRoot 98 58 45 94 0 2 4 29 16 87 74 ++
    stageProp 138 58 1 2 29 16 87 74 ++
    stageClear 161 58 45 94 1 29 16 87 74 ++
    stageInc 205 45 58 97 29 87 ++
    stagePrio 218 137 160 204 217 45 0 5 6 158 58 97 ++
    stagePhase 226 58 ++
    stageView 233 29 58 33 34 14 35 21 22 23 24 30 31 10 32 17 18 19 20 ++
    stageView 243 87 58 91 92 72 93 79 80 81 82 88 89 68 90 75 76 77 78 ++
    stageNeed 253 137 160 204 217 228 50 43 0

def editBase (δ : Bool) : Nat := if δ then 369 else 264
def outBase (δ : Bool) : Nat := editBase δ + 41

/-- Choice-specific copy of the native-edit circuit. -/
def buildEdit (δ : Bool) : List Code :=
  stageEdit (editBase δ) 246 1 3 249 63 43 0 50
    (if δ then 6 else 5) 51 5 245 235 52 62 241 238 64 53 252
    227 228 229 230 231 232

/-- A four-instruction mux chain, one for each non-clock output field.
Addresses 0–3 are prior words, 4–7 new words, 8–11 prior bits,
and 12–15 new bits. Other indices are not assembled. -/
def outChunk (δ : Bool) (j : Nat) : List Code :=
  let o := outBase δ + 4*j
  if j < 4 then
    stageWinW o 137 160 204 217 0
      ([62,63,43,64].getD j 0) ([59,60,39,61].getD j 0)
  else if j < 8 then
    stageWinW o 137 160 204 217 0
      (editBase δ+33+(j-4)) ([62,63,43,64].getD (j-4) 0)
  else if j < 12 then
    stageWinB o 137 160 204 217 5
      (50+(j-8)) (46+(j-8))
  else
    stageWinB o 137 160 204 217 5
      (editBase δ+37+(j-12)) (50+(j-12))

def buildOut (δ : Bool) : List Code := (List.range 16).flatMap (outChunk δ)

/-- The complete stage assembly, before any readout. -/
def build : List Code :=
  buildPrefix ++ buildEdit false ++ buildOut false ++ buildEdit true ++ buildOut true

theorem buildPrefix_length : buildPrefix.length=264 := by decide +kernel

theorem buildEdit_length (δ : Bool) : (buildEdit δ).length=41 := by
  cases δ <;> decide +kernel

theorem outChunk_length (δ : Bool) (j : Nat) : (outChunk δ j).length=4 := by
  unfold outChunk
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

theorem buildOut_length (δ : Bool) : (buildOut δ).length=64 := by
  cases δ <;> decide +kernel

/-- The two clock outputs are common to both choice programs. -/
theorem out_clock_ix (δ : Bool) :
    (outIx δ).1 0 = 225 ∧ (outIx δ).2 0 = 221 := by
  cases δ <;> decide +kernel

/-- Output readout indices are the last instructions of the output chunks. -/
theorem out_payload_ix (δ : Bool) (j : Fin 8) :
    (outIx δ).1 j.succ = outBase δ + 4*j.val + 3 ∧
    (outIx δ).2 j.succ = outBase δ + 4*(8+j.val) + 3 := by
  have h : ∀ (d : Bool) (k : Fin 8),
      (outIx d).1 k.succ = outBase d + 4*k.val + 3 ∧
      (outIx d).2 k.succ = outBase d + 4*(8+k.val) + 3 := by
    decide +kernel
  exact h δ j

/-- Static equality with the immutable dump, independently of execution. -/
theorem build_eq_literal : build=literal := by
  decide +kernel

end L4.Compiler.Native
