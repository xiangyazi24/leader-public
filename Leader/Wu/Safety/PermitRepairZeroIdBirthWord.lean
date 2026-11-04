import Leader.Wu.Safety.PermitRepairQuietLap
import Leader.Wu.Birth.CheckPermitRepairLeaf

namespace R1ZeroIdBirthWord

open PPLLExpiringComparisonRepair R1CandidateKernel

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

private abbrev Cell := ExpiringAgentState 3 3 48
private abbrev Cfg := FC 9 3 3 48

/-- Witness has just one true bit, at 8; clearing every bit changes only it.
All other fields, including the initial zero stall credits, are retained. -/
def w0Seed (i : Fin 9) : ExpiringAgentState 3 3 48 :=
  let u := R1CandidateKernel.witness i
  let b := { u.core.core with bit := false }
  ⟨⟨b, u.core.path0Crossed⟩, u.stall⟩

def zeroIdWord : List (Fin 9) :=
  [3,3,3,3,3,3,3,3,3,3,3,3, 4,3, 5,6,7, 4,5,6, 3,4,5, 6,7]

private def step : Cfg → Fin 9 → Cfg :=
  BirthCheckPermitRepairLeaf.step1
    (by decide : 0 < 3) (by decide : 2 ≤ 3) witnessRing

/-- A literal record template; this definition contains no transition call. -/
private def literalCell (i : Fin 9)
    (state : MainState := .none)
    (path : BoundedPathInfo 3 := .bot)
    (stall : Fin 49 := 48) (count : Fin 4 := 0)
    (h : Bool := false) (wait : Bool := true) (reset : Bool := false)
    (p4 : Option (CleaningLabel 3 × Fin 2) := none)
    (p5 : Option (CleaningLabel 3 × Fin 2) := none)
    (crossed : Bool := false) (ws : WriteState := .none) : Cell :=
  let b := { (w0Seed i).core.core with
    state := state, path := path, count := count, h_field := h,
    wait := wait, reset := reset, path4 := p4, path5 := p5,
    write_state := ws }
  ⟨⟨b, crossed⟩, stall⟩

private def cp (label : Fin 3) (bit : Fin 2 := 1) :
    Option (CleaningLabel 3 × Fin 2) := some (.normal label, bit)

/-- Literal pair replacement, not a protocol step. -/
private def put (C : Cfg) (e : Fin 9) (l r : Cell) : Cfg :=
  fun i => if i = e then l
    else if i = witnessRing.rightNeighbor e then r else C i

private def clock (count : Fin 4) (lo hi : Bool) (stall : Fin 49) : Cfg :=
  put w0Seed 3
    (literalCell 3 (stall := stall) (h := lo))
    (literalCell 4 (stall := stall) (count := count) (h := hi)
      (ws := .depart))

private def c01 : Cfg := clock 0 true  false 48
private def c02 : Cfg := clock 0 false true  47
private def c03 : Cfg := clock 0 true  true  46
private def c04 : Cfg := clock 1 false false 45
private def c05 : Cfg := clock 1 true  false 44
private def c06 : Cfg := clock 1 false true  43
private def c07 : Cfg := clock 1 true  true  42
private def c08 : Cfg := clock 2 false false 41
private def c09 : Cfg := clock 2 true  false 40
private def c10 : Cfg := clock 2 false true  39
private def c11 : Cfg := clock 2 true  true  38

/-- Final COMPARE clears the pathless initiator's produce state.
Path-only expiry spends a credit at both endpoints. -/
private def c12 : Cfg :=
  put w0Seed 3
    (literalCell 3 (stall := 37) (wait := false))
    (literalCell 4 .produce (stall := 37) (count := 3) (ws := .depart))

private def c13 : Cfg :=
  put c12 4
    (literalCell 4 .done (.some 1 0) (count := 3) (p4 := cp 1))
    (literalCell 5 .depart (.some 2 0) (ws := .depart))

private def c14 : Cfg :=
  put c13 3
    (literalCell 3 .depart (.some 0 0) (h := true))
    (literalCell 4 .depart (.some 1 0) (stall := 47) (count := 3)
      (p5 := cp 1) (ws := .depart))

-- Transport payload 2 to cell 8: [5,6,7].
private def c15 : Cfg :=
  put c14 5
    (literalCell 5 (p4 := cp 2))
    (literalCell 6 .none (.some 2 0) (reset := true) (ws := .depart))

private def c16 : Cfg :=
  put c15 6
    (literalCell 6 (h := true) (p4 := cp 2))
    (literalCell 7 .none (.some 2 0) (ws := .depart))

private def c17 : Cfg :=
  put c16 7
    (literalCell 7 (p4 := cp 2))
    (literalCell 8 .CHECK_ready (.some 2 0) (ws := .depart))

-- Transport payload 1 to cell 7: [4,5,6].
private def c18 : Cfg :=
  put c17 4
    (literalCell 4 (count := 3) (p4 := cp 1))
    (literalCell 5 .none (.some 1 0) (p5 := cp 1 0) (ws := .depart))

private def c19 : Cfg :=
  put c18 5
    (literalCell 5 (p4 := cp 1))
    (literalCell 6 .none (.some 1 0) (reset := true)
      (p5 := cp 1) (ws := .depart))

private def c20 : Cfg :=
  put c19 6
    (literalCell 6 (h := true) (p4 := cp 1))
    (literalCell 7 .CHECK_ready (.some 1 0) (p5 := cp 1) (ws := .depart))

-- Transport payload 0 to cell 6: [3,4,5].
private def c21 : Cfg :=
  put c20 3
    (literalCell 3 (wait := false))
    (literalCell 4 .none (.some 0 0) (count := 3) (h := true)
      (p5 := cp 0) (ws := .depart))

private def c22 : Cfg :=
  put c21 4
    (literalCell 4 (count := 3) (h := true))
    (literalCell 5 .none (.some 0 0) (p5 := cp 0 0) (ws := .depart))

private def c23 : Cfg :=
  put c22 5
    (literalCell 5)
    (literalCell 6 .CHECK_ready (.some 0 0) (reset := true)
      (p5 := cp 0) (crossed := true) (ws := .depart))

/-- Edge 6 checks 0 and 1. R1 consumes the left permit before COMPARE. -/
private def c24 : Cfg :=
  put c23 6
    (literalCell 6 .equal (.some 0 0) (h := true))
    (literalCell 7 .equal (.some 1 0) (stall := 47)
      (p5 := cp 1) (ws := .depart))

/-- Only the final service remains a transition expression. -/
def after25 : FC 9 3 3 48 := step c24 7

private theorem after25_eq : after25 = step c24 7 := rfl

/-- Initial leader fields only; no CandR1 hypothesis. -/
theorem w0Seed_leaders :
    (w0Seed (0 : Fin 9)).core.core.leader = true ∧
    ∀ i : Fin 9, i ≠ 0 → (w0Seed i).core.core.leader = false := by
  decide +kernel

theorem w0Seed_bits (i : Fin 9) : (w0Seed i).core.core.bit = false := rfl

private theorem id1 : lapID witnessRing w0Seed (0 : Fin 9) 1 = 0 := by
  decide +kernel

private theorem id2 : lapID witnessRing w0Seed (0 : Fin 9) 2 = 0 := by
  decide +kernel

theorem zeroIdWord_length : zeroIdWord.length = 25 := by decide

-- Closed pointwise equalities: exactly ONE actual service per check.
-- No input below contains an earlier invocation of step or row.
private theorem s01 : ∀ i : Fin 9, step w0Seed 3 i = c01 i := by
  decide +kernel
private theorem s02 : ∀ i : Fin 9, step c01 3 i = c02 i := by
  decide +kernel
private theorem s03 : ∀ i : Fin 9, step c02 3 i = c03 i := by
  decide +kernel
private theorem s04 : ∀ i : Fin 9, step c03 3 i = c04 i := by
  decide +kernel
private theorem s05 : ∀ i : Fin 9, step c04 3 i = c05 i := by
  decide +kernel
private theorem s06 : ∀ i : Fin 9, step c05 3 i = c06 i := by
  decide +kernel
private theorem s07 : ∀ i : Fin 9, step c06 3 i = c07 i := by
  decide +kernel
private theorem s08 : ∀ i : Fin 9, step c07 3 i = c08 i := by
  decide +kernel
private theorem s09 : ∀ i : Fin 9, step c08 3 i = c09 i := by
  decide +kernel
private theorem s10 : ∀ i : Fin 9, step c09 3 i = c10 i := by
  decide +kernel
private theorem s11 : ∀ i : Fin 9, step c10 3 i = c11 i := by
  decide +kernel
private theorem s12 : ∀ i : Fin 9, step c11 3 i = c12 i := by
  decide +kernel
private theorem s13 : ∀ i : Fin 9, step c12 4 i = c13 i := by
  decide +kernel
private theorem s14 : ∀ i : Fin 9, step c13 3 i = c14 i := by
  decide +kernel
private theorem s15 : ∀ i : Fin 9, step c14 5 i = c15 i := by
  decide +kernel
private theorem s16 : ∀ i : Fin 9, step c15 6 i = c16 i := by
  decide +kernel
private theorem s17 : ∀ i : Fin 9, step c16 7 i = c17 i := by
  decide +kernel
private theorem s18 : ∀ i : Fin 9, step c17 4 i = c18 i := by
  decide +kernel
private theorem s19 : ∀ i : Fin 9, step c18 5 i = c19 i := by
  decide +kernel
private theorem s20 : ∀ i : Fin 9, step c19 6 i = c20 i := by
  decide +kernel
private theorem s21 : ∀ i : Fin 9, step c20 3 i = c21 i := by
  decide +kernel
private theorem s22 : ∀ i : Fin 9, step c21 4 i = c22 i := by
  decide +kernel
private theorem s23 : ∀ i : Fin 9, step c22 5 i = c23 i := by
  decide +kernel
private theorem s24 : ∀ i : Fin 9, step c23 6 i = c24 i := by
  decide +kernel

-- Separate closed single-field checks for the last actual row.
private theorem after25_root : (after25 (0 : Fin 9)).core.core.leader = true := by
  decide +kernel
private theorem after25_new : (after25 (8 : Fin 9)).core.core.leader = true := by
  decide +kernel

-- Stop elaborator reduction before using the computational facts abstractly.
attribute [local irreducible]
  w0Seed step literalCell cp put clock
  c01 c02 c03 c04 c05 c06 c07 c08 c09 c10 c11 c12
  c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 after25
  BirthCheckPermitRepairLeaf.step1 BirthCheckPermitRepair.row

/-- W0 violates PositivePeak, regardless of the remaining candidate clauses. -/
theorem w0Seed_not_mem :
    ¬ CandR1 (by decide : 0 < 3) (by decide : 2 ≤ 3) witnessRing w0Seed := by
  intro hC
  obtain ⟨root, hRoot, _, hPeak, _⟩ := hC
  have hroot : root = (0 : Fin 9) :=
    (hRoot.2.1 (0 : Fin 9) w0Seed_leaders.1).symm
  subst root
  have hids : lapID witnessRing w0Seed (0 : Fin 9) 1 =
      lapID witnessRing w0Seed (0 : Fin 9) 2 := id1.trans id2.symm
  obtain ⟨k, hlo, hhi, _⟩ :=
    hPeak (1 : Fin 9) (2 : Fin 9) (by decide) (by decide) (by decide) hids
  have hlo' : 1 < k.val := hlo
  have hhi' : k.val < 2 := hhi
  omega

private theorem word_eq : zeroIdWord.foldl step w0Seed = after25 := by
  simp only [zeroIdWord, List.foldl_cons, List.foldl_nil]
  rw [funext s01, funext s02, funext s03, funext s04]
  rw [funext s05, funext s06, funext s07, funext s08]
  rw [funext s09, funext s10, funext s11, funext s12]
  rw [funext s13, funext s14, funext s15, funext s16]
  rw [funext s17, funext s18, funext s19, funext s20]
  rw [funext s21, funext s22, funext s23, funext s24]
  exact after25_eq.symm

/-- The endpoint is reached by the requested word under the actual step1. -/
theorem zeroId_endpoint :
    zeroIdWord.foldl
      (BirthCheckPermitRepairLeaf.step1
        (by decide : 0 < 3) (by decide : 2 ≤ 3) witnessRing)
      w0Seed = after25 := by
  simpa only [step] using word_eq

/-- Named second-leader location, independent of the existential packaging. -/
theorem zeroId_leader8 :
    ((zeroIdWord.foldl
      (BirthCheckPermitRepairLeaf.step1
        (by decide : 0 < 3) (by decide : 2 ≤ 3) witnessRing)
      w0Seed) (8 : Fin 9)).core.core.leader = true := by
  rw [zeroId_endpoint]
  exact after25_new

/-- The old leader at 0 survives and the word also produces a leader at 8. -/
theorem zeroId_two_leaders :
    ((zeroIdWord.foldl
      (BirthCheckPermitRepairLeaf.step1
        (by decide : 0 < 3) (by decide : 2 ≤ 3) witnessRing)
      w0Seed) (0 : Fin 9)).core.core.leader = true ∧
    ∃ j : Fin 9, j ≠ 0 ∧
      ((zeroIdWord.foldl
        (BirthCheckPermitRepairLeaf.step1
          (by decide : 0 < 3) (by decide : 2 ≤ 3) witnessRing)
        w0Seed) j).core.core.leader = true := by
  simp only [zeroId_endpoint]
  exact ⟨after25_root, 8, by decide, after25_new⟩

end R1ZeroIdBirthWord
