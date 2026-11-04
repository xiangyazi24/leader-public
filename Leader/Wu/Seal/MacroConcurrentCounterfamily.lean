import Leader.Wu.Seal.MacroConcurrentCycle

/-!
# An unbounded all-sealed counterfamily for the macro seal sweep

This file concerns only the exact four-state macro protocol from
`SealSweepConcurrentCycleSol`.  It does not assert an implementation by
`P_partial`.

For every `m >= 2`, the alternating all-sealed configuration on `2 * m`
sites is periodic.  One period first executes all even edges, changing every
disjoint `LS, FS` pair to `LU, FU`, and then executes all odd edges, changing
every disjoint `FU, LU` pair back to `FS, LS`.  The last odd edge performs the
wrap-around closure.  Thus one period uses every directed edge exactly once.
-/

namespace SealSweepConcurrentCounterfamilySol

open PPLLResearchFormulation
open SealSweepConcurrentCycleSol
open SealSweepConcurrentCycleSol.SealMacroState

abbrev EvenSealConfig (m : Nat) := Fin (2 * m) → SealMacroState

theorem evenRing (m : Nat) (hm : 0 < m) : DirectedRing (2 * m) :=
  ⟨by omega⟩

def evenEdge (m s : Nat) (hs : s < m) : Fin (2 * m) :=
  ⟨2 * s, by omega⟩

def oddEdge (m s : Nat) (hs : s < m) : Fin (2 * m) :=
  ⟨2 * s + 1, by omega⟩

/-- After the first `s` even edges, exactly the initial interval of `2*s`
sites has been unsealed. -/
def activationConfig (m s : Nat) : EvenSealConfig m := fun i =>
  if i.val < 2 * s then
    if i.val % 2 = 0 then LU else FU
  else
    if i.val % 2 = 0 then LS else FS

/-- The alternating all-sealed source configuration. -/
def alternatingSealed (m : Nat) : EvenSealConfig m :=
  activationConfig m 0

/-- The alternating all-unsealed midpoint configuration. -/
def alternatingUnsealed (m : Nat) : EvenSealConfig m :=
  activationConfig m m

theorem alternatingSealed_pointwise (m : Nat) (i : Fin (2 * m)) :
    alternatingSealed m i =
      if i.val % 2 = 0 then LS else FS := by
  simp [alternatingSealed, activationConfig]

theorem alternatingUnsealed_pointwise (m : Nat) (i : Fin (2 * m)) :
    alternatingUnsealed m i =
      if i.val % 2 = 0 then LU else FU := by
  have hi : i.val < 2 * m := i.isLt
  simp [alternatingUnsealed, activationConfig, hi]

private theorem evenEdge_rightNeighbor
    (m s : Nat) (hm : 0 < m) (hs : s < m) :
    (evenRing m hm).rightNeighbor (evenEdge m s hs) =
      ⟨2 * s + 1, by omega⟩ := by
  apply Fin.ext
  simp [DirectedRing.rightNeighbor, evenEdge,
    Nat.mod_eq_of_lt (by omega : 2 * s + 1 < 2 * m)]

private theorem activationConfig_evenEdge
    (m s : Nat) (hs : s < m) :
    activationConfig m s (evenEdge m s hs) = LS := by
  simp [activationConfig, evenEdge]

private theorem activationConfig_evenResponder
    (m s : Nat) (hs : s < m) :
    activationConfig m s ⟨2 * s + 1, by omega⟩ = FS := by
  have hnot : ¬ 2 * s + 1 < 2 * s := by omega
  simp [activationConfig, hnot]

/-- Executing the next even edge advances the activation frontier by one
disjoint pair. -/
theorem activation_step
    (m s : Nat) (hm : 0 < m) (hs : s < m) :
    sealMacroProtocol.step (evenRing m hm) (activationConfig m s)
        (evenEdge m s hs) =
      activationConfig m (s + 1) := by
  let e := evenEdge m s hs
  let j : Fin (2 * m) := ⟨2 * s + 1, by omega⟩
  have hr : (evenRing m hm).rightNeighbor e = j := by
    exact evenEdge_rightNeighbor m s hm hs
  have he : activationConfig m s e = LS := by
    exact activationConfig_evenEdge m s hs
  have hj : activationConfig m s j = FS := by
    exact activationConfig_evenResponder m s hs
  have hje : j ≠ e := by
    intro h
    have hv : j.val = e.val := congrArg Fin.val h
    change 2 * s + 1 = 2 * s at hv
    omega
  have hleft :
      sealMacroProtocol.step (evenRing m hm) (activationConfig m s) e e =
        (sealMacroTransition (activationConfig m s e)
          (activationConfig m s j)).1 := by
    simp [PopulationProtocol.step, sealMacroProtocol, hr]
  have hright :
      sealMacroProtocol.step (evenRing m hm) (activationConfig m s) e j =
        (sealMacroTransition (activationConfig m s e)
          (activationConfig m s j)).2 := by
    simp [PopulationProtocol.step, sealMacroProtocol, hr, hje]
  have heNext : activationConfig m (s + 1) e = LU := by
    simp [activationConfig, e, evenEdge]
  have hjNext : activationConfig m (s + 1) j = FU := by
    have hlt : 2 * s + 1 < 2 * (s + 1) := by omega
    simp [activationConfig, j, hlt]
  funext i
  by_cases hie : i = e
  · subst i
    rw [hleft, he, hj, heNext]
    rfl
  by_cases hij : i = j
  · subst i
    rw [hright, he, hj, hjNext]
    rfl
  · have hcut : i.val < 2 * s ↔ i.val < 2 * (s + 1) := by
      constructor
      · omega
      · intro hnew
        by_cases hold : i.val < 2 * s
        · exact hold
        · have hcases : i.val = 2 * s ∨ i.val = 2 * s + 1 := by
            omega
          rcases hcases with hval | hval
          · exact False.elim (hie (Fin.ext hval))
          · exact False.elim (hij (Fin.ext hval))
    have hoff :
        sealMacroProtocol.step (evenRing m hm) (activationConfig m s) e i =
          activationConfig m s i := by
      simp [PopulationProtocol.step, sealMacroProtocol, hr, hie, hij]
    rw [hoff]
    by_cases hold : i.val < 2 * s
    · have hnew : i.val < 2 * (s + 1) := hcut.mp hold
      simp [activationConfig, hold, hnew]
      rfl
    · have hnew : ¬ i.val < 2 * (s + 1) := by
        intro h
        exact hold (hcut.mpr h)
      simp [activationConfig, hold, hnew]
      rfl

/-! ## The closure batch -/

/-- After the first `s` odd edges, the processed odd sites are sealed
followers and their even responders are sealed leaders.  Before the final
wrap-around edge, site zero remains the sole exceptional unsealed even site. -/
def closureConfig (m s : Nat) : EvenSealConfig m := fun i =>
  if i.val % 2 = 1 then
    if i.val < 2 * s then FS else FU
  else if s = m then
    LS
  else if 0 < i.val ∧ i.val ≤ 2 * s then
    LS
  else
    LU

theorem closureConfig_zero_eq_unsealed (m : Nat) (hm : 0 < m) :
    closureConfig m 0 = alternatingUnsealed m := by
  funext i
  rw [alternatingUnsealed_pointwise]
  have hs : (0 : Nat) ≠ m := by omega
  have hmod : i.val % 2 < 2 := Nat.mod_lt _ (by omega)
  by_cases hodd : i.val % 2 = 1
  · simp [closureConfig, hodd]
  · have heven : i.val % 2 = 0 := by omega
    have hbad : ¬ (0 < i.val ∧ i.val = 0) := by omega
    simp [closureConfig, heven, hs, hbad]

theorem closureConfig_full_eq_sealed (m : Nat) :
    closureConfig m m = alternatingSealed m := by
  funext i
  rw [alternatingSealed_pointwise]
  have hi : i.val < 2 * m := i.isLt
  have hmod : i.val % 2 < 2 := Nat.mod_lt _ (by omega)
  by_cases hodd : i.val % 2 = 1
  · simp [closureConfig, hodd, hi]
  · have heven : i.val % 2 = 0 := by omega
    simp [closureConfig, heven]

private theorem oddEdge_rightNeighbor_nonlast
    (m s : Nat) (hm : 0 < m) (hs : s + 1 < m) :
    (evenRing m hm).rightNeighbor (oddEdge m s (by omega)) =
      ⟨2 * s + 2, by omega⟩ := by
  apply Fin.ext
  simp [DirectedRing.rightNeighbor, oddEdge,
    Nat.mod_eq_of_lt (by omega : 2 * s + 2 < 2 * m)]

private theorem oddEdge_rightNeighbor_last
    (m s : Nat) (hm : 0 < m) (hlast : s + 1 = m) :
    (evenRing m hm).rightNeighbor (oddEdge m s (by omega)) =
      ⟨0, by omega⟩ := by
  apply Fin.ext
  change (2 * s + 1 + 1) % (2 * m) = 0
  have heq : 2 * s + 1 + 1 = 2 * m := by omega
  rw [heq]
  simp

private theorem closureConfig_oddEdge_unprocessed
    (m s : Nat) (hs : s < m) :
    closureConfig m s (oddEdge m s hs) = FU := by
  have hmod : (2 * s + 1) % 2 = 1 := by omega
  have hnot : ¬ 2 * s + 1 < 2 * s := by omega
  simp [closureConfig, oddEdge, hmod, hnot]

private theorem closureConfig_evenResponder_unprocessed
    (m s : Nat) (hs : s + 1 < m) :
    closureConfig m s ⟨2 * s + 2, by omega⟩ = LU := by
  have hsm : s ≠ m := by omega
  have hnot : ¬ 2 * s + 2 ≤ 2 * s := by omega
  simp [closureConfig, hsm, hnot]

/-- Every non-wrapping odd edge advances the closure frontier by one pair. -/
private theorem closure_step_nonlast
    (m s : Nat) (hm : 0 < m) (hs : s + 1 < m) :
    sealMacroProtocol.step (evenRing m hm) (closureConfig m s)
        (oddEdge m s (by omega)) =
      closureConfig m (s + 1) := by
  let e := oddEdge m s (by omega)
  let j : Fin (2 * m) := ⟨2 * s + 2, by omega⟩
  have hr : (evenRing m hm).rightNeighbor e = j := by
    exact oddEdge_rightNeighbor_nonlast m s hm hs
  have he : closureConfig m s e = FU := by
    exact closureConfig_oddEdge_unprocessed m s (by omega)
  have hj : closureConfig m s j = LU := by
    exact closureConfig_evenResponder_unprocessed m s hs
  have hje : j ≠ e := by
    intro h
    have hv : j.val = e.val := congrArg Fin.val h
    change 2 * s + 2 = 2 * s + 1 at hv
    omega
  have hleft :
      sealMacroProtocol.step (evenRing m hm) (closureConfig m s) e e =
        (sealMacroTransition (closureConfig m s e)
          (closureConfig m s j)).1 := by
    simp [PopulationProtocol.step, sealMacroProtocol, hr]
  have hright :
      sealMacroProtocol.step (evenRing m hm) (closureConfig m s) e j =
        (sealMacroTransition (closureConfig m s e)
          (closureConfig m s j)).2 := by
    simp [PopulationProtocol.step, sealMacroProtocol, hr, hje]
  have heNext : closureConfig m (s + 1) e = FS := by
    have hmod : (2 * s + 1) % 2 = 1 := by omega
    have hlt : 2 * s + 1 < 2 * (s + 1) := by omega
    simp [closureConfig, e, oddEdge, hmod, hlt]
  have hjNext : closureConfig m (s + 1) j = LS := by
    have hnext : s + 1 ≠ m := by omega
    have hinside : 0 < 2 * s + 2 ∧ 2 * s + 2 ≤ 2 * (s + 1) := by
      omega
    simp [closureConfig, j, hnext, hinside]
  funext i
  by_cases hie : i = e
  · subst i
    rw [hleft, he, hj, heNext]
    rfl
  by_cases hij : i = j
  · subst i
    rw [hright, he, hj, hjNext]
    rfl
  · have hoff :
        sealMacroProtocol.step (evenRing m hm) (closureConfig m s) e i =
          closureConfig m s i := by
      simp [PopulationProtocol.step, sealMacroProtocol, hr, hie, hij]
    rw [hoff]
    have hmodlt : i.val % 2 < 2 := Nat.mod_lt _ (by omega)
    by_cases hodd : i.val % 2 = 1
    · unfold closureConfig
      rw [if_pos hodd, if_pos hodd]
      by_cases hold : i.val < 2 * s
      · have hnew : i.val < 2 * (s + 1) := by omega
        rw [if_pos hold, if_pos hnew]
      · have hnew : ¬ i.val < 2 * (s + 1) := by
          intro h
          have hval : i.val = 2 * s + 1 := by omega
          exact hie (Fin.ext hval)
        rw [if_neg hold, if_neg hnew]
    · have heven : i.val % 2 = 0 := by omega
      have hsm : s ≠ m := by omega
      have hnext : s + 1 ≠ m := by omega
      unfold closureConfig
      rw [if_neg hodd, if_neg hodd, if_neg hsm, if_neg hnext]
      by_cases hold : 0 < i.val ∧ i.val ≤ 2 * s
      · have hnew : 0 < i.val ∧ i.val ≤ 2 * (s + 1) := by omega
        rw [if_pos hold, if_pos hnew]
      · have hnew : ¬ (0 < i.val ∧ i.val ≤ 2 * (s + 1)) := by
          intro h
          have hval : i.val = 2 * s + 2 := by omega
          exact hij (Fin.ext hval)
        rw [if_neg hold, if_neg hnew]

/-- The final odd edge closes the wrap-around pair and seals site zero. -/
private theorem closure_step_last
    (m s : Nat) (hm : 0 < m) (hlast : s + 1 = m) :
    sealMacroProtocol.step (evenRing m hm) (closureConfig m s)
        (oddEdge m s (by omega)) =
      closureConfig m (s + 1) := by
  let e := oddEdge m s (by omega)
  let j : Fin (2 * m) := ⟨0, by omega⟩
  have hr : (evenRing m hm).rightNeighbor e = j := by
    exact oddEdge_rightNeighbor_last m s hm hlast
  have he : closureConfig m s e = FU := by
    exact closureConfig_oddEdge_unprocessed m s (by omega)
  have hj : closureConfig m s j = LU := by
    have hodd : (0 : Nat) % 2 ≠ 1 := by omega
    have hsm : s ≠ m := by omega
    simp [closureConfig, j, hodd, hsm]
  have hje : j ≠ e := by
    intro h
    have hv : j.val = e.val := congrArg Fin.val h
    change 0 = 2 * s + 1 at hv
    omega
  have hleft :
      sealMacroProtocol.step (evenRing m hm) (closureConfig m s) e e =
        (sealMacroTransition (closureConfig m s e)
          (closureConfig m s j)).1 := by
    simp [PopulationProtocol.step, sealMacroProtocol, hr]
  have hright :
      sealMacroProtocol.step (evenRing m hm) (closureConfig m s) e j =
        (sealMacroTransition (closureConfig m s e)
          (closureConfig m s j)).2 := by
    simp [PopulationProtocol.step, sealMacroProtocol, hr, hje]
  have heNext : closureConfig m (s + 1) e = FS := by
    have hmod : (2 * s + 1) % 2 = 1 := by omega
    have hlt : 2 * s + 1 < 2 * (s + 1) := by omega
    simp [closureConfig, e, oddEdge, hmod, hlt]
  have hjNext : closureConfig m (s + 1) j = LS := by
    have hodd : (0 : Nat) % 2 ≠ 1 := by omega
    simp [closureConfig, j, hodd, hlast]
  funext i
  by_cases hie : i = e
  · subst i
    rw [hleft, he, hj, heNext]
    rfl
  by_cases hij : i = j
  · subst i
    rw [hright, he, hj, hjNext]
    rfl
  · have hoff :
        sealMacroProtocol.step (evenRing m hm) (closureConfig m s) e i =
          closureConfig m s i := by
      simp [PopulationProtocol.step, sealMacroProtocol, hr, hie, hij]
    rw [hoff]
    have hmodlt : i.val % 2 < 2 := Nat.mod_lt _ (by omega)
    by_cases hodd : i.val % 2 = 1
    · have hold : i.val < 2 * s := by
        by_cases h : i.val < 2 * s
        · exact h
        · have hi : i.val < 2 * m := i.isLt
          have hval : i.val = 2 * s + 1 := by omega
          exact False.elim (hie (Fin.ext hval))
      have hnew : i.val < 2 * (s + 1) := by omega
      unfold closureConfig
      rw [if_pos hodd, if_pos hodd, if_pos hold, if_pos hnew]
    · have heven : i.val % 2 = 0 := by omega
      have hsm : s ≠ m := by omega
      have hpos : 0 < i.val := by
        by_cases hz : i.val = 0
        · exact False.elim (hij (Fin.ext hz))
        · omega
      have hle : i.val ≤ 2 * s := by
        have hi : i.val < 2 * m := i.isLt
        omega
      have hinside : 0 < i.val ∧ i.val ≤ 2 * s := ⟨hpos, hle⟩
      unfold closureConfig
      rw [if_neg hodd, if_neg hodd, if_neg hsm, if_pos hlast,
        if_pos hinside]

/-- Every odd edge, including the final wrapping edge, advances the closure
frontier. -/
theorem closure_step
    (m s : Nat) (hm : 0 < m) (hs : s < m) :
    sealMacroProtocol.step (evenRing m hm) (closureConfig m s)
        (oddEdge m s hs) =
      closureConfig m (s + 1) := by
  by_cases hlast : s + 1 = m
  · exact closure_step_last m s hm hlast
  · have hnonlast : s + 1 < m := by omega
    exact closure_step_nonlast m s hm hnonlast

/-! ## Exact finite period -/

def evenPrefixWord (m s : Nat) (hs : s ≤ m) : List (Fin (2 * m)) :=
  List.ofFn fun k : Fin s => evenEdge m k.val (by omega)

def oddPrefixWord (m s : Nat) (hs : s ≤ m) : List (Fin (2 * m)) :=
  List.ofFn fun k : Fin s => oddEdge m k.val (by omega)

private theorem runSchedule_append
    {n : Nat} (P : PopulationProtocol) (ring : DirectedRing n)
    (C : P.Configuration n) (xs ys : List (Fin n)) :
    runSchedule P ring C (xs ++ ys) =
      runSchedule P ring (runSchedule P ring C xs) ys := by
  induction xs generalizing C with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.cons_append, runSchedule]
      exact ih (P.step ring C e)

private theorem evenRunSchedule_append
    (m : Nat) (hm : 0 < m) (C : EvenSealConfig m)
    (xs ys : List (Fin (2 * m))) :
    runSchedule sealMacroProtocol (evenRing m hm) C (xs ++ ys) =
      runSchedule sealMacroProtocol (evenRing m hm)
        (runSchedule sealMacroProtocol (evenRing m hm) C xs) ys := by
  exact runSchedule_append sealMacroProtocol (evenRing m hm) C xs ys

private theorem evenPrefixWord_succ
    (m s : Nat) (hs : s + 1 ≤ m) :
    evenPrefixWord m (s + 1) hs =
      evenPrefixWord m s (by omega) ++ [evenEdge m s (by omega)] := by
  unfold evenPrefixWord
  rw [List.ofFn_succ_last]
  congr 1

private theorem oddPrefixWord_succ
    (m s : Nat) (hs : s + 1 ≤ m) :
    oddPrefixWord m (s + 1) hs =
      oddPrefixWord m s (by omega) ++ [oddEdge m s (by omega)] := by
  unfold oddPrefixWord
  rw [List.ofFn_succ_last]
  congr 1

/-- Running the first `s` even edges realizes the activation-prefix formula. -/
theorem run_evenPrefixWord
    (m s : Nat) (hm : 0 < m) (hs : s ≤ m) :
    runSchedule sealMacroProtocol (evenRing m hm) (alternatingSealed m)
        (evenPrefixWord m s hs) =
      activationConfig m s := by
  induction s with
  | zero =>
      rfl
  | succ s ih =>
      rw [evenPrefixWord_succ m s hs,
        evenRunSchedule_append m hm]
      rw [ih (by omega)]
      change sealMacroProtocol.step (evenRing m hm) (activationConfig m s)
          (evenEdge m s (by omega)) = activationConfig m (s + 1)
      exact activation_step m s hm (by omega)

/-- Running the first `s` odd edges realizes the closure-prefix formula. -/
theorem run_oddPrefixWord
    (m s : Nat) (hm : 0 < m) (hs : s ≤ m) :
    runSchedule sealMacroProtocol (evenRing m hm) (alternatingUnsealed m)
        (oddPrefixWord m s hs) =
      closureConfig m s := by
  induction s with
  | zero =>
      exact (closureConfig_zero_eq_unsealed m hm).symm
  | succ s ih =>
      rw [oddPrefixWord_succ m s hs,
        evenRunSchedule_append m hm]
      rw [ih (by omega)]
      change sealMacroProtocol.step (evenRing m hm) (closureConfig m s)
          (oddEdge m s (by omega)) = closureConfig m (s + 1)
      exact closure_step m s hm (by omega)

def evenWord (m : Nat) : List (Fin (2 * m)) :=
  evenPrefixWord m m (by omega)

def oddWord (m : Nat) : List (Fin (2 * m)) :=
  oddPrefixWord m m (by omega)

/-- A period lists all even edges, then all odd edges. -/
def evenPeriodWord (m : Nat) : List (Fin (2 * m)) :=
  evenWord m ++ oddWord m

theorem evenPeriodWord_length (m : Nat) :
    (evenPeriodWord m).length = 2 * m := by
  simp [evenPeriodWord, evenWord, oddWord, evenPrefixWord, oddPrefixWord]
  omega

/-- One complete even/odd sweep returns exactly to the all-sealed source. -/
theorem run_evenPeriodWord_eq
    (m : Nat) (hm : 0 < m) :
    runSchedule sealMacroProtocol (evenRing m hm) (alternatingSealed m)
        (evenPeriodWord m) =
      alternatingSealed m := by
  rw [evenPeriodWord, evenRunSchedule_append m hm]
  rw [show runSchedule sealMacroProtocol (evenRing m hm)
      (alternatingSealed m) (evenWord m) = alternatingUnsealed m by
        exact run_evenPrefixWord m m hm (by omega)]
  rw [show runSchedule sealMacroProtocol (evenRing m hm)
      (alternatingUnsealed m) (oddWord m) = closureConfig m m by
        exact run_oddPrefixWord m m hm (by omega)]
  exact closureConfig_full_eq_sealed m

/-! ## All-sealed and two-leader certificates -/

def EvenAllSealed (m : Nat) (C : EvenSealConfig m) : Prop :=
  ∀ i : Fin (2 * m), sealMacroSealed (C i) = true

def EvenHasTwoLeaders (m : Nat) (C : EvenSealConfig m) : Prop :=
  ∃ i j : Fin (2 * m), i ≠ j ∧
    sealMacroOutput (C i) = true ∧
    sealMacroOutput (C j) = true

theorem alternatingSealed_allSealed (m : Nat) :
    EvenAllSealed m (alternatingSealed m) := by
  intro i
  rw [alternatingSealed_pointwise]
  by_cases h : i.val % 2 = 0
  · simp [h, sealMacroSealed]
  · simp [h, sealMacroSealed]

private theorem zero_ne_two (m : Nat) (hm : 2 ≤ m) :
    (⟨0, by omega⟩ : Fin (2 * m)) ≠ ⟨2, by omega⟩ := by
  intro h
  have hv := Fin.mk.inj h
  omega

private theorem activationConfig_zero_leader
    (m s : Nat) (hm : 0 < m) :
    sealMacroOutput (activationConfig m s ⟨0, by omega⟩) = true := by
  by_cases h : 0 < s
  · simp [activationConfig, sealMacroOutput, h]
  · simp [activationConfig, sealMacroOutput, h]

private theorem activationConfig_two_leader
    (m s : Nat) (hm : 2 ≤ m) :
    sealMacroOutput (activationConfig m s ⟨2, by omega⟩) = true := by
  by_cases h : 1 < s
  · simp [activationConfig, sealMacroOutput, h]
  · simp [activationConfig, sealMacroOutput, h]

private theorem closureConfig_zero_leader
    (m s : Nat) (hm : 0 < m) :
    sealMacroOutput (closureConfig m s ⟨0, by omega⟩) = true := by
  by_cases h : s = m
  · simp [closureConfig, sealMacroOutput, h]
  · simp [closureConfig, sealMacroOutput, h]

private theorem closureConfig_two_leader
    (m s : Nat) (hm : 2 ≤ m) :
    sealMacroOutput (closureConfig m s ⟨2, by omega⟩) = true := by
  by_cases hsm : s = m
  · simp [closureConfig, sealMacroOutput, hsm]
  · by_cases h : 2 ≤ 2 * s
    · simp [closureConfig, sealMacroOutput, hsm, h]
    · simp [closureConfig, sealMacroOutput, hsm, h]

theorem activationConfig_hasTwo
    (m s : Nat) (hm : 2 ≤ m) :
    EvenHasTwoLeaders m (activationConfig m s) := by
  exact ⟨⟨0, by omega⟩, ⟨2, by omega⟩, zero_ne_two m hm,
    activationConfig_zero_leader m s (by omega),
    activationConfig_two_leader m s hm⟩

theorem closureConfig_hasTwo
    (m s : Nat) (hm : 2 ≤ m) :
    EvenHasTwoLeaders m (closureConfig m s) := by
  exact ⟨⟨0, by omega⟩, ⟨2, by omega⟩, zero_ne_two m hm,
    closureConfig_zero_leader m s (by omega),
    closureConfig_two_leader m s hm⟩

theorem evenHasTwo_not_isSafe
    (m : Nat) (hm : 0 < m) {C : EvenSealConfig m}
    (htwo : EvenHasTwoLeaders m C) :
    ¬ PopulationProtocol.IsSafe
      sealMacroProtocol (evenRing m hm) C id := by
  intro hsafe
  obtain ⟨root, _, honly⟩ := hsafe.1
  obtain ⟨i, j, hij, hi, hj⟩ := htwo
  have hir : i = root := honly i hi
  have hjr : j = root := honly j hj
  exact hij (hir.trans hjr.symm)

/-! ## Periodic weakly edge-fair execution -/

/-- The phase permutation sends phases `0,…,m-1` to the even edges and
phases `m,…,2m-1` to the odd edges. -/
def evenOddPhase (m : Nat) (_hm : 0 < m) (r : Fin (2 * m)) :
    Fin (2 * m) :=
  if h : r.val < m then
    evenEdge m r.val h
  else
    oddEdge m (r.val - m) (by omega)

def evenPeriodicSchedule (m : Nat) (hm : 0 < m) (t : Nat) :
    Fin (2 * m) :=
  evenOddPhase m hm ⟨t % (2 * m), Nat.mod_lt _ (by omega)⟩

def WeakEdgeFairEven (m : Nat) (schedule : Nat → Fin (2 * m)) : Prop :=
  ∀ e : Fin (2 * m), ∀ t : Nat,
    ∃ u : Nat, t ≤ u ∧ schedule u = e

private theorem evenOddPhase_surjective
    (m : Nat) (hm : 0 < m) (e : Fin (2 * m)) :
    ∃ r : Fin (2 * m), evenOddPhase m hm r = e := by
  have hmodlt : e.val % 2 < 2 := Nat.mod_lt _ (by omega)
  have hdecomp := Nat.mod_add_div e.val 2
  by_cases heven : e.val % 2 = 0
  · have heq : 2 * (e.val / 2) = e.val := by omega
    have hq : e.val / 2 < m := by omega
    let r : Fin (2 * m) := ⟨e.val / 2, by omega⟩
    refine ⟨r, ?_⟩
    simp [evenOddPhase, r, hq]
    apply Fin.ext
    exact heq
  · have hodd : e.val % 2 = 1 := by omega
    have heq : 2 * (e.val / 2) + 1 = e.val := by omega
    have hq : e.val / 2 < m := by omega
    let r : Fin (2 * m) := ⟨m + e.val / 2, by omega⟩
    refine ⟨r, ?_⟩
    have hrm : ¬ r.val < m := by simp [r]
    simp [evenOddPhase, r, hrm]
    apply Fin.ext
    exact heq

/-- Repeating the even/odd permutation selects every directed edge
infinitely often. -/
theorem evenPeriodicSchedule_fair
    (m : Nat) (hm : 0 < m) :
    WeakEdgeFairEven m (evenPeriodicSchedule m hm) := by
  intro e t
  obtain ⟨r, hr⟩ := evenOddPhase_surjective m hm e
  let u := (2 * m) * t + r.val
  refine ⟨u, ?_, ?_⟩
  · have hfactor : 1 ≤ 2 * m := by omega
    have hmul : t ≤ (2 * m) * t := by
      have h := Nat.mul_le_mul_right t hfactor
      simpa using h
    exact Nat.le_trans hmul (Nat.le_add_right _ _)
  · have hphase : u % (2 * m) = r.val := by
      simp [u, Nat.mod_eq_of_lt r.isLt]
    unfold evenPeriodicSchedule
    have hfin :
        (⟨u % (2 * m), Nat.mod_lt _ (by omega)⟩ : Fin (2 * m)) = r := by
      apply Fin.ext
      exact hphase
    rw [hfin, hr]

/-- Closed-form trajectory for the repeated period.  The first half of each
period is an activation prefix and the second half is a closure prefix. -/
def evenPeriodicExecution (m : Nat) (_hm : 0 < m) (t : Nat) :
    EvenSealConfig m :=
  let r := t % (2 * m)
  if r < m then activationConfig m r
  else closureConfig m (r - m)

private theorem next_mod_nowrap
    (m t : Nat) (hm : 0 < m)
    (hnext : t % (2 * m) + 1 < 2 * m) :
    (t + 1) % (2 * m) = t % (2 * m) + 1 := by
  rw [Nat.add_mod]
  have hone : 1 % (2 * m) = 1 := Nat.mod_eq_of_lt (by omega)
  rw [hone]
  exact Nat.mod_eq_of_lt hnext

private theorem next_mod_wrap
    (m t : Nat) (hm : 0 < m)
    (hwrap : t % (2 * m) + 1 = 2 * m) :
    (t + 1) % (2 * m) = 0 := by
  rw [Nat.add_mod]
  have hone : 1 % (2 * m) = 1 := Nat.mod_eq_of_lt (by omega)
  rw [hone, hwrap]
  simp

theorem evenPeriodicExecution_initial
    (m : Nat) (hm : 0 < m) :
    evenPeriodicExecution m hm 0 = alternatingSealed m := by
  simp [evenPeriodicExecution, hm, alternatingSealed]

/-- The closed-form trajectory follows the exact macro transition at every
scheduled interaction. -/
theorem evenPeriodicExecution_step
    (m : Nat) (hm : 0 < m) (t : Nat) :
    sealMacroProtocol.step (evenRing m hm) (evenPeriodicExecution m hm t)
        (evenPeriodicSchedule m hm t) =
      evenPeriodicExecution m hm (t + 1) := by
  let r := t % (2 * m)
  have hrlt : r < 2 * m := Nat.mod_lt _ (by omega)
  by_cases hact : r < m
  · have hexec : evenPeriodicExecution m hm t = activationConfig m r := by
      simp [evenPeriodicExecution, r, hact]
    have hsched : evenPeriodicSchedule m hm t = evenEdge m r hact := by
      simp [evenPeriodicSchedule, evenOddPhase, r, hact]
    by_cases hnext : r + 1 < m
    · have hmodnext : (t + 1) % (2 * m) = r + 1 := by
        rw [next_mod_nowrap m t hm (by omega)]
      have hexecNext :
          evenPeriodicExecution m hm (t + 1) =
            activationConfig m (r + 1) := by
        simp [evenPeriodicExecution, hmodnext, hnext]
      rw [hexec, hsched, hexecNext]
      exact activation_step m r hm hact
    · have hboundary : r + 1 = m := by omega
      have hmodnext : (t + 1) % (2 * m) = m := by
        rw [next_mod_nowrap m t hm (by omega)]
        exact hboundary
      have hmnot : ¬ m < m := by omega
      have hexecNext :
          evenPeriodicExecution m hm (t + 1) = closureConfig m 0 := by
        simp [evenPeriodicExecution, hmodnext, hmnot]
      rw [hexec, hsched, hexecNext]
      rw [activation_step m r hm hact, hboundary]
      exact (closureConfig_zero_eq_unsealed m hm).symm
  · let s := r - m
    have hs : s < m := by omega
    have hexec : evenPeriodicExecution m hm t = closureConfig m s := by
      simp [evenPeriodicExecution, r, hact, s]
    have hsched : evenPeriodicSchedule m hm t = oddEdge m s hs := by
      simp [evenPeriodicSchedule, evenOddPhase, r, hact, s]
    by_cases hnext : r + 1 < 2 * m
    · have hmodnext : (t + 1) % (2 * m) = r + 1 := by
        rw [next_mod_nowrap m t hm hnext]
      have hnextNotAct : ¬ r + 1 < m := by omega
      have hsub : r + 1 - m = s + 1 := by omega
      have hexecNext :
          evenPeriodicExecution m hm (t + 1) = closureConfig m (s + 1) := by
        simp [evenPeriodicExecution, hmodnext, hnextNotAct, hsub]
      rw [hexec, hsched, hexecNext]
      exact closure_step m s hm hs
    · have hwrap : r + 1 = 2 * m := by omega
      have hmodnext : (t + 1) % (2 * m) = 0 := by
        exact next_mod_wrap m t hm (by simpa [r] using hwrap)
      have hexecNext :
          evenPeriodicExecution m hm (t + 1) = activationConfig m 0 := by
        simp [evenPeriodicExecution, hmodnext, hm]
      have hsfull : s + 1 = m := by omega
      rw [hexec, hsched, hexecNext]
      rw [closure_step m s hm hs, hsfull]
      exact closureConfig_full_eq_sealed m

theorem evenPeriodicExecution_hasTwo
    (m : Nat) (hm : 2 ≤ m) (t : Nat) :
    EvenHasTwoLeaders m (evenPeriodicExecution m (by omega) t) := by
  unfold evenPeriodicExecution
  by_cases h : t % (2 * m) < m
  · simp [h]
    exact activationConfig_hasTwo m (t % (2 * m)) hm
  · simp [h]
    exact closureConfig_hasTwo m (t % (2 * m) - m) hm

theorem evenPeriodicExecution_not_isSafe
    (m : Nat) (hm : 2 ≤ m) (t : Nat) :
    ¬ PopulationProtocol.IsSafe sealMacroProtocol
      (evenRing m (by omega)) (evenPeriodicExecution m (by omega) t) id := by
  exact evenHasTwo_not_isSafe m (by omega)
    (evenPeriodicExecution_hasTwo m hm t)

theorem evenPeriodicExecution_periodic
    (m : Nat) (hm : 0 < m) (t : Nat) :
    evenPeriodicExecution m hm (t + 2 * m) =
      evenPeriodicExecution m hm t := by
  simp [evenPeriodicExecution]

theorem evenPeriodicExecution_reachable
    (m : Nat) (hm : 0 < m) (t : Nat) :
    PopulationProtocol.Reachable sealMacroProtocol (evenRing m hm)
      (alternatingSealed m) (evenPeriodicExecution m hm t) := by
  induction t with
  | zero =>
      rw [evenPeriodicExecution_initial]
      exact @PopulationProtocol.Reachable.refl (2 * m)
        sealMacroProtocol (evenRing m hm) (alternatingSealed m)
  | succ t ih =>
      exact @PopulationProtocol.Reachable.step (2 * m)
        sealMacroProtocol (evenRing m hm)
        (alternatingSealed m) (evenPeriodicExecution m hm t)
        (evenPeriodicExecution m hm (t + 1)) ih
        ⟨evenPeriodicSchedule m hm t,
          (evenPeriodicExecution_step m hm t).symm⟩

/-- Main unbounded counterfamily.  For every even size `2*m >= 4`, this
supplies an all-sealed source, an exact periodic execution, and a weakly
edge-fair schedule.  Every state on the execution has at least two leader
outputs and is therefore not semantically safe. -/
theorem all_even_sizes_counterexecution :
    ∀ m : Nat, ∀ hm : 2 ≤ m,
      ∃ schedule : Nat → Fin (2 * m),
      ∃ execution : Nat → EvenSealConfig m,
        execution 0 = alternatingSealed m ∧
        EvenAllSealed m (execution 0) ∧
        WeakEdgeFairEven m schedule ∧
        (∀ t, sealMacroProtocol.step (evenRing m (by omega))
            (execution t) (schedule t) = execution (t + 1)) ∧
        (∀ t, execution (t + 2 * m) = execution t) ∧
        (∀ t, EvenHasTwoLeaders m (execution t)) ∧
        (∀ t, ¬ PopulationProtocol.IsSafe sealMacroProtocol
          (evenRing m (by omega)) (execution t) id) ∧
        runSchedule sealMacroProtocol (evenRing m (by omega))
          (alternatingSealed m) (evenPeriodWord m) = alternatingSealed m := by
  intro m hm
  have hmpos : 0 < m := by omega
  refine ⟨evenPeriodicSchedule m hmpos, evenPeriodicExecution m hmpos,
    evenPeriodicExecution_initial m hmpos, ?_,
    evenPeriodicSchedule_fair m hmpos, evenPeriodicExecution_step m hmpos,
    evenPeriodicExecution_periodic m hmpos,
    evenPeriodicExecution_hasTwo m hm,
    evenPeriodicExecution_not_isSafe m hm,
    run_evenPeriodWord_eq m hmpos⟩
  rw [evenPeriodicExecution_initial]
  exact alternatingSealed_allSealed m

end SealSweepConcurrentCounterfamilySol
