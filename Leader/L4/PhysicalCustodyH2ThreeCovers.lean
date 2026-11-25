import Leader.L4.Height.LeaderBridge

/-! The three physical cover stages. Each scheduler letter is
recorded verbatim. The nominated letter only controls when a block ends. -/

namespace L4.Height.ThreeCoverClock

set_option autoImplicit false

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

variable {S : Type} {n : Nat}

/-- Three consecutive full covers on a single raw word from the given start. -/
def ThreeActualCovers (next : S → Fin n → S) (x y : S) : Prop :=
  ∃ blocks : List (List (Fin n)), blocks.length = 3 ∧
    (∀ w ∈ blocks, ∀ e : Fin n, e ∈ w) ∧
    runWord next x blocks.flatten = y

/-- Record each physical scheduler mark alongside its physical update. -/
def threeCoverHistoryNext (next : S → Fin n → S) (z : S × List (Fin n))
    (e : Fin n) : S × List (Fin n) :=
  (next z.1 e, z.2 ++ [e])

/-- The recorded raw tape itself splits into three consecutive full covers. -/
def ThreeCoverHistory (next : S → Fin n → S) (x : S) (z : S × List (Fin n)) : Prop :=
  ∃ blocks : List (List (Fin n)), blocks.length = 3 ∧
    (∀ w ∈ blocks, ∀ e : Fin n, e ∈ w) ∧
    blocks.flatten = z.2 ∧ runWord next x blocks.flatten = z.1

private structure CoverTape (n : Nat) where
  done : List (List (Fin n))
  current : List (Fin n)
  index : Fin n
  bounded : done.length ≤ 3
  full : ∀ w ∈ done, ∀ e : Fin n, e ∈ w
  seen : ∀ e : Fin n, e.val < index.val → e ∈ current

private def emptyTape (hn : 0 < n) : CoverTape n where
  done := []
  current := []
  index := ⟨0, hn⟩
  bounded := by simp
  full := by simp
  seen := fun e h => False.elim (Nat.not_lt_zero _ h)

private def tapeWord (z : CoverTape n) : List (Fin n) :=
  z.done.reverse.flatten ++ z.current

private abbrev finished (z : CoverTape n) : Prop :=
  3 ≤ z.done.length

private def recordMark (z : CoverTape n) (e : Fin n) (j : Fin n)
    (seen : ∀ a : Fin n, a.val < j.val → a ∈ z.current ++ [e]) : CoverTape n :=
  { z with current := z.current ++ [e], index := j, seen := seen }

private def keepIndex (z : CoverTape n) (e : Fin n) : CoverTape n :=
  recordMark z e z.index (fun a ha => List.mem_append_left _ (z.seen a ha))

private def closeBlock (hn : 0 < n) (z : CoverTape n) (e : Fin n)
    (hOpen : ¬ finished z) (hMatch : e = z.index)
    (hLast : ¬ z.index.val + 1 < n) : CoverTape n where
  done := (z.current ++ [e]) :: z.done
  current := []
  index := ⟨0, hn⟩
  bounded := by
    have h : ¬ 3 ≤ z.done.length := hOpen
    simp only [List.length_cons]
    omega
  full := by
    intro w hw a
    rcases List.mem_cons.mp hw with rfl | hw
    · by_cases ha : a.val < z.index.val
      · exact List.mem_append_left _ (z.seen a ha)
      · have he : a = e := by
          subst e
          apply Fin.ext
          have hna := a.isLt
          have hni := z.index.isLt
          omega
        simp [he]
    · exact z.full w hw a
  seen := fun a ha => False.elim (Nat.not_lt_zero _ ha)

private def tapeStep (hn : 0 < n) (z : CoverTape n) (e : Fin n) : CoverTape n :=
  if hStop : finished z then
    keepIndex z e
  else if hMatch : e = z.index then
    if hMore : z.index.val + 1 < n then
      recordMark z e ⟨z.index.val + 1, hMore⟩ (by
        intro a ha
        by_cases hPrev : a.val < z.index.val
        · exact List.mem_append_left _ (z.seen a hPrev)
        · have he : a = e := by
            subst e
            apply Fin.ext
            change a.val < z.index.val + 1 at ha
            omega
          simp [he])
    else
      closeBlock hn z e hStop hMatch hMore
  else
    keepIndex z e

private theorem tapeWord_step (hn : 0 < n) (z : CoverTape n) (e : Fin n) :
    tapeWord (tapeStep hn z e) = tapeWord z ++ [e] := by
  unfold tapeStep
  split
  · simp [keepIndex, recordMark, tapeWord, List.append_assoc]
  · split
    · split
      · simp [recordMark, tapeWord, List.append_assoc]
      · simp [closeBlock, tapeWord, List.reverse_cons, List.flatten_append, List.append_assoc]
    · simp [keepIndex, recordMark, tapeWord, List.append_assoc]

private theorem tapeWord_full (z : CoverTape n) (hz : finished z) :
    ∃ blocks : List (List (Fin n)), blocks.length = 3 ∧
      (∀ w ∈ blocks, ∀ e : Fin n, e ∈ w) ∧
      blocks.flatten = tapeWord z := by
  have hBound := z.bounded
  change 3 ≤ z.done.length at hz
  cases hd : z.done with
  | nil =>
      simp only [hd, List.length_nil] at hz
      omega
  | cons last earlier =>
      refine ⟨earlier.reverse ++ [last ++ z.current], ?_, ?_, ?_⟩
      · simp only [hd, List.length_cons] at hz hBound
        simp only [List.length_append, List.length_reverse, List.length_cons, List.length_nil]
        omega
      · intro w hw e
        rcases List.mem_append.mp hw with hearlier | hlast
        · have h : w ∈ earlier := List.mem_reverse.mp hearlier
          exact z.full w (hd.symm ▸ List.mem_cons_of_mem last h) e
        · have h : w = last ++ z.current := List.mem_singleton.mp hlast
          subst w
          exact List.mem_append_left _ (z.full last (hd.symm ▸ List.mem_cons_self) e)
      · simp [tapeWord, hd, List.reverse_cons, List.flatten_append, List.append_assoc]

private def remaining (z : CoverTape n) : Nat :=
  (3 - z.done.length) * n - z.index.val

private theorem remaining_drop (hn : 0 < n) (z : CoverTape n) (hz : ¬ finished z) :
    remaining (tapeStep hn z z.index) + 1 ≤ remaining z := by
  have hOpen : z.done.length < 3 := Nat.lt_of_not_ge hz
  have hRank : n ≤ (3 - z.done.length) * n := by
    simpa only [Nat.one_mul] using
      (Nat.mul_le_mul_right n (show 1 ≤ 3 - z.done.length by omega))
  have hIndex := z.index.isLt
  by_cases hMore : z.index.val + 1 < n
  · simp only [tapeStep, dif_neg hz, dif_pos rfl, dif_pos hMore, recordMark, remaining]
    omega
  · simp only [tapeStep, dif_neg hz, dif_pos rfl, dif_neg hMore, closeBlock, remaining,
      List.length_cons, Nat.sub_zero]
    have hRounds : 3 - z.done.length = (3 - (z.done.length + 1)) + 1 := by omega
    rw [hRounds, Nat.add_mul, Nat.one_mul]
    omega

private theorem remaining_noninc (hn : 0 < n) (z : CoverTape n)
    (hz : ¬ finished z) (e : Fin n) :
    remaining (tapeStep hn z e) ≤ remaining z := by
  by_cases he : e = z.index
  · subst e
    have h := remaining_drop hn z hz
    omega
  · simp [tapeStep, hz, he, remaining, keepIndex, recordMark]

private def coverProjection (next : S → Fin n → S) (x : S) (z : CoverTape n) : S :=
  runWord next x (tapeWord z)

private theorem coverProjection_step (next : S → Fin n → S) (x : S) (hn : 0 < n)
    (z : CoverTape n) (e : Fin n) :
    coverProjection next x (tapeStep hn z e) = next (coverProjection next x z) e := by
  simp only [coverProjection, tapeWord_step, runWord, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

private theorem projected_cost_le (next : S → Fin n → S) (hn : 0 < n)
    (P : S → Prop) (project : CoverTape n → S)
    (step : ∀ z e, project (tapeStep hn z e) = next (project z) e)
    (hit : ∀ z, finished z → P (project z)) :
    ∀ (t : Nat) (z : CoverTape n),
      costNumerator next P (project z) t ≤
        costNumerator (tapeStep hn) finished z t := by
  classical
  intro t
  induction t with
  | zero =>
      intro z
      simp only [costNumerator_zero, Nat.le_refl]
  | succ t ih =>
      intro z
      by_cases h : P (project z)
      · rw [costNumerator_terminal next _ _ h (t + 1)]
        exact Nat.zero_le _
      · have hUnfinished : ¬ finished z := fun hz => h (hit z hz)
        rw [costNumerator_succ next _ _ h t,
          costNumerator_succ (tapeStep hn) _ _ hUnfinished t]
        apply Nat.add_le_add_left
        exact ofFn_sum_le _ _ (fun e => by
          rw [← step z e]
          exact ih (tapeStep hn z e))

private theorem projected_expected (next : S → Fin n → S) (hn : 0 < n)
    (P : S → Prop) (project : CoverTape n → S)
    (step : ∀ z e, project (tapeStep hn z e) = next (project z) e)
    (hit : ∀ z, finished z → P (project z)) :
    IIDExpectedHittingTimeAtMost next P (project (emptyTape hn)) (3 * n ^ 2) := by
  intro t
  rw [iidHitCost_eq_costNumerator, Nat.mul_comm (3 * n ^ 2)]
  refine Nat.le_trans (projected_cost_le next hn P project step hit t (emptyTape hn)) ?_
  have hCost := L3.Prob.costNumerator_le_of_nominated_edge (tapeStep hn)
    finished remaining CoverTape.index (remaining_drop hn) (remaining_noninc hn)
    (emptyTape hn) t
  have hBudget : n * remaining (emptyTape hn) = 3 * n ^ 2 := by
    simp only [remaining, emptyTape, List.length_nil, Nat.sub_zero, Nat.pow_two]
    ac_rfl
  simpa only [hBudget] using hCost

/-- The first hit of a state admitting a two-cover physical history has
expected cost at most two times the square of the number of marks. -/
theorem three_full_covers_expected (next : S → Fin n → S) (hn : 0 < n) (x : S) :
    IIDExpectedHittingTimeAtMost next (ThreeActualCovers next x) x (3 * n ^ 2) := by
  apply projected_expected next hn (ThreeActualCovers next x) (coverProjection next x)
    (coverProjection_step next x hn)
  intro z hz
  obtain ⟨blocks, hlen, hfull, hword⟩ := tapeWord_full z hz
  exact ⟨blocks, hlen, hfull, congrArg (runWord next x) hword⟩

/-- Two full blocks are obtained on the actual continuing tape within the
same quadratic bound. Each mark is executed in the physical component. -/
theorem three_cover_history_expected (next : S → Fin n → S) (hn : 0 < n) (x : S) :
    IIDExpectedHittingTimeAtMost (threeCoverHistoryNext next) (ThreeCoverHistory next x)
      (x, []) (3 * n ^ 2) := by
  let project : CoverTape n → S × List (Fin n) :=
    fun z => (coverProjection next x z, tapeWord z)
  have hStep : ∀ z e, project (tapeStep hn z e) = threeCoverHistoryNext next (project z) e := by
    intro z e
    exact Prod.ext (coverProjection_step next x hn z e) (tapeWord_step hn z e)
  apply projected_expected (threeCoverHistoryNext next) hn (ThreeCoverHistory next x) project hStep
  intro z hz
  obtain ⟨blocks, hlen, hfull, hword⟩ := tapeWord_full z hz
  exact ⟨blocks, hlen, hfull, hword, congrArg (runWord next x) hword⟩

end L4.Height.ThreeCoverClock
