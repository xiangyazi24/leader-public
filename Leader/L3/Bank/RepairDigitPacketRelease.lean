import Leader.L3.Bank.RepairDigitCohortDomination
import Leader.L3.ProbStages

/-!
# Lemma e-packet, phase 1: release of a pending export (repair.tex 1223-1250)

One complete interior pair on one lane, in the T22 lane model `L3.CohortDomination`
(`CohortLane`, `cohortEdge`: the literal Pipe/Del/Fin/Term rows; `cohortBankStep` transports the
masked projection of a BANK state by exactly these rows). Target cell `q ∈ [R, 2R)` holds an input
shape and a carry-live bit; the border is cell `R`.

The paper's release phase: until the border is free (empty input, no carry), no packet enters
the target, and the target makes at most `3r^2+4r+1` changing services; one more hit pays the
export (`B = 3r^2+4r+2`). Here the count is an explicit weight on the target cells, at distance
`d = 2R-1-q` from the terminal end:

  `X ↦ d+1`, `S _ ↦ d+2`, `P _ ↦ d+3`, `E ↦ 0`, and a live carry adds `d+1`.

Every target-changing service lowers it, no service raises it while the border is occupied
(`edgeMono`), and while the border is occupied some edge of the pair lowers it (`edgeDrop`: the
rightmost-blocker argument of the paper). Its initial value is at most `R (2R+2) ≤ 3R^2+4R+1`.
Model check (all target scratch, R = 2..5, research/lean-l3/wip/r10c-mc/release_mc.py): no cycle,
no stuck state, longest change chain 5, 8, 11, 16, weight never violated, maximum `R (R+3)`.

The weight reads no source register, so the clock is uniform over source values and source
scratch.
-/

namespace L3.DigitPacketRelease

set_option autoImplicit false

open L3.RenewalReferenceClock
open L3.CohortDomination
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-! ### The weight -/

/-- Weight of an input token at distance `d` from the terminal end. Consumer: `cellW`. -/
def inW (d : Nat) : BankRepairDigitInSh → Nat
  | .E => 0
  | .X => d + 1
  | .S _ => d + 2
  | .P _ => d + 3

/-- Weight of one target cell. Consumer: `releaseWeight`. -/
def cellW (d : Nat) (i : BankRepairDigitInSh) (l : Bool) : Nat :=
  inW d i + (if l then d + 1 else 0)

/-- The release weight of the target cells `R .. 2R-1`. Consumer: `releaseClock`. -/
def releaseWeight (R : Nat) (s : CohortLane) : Nat :=
  bankRepairDigitSumCnt (fun q => cellW (2 * R - 1 - q) (s.inp q) (s.live q)) R R

/-- The border is free: empty input and no live carry at target offset zero. Consumer:
`releaseClock` (target of the release phase). -/
def BorderFree (R : Nat) (s : CohortLane) : Prop := s.inp R = .E ∧ s.live R = false

/-! ### Local rows -/

/-- The input-motion row never raises the weight of its two cells. Consumer: `edgeMono`. -/
theorem finLocal (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool) (iy : BankRepairDigitInSh)
    (ky : Bool) (d : Nat) :
    cellW (d + 1) (bankRepairDigitFinStep bx ix kx iy ky).1
        (bankRepairDigitFinStep bx ix kx iy ky).2.1 +
      cellW d (bankRepairDigitFinStep bx ix kx iy ky).2.2.1
        (bankRepairDigitFinStep bx ix kx iy ky).2.2.2 ≤
      cellW (d + 1) ix kx + cellW d iy ky := by
  cases bx <;> cases kx <;> cases ky <;>
    rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    simp [bankRepairDigitFinStep, cellW, inW] <;> omega

/-- The input-motion row strictly lowers the weight when its left cell carries, holds a front,
holds a border settled operand (launch), or holds a moving packet with a free or settled
carry-free right cell. Consumer: `activeDrop`. -/
theorem finDrop (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool) (iy : BankRepairDigitInSh)
    (ky : Bool) (d : Nat)
    (h : kx = true ∨ ix = .X ∨ (bx = true ∧ ∃ T, ix = .S T) ∨
      ((∃ T, ix = .P T) ∧ ky = false ∧ (iy = .E ∨ ∃ T, iy = .S T))) :
    cellW (d + 1) (bankRepairDigitFinStep bx ix kx iy ky).1
        (bankRepairDigitFinStep bx ix kx iy ky).2.1 +
      cellW d (bankRepairDigitFinStep bx ix kx iy ky).2.2.1
        (bankRepairDigitFinStep bx ix kx iy ky).2.2.2 + 1 ≤
      cellW (d + 1) ix kx + cellW d iy ky := by
  cases bx <;> cases kx <;> cases ky <;>
    rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    simp [bankRepairDigitFinStep, cellW, inW] at h ⊢ <;> omega

/-- The terminal row never raises the weight of the last cell. Consumer: `edgeMono`. -/
theorem termLocal (ix : BankRepairDigitInSh) (kx : Bool) :
    cellW 0 (cohortTermStep ix kx).1 (cohortTermStep ix kx).2 ≤ cellW 0 ix kx := by
  cases kx <;> rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> simp [cohortTermStep, cellW, inW] <;>
    omega

/-- The terminal row strictly lowers the weight of a carrying, front or moving last cell.
Consumer: `activeDrop`. -/
theorem termDrop (ix : BankRepairDigitInSh) (kx : Bool)
    (h : kx = true ∨ ix = .X ∨ ∃ T, ix = .P T) :
    cellW 0 (cohortTermStep ix kx).1 (cohortTermStep ix kx).2 + 1 ≤ cellW 0 ix kx := by
  cases kx <;> rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    simp [cohortTermStep, cellW, inW] at h ⊢ <;> omega

/-- While the border is occupied, the delivery row only clears a carry host's input. Consumer:
`edgeMono`. -/
theorem delLocal (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky : Bool) (d : Nat)
    (h : ¬ (iy = .E ∧ ky = false)) :
    cellW d (bankRepairDigitDelStep ox iy ky).2.1 (bankRepairDigitDelStep ox iy ky).2.2 ≤
      cellW d iy ky := by
  rcases ox with _ | _ | ⟨_ | _⟩ <;> cases ky <;> rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    simp [bankRepairDigitDelStep, cellW, inW] at h ⊢ <;> omega

/-! ### The rows of one edge on the target cells -/

/-- The input-motion row of edge `k`. Consumer: `finWeight`. -/
def finOf (R : Nat) (s : CohortLane) (k : Nat) :
    BankRepairDigitInSh × Bool × BankRepairDigitInSh × Bool :=
  bankRepairDigitFinStep (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1)) (s.live (k + 1))

/-- Output motion leaves the target. Consumer: `edgeMono`. -/
theorem edgePipe (R k : Nat) (s : CohortLane) (h : k + 1 < R) :
    (cohortEdge R s k).inp = s.inp ∧ (cohortEdge R s k).live = s.live := by
  unfold cohortEdge
  rw [if_pos h]
  exact ⟨rfl, rfl⟩

/-- Delivery changes only the border cell. Consumer: `edgeMono`. -/
theorem edgeDel (R k : Nat) (s : CohortLane) (h : k + 1 = R) :
    (cohortEdge R s k).inp = cohortUpd s.inp (k + 1)
        (bankRepairDigitDelStep (s.out k) (s.inp (k + 1)) (s.live (k + 1))).2.1 ∧
      (cohortEdge R s k).live = cohortUpd s.live (k + 1)
        (bankRepairDigitDelStep (s.out k) (s.inp (k + 1)) (s.live (k + 1))).2.2 := by
  unfold cohortEdge
  rw [if_neg (by omega), if_pos h]
  exact ⟨rfl, rfl⟩

/-- Input motion changes only cells `k, k+1`. Consumer: `finWeight`. -/
theorem edgeFin (R k : Nat) (s : CohortLane) (h1 : R ≤ k) (h2 : k + 1 < 2 * R) :
    (cohortEdge R s k).inp = cohortUpd (cohortUpd s.inp k (finOf R s k).1) (k + 1)
        (finOf R s k).2.2.1 ∧
      (cohortEdge R s k).live = cohortUpd (cohortUpd s.live k (finOf R s k).2.1) (k + 1)
        (finOf R s k).2.2.2 := by
  unfold cohortEdge
  rw [if_neg (by omega), if_neg (by omega), if_pos h2]
  exact ⟨rfl, rfl⟩

/-- The terminal row changes only the last cell. Consumer: `termWeight`. -/
theorem edgeTerm (R k : Nat) (s : CohortLane) (h : k + 1 = 2 * R) :
    (cohortEdge R s k).inp = cohortUpd s.inp k (cohortTermStep (s.inp k) (s.live k)).1 ∧
      (cohortEdge R s k).live = cohortUpd s.live k (cohortTermStep (s.inp k) (s.live k)).2 := by
  unfold cohortEdge
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h]
  exact ⟨rfl, rfl⟩

/-! ### Weight frames -/

/-- Two adjacent changed target cells. Consumer: `finWeight`. -/
theorem weightPair (R k δ : Nat) (s s' : CohortLane) (hk : R ≤ k) (hk2 : k + 1 < 2 * R)
    (hsame : ∀ i, i ≠ k → i ≠ k + 1 → s'.inp i = s.inp i ∧ s'.live i = s.live i)
    (hloc : cellW (2 * R - 1 - k) (s'.inp k) (s'.live k) +
        cellW (2 * R - 1 - (k + 1)) (s'.inp (k + 1)) (s'.live (k + 1)) + δ ≤
      cellW (2 * R - 1 - k) (s.inp k) (s.live k) +
        cellW (2 * R - 1 - (k + 1)) (s.inp (k + 1)) (s.live (k + 1))) :
    releaseWeight R s' + δ ≤ releaseWeight R s := by
  unfold releaseWeight
  exact bankRepairDigitSumCntPair _ _ R k δ R
    (fun i _ _ h1 h2 => Nat.le_of_eq (by
      obtain ⟨a, b⟩ := hsame i h1 h2
      rw [a, b])) hk (by omega) hloc

/-- One changed target cell. Consumer: `edgeMono`, `termWeight`. -/
theorem weightPoint (R k δ : Nat) (s s' : CohortLane) (hk : R ≤ k) (hk2 : k < 2 * R)
    (hsame : ∀ i, i ≠ k → s'.inp i = s.inp i ∧ s'.live i = s.live i)
    (hloc : cellW (2 * R - 1 - k) (s'.inp k) (s'.live k) + δ ≤
      cellW (2 * R - 1 - k) (s.inp k) (s.live k)) :
    releaseWeight R s' + δ ≤ releaseWeight R s := by
  unfold releaseWeight
  exact bankRepairDigitSumCntPoint _ _ R k δ R
    (fun i _ _ h1 => Nat.le_of_eq (by
      obtain ⟨a, b⟩ := hsame i h1
      rw [a, b])) hk (by omega) hloc

/-- The weight after input motion on edge `k`, from the two-cell inequality at distance
`d = 2R-1-(k+1)`. Consumer: `edgeMono`, `activeDrop`. -/
theorem finWeight (R k δ : Nat) (s : CohortLane) (h1 : R ≤ k) (h2 : k + 1 < 2 * R)
    (hloc : cellW (2 * R - 1 - (k + 1) + 1) (finOf R s k).1 (finOf R s k).2.1 +
        cellW (2 * R - 1 - (k + 1)) (finOf R s k).2.2.1 (finOf R s k).2.2.2 + δ ≤
      cellW (2 * R - 1 - (k + 1) + 1) (s.inp k) (s.live k) +
        cellW (2 * R - 1 - (k + 1)) (s.inp (k + 1)) (s.live (k + 1))) :
    releaseWeight R (cohortEdge R s k) + δ ≤ releaseWeight R s := by
  obtain ⟨hi, hl⟩ := edgeFin R k s h1 h2
  have hd : 2 * R - 1 - k = 2 * R - 1 - (k + 1) + 1 := by omega
  apply weightPair R k δ s (cohortEdge R s k) h1 h2
  · intro i hi1 hi2
    rw [hi, hl]
    simp [cohortUpd, hi1, hi2]
  · have hne : k ≠ k + 1 := by omega
    have hne' : k + 1 ≠ k := by omega
    rw [hi, hl, hd]
    simpa [cohortUpd, hne, hne'] using hloc

/-- The weight after the terminal row. Consumer: `edgeMono`, `activeDrop`. -/
theorem termWeight (R k δ : Nat) (s : CohortLane) (h : k + 1 = 2 * R)
    (hloc : cellW 0 (cohortTermStep (s.inp k) (s.live k)).1
        (cohortTermStep (s.inp k) (s.live k)).2 + δ ≤ cellW 0 (s.inp k) (s.live k)) :
    releaseWeight R (cohortEdge R s k) + δ ≤ releaseWeight R s := by
  obtain ⟨hi, hl⟩ := edgeTerm R k s h
  have hd : 2 * R - 1 - k = 0 := by omega
  apply weightPoint R k δ s (cohortEdge R s k) (by omega) (by omega)
  · intro i hi1
    rw [hi, hl]
    simp [cohortUpd, hi1]
  · rw [hi, hl, hd]
    simpa [cohortUpd] using hloc

/-! ### No service raises the weight while the border is occupied -/

/-- **Monotonicity.** While the border is occupied, no edge raises the release weight.
Consumer: `releaseClock`. -/
theorem edgeMono (R k : Nat) (s : CohortLane) (hR : 2 ≤ R) (hnf : ¬ BorderFree R s) :
    releaseWeight R (cohortEdge R s k) ≤ releaseWeight R s := by
  by_cases h1 : k + 1 < R
  · obtain ⟨hi, hl⟩ := edgePipe R k s h1
    unfold releaseWeight
    rw [hi, hl]
    exact Nat.le_refl _
  by_cases h2 : k + 1 = R
  · obtain ⟨hi, hl⟩ := edgeDel R k s h2
    have h := weightPoint R (k + 1) 0 s (cohortEdge R s k) (by omega) (by omega)
      (fun i hi1 => by
        rw [hi, hl]
        simp [cohortUpd, hi1])
      (by
        rw [hi, hl]
        unfold cohortUpd
        rw [if_pos rfl, if_pos rfl, Nat.add_zero]
        apply delLocal
        intro ⟨ha, hb⟩
        exact hnf (by unfold BorderFree; rw [← h2]; exact ⟨ha, hb⟩))
    omega
  by_cases h3 : k + 1 < 2 * R
  · have h := finWeight R k 0 s (by omega) h3 (by
      rw [Nat.add_zero]
      unfold finOf
      exact finLocal _ _ _ _ _ _)
    omega
  by_cases h4 : k + 1 = 2 * R
  · have h := termWeight R k 0 s h4 (by
      rw [Nat.add_zero]
      exact termLocal _ _)
    omega
  · rw [cohortEdgeFar R k s (by omega)]
    exact Nat.le_refl _

/-! ### Some edge lowers the weight while the border is occupied -/

/-- A target cell with work that must move: a live carry, a front, a moving packet, or a border
settled operand. Consumer: `activeDrop`, `edgeDrop`. -/
def Active (R : Nat) (s : CohortLane) (q : Nat) : Prop :=
  s.live q = true ∨ s.inp q = .X ∨ (∃ T, s.inp q = .P T) ∨ (q = R ∧ ∃ T, s.inp q = .S T)

/-- **The rightmost blocker.** From an active target cell, some edge of the pair lowers the
weight: a carry, front or border operand acts on its own edge; a moving packet moves or settles,
or its right neighbour is active. Consumer: `edgeDrop`. -/
theorem activeDrop (R : Nat) (s : CohortLane) (hR : 2 ≤ R) :
    ∀ m q, 2 * R - 1 - q = m → R ≤ q → q < 2 * R → Active R s q →
      ∃ k, k < 2 * R ∧ releaseWeight R (cohortEdge R s k) + 1 ≤ releaseWeight R s := by
  intro m
  induction m with
  | zero =>
    intro q hm hq1 hq2 ha
    have hq : q + 1 = 2 * R := by omega
    refine ⟨q, by omega, termWeight R q 1 s hq (termDrop (s.inp q) (s.live q) ?_)⟩
    rcases ha with h | h | h | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · omega
  | succ m ih =>
    intro q hm hq1 hq2 ha
    have hq3 : q + 1 < 2 * R := by omega
    have hm' : 2 * R - 1 - (q + 1) = m := by omega
    have hq4 : R ≤ q + 1 := by omega
    have hdrop : (s.live q = true ∨ s.inp q = .X ∨ (decide (q = R) = true ∧
        ∃ T, s.inp q = .S T) ∨ ((∃ T, s.inp q = .P T) ∧ s.live (q + 1) = false ∧
        (s.inp (q + 1) = .E ∨ ∃ T, s.inp (q + 1) = .S T))) →
        ∃ k, k < 2 * R ∧ releaseWeight R (cohortEdge R s k) + 1 ≤ releaseWeight R s :=
      fun h => ⟨q, by omega, finWeight R q 1 s hq1 hq3 (finDrop (decide (q = R)) (s.inp q)
        (s.live q) (s.inp (q + 1)) (s.live (q + 1)) (2 * R - 1 - (q + 1)) h)⟩
    rcases ha with h | h | ⟨T, h⟩ | ⟨h, T, h'⟩
    · exact hdrop (Or.inl h)
    · exact hdrop (Or.inr (Or.inl h))
    · have hnext := ih (q + 1) hm' hq4 hq3
      cases hk : s.live (q + 1)
      · rcases hi : s.inp (q + 1) with _ | _ | T' | T'
        · exact hdrop (Or.inr (Or.inr (Or.inr ⟨⟨T, h⟩, hk, Or.inl hi⟩)))
        · exact hnext (Or.inr (Or.inl hi))
        · exact hnext (Or.inr (Or.inr (Or.inl ⟨T', hi⟩)))
        · exact hdrop (Or.inr (Or.inr (Or.inr ⟨⟨T, h⟩, hk, Or.inr ⟨T', hi⟩⟩)))
      · exact hnext (Or.inl hk)
    · exact hdrop (Or.inr (Or.inr (Or.inl ⟨by simp [h], T, h'⟩)))

/-- **Progress.** While the border is occupied, some edge of the pair lowers the release weight.
Consumer: `releaseClock`. -/
theorem edgeDrop (R : Nat) (s : CohortLane) (hR : 2 ≤ R) (hnf : ¬ BorderFree R s) :
    ∃ k, k < 2 * R ∧ releaseWeight R (cohortEdge R s k) + 1 ≤ releaseWeight R s := by
  apply activeDrop R s hR (2 * R - 1 - R) R rfl (Nat.le_refl R) (by omega)
  rcases hi : s.inp R with _ | _ | T | T
  · cases hk : s.live R
    · exact absurd ⟨hi, hk⟩ hnf
    · exact Or.inl hk
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr (Or.inl ⟨T, hi⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, T, hi⟩))

/-! ### The initial weight and the clock -/

/-- **The release budget**: at most `R (2R+2)` changing services, below the paper's
`B - 1 = 3r^2+4r+1`. Consumer: `releaseClock`. -/
theorem releaseWeightLe (R : Nat) (s : CohortLane) : releaseWeight R s ≤ R * (2 * R + 2) := by
  unfold releaseWeight
  apply bankRepairDigitSumCntBound
  intro i h1 h2
  have hd : 2 * R - 1 - i ≤ R - 1 := by omega
  show cellW (2 * R - 1 - i) (s.inp i) (s.live i) ≤ 2 * R + 2
  unfold cellW
  cases s.inp i <;> cases s.live i <;> simp [inW] <;> omega

/-- The masked lane chain of one pair: a scheduler letter acts by the lane step of the pair
edge it names. Consumer: `releaseClock`. -/
def releaseNext {n : Nat} (R : Nat) (edgeOf : Fin n → Option Nat) (s : CohortLane)
    (e : Fin n) : CohortLane :=
  cohortLaneStep R s (edgeOf e)

/-- **Lemma e-packet, release phase.** From arbitrary lane scratch, the border of the target is
free (empty input, no carry) at charge `n R (2R+2)`, uniformly over every source register;
`B = 3r^2+4r+2` in the paper adds the export hit. Consumer: the e-packet phase composition
(distinguished-tail phase `F`, which pays `(2r^2+1)` releases), transported to BANK states by
`cohortBankStep` and `L3.Projection.costProjectLe`. -/
theorem releaseClock {n R : Nat} (hR : 2 ≤ R) (site : Nat → Fin n)
    (edgeOf : Fin n → Option Nat) (hedge : ∀ k, k < 2 * R → edgeOf (site k) = some k) :
    ∀ s T, costNumerator (releaseNext R edgeOf) (BorderFree R) s T ≤
      n ^ T * (n * (R * (2 * R + 2))) := by
  intro s T
  have hex : ∀ s : CohortLane, ∃ e : Fin n, ¬ BorderFree R s →
      releaseWeight R (releaseNext R edgeOf s e) + 1 ≤ releaseWeight R s := by
    intro s
    by_cases hb : BorderFree R s
    · exact ⟨site 0, fun h => absurd hb h⟩
    · obtain ⟨k, hk, hd⟩ := edgeDrop R s hR hb
      refine ⟨site k, fun _ => ?_⟩
      show releaseWeight R (cohortLaneStep R s (edgeOf (site k))) + 1 ≤ releaseWeight R s
      rw [hedge k hk]
      exact hd
  have h := L3.Prob.costNumerator_le_of_nominated_edge (releaseNext R edgeOf) (BorderFree R)
    (releaseWeight R) (fun s => Classical.choose (hex s))
    (fun s hs => Classical.choose_spec (hex s) hs)
    (fun s hs e => by
      show releaseWeight R (cohortLaneStep R s (edgeOf e)) ≤ releaseWeight R s
      cases edgeOf e with
      | none => exact Nat.le_refl _
      | some k => exact edgeMono R k s hR hs) s T
  exact Nat.le_trans h (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (releaseWeightLe R s)))

end L3.DigitPacketRelease

#print axioms L3.DigitPacketRelease.finLocal
#print axioms L3.DigitPacketRelease.finDrop
#print axioms L3.DigitPacketRelease.termLocal
#print axioms L3.DigitPacketRelease.termDrop
#print axioms L3.DigitPacketRelease.delLocal
#print axioms L3.DigitPacketRelease.edgePipe
#print axioms L3.DigitPacketRelease.edgeDel
#print axioms L3.DigitPacketRelease.edgeFin
#print axioms L3.DigitPacketRelease.edgeTerm
#print axioms L3.DigitPacketRelease.weightPair
#print axioms L3.DigitPacketRelease.weightPoint
#print axioms L3.DigitPacketRelease.finWeight
#print axioms L3.DigitPacketRelease.termWeight
#print axioms L3.DigitPacketRelease.edgeMono
#print axioms L3.DigitPacketRelease.activeDrop
#print axioms L3.DigitPacketRelease.edgeDrop
#print axioms L3.DigitPacketRelease.releaseWeightLe
#print axioms L3.DigitPacketRelease.releaseClock
