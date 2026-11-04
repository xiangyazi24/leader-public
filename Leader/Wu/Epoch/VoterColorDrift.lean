import Leader.Wu.Epoch.VoterSumTools

/-!
# Color drift for the directed epoch voter process

This module develops the color-mass potential and its exact one-step scheduler
drift.  Every public declaration remains in the historical epoch-voter
namespace.
-/

namespace PPLLEpochVoterPolynomialUpper

open PPLLEpochVoterReduction PPLLEpochVoterTwoDomain
  PPLLEpochVoterFiniteTree PPLLResearchFormulation
  PPLLProtectedEpochProtocol PPLLDerivedEpochRepair
  PPLLDerivedEpochRuntimeNoGo
open PPLLEpochVoterSumTools

/-! ## Color masses and the exact one-copy identity -/

/-- Number of physical positions carrying color `c`. -/
def voterColorMass (D : Fin n → Fin n) (c : Fin n) : Nat :=
  (List.ofFn (fun i => if D i = c then 1 else 0)).sum

/-- Sum of squared color-class sizes.  Consensus has value `n^2`; arbitrary
states have value at most `n^2`. -/
def voterAgreementPotential (D : Fin n → Fin n) : Nat :=
  (List.ofFn (fun c => voterColorMass D c ^ 2)).sum

/-- Number of clockwise edges whose endpoint colors disagree. -/
def voterWallCount (ring : DirectedRing n) (D : Fin n → Fin n) : Nat :=
  (List.ofFn (fun e =>
    if D e = D (ring.rightNeighbor e) then 0 else 1)).sum

/-- Replace the color at one physical position. -/
def recolorAt (D : Fin n → Fin n) (j color : Fin n) : Fin n → Fin n :=
  fun i => if i = j then color else D i

private theorem indicator_color_sum (c : Fin n) :
    (List.ofFn (fun x : Fin n => if c = x then 1 else 0)).sum = 1 := by
  have h := sum_ofFn_balance_one
    (fun x : Fin n => if c = x then 1 else 0)
    (fun _ : Fin n => 0) c (by
      intro x hxc
      simp [Ne.symm hxc])
  rw [sum_ofFn_const] at h
  simpa using h

/-- Each physical position contributes to exactly one color mass. -/
theorem voterColorMass_sum (D : Fin n → Fin n) :
    (List.ofFn (fun c => voterColorMass D c)).sum = n := by
  unfold voterColorMass
  rw [sum_ofFn_swap]
  calc
    (List.ofFn
        (fun i => (List.ofFn (fun c => if D i = c then 1 else 0)).sum)).sum =
        (List.ofFn (fun _ : Fin n => 1)).sum := by
          apply sum_ofFn_eq
          intro i
          exact indicator_color_sum (D i)
    _ = n := by simpa using sum_ofFn_const n 1

/-- A color class contains at most all `n` positions. -/
theorem voterColorMass_le (D : Fin n → Fin n) (c : Fin n) :
    voterColorMass D c ≤ n := by
  unfold voterColorMass
  calc
    (List.ofFn (fun i => if D i = c then 1 else 0)).sum ≤
        (List.ofFn (fun _ : Fin n => 1)).sum := by
          apply sum_ofFn_le
          intro i
          split <;> omega
    _ = n := by simpa using sum_ofFn_const n 1

/-- The agreement potential is bounded by the number `n^2` of ordered pairs
of physical positions. -/
theorem voterAgreementPotential_le_square (D : Fin n → Fin n) :
    voterAgreementPotential D ≤ n ^ 2 := by
  unfold voterAgreementPotential
  calc
    (List.ofFn (fun c => voterColorMass D c ^ 2)).sum ≤
        (List.ofFn (fun c => n * voterColorMass D c)).sum := by
          apply sum_ofFn_le
          intro c
          have h := Nat.mul_le_mul_right (voterColorMass D c)
            (voterColorMass_le D c)
          simpa [Nat.pow_two, Nat.mul_comm] using h
    _ = n * (List.ofFn (fun c => voterColorMass D c)).sum :=
      sum_ofFn_mul_left n _
    _ = n ^ 2 := by rw [voterColorMass_sum]; simp [Nat.pow_two]

private theorem voterColorMass_recolor_balance
    (D : Fin n → Fin n) (j color c : Fin n) :
    voterColorMass (recolorAt D j color) c +
        (if D j = c then 1 else 0) =
      voterColorMass D c + (if color = c then 1 else 0) := by
  unfold voterColorMass
  have h := sum_ofFn_balance_one
    (fun i => if recolorAt D j color i = c then 1 else 0)
    (fun i => if D i = c then 1 else 0) j (by
      intro i hij
      simp [recolorAt, hij])
  simpa [recolorAt] using h

private theorem voterColorMass_recolor_source
    (D : Fin n → Fin n) (j source : Fin n)
    (hneq : source ≠ D j) :
    voterColorMass (recolorAt D j source) source =
      voterColorMass D source + 1 := by
  have h := voterColorMass_recolor_balance D j source source
  simp [Ne.symm hneq] at h
  exact h

private theorem voterColorMass_recolor_target
    (D : Fin n → Fin n) (j source : Fin n)
    (hneq : source ≠ D j) :
    voterColorMass D (D j) =
      voterColorMass (recolorAt D j source) (D j) + 1 := by
  have h := voterColorMass_recolor_balance D j source (D j)
  simp [hneq] at h
  omega

private theorem voterColorMass_recolor_other
    (D : Fin n → Fin n) (j source c : Fin n)
    (hcs : c ≠ source) (hct : c ≠ D j) :
    voterColorMass (recolorAt D j source) c = voterColorMass D c := by
  have h := voterColorMass_recolor_balance D j source c
  simp [Ne.symm hcs, Ne.symm hct] at h
  exact h

/-- Exact subtraction-free potential change when one color overwrites a
different target color. -/
theorem voterAgreementPotential_recolor_balance
    (D : Fin n → Fin n) (j source : Fin n)
    (hneq : source ≠ D j) :
    voterAgreementPotential (recolorAt D j source) +
        2 * voterColorMass D (D j) =
      voterAgreementPotential D + 2 * voterColorMass D source + 2 := by
  let f : Fin n → Nat := fun c =>
    voterColorMass (recolorAt D j source) c ^ 2
  let g : Fin n → Nat := fun c => voterColorMass D c ^ 2
  have hsum := sum_ofFn_balance_two f g source (D j) hneq (by
    intro c hcs hct
    dsimp [f, g]
    rw [voterColorMass_recolor_other D j source c hcs hct])
  have hsource := voterColorMass_recolor_source D j source hneq
  have htarget := voterColorMass_recolor_target D j source hneq
  change voterAgreementPotential (recolorAt D j source) +
      g source + g (D j) = voterAgreementPotential D +
        f source + f (D j) at hsum
  dsimp [f, g] at hsum
  rw [hsource] at hsum
  have hsq : voterColorMass D (D j) =
      voterColorMass (recolorAt D j source) (D j) + 1 := htarget
  rw [hsq] at hsum ⊢
  simp only [Nat.pow_two] at hsum ⊢
  grind

/-! ## Exact scheduler drift -/

/-- On a nontrivial ring, an edge's responder is distinct from its initiator. -/
theorem rightNeighbor_ne
    (hn2 : 1 < n) (ring : DirectedRing n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega

/-- A directed voter step is a single responder recoloring; the initiator arm
of the definition is extensionally redundant. -/
theorem directedVoterStep_eq_recolorAt
    (hn2 : 1 < n) (ring : DirectedRing n)
    (D : Fin n → Fin n) (e : Fin n) :
    directedVoterStep ring D e =
      recolorAt D (ring.rightNeighbor e) (D e) := by
  funext i
  have hne := rightNeighbor_ne hn2 ring e
  unfold directedVoterStep recolorAt
  by_cases hie : i = e
  · subst i
    simp [Ne.symm hne]
  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      simp [hie]
    · simp [hie, hij]

/-- Subtraction-free one-edge potential identity.  The wall indicator is zero
on a stutter edge and one when a genuine copy occurs. -/
theorem voterAgreementPotential_step_balance
    (hn2 : 1 < n) (ring : DirectedRing n)
    (D : Fin n → Fin n) (e : Fin n) :
    voterAgreementPotential (directedVoterStep ring D e) +
        2 * voterColorMass D (D (ring.rightNeighbor e)) =
      voterAgreementPotential D + 2 * voterColorMass D (D e) +
        2 * (if D e = D (ring.rightNeighbor e) then 0 else 1) := by
  by_cases heq : D e = D (ring.rightNeighbor e)
  · rw [directedVoterStep_eq_of_edge_eq ring D e heq, heq]
    simp
  · rw [directedVoterStep_eq_recolorAt hn2 ring D e]
    simpa [heq] using voterAgreementPotential_recolor_balance
      D (ring.rightNeighbor e) (D e) heq


/-- Exact scheduler drift: the total potential over all `n` possible next
edges is the old total plus twice the number of directed color walls. -/
theorem voterAgreementPotential_step_sum
    (hn2 : 1 < n) (ring : DirectedRing n) (D : Fin n → Fin n) :
    (List.ofFn (fun e =>
      voterAgreementPotential (directedVoterStep ring D e))).sum =
      n * voterAgreementPotential D + 2 * voterWallCount ring D := by
  have hsum := sum_ofFn_eq
    (fun e => voterAgreementPotential (directedVoterStep ring D e) +
      2 * voterColorMass D (D (ring.rightNeighbor e)))
    (fun e => voterAgreementPotential D +
      2 * voterColorMass D (D e) +
      2 * (if D e = D (ring.rightNeighbor e) then 0 else 1))
    (fun e => voterAgreementPotential_step_balance hn2 ring D e)
  rw [sum_ofFn_add, sum_ofFn_mul_left,
    sum_ofFn_add, sum_ofFn_add, sum_ofFn_const,
    sum_ofFn_mul_left, sum_ofFn_mul_left] at hsum
  have hmass := sum_ofFn_rightNeighbor ring
    (fun e => voterColorMass D (D e))
  unfold voterWallCount
  omega

/-! ## A live voter word has positive drift -/

/-- If every clockwise edge is monochromatic, the whole directed cycle is in
color consensus. -/
theorem voterConsensus_of_forall_edge_eq
    (ring : DirectedRing n) (D : Fin n → Fin n)
    (hall : ∀ e, D e = D (ring.rightNeighbor e)) :
    VoterConsensus D := by
  let z : Fin n := ⟨0, ring.hn⟩
  have hprefix : ∀ k (hk : k < n), D ⟨k, hk⟩ = D z := by
    intro k
    induction k with
    | zero =>
        intro hk
        rfl
    | succ k ih =>
        intro hk
        let e : Fin n := ⟨k, by omega⟩
        have hneighbor : ring.rightNeighbor e = ⟨k + 1, hk⟩ := by
          apply Fin.ext
          change (k + 1) % n = k + 1
          exact Nat.mod_eq_of_lt hk
        rw [← hneighbor, ← hall e]
        exact ih (by omega)
  exact ⟨D z, fun i => hprefix i.val i.isLt⟩

/-- Every non-consensus cyclic word has at least one directed color wall. -/
theorem voterWallCount_pos_of_not_consensus
    (ring : DirectedRing n) (D : Fin n → Fin n)
    (hD : ¬VoterConsensus D) :
    0 < voterWallCount ring D := by
  have hex : ∃ e, D e ≠ D (ring.rightNeighbor e) := by
    apply Classical.not_forall.mp
    intro hall
    apply hD
    apply voterConsensus_of_forall_edge_eq ring D
    exact hall
  obtain ⟨e, he⟩ := hex
  have ht := term_le_sum_ofFn
    (fun e => if D e = D (ring.rightNeighbor e) then 0 else 1) e
  unfold voterWallCount
  rw [if_neg he] at ht
  exact ht

/-- A live configuration gains at least two units of total agreement potential
across the `n` exact scheduler choices. -/
theorem voterAgreementPotential_step_sum_live
    (hn2 : 1 < n) (ring : DirectedRing n) (D : Fin n → Fin n)
    (hD : ¬VoterConsensus D) :
    n * voterAgreementPotential D + 2 ≤
      (List.ofFn (fun e =>
        voterAgreementPotential (directedVoterStep ring D e))).sum := by
  rw [voterAgreementPotential_step_sum hn2 ring D]
  have hw := voterWallCount_pos_of_not_consensus ring D hD
  omega


end PPLLEpochVoterPolynomialUpper

