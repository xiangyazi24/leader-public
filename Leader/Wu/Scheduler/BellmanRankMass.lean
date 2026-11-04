import Leader.Wu.Scheduler.RankRowSum
import Leader.Wu.Birth.InstalledBlockEscape
import Leader.Wu.Birth.TwoStageEscape
import Leader.Wu.Birth.LeafBoost

set_option autoImplicit false
set_option Elab.async false

/-!
# Generic Bellman rank-to-mass transfer

This is the reusable abstraction of the worked proof in
`R2WriterLeaseMass.ScrubBellman`.

The scheduler alphabet is exactly `Fin n`.  The state type itself need not be
finite and does not need decidable equality: only the finite scheduler row is
summed.  Membership in `Bad` is inspected noncomputably with `classical`, so no
`DecidablePred Bad` premise is exposed.
-/

namespace ZZBellmanTemplate

open BirthLeaderlessBirthMassRenewal BirthTwoStageEscape
open FiniteUniformStoppingTree

variable {S : Type} {n : Nat}

/-- Canonical Q=2 horizon for a raw Nat rank bounded by `K`.
The Bellman potential is `n * rank`, hence has bound `n * K`. -/
def rankHalfH (n K : Nat) : Nat := 2 * (n * K)

/-- Active states are exactly the currently bad states. -/
abbrev Active (Bad : S → Prop) := { x : S // Bad x }

/-- Stop as soon as `Bad` becomes false.  There is no failure outcome in this
specialization, but keeping the common `StopNode` interface lets us reuse the
repository Bellman machinery verbatim. -/
noncomputable def stopStep
    (step : S → Fin n → S) (Bad : S → Prop) :
    Active Bad → Fin n → StopNode (Active Bad) := by
  classical
  intro X e
  let D := step X.1 e
  exact if hD : Bad D then .active ⟨D, hD⟩ else .success

/-- Raw rank on active nodes, zero on both absorbing outcomes. -/
def stopRank (rank : S → Nat) (Bad : S → Prop) :
    StopNode (Active Bad) → Nat
  | .active X => rank X.1
  | .success => 0
  | .failure => 0

/-- Exact scaling used by `R2WriterLeaseMass`: multiply the raw rank by the
scheduler arity `n`. -/
def bellmanPotential
    (n : Nat) (rank : S → Nat) (Bad : S → Prop) :
    StopNode (Active Bad) → Nat :=
  fun x => n * stopRank rank Bad x

private theorem stopStep_active
    (step : S → Fin n → S) (Bad : S → Prop) (X : Active Bad) (e : Fin n)
    (hD : Bad (step X.1 e)) :
    stopStep step Bad X e = .active ⟨step X.1 e, hD⟩ := by
  unfold stopStep
  dsimp only
  rw [dif_pos hD]

private theorem stopStep_success
    (step : S → Fin n → S) (Bad : S → Prop) (X : Active Bad) (e : Fin n)
    (hD : ¬ Bad (step X.1 e)) :
    stopStep step Bad X e = .success := by
  unfold stopStep
  dsimp only
  rw [dif_neg hD]

private theorem stopRank_step_le
    (step : S → Fin n → S) (Bad : S → Prop) (rank : S → Nat)
    (X : Active Bad) (e : Fin n) :
    stopRank rank Bad (stopStep step Bad X e) ≤ rank (step X.1 e) := by
  classical
  by_cases hD : Bad (step X.1 e)
  · rw [stopStep_active step Bad X e hD]
    exact Nat.le_refl _
  · rw [stopStep_success step Bad X e hD]
    exact Nat.zero_le _

/-- Generic Bellman supersolution extracted from the writer-lease proof.
The load-bearing input is the aggregate row inequality supplied by
`ZZMassTemplate.rank_row_sum_generic`: all-letter nonincrease plus one
existential strict child at every bad state. -/
theorem natBellman_generic
    (step : S → Fin n → S) (Bad : S → Prop) (rank : S → Nat)
    (hmono : ∀ x e, rank (step x e) ≤ rank x)
    (hdesc : ∀ x, Bad x → ∃ e, rank (step x e) < rank x) :
    NatBellmanSuperSolution (stopStep step Bad) 1
      (bellmanPotential n rank Bad) := by
  refine ⟨rfl, rfl, ?_⟩
  intro X
  have hs :=
    ZZMassTemplate.rank_row_sum_generic
      step Bad rank hmono hdesc X.1 X.2
  have hchildren :
      (List.ofFn (fun e : Fin n =>
        stopRank rank Bad (stopStep step Bad X e))).sum ≤
      (List.ofFn (fun e : Fin n => rank (step X.1 e))).sum :=
    FiniteUniformStoppingTree.ofFn_sum_le _ _
      (fun e => stopRank_step_le step Bad rank X e)
  unfold bellmanPotential
  rw [FiniteUniformStoppingTree.ofFn_sum_mul_left]
  simp only [Nat.one_mul, stopRank]
  calc
    n + n * (List.ofFn (fun e : Fin n =>
        stopRank rank Bad (stopStep step Bad X e))).sum ≤
      n + n * (List.ofFn (fun e : Fin n => rank (step X.1 e))).sum :=
        Nat.add_le_add_left (Nat.mul_le_mul_left n hchildren) n
    _ = n * (1 + (List.ofFn (fun e : Fin n =>
        rank (step X.1 e))).sum) := by
          rw [Nat.mul_add, Nat.mul_one]
    _ ≤ n * (n * rank X.1) :=
      Nat.mul_le_mul_left n (by simpa [Nat.add_comm] using hs)

private theorem bellmanPotential_le
    (Bad : S → Prop) (rank : S → Nat) (K : Nat)
    (hbound : ∀ x, rank x ≤ K)
    (x : StopNode (Active Bad)) :
    bellmanPotential n rank Bad x ≤ n * K := by
  cases x with
  | success => simp [bellmanPotential, stopRank]
  | failure => simp [bellmanPotential, stopRank]
  | active X =>
      unfold bellmanPotential stopRank
      exact Nat.mul_le_mul_left n (hbound X.1)

/-- Bellman + finite-tree Markov conversion at an arbitrary horizon satisfying
the exact scale condition `2 * (n*K) ≤ L`. -/
private theorem active_half_at
    (step : S → Fin n → S) (Bad : S → Prop) (rank : S → Nat)
    (K L : Nat)
    (hbound : ∀ x, rank x ≤ K)
    (hmono : ∀ x e, rank (step x e) ≤ rank x)
    (hdesc : ∀ x, Bad x → ∃ e, rank (step x e) < rank x)
    (hL : 0 < L)
    (hscale : 2 * (n * K) ≤ L)
    (X : Active Bad) :
    2 * activeCount (stopStep step Bad) (.active X) L ≤ n ^ L := by
  have hcost0 :=
    FiniteUniformStoppingTree.truncatedActiveCostNumerator_mul_le_of_natSuperSolution
      (stopStep step Bad) 1 (bellmanPotential n rank Bad)
      (natBellman_generic step Bad rank hmono hdesc) (.active X) L
  have hcost :
      1 * FiniteUniformStoppingTree.truncatedActiveCostNumerator
        (stopStep step Bad) (.active X) L ≤ (n * K) * n ^ L := by
    calc
      1 * FiniteUniformStoppingTree.truncatedActiveCostNumerator
          (stopStep step Bad) (.active X) L ≤
        n ^ L * bellmanPotential n rank Bad (.active X) := hcost0
      _ ≤ n ^ L * (n * K) :=
        Nat.mul_le_mul_left _
          (bellmanPotential_le (n := n) Bad rank K hbound (.active X))
      _ = (n * K) * n ^ L := Nat.mul_comm _ _
  exact
    FiniteUniformStoppingTree.two_mul_activeCount_le_pow_of_scaled_cost
      (stopStep step Bad) (.active X) hL (by omega) hcost
      (by simpa using hscale)

/-- Zero-horizon alive count at a bad state. -/
private theorem aliveCount_zero_of_bad
    (step : S → Fin n → S) (Bad : S → Prop)
    (x : S) (hx : Bad x) :
    aliveCount step Bad x 0 = 1 := by
  unfold aliveCount FixedSpanRenewalPayload.wordSum
  classical
  simp [allSchedules, aliveBit, AliveAlong, hx]

/-- The stopped active tree is exactly the alive-word count for `Bad`. -/
private theorem activeCount_eq_aliveCount
    (step : S → Fin n → S) (Bad : S → Prop) :
    ∀ (X : Active Bad) (T : Nat),
      activeCount (stopStep step Bad) (.active X) T =
        aliveCount step Bad X.1 T := by
  intro X T
  induction T generalizing X with
  | zero =>
      rw [aliveCount_zero_of_bad step Bad X.1 X.2]
      rfl
  | succ T ih =>
      rw [BirthTwoStageEscape.aliveCount_succ step Bad X.1 X.2 T]
      unfold activeCount
      simp only [treeWeight, stepNode]
      apply FiniteUniformStoppingTree.ofFn_sum_eq
      intro e
      by_cases hD : Bad (step X.1 e)
      · have hstop :
            stopStep step Bad X e =
              StopNode.active ⟨step X.1 e, hD⟩ := by
          unfold stopStep
          dsimp only
          rw [dif_pos hD]
        rw [hstop]
        change activeCount (stopStep step Bad)
          (.active ⟨step X.1 e, hD⟩) T =
            aliveCount step Bad (step X.1 e) T
        exact ih ⟨step X.1 e, hD⟩
      · have hstop : stopStep step Bad X e = StopNode.success := by
          unfold stopStep
          dsimp only
          rw [dif_neg hD]
        rw [hstop, FiniteUniformStoppingTree.treeWeight_success,
          BirthTwoStageEscape.aliveCount_not_good
            step Bad (step X.1 e) hD T]
        simp [FiniteUniformStoppingTree.activeWeight]

/-- Exact worked-proof spelling: active leaves equal words that stay in `True`
and avoid the complement of `Bad` at every prefix endpoint. -/
private theorem activeCount_eq_avoidCount
    (step : S → Fin n → S) (Bad : S → Prop) :
    ∀ (X : Active Bad) (T : Nat),
      activeCount (stopStep step Bad) (.active X) T =
        avoidCount step (fun _ : S => True) (fun y => ¬ Bad y) X.1 T := by
  intro X T
  induction T generalizing X with
  | zero =>
      have hx : True ∧ ¬ (¬ Bad X.1) :=
        ⟨trivial, fun h => h X.2⟩
      rw [BirthTwoStageEscape.avoidCount_zero
        step (fun _ : S => True) (fun y => ¬ Bad y) X.1 hx]
      rfl
  | succ T ih =>
      have hx : True ∧ ¬ (¬ Bad X.1) :=
        ⟨trivial, fun h => h X.2⟩
      rw [BirthTwoStageEscape.avoidCount_succ
        step (fun _ : S => True) (fun y => ¬ Bad y) X.1 hx T]
      unfold activeCount
      simp only [treeWeight, stepNode]
      apply FiniteUniformStoppingTree.ofFn_sum_eq
      intro e
      by_cases hD : Bad (step X.1 e)
      · have hstop :
            stopStep step Bad X e =
              StopNode.active ⟨step X.1 e, hD⟩ := by
          unfold stopStep
          dsimp only
          rw [dif_pos hD]
        rw [hstop]
        change activeCount (stopStep step Bad)
          (.active ⟨step X.1 e, hD⟩) T =
            avoidCount step (fun _ : S => True) (fun y => ¬ Bad y)
              (step X.1 e) T
        exact ih ⟨step X.1 e, hD⟩
      · have hz := BirthTwoStageEscape.avoidCount_zero_of
          step (fun _ : S => True) (fun y => ¬ Bad y) (step X.1 e)
          (fun h => h.2 hD) T
        have hstop : stopStep step Bad X e = StopNode.success := by
          unfold stopStep
          dsimp only
          rw [dif_neg hD]
        rw [hstop, FiniteUniformStoppingTree.treeWeight_success]
        simp only [FiniteUniformStoppingTree.activeWeight, Nat.mul_zero]
        exact hz.symm

/-- Exact first-hit form at any horizon satisfying the Bellman scale relation. -/
theorem rank_half_avoidCount_at
    (step : S → Fin n → S) (Bad : S → Prop) (rank : S → Nat)
    (K L : Nat)
    (hbound : ∀ x, rank x ≤ K)
    (hmono : ∀ x e, rank (step x e) ≤ rank x)
    (hdesc : ∀ x, Bad x → ∃ e, rank (step x e) < rank x)
    (hL : 0 < L)
    (hscale : 2 * (n * K) ≤ L) :
    ∀ x, Bad x →
      2 * avoidCount step (fun _ : S => True) (fun y => ¬ Bad y) x L ≤
        n ^ L := by
  intro x hx
  let X : Active Bad := ⟨x, hx⟩
  have h := active_half_at step Bad rank K L
    hbound hmono hdesc hL hscale X
  rw [activeCount_eq_avoidCount step Bad X L] at h
  simpa [X] using h

/-- Q=2 alive-mass form at any horizon satisfying the exact scale relation. -/
theorem rank_half_uniformEscapeMass_at
    (step : S → Fin n → S) (Bad : S → Prop) (rank : S → Nat)
    (K L : Nat)
    (hbound : ∀ x, rank x ≤ K)
    (hmono : ∀ x e, rank (step x e) ≤ rank x)
    (hdesc : ∀ x, Bad x → ∃ e, rank (step x e) < rank x)
    (hL : 0 < L)
    (hscale : 2 * (n * K) ≤ L) :
    UniformEscapeMass step Bad L 2 := by
  intro x hx
  let X : Active Bad := ⟨x, hx⟩
  have h := active_half_at step Bad rank K L
    hbound hmono hdesc hL hscale X
  rw [activeCount_eq_aliveCount step Bad X L] at h
  simpa [X] using h

private theorem rankHalfH_pos_of_bad
    (step : S → Fin n → S) (Bad : S → Prop) (rank : S → Nat)
    (K : Nat)
    (hbound : ∀ x, rank x ≤ K)
    (hdesc : ∀ x, Bad x → ∃ e, rank (step x e) < rank x)
    (x : S) (hx : Bad x) :
    0 < rankHalfH n K := by
  obtain ⟨e, he⟩ := hdesc x hx
  have hn : 0 < n := by
    have heLt := e.isLt
    omega
  have hr : 0 < rank x := by omega
  have hK : 0 < K := by
    have hb := hbound x
    omega
  unfold rankHalfH
  exact Nat.mul_pos (by omega) (Nat.mul_pos hn hK)

/-- Canonical first-hit theorem, in the exact `avoidCount` shape of the worked
writer-scrub mass theorem. -/
theorem rank_half_avoidCount
    (step : S → Fin n → S) (Bad : S → Prop) (rank : S → Nat)
    (K : Nat)
    (hbound : ∀ x, rank x ≤ K)
    (hmono : ∀ x e, rank (step x e) ≤ rank x)
    (hdesc : ∀ x, Bad x → ∃ e, rank (step x e) < rank x) :
    ∀ x, Bad x →
      2 * avoidCount step (fun _ : S => True) (fun y => ¬ Bad y)
          x (rankHalfH n K) ≤
        n ^ rankHalfH n K := by
  intro x hx
  have hL := rankHalfH_pos_of_bad step Bad rank K hbound hdesc x hx
  have hscale : 2 * (n * K) ≤ rankHalfH n K := by
    unfold rankHalfH
    exact Nat.le_refl _
  exact rank_half_avoidCount_at step Bad rank K (rankHalfH n K)
    hbound hmono hdesc hL hscale x hx

/-- Canonical generic transfer theorem requested by R384. -/
theorem rank_half_uniformEscapeMass
    (step : S → Fin n → S) (Bad : S → Prop) (rank : S → Nat)
    (K : Nat)
    (hbound : ∀ x, rank x ≤ K)
    (hmono : ∀ x e, rank (step x e) ≤ rank x)
    (hdesc : ∀ x, Bad x → ∃ e, rank (step x e) < rank x) :
    UniformEscapeMass step Bad (rankHalfH n K) 2 := by
  intro x hx
  have hL := rankHalfH_pos_of_bad step Bad rank K hbound hdesc x hx
  have hscale : 2 * (n * K) ≤ rankHalfH n K := by
    unfold rankHalfH
    exact Nat.le_refl _
  exact
    (rank_half_uniformEscapeMass_at
      step Bad rank K (rankHalfH n K)
      hbound hmono hdesc hL hscale) x hx

/-- Direct boost of the generic Q=2 block to the repository's Q=8 block. -/
theorem rank_eighth_uniformEscapeMass
    (step : S → Fin n → S) (Bad : S → Prop) (rank : S → Nat)
    (K : Nat)
    (hbound : ∀ x, rank x ≤ K)
    (hmono : ∀ x e, rank (step x e) ≤ rank x)
    (hdesc : ∀ x, Bad x → ∃ e, rank (step x e) < rank x) :
    UniformEscapeMass step Bad (3 * 2 * rankHalfH n K) 8 := by
  exact BirthLeafBoost.escape_boost
    step Bad (rankHalfH n K) 2 (by omega)
    (rank_half_uniformEscapeMass step Bad rank K hbound hmono hdesc)

/-- Exact two-stage + boost horizon when the generic rank theorem supplies
stage 2 with `Q₂ = 2`.  The rank hypotheses are global on `Bad`, so the extra
`R x` premise required by `two_stage_escape` is intentionally unused. -/
theorem two_stage_eighth_of_rank
    (step : S → Fin n → S) (Bad R : S → Prop) (rank : S → Nat)
    (K B₁ Q₁ : Nat)
    (hQ₁ : 1 ≤ Q₁)
    (h1 : ∀ x, Bad x →
      Q₁ * avoidCount step Bad R x B₁ ≤ (Q₁ - 1) * n ^ B₁)
    (hbound : ∀ x, rank x ≤ K)
    (hmono : ∀ x e, rank (step x e) ≤ rank x)
    (hdesc : ∀ x, Bad x → ∃ e, rank (step x e) < rank x) :
    UniformEscapeMass step Bad
      (3 * (Q₁ * 2) * (B₁ + rankHalfH n K)) 8 := by
  have hhalf :=
    rank_half_uniformEscapeMass step Bad rank K hbound hmono hdesc
  have h2 : ∀ x, Bad x → R x →
      2 * aliveCount step Bad x (rankHalfH n K) ≤
        (2 - 1) * n ^ rankHalfH n K := by
    intro x hx _
    exact hhalf x hx
  have h12 := BirthTwoStageEscape.two_stage_escape
    step Bad R B₁ (rankHalfH n K) Q₁ 2
    hQ₁ (by omega) h1 h2
  have hQ : 1 ≤ Q₁ * 2 := by omega
  exact BirthLeafBoost.escape_boost
    step Bad (B₁ + rankHalfH n K) (Q₁ * 2) hQ h12

/-! ## Exact installed-V3 instantiation interface -/

namespace InstalledV3

variable {ψ κ τ : Nat}

/-- Ingredient (a): a uniform Nat bound on the proposed installed-step rank. -/
def InstalledRankBoundV3
    (rank : ZZFinalCarrierV3.Config n ψ κ τ → Nat) (K : Nat) : Prop :=
  ∀ C, rank C ≤ K

/-- Ingredient (b): every `Fin n` scheduler letter is rank-nonincreasing for
the exact installed V3 step.  Any old `PairRiskNoRaise` burden belongs in a
proof of this obligation; it is not smuggled into the Bellman theorem. -/
noncomputable def InstalledRankNonincreaseV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (rank : ZZFinalCarrierV3.Config n ψ κ τ → Nat) : Prop :=
  ∀ C e,
    rank (ZZFinalCarrierV3.stepConcreteV3
      (κ := κ) (τ := τ) hψ h2 ring C e) ≤ rank C

/-- Ingredient (c): from every state counted by the installed consumer's exact
`Good` predicate, some scheduler edge strictly lowers the rank. -/
noncomputable def InstalledRankDescentV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (rank : ZZFinalCarrierV3.Config n ψ κ τ → Nat) : Prop :=
  ∀ C,
    ZZBlockEscape.FinalLeaderlessV3 C →
    ∃ e : Fin n,
      rank (ZZFinalCarrierV3.stepConcreteV3
        (κ := κ) (τ := τ) hψ h2 ring C e) < rank C

/-- Exact installed first-hit spelling corresponding to
`R2WriterLeaseMass.writerScrub_half_mass_unconditional`. -/
theorem installed_half_avoidCount_of_rank
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (rank : ZZFinalCarrierV3.Config n ψ κ τ → Nat) (K : Nat)
    (hBound : InstalledRankBoundV3 rank K)
    (hMono : InstalledRankNonincreaseV3 hψ h2 ring rank)
    (hDesc : InstalledRankDescentV3 hψ h2 ring rank) :
    ∀ C, ZZBlockEscape.FinalLeaderlessV3 C →
      2 * avoidCount
          (ZZFinalCarrierV3.stepConcreteV3
            (κ := κ) (τ := τ) hψ h2 ring)
          (fun _ : ZZFinalCarrierV3.Config n ψ κ τ => True)
          (fun D => ¬ ZZBlockEscape.FinalLeaderlessV3 D)
          C (rankHalfH n K) ≤
        n ^ rankHalfH n K := by
  apply rank_half_avoidCount
    (step := ZZFinalCarrierV3.stepConcreteV3
      (κ := κ) (τ := τ) hψ h2 ring)
    (Bad := ZZBlockEscape.FinalLeaderlessV3)
    (rank := rank) (K := K)
  · simpa [InstalledRankBoundV3] using hBound
  · simpa [InstalledRankNonincreaseV3] using hMono
  · simpa [InstalledRankDescentV3] using hDesc

/-- The three named installed obligations imply an exact Q=2 block mass for
the terminal consumer's `FinalLeaderlessV3` predicate. -/
theorem installed_half_mass_of_rank
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (rank : ZZFinalCarrierV3.Config n ψ κ τ → Nat) (K : Nat)
    (hBound : InstalledRankBoundV3 rank K)
    (hMono : InstalledRankNonincreaseV3 hψ h2 ring rank)
    (hDesc : InstalledRankDescentV3 hψ h2 ring rank) :
    UniformEscapeMass
      (ZZFinalCarrierV3.stepConcreteV3
        (κ := κ) (τ := τ) hψ h2 ring)
      ZZBlockEscape.FinalLeaderlessV3 (rankHalfH n K) 2 := by
  apply rank_half_uniformEscapeMass
    (step := ZZFinalCarrierV3.stepConcreteV3
      (κ := κ) (τ := τ) hψ h2 ring)
    (Bad := ZZBlockEscape.FinalLeaderlessV3)
    (rank := rank) (K := K)
  · simpa [InstalledRankBoundV3] using hBound
  · simpa [InstalledRankNonincreaseV3] using hMono
  · simpa [InstalledRankDescentV3] using hDesc

/-- Direct connection to the exact Q=8 installed block-escape interface. -/
theorem installed_eighth_block_escape_of_rank
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (rank : ZZFinalCarrierV3.Config n ψ κ τ → Nat) (K : Nat)
    (hBound : InstalledRankBoundV3 rank K)
    (hMono : InstalledRankNonincreaseV3 hψ h2 ring rank)
    (hDesc : InstalledRankDescentV3 hψ h2 ring rank) :
    ZZBlockEscape.LeaderlessBlockEscapeV3
      n ψ κ τ (3 * 2 * rankHalfH n K) hψ h2 ring := by
  change UniformEscapeMass
    (ZZFinalCarrierV3.stepConcreteV3
      (κ := κ) (τ := τ) hψ h2 ring)
    ZZBlockEscape.FinalLeaderlessV3
    (3 * 2 * rankHalfH n K) 8
  apply rank_eighth_uniformEscapeMass
    (step := ZZFinalCarrierV3.stepConcreteV3
      (κ := κ) (τ := τ) hψ h2 ring)
    (Bad := ZZBlockEscape.FinalLeaderlessV3)
    (rank := rank) (K := K)
  · simpa [InstalledRankBoundV3] using hBound
  · simpa [InstalledRankNonincreaseV3] using hMono
  · simpa [InstalledRankDescentV3] using hDesc

end InstalledV3

end ZZBellmanTemplate
