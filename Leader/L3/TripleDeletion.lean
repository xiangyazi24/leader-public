import Leader.L3.SealedClose
import Leader.L3.SealedPrep

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-!
For tokens.tex lem:app-ld.
The missing physical trial and renewal premises are exposed explicitly.
-/

abbrev TripleNativeState (n : Nat) := Fin n → CertNative

/-- Cyclically successive tagged leaders; i=k is the two-leader case. -/
def TaggedTriple {n : Nat} (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat) (N : TripleNativeState n) : Prop :=
  P ring N ∧ ConsecutiveNative ring N i j a ∧
    ConsecutiveNative ring N j k b

/-- First deletion of any distinct tag, even when i=k. -/
def TaggedDeleted {n : Nat} (i j k : Fin n)
    (N : TripleNativeState n) : Prop :=
  (N i).l = false ∨ (N j).l = false ∨ (N k).l = false

def TaggedSealed {n : Nat} (ring : DirectedRing n)
    (i j : Fin n) (a b : Nat) (N : TripleNativeState n) : Prop :=
  Sealed ring N i a ∧ Sealed ring N j b

/-- Moderate attack: the attacker is sealed and target B is Ready. -/
def TaggedPrepared {n : Nat} (ring : DirectedRing n)
    (i j : Fin n) (a b : Nat) (N : TripleNativeState n) : Prop :=
  Sealed ring N i a ∧ SealedCleanReady ring N j b

/-- Clean dummy at offset zero, with its shield zero by the phase rule. -/
def TaggedCleanDummy {n : Nat} (ring : DirectedRing n)
    (i j : Fin n) (a b : Nat) (N : TripleNativeState n) : Prop :=
  Sealed ring N i a ∧
    SealedPhaseHolds ring N j b (.dummy (sealedZero ring))

theorem tagged_clean_dummy_sealed {n : Nat}
    (ring : DirectedRing n) (i j : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (h : TaggedCleanDummy ring i j a b N) :
    TaggedSealed ring i j a b N :=
  ⟨h.1, ⟨.dummy (sealedZero ring), h.2⟩⟩

theorem tagged_prepared_sealed {n : Nat}
    (ring : DirectedRing n) (i j : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (h : TaggedPrepared ring i j a b N) :
    TaggedSealed ring i j a b N :=
  ⟨h.1, sealed_of_clean_ready ring N j b h.2⟩

/-- One actual nativeE edge preserves peace and consecutive tags
as long as no tag dies. -/
theorem tagged_triple_step_of_survival {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n) (e : Fin n)
    (h : TaggedTriple ring i j k a b N)
    (hnot : ¬ TaggedDeleted i j k (nativeE ring N e)) :
    TaggedTriple ring i j k a b (nativeE ring N e) := by
  have hi : (nativeE ring N e i).l = true := by
    cases hx : (nativeE ring N e i).l with
    | false => exact False.elim (hnot (Or.inl hx))
    | true => rfl
  have hj : (nativeE ring N e j).l = true := by
    cases hx : (nativeE ring N e j).l with
    | false => exact False.elim (hnot (Or.inr (Or.inl hx)))
    | true => rfl
  have hk : (nativeE ring N e k).l = true := by
    cases hx : (nativeE ring N e k).l with
    | false => exact False.elim (hnot (Or.inr (Or.inr hx)))
    | true => rfl
  exact ⟨nativeE_preserves_P hn ring N e h.1,
    consecutive_native_step_of_survival
      ring N i j a e h.2.1 hi hj,
    consecutive_native_step_of_survival
      ring N j k b e h.2.2 hj hk⟩

/-- Both sectors are advanced by the SAME physical edge, including i=k. -/
theorem tagged_sealed_step_of_survival {n : Nat}
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n) (e : Fin n)
    (h : TaggedTriple ring i j k a b N)
    (hs : TaggedSealed ring i j a b N)
    (hnot : ¬ TaggedDeleted i j k (nativeE ring N e)) :
    TaggedSealed ring i j a b (nativeE ring N e) := by
  have hleft :=
    sealed_all_edge_closed ring N i j a e h.2.1 hs.1
  have hright :=
    sealed_all_edge_closed ring N j k b e h.2.2 hs.2
  constructor
  · rcases hleft with hi | hj | hnew
    · exact False.elim (hnot (Or.inl hi))
    · exact False.elim (hnot (Or.inr (Or.inl hj)))
    · exact hnew
  · rcases hright with hj | hk | hnew
    · exact False.elim (hnot (Or.inr (Or.inl hj)))
    · exact False.elim (hnot (Or.inr (Or.inr hk)))
    · exact hnew

/-- Physical vulnerable trial: a Ready-time outgoing R_j is failure.
Native triple deletion on the selected row is success. -/
noncomputable def taggedTrialStep {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (b : Nat) :
    TripleNativeState n → Fin n → StopNode (TripleNativeState n) := by
  classical
  exact fun N e =>
    let M := nativeE ring N e
    if TaggedDeleted i j k M then .success
    else if SealedCleanReady ring N j b ∧ e = j then .failure
    else .active M

/-- Paper scheduler Q: at a Ready target only, redirect raw R_j to
actual incoming L_j, applying the original nativeE row unchanged. -/
noncomputable def taggedRedirection {n : Nat}
    (ring : DirectedRing n) (j : Fin n) (b : Nat)
    (hn : 2 ≤ n) (hports : ring.leftNeighbor j ≠ j) :
    ControlledSchedulerMass.Redirection (TripleNativeState n) n := by
  classical
  exact
    { two_le := hn
      gate := fun N => decide (SealedCleanReady ring N j b)
      portA := fun _ => ring.leftNeighbor j
      portB := fun _ => j
      distinct := by
        intro N hg
        exact hports }

theorem tagged_redirection_ready_right {n : Nat}
    (ring : DirectedRing n) (j : Fin n) (b : Nat)
    (hn : 2 ≤ n) (hports : ring.leftNeighbor j ≠ j)
    (N : TripleNativeState n)
    (hready : SealedCleanReady ring N j b) :
    (taggedRedirection ring j b hn hports).effective N j =
      ring.leftNeighbor j := by
  classical
  have hg : (taggedRedirection ring j b hn hports).gate N = true := by
    simp [taggedRedirection, hready]
  exact (taggedRedirection ring j b hn hports).effective_B N hg

/-- Exact variable-weight finite-schedule likelihood transfer:
each Ready-time L_j event has two raw preimages. -/
theorem tagged_weighted_success_transfer {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (b : Nat)
    (hn : 2 ≤ n) (hports : ring.leftNeighbor j ≠ j)
    (N : TripleNativeState n) (T : Nat) :
    PPL.Convergence.LDLocal.weightedQSuccessNumerator
      (taggedTrialStep ring i j k b)
      (taggedRedirection ring j b hn hports)
      (.active N) T ≤
    2 ^ T * successCount (taggedTrialStep ring i j k b)
      (.active N) T := by
  exact PPL.Convergence.LDLocal.weighted_changeOfMeasure_success
    (taggedTrialStep ring i j k b)
    (taggedRedirection ring j b hn hports) (.active N) T

/-- If controlled success at finite horizon has mass >=1/q
with at most M collapsed events, original success has mass
>=1/(q*2^M). The Q-mass hypothesis must be proved separately. -/
theorem tagged_fraction_from_controlled_budget {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (b : Nat)
    (hn : 2 ≤ n) (hports : ring.leftNeighbor j ≠ j)
    (N : TripleNativeState n) (T M q : Nat)
    (hcontrolled :
      n ^ T ≤ q * ControlledSchedulerMass.boundedSuccessCount
        (taggedTrialStep ring i j k b)
        (taggedRedirection ring j b hn hports)
        (.active N) T M) :
    n ^ T ≤ (q * 2 ^ M) *
      successCount (taggedTrialStep ring i j k b) (.active N) T := by
  exact ControlledSchedulerMass.raw_success_mass_lower
    (taggedTrialStep ring i j k b)
    (taggedRedirection ring j b hn hports)
    (.active N) T M q hcontrolled

/-! Quantitative interface for D.9. -/

/-- Exact natural ceiling of (745/3) n (a+b). -/
def taggedTripleCeiling (n a b : Nat) : Nat :=
  (745 * n * (a + b) + 2) / 3

/-- The moderate paper trial needs 1/64 at b=2.
At b>=3, 1/52 suffices for the same final ceiling. -/
def taggedModerateMultiplier (b : Nat) : Nat :=
  if b = 2 then 64 else 52

private theorem tagged_ceiling_of_scaled
    (n a b W : Nat) (h : 3 * W ≤ 745 * n * (a + b)) :
    W ≤ taggedTripleCeiling n a b := by
  unfold taggedTripleCeiling
  omega

theorem tagged_short_rate_le_ceiling (n a b : Nat) :
    6 * n * (a + b) ≤ taggedTripleCeiling n a b := by
  have h : 3 * (6 * n * (a + b)) ≤ 745 * n * (a + b) := by
    rw [Nat.mul_assoc 6, Nat.mul_assoc 745]
    generalize n * (a + b) = X
    omega
  exact tagged_ceiling_of_scaled n a b _ h

theorem tagged_long_rate_le_ceiling (n a b : Nat) :
    112 * n * (a + b) ≤ taggedTripleCeiling n a b := by
  have h : 3 * (112 * n * (a + b)) ≤ 745 * n * (a + b) := by
    rw [Nat.mul_assoc 112, Nat.mul_assoc 745]
    generalize n * (a + b) = X
    omega
  exact tagged_ceiling_of_scaled n a b _ h

theorem tagged_moderate_rate_le_ceiling
    (n a b : Nat) (ha : 1 ≤ a) (hb : 2 ≤ b)
    (hab : a ≤ 2 * b) :
    3 * n * (a + b) +
      taggedModerateMultiplier b * n * (5 * a + 4 * b - 5) ≤
      taggedTripleCeiling n a b := by
  have hs :
      3 * (3 * (a + b) +
        taggedModerateMultiplier b * (5 * a + 4 * b - 5)) ≤
      745 * (a + b) := by
    by_cases he : b = 2
    · subst b
      simp only [taggedModerateMultiplier, ↓reduceIte]
      omega
    · have hthree : 3 ≤ b := by omega
      simp only [taggedModerateMultiplier, if_neg he]
      omega
  have hscale :
      3 * (3 * n * (a + b) +
        taggedModerateMultiplier b * n * (5 * a + 4 * b - 5)) =
      n * (3 * (3 * (a + b) +
        taggedModerateMultiplier b * (5 * a + 4 * b - 5))) := by
    simp only [Nat.mul_add, Nat.mul_assoc]
    ac_rfl
  have h :
      3 * (3 * n * (a + b) +
        taggedModerateMultiplier b * n * (5 * a + 4 * b - 5)) ≤
      745 * n * (a + b) := by
    calc
      _ = n * (3 * (3 * (a + b) +
            taggedModerateMultiplier b * (5 * a + 4 * b - 5))) := hscale
      _ ≤ n * (745 * (a + b)) := Nat.mul_le_mul_left n hs
      _ = 745 * n * (a + b) := by ac_rfl
  exact tagged_ceiling_of_scaled n a b _ h

/-- Real nativeE retry transfer from the existing renewal API.
The retry payload is the reached configuration; no fake reset is allowed.
The attempt-cost, failure mass, and simulation remain named premises. -/
theorem tagged_prepared_cost_of_retry_kernel {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    {A Seed : Type}
    (K : PPL.Convergence.LDLocal.RetryKernel A Seed n)
    (Rel : TripleNativeState n → A → Prop)
    (hsim : Prob.RetrySimulation K (nativeE ring)
      (TaggedDeleted i j k) Rel)
    (B num den : Nat) (hrho : num < den)
    (hcost : ∀ s, K.valid s → ∀ T,
      costNumerator (Prob.attemptStepper K)
        (fun q => Prob.attemptGood q ∨ Prob.attemptFail q)
        (.active (K.start s)) T ≤ n ^ T * B)
    (hfail : ∀ s, K.valid s → ∀ T,
      den * PPL.Convergence.LDLocal.retryCount K (.active (K.start s)) T ≤ num * n ^ T)
    (hentry : ∀ M : TripleNativeState n,
      TaggedPrepared ring i j a b M →
        ∃ s : Seed, K.valid s ∧ Rel M (K.start s))
    (M : TripleNativeState n)
    (hready : TaggedPrepared ring i j a b M) :
    ∀ T, costNumerator (nativeE ring)
      (TaggedDeleted i j k) M T ≤
        n ^ T * Prob.renewalCeiling B num den := by
  obtain ⟨s, hs, hrel⟩ := hentry M hready
  exact Prob.costNumerator_renewal_le
    (nativeE ring) (TaggedDeleted i j k) K Rel hsim
    B num den hrho hcost hfail M s hs hrel

/-- Conditional D.9 assembly. The single preparation hypothesis is a
3n(a+b) named input, not an unconditional consequence of SealedPrep.
The moderate, long and one-edge clocks are not proved here. -/
theorem tagged_deletion_cost_of_stage_bounds {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (htriple : TaggedTriple ring i j k a b N)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hprep : ∀ T,
      costNumerator (nativeE ring)
        (fun M => (TaggedTriple ring i j k a b M ∧
          TaggedPrepared ring i j a b M) ∨
          TaggedDeleted i j k M) N T ≤
        n ^ T * (3 * n * (a + b)))
    (hmoderate : 2 ≤ b → a ≤ 2 * b →
      ∀ M, TaggedTriple ring i j k a b M →
        TaggedPrepared ring i j a b M → ∀ T,
        costNumerator (nativeE ring) (TaggedDeleted i j k) M T ≤
        n ^ T * (taggedModerateMultiplier b * n *
          (5 * a + 4 * b - 5)))
    (hlong : 2 ≤ b → 2 * b + 1 ≤ a → ∀ T,
      costNumerator (nativeE ring) (TaggedDeleted i j k) N T ≤
        n ^ T * (112 * n * (a + b)))
    (hshort : b = 1 → ∀ T,
      costNumerator (nativeE ring) (TaggedDeleted i j k) N T ≤
        n ^ T * (6 * n * (a + b))) :
    ∀ T,
      costNumerator (nativeE ring) (TaggedDeleted i j k) N T ≤
        n ^ T * taggedTripleCeiling n a b := by
  intro T
  by_cases hone : b = 1
  · calc
      costNumerator (nativeE ring) (TaggedDeleted i j k) N T ≤
          n ^ T * (6 * n * (a + b)) := hshort hone T
      _ ≤ n ^ T * taggedTripleCeiling n a b :=
        Nat.mul_le_mul_left _ (tagged_short_rate_le_ceiling n a b)
  · have htwo : 2 ≤ b := by omega
    by_cases hmoder : a ≤ 2 * b
    · have hcombined := Prob.costNumerator_stage_le
        (nativeE ring) N
        (fun M => TaggedTriple ring i j k a b M ∧
          TaggedPrepared ring i j a b M) (TaggedDeleted i j k)
        (3 * n * (a + b))
        (taggedModerateMultiplier b * n * (5 * a + 4 * b - 5))
        hprep (fun M hM t =>
           hmoderate htwo hmoder M hM.1 hM.2 t)
      calc
        costNumerator (nativeE ring) (TaggedDeleted i j k) N T ≤
            n ^ T * (3 * n * (a + b) +
              taggedModerateMultiplier b * n *
                (5 * a + 4 * b - 5)) := hcombined T
        _ ≤ n ^ T * taggedTripleCeiling n a b :=
          Nat.mul_le_mul_left _
            (tagged_moderate_rate_le_ceiling n a b ha htwo hmoder)
    · have hlarge : 2 * b + 1 ≤ a := by omega
      calc
        costNumerator (nativeE ring) (TaggedDeleted i j k) N T ≤
            n ^ T * (112 * n * (a + b)) :=
          hlong htwo hlarge T
        _ ≤ n ^ T * taggedTripleCeiling n a b :=
          Nat.mul_le_mul_left _ (tagged_long_rate_le_ceiling n a b)

/-- Conditional first-deletion expectation with the Nat ceiling.
The sharp rational D.9 remains unestablished as a Lean theorem. -/
theorem tagged_deletion_expected_of_stage_bounds {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat) (N : TripleNativeState n)
    (htriple : TaggedTriple ring i j k a b N)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hprep : ∀ T,
      costNumerator (nativeE ring)
        (fun M => (TaggedTriple ring i j k a b M ∧
          TaggedPrepared ring i j a b M) ∨
          TaggedDeleted i j k M) N T ≤
        n ^ T * (3 * n * (a + b)))
    (hmoderate : 2 ≤ b → a ≤ 2 * b →
      ∀ M, TaggedTriple ring i j k a b M →
        TaggedPrepared ring i j a b M → ∀ T,
        costNumerator (nativeE ring) (TaggedDeleted i j k) M T ≤
        n ^ T * (taggedModerateMultiplier b * n *
          (5 * a + 4 * b - 5)))
    (hlong : 2 ≤ b → 2 * b + 1 ≤ a → ∀ T,
      costNumerator (nativeE ring) (TaggedDeleted i j k) N T ≤
        n ^ T * (112 * n * (a + b)))
    (hshort : b = 1 → ∀ T,
      costNumerator (nativeE ring) (TaggedDeleted i j k) N T ≤
        n ^ T * (6 * n * (a + b))) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (nativeE ring) (TaggedDeleted i j k) N
      ((taggedTripleCeiling n a b : Nat) : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (nativeE ring) (TaggedDeleted i j k)
    (by omega : 0 < n) N (taggedTripleCeiling n a b)).2
  exact tagged_deletion_cost_of_stage_bounds
    ring i j k a b N htriple ha hb
    hprep hmoderate hlong hshort

end L3


/-! ## Actual native-sector preparation stage composition

This section addresses the hprep obligation in lem:app-ld. The initial stage
reaches CleanReady(i) or tag deletion; the second reaches CleanReady(j)
or tag deletion, while Sealed(i) is maintained across all services.
All costs are physical nativeE costs on the same IID edge scheduler.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- A stage-one success retains the actual triple domain so that its
second-sector clock can be restarted at the physical first-hit cut. -/
private def TaggedFirstReady {n : Nat} (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat) (M : TripleNativeState n) : Prop :=
  TaggedTriple ring i j k a b M ∧ SealedCleanReady ring M i a

/-- Invariant-restricted target comparison. The invariant needs to
survive only edges which have not yet reached the LHS target. This
lemma is finite-horizon and does not use a future-defined last cut. -/
private theorem tagged_cost_invariant_target_le {S : Type} {n : Nat}
    (next : S → Fin n → S) (Inv Q R : S → Prop)
    (hstep : ∀ x, Inv x → ∀ e, ¬ Q (next x e) →
      Inv (next x e))
    (htarget : ∀ x, Inv x → R x → Q x) :
    ∀ x, Inv x → ∀ T,
      costNumerator next Q x T ≤ costNumerator next R x T := by
  classical
  have hmain : ∀ (T : Nat) (x : S), Inv x →
      costNumerator next Q x T ≤ costNumerator next R x T := by
    intro T
    induction T with
    | zero =>
        intro x hx
        simp only [costNumerator_zero]
        exact Nat.le_refl 0
    | succ T ih =>
        intro x hx
        by_cases hq : Q x
        · rw [costNumerator_terminal next Q x hq (T + 1)]
          exact Nat.zero_le _
        · have hr : ¬ R x := by
            intro hp
            exact hq (htarget x hx hp)
          rw [costNumerator_succ next Q x hq T,
            costNumerator_succ next R x hr T]
          have hs :
              (List.ofFn (fun e : Fin n =>
                costNumerator next Q (next x e) T)).sum ≤
              (List.ofFn (fun e : Fin n =>
                costNumerator next R (next x e) T)).sum := by
            apply ofFn_sum_le
            intro e
            by_cases hnext : Q (next x e)
            · cases T with
              | zero =>
                  simp only [costNumerator_zero]
                  exact Nat.le_refl 0
              | succ t =>
                  rw [costNumerator_terminal next Q (next x e)
                    hnext (t + 1)]
                  exact Nat.zero_le _
            · exact ih (next x e) (hstep x hx e hnext)
          exact Nat.add_le_add_left hs _
  intro x hx T
  exact hmain T x hx

/-- The proof of the sealed sector bound needs only three sites:
the native-domain stopping-cost identity has hypothesis
3 ≤ n, and both existing strict/weak row structures have
no five-site premise. On n≥5 use sealed_prep_expected directly;
on n=3,4 instantiate those same drift certificates. -/
private theorem tagged_sealed_prep_expected_three {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (x y : Fin n) (d : Nat)
    (hd : 0 < d) (hdn : d < n)
    (N : TripleNativeState n)
    (hP : P ring N)
    (hconsec : ConsecutiveNative ring N x y d) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (nativeE ring) (SealedPrepTarget ring x y d)
      N ((3 * n * d : Nat) : Rat) := by
  by_cases hfive : 5 ≤ n
  · exact sealed_prep_expected hfive ring x y d
      hd hdn N hP hconsec
  · classical
    let rank : TripleNativeState n → Nat :=
      sealed_prep_minimum_rank ring x y d hd hdn
    let choose : TripleNativeState n → Fin n :=
      sealed_prep_minimum_choose ring x y d hd hdn
    have hcap : ∀ M, rank M ≤ 3 * d := by
      intro M
      exact sealed_prep_potential_cap d
        (M, sealed_prep_best_mode ring x y d hd hdn M)
    have hdropStop : ∀ M,
        ¬ SealedPrepNativeStop ring x y d M →
        rank (nativeE ring M (choose M)) + 1 ≤ rank M := by
      intro M hstop
      have hgood : SealedPrepNativeDomain ring x y d M := by
        by_cases hg : SealedPrepNativeDomain ring x y d M
        · exact hg
        · exact False.elim (hstop (Or.inr hg))
      have hnot : ¬ SealedPrepTarget ring x y d M := by
        intro ht
        exact hstop (Or.inl ht)
      obtain ⟨mode, hv, hstrict⟩ :=
        sealed_prep_hdrop_of_cases ring x y d hd hdn
          (sealed_prep_strict_cases ring x y d) M hgood hnot
      have hbest := sealed_prep_minimum_rank_le_of_witness
        ring x y d hd hdn
        (nativeE ring M (choose M)) mode hv
      dsimp only [rank, choose] at *
      omega
    have hmonoStop : ∀ M,
        ¬ SealedPrepNativeStop ring x y d M →
        ∀ e, rank (nativeE ring M e) ≤ rank M := by
      intro M hstop e
      have hgood : SealedPrepNativeDomain ring x y d M := by
        by_cases hg : SealedPrepNativeDomain ring x y d M
        · exact hg
        · exact False.elim (hstop (Or.inr hg))
      have hnot : ¬ SealedPrepTarget ring x y d M := by
        intro ht
        exact hstop (Or.inl ht)
      obtain ⟨mode, hv, hle⟩ :=
        sealed_prep_hnoninc_of_cases ring x y d hd hdn
          (sealed_prep_strict_cases ring x y d)
          (sealed_prep_weak_cases ring x y d)
          M hgood hnot e
      have hbest := sealed_prep_minimum_rank_le_of_witness
        ring x y d hd hdn (nativeE ring M e) mode hv
      dsimp only [rank] at *
      omega
    apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (nativeE ring) (SealedPrepTarget ring x y d)
      (by omega : 0 < n) N (3 * n * d)).2
    intro T
    have hword := Prob.costNumerator_le_of_nominated_edge
      (nativeE ring) (SealedPrepNativeStop ring x y d)
      rank choose hdropStop hmonoStop N T
    calc
      costNumerator (nativeE ring)
          (SealedPrepTarget ring x y d) N T =
        costNumerator (nativeE ring)
          (SealedPrepNativeStop ring x y d) N T :=
          (sealed_prep_native_stop_cost_eq hn ring x y d
            T N ⟨hP, hconsec⟩).symm
      _ ≤ n ^ T * (n * rank N) := hword
      _ ≤ n ^ T * (n * (3 * d)) :=
        Nat.mul_le_mul_left (n ^ T)
          (Nat.mul_le_mul_left n (hcap N))
      _ = n ^ T * (3 * n * d) := by ac_rfl

/-- Stage one: prepare the attacker i→j, stopping also when any
tagged leader is deleted. In the surviving first-hit branch the
original triple domain is an actual invariant, not an assumption
placed on arbitrary restarted configurations. -/
private theorem tagged_prep_first_stage_cost {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (htriple : TaggedTriple ring i j k a b N) :
    ∀ T,
      costNumerator (nativeE ring)
        (fun M => TaggedFirstReady ring i j k a b M ∨
          (TaggedPrepared ring i j a b M ∨ TaggedDeleted i j k M))
        N T ≤ n ^ T * (3 * n * a) := by
  have hconsec : ConsecutiveNative ring N i j a := htriple.2.1
  have ha : 0 < a := hconsec.1
  have han : a < n := hconsec.2.1
  have hclosed :
      ∀ M : TripleNativeState n,
        TaggedTriple ring i j k a b M → ∀ e,
        ¬ (TaggedFirstReady ring i j k a b
             (nativeE ring M e) ∨
           (TaggedPrepared ring i j a b (nativeE ring M e) ∨
             TaggedDeleted i j k (nativeE ring M e))) →
        TaggedTriple ring i j k a b (nativeE ring M e) := by
    intro M hgood e hnot
    have hnodelete : ¬ TaggedDeleted i j k (nativeE ring M e) := by
      intro hdel
      exact hnot (Or.inr (Or.inr hdel))
    exact tagged_triple_step_of_survival hn ring
      i j k a b M e hgood hnodelete
  have htarget :
      ∀ M : TripleNativeState n,
        TaggedTriple ring i j k a b M →
        SealedPrepTarget ring i j a M →
        TaggedFirstReady ring i j k a b M ∨
          (TaggedPrepared ring i j a b M ∨
            TaggedDeleted i j k M) := by
    intro M hgood hprep
    change (M i).l = false ∨ (M j).l = false ∨
      SealedCleanReady ring M i a at hprep
    rcases hprep with hi | hj | hready
    · exact Or.inr (Or.inr (Or.inl hi))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hj)))
    · exact Or.inl ⟨hgood, hready⟩
  have hmonotone := tagged_cost_invariant_target_le
    (nativeE ring)
    (TaggedTriple ring i j k a b)
    (fun M => TaggedFirstReady ring i j k a b M ∨
      (TaggedPrepared ring i j a b M ∨ TaggedDeleted i j k M))
    (SealedPrepTarget ring i j a)
    hclosed htarget N htriple
  have hclock :=
    (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (nativeE ring) (SealedPrepTarget ring i j a)
      (by omega : 0 < n) N (3 * n * a)).1
      (tagged_sealed_prep_expected_three
        hn ring i j a ha han N htriple.1 hconsec)
  intro T
  exact Nat.le_trans (hmonotone T) (hclock T)

/-- Stage two: the first sector need not remain Ready, but its
Sealed invariant is closed under every actual native edge until
a tagged deletion. The second sector's P and consecutiveness also
survive these same edges. -/
private theorem tagged_prep_second_stage_cost {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (M : TripleNativeState n)
    (hfirst : TaggedFirstReady ring i j k a b M) :
    ∀ T,
      costNumerator (nativeE ring)
        (fun W => TaggedPrepared ring i j a b W ∨ TaggedDeleted i j k W)
        M T ≤ n ^ T * (3 * n * b) := by
  have htriple : TaggedTriple ring i j k a b M := hfirst.1
  have hsealed : Sealed ring M i a :=
    sealed_of_clean_ready ring M i a hfirst.2
  have hinv : TaggedTriple ring i j k a b M ∧
      Sealed ring M i a := ⟨htriple, hsealed⟩
  have hclosed :
      ∀ W : TripleNativeState n,
        (TaggedTriple ring i j k a b W ∧ Sealed ring W i a) →
        ∀ e, ¬ (TaggedPrepared ring i j a b (nativeE ring W e) ∨
                   TaggedDeleted i j k (nativeE ring W e)) →
        TaggedTriple ring i j k a b (nativeE ring W e) ∧
          Sealed ring (nativeE ring W e) i a := by
    intro W hgood e hnot
    have hnodelete : ¬ TaggedDeleted i j k (nativeE ring W e) := by
      intro hd
      exact hnot (Or.inr hd)
    have hnext : TaggedTriple ring i j k a b
        (nativeE ring W e) :=
      tagged_triple_step_of_survival hn ring
        i j k a b W e hgood.1 hnodelete
    have hleft : Sealed ring (nativeE ring W e) i a := by
      rcases sealed_all_edge_closed ring W i j a e
        hgood.1.2.1 hgood.2 with hi | hj | hs
      · exact False.elim (hnodelete (Or.inl hi))
      · exact False.elim (hnodelete (Or.inr (Or.inl hj)))
      · exact hs
    exact ⟨hnext, hleft⟩
  have htarget :
      ∀ W : TripleNativeState n,
        (TaggedTriple ring i j k a b W ∧ Sealed ring W i a) →
        SealedPrepTarget ring j k b W →
        TaggedPrepared ring i j a b W ∨ TaggedDeleted i j k W := by
    intro W hgood hprep
    change (W j).l = false ∨ (W k).l = false ∨
      SealedCleanReady ring W j b at hprep
    rcases hprep with hj | hk | hready
    · exact Or.inr (Or.inr (Or.inl hj))
    · exact Or.inr (Or.inr (Or.inr hk))
    · exact Or.inl ⟨hgood.2, hready⟩
  have hmonotone := tagged_cost_invariant_target_le
    (nativeE ring)
    (fun W => TaggedTriple ring i j k a b W ∧ Sealed ring W i a)
    (fun W => TaggedPrepared ring i j a b W ∨ TaggedDeleted i j k W)
    (SealedPrepTarget ring j k b)
    hclosed htarget M hinv
  have hconsec : ConsecutiveNative ring M j k b := htriple.2.2
  have hb : 0 < b := hconsec.1
  have hbn : b < n := hconsec.2.1
  have hclock :=
    (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (nativeE ring) (SealedPrepTarget ring j k b)
      (by omega : 0 < n) M (3 * n * b)).1
      (tagged_sealed_prep_expected_three
        hn ring j k b hb hbn M htriple.1 hconsec)
  intro T
  exact Nat.le_trans (hmonotone T) (hclock T)

/-- The previously conditional hprep for every peaceful tagged
triple, including two-leader i=k and rings n=3,4. Each sector is
charged once and both stages share the same physical scheduler. -/
theorem tagged_deletion_prep_cost {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (htriple : TaggedTriple ring i j k a b N) :
    ∀ T,
      costNumerator (nativeE ring)
        (fun M => TaggedPrepared ring i j a b M ∨
          TaggedDeleted i j k M) N T ≤
        n ^ T * (3 * n * (a + b)) := by
  have hfirst := tagged_prep_first_stage_cost
    hn ring i j k a b N htriple
  have hsecond :
      ∀ M : TripleNativeState n,
        TaggedFirstReady ring i j k a b M → ∀ T,
        costNumerator (nativeE ring)
          (fun W => TaggedPrepared ring i j a b W ∨
            TaggedDeleted i j k W) M T ≤
          n ^ T * (3 * n * b) := by
    intro M hready
    exact tagged_prep_second_stage_cost
      hn ring i j k a b M hready
  have hcombined := Prob.costNumerator_stage_le
    (nativeE ring) N
    (TaggedFirstReady ring i j k a b)
    (fun M => TaggedPrepared ring i j a b M ∨ TaggedDeleted i j k M)
    (3 * n * a) (3 * n * b)
    hfirst hsecond
  intro T
  calc
    costNumerator (nativeE ring)
        (fun M => TaggedPrepared ring i j a b M ∨
          TaggedDeleted i j k M) N T ≤
      n ^ T * (3 * n * a + 3 * n * b) := hcombined T
    _ = n ^ T * (3 * n * (a + b)) := by rw [Nat.mul_add (3 * n) a b]


/-- Physical preparation retains the tagged triple, including at
the surviving moderate entrance. No arbitrary Prepared-state reset. -/
theorem tagged_deletion_prep_cost_triple {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (htriple : TaggedTriple ring i j k a b N) :
    ∀ T,
      costNumerator (nativeE ring)
        (fun M => (TaggedTriple ring i j k a b M ∧
          TaggedPrepared ring i j a b M) ∨
          TaggedDeleted i j k M) N T ≤
      n ^ T * (3 * n * (a + b)) := by
  have hclosed :
      ∀ M : TripleNativeState n,
        TaggedTriple ring i j k a b M → ∀ e,
          ¬ ((TaggedTriple ring i j k a b (nativeE ring M e) ∧
                TaggedPrepared ring i j a b (nativeE ring M e)) ∨
              TaggedDeleted i j k (nativeE ring M e)) →
          TaggedTriple ring i j k a b (nativeE ring M e) := by
    intro M hgood e hnot
    have hsurvive :
        ¬ TaggedDeleted i j k (nativeE ring M e) := by
      intro hdel
      exact hnot (Or.inr hdel)
    exact tagged_triple_step_of_survival hn ring
      i j k a b M e hgood hsurvive
  have htarget :
      ∀ M : TripleNativeState n,
        TaggedTriple ring i j k a b M →
        (TaggedPrepared ring i j a b M ∨
          TaggedDeleted i j k M) →
        (TaggedTriple ring i j k a b M ∧
          TaggedPrepared ring i j a b M) ∨
          TaggedDeleted i j k M := by
    intro M hgood hh
    rcases hh with hp | hd
    · exact Or.inl ⟨hgood, hp⟩
    · exact Or.inr hd
  have hcompare := tagged_cost_invariant_target_le
    (nativeE ring)
    (TaggedTriple ring i j k a b)
    (fun M => (TaggedTriple ring i j k a b M ∧
      TaggedPrepared ring i j a b M) ∨
      TaggedDeleted i j k M)
    (fun M => TaggedPrepared ring i j a b M ∨
      TaggedDeleted i j k M)
    hclosed htarget N htriple
  intro T
  exact Nat.le_trans (hcompare T)
    (tagged_deletion_prep_cost hn ring i j k a b N htriple T)

/-- The original conditional D.9 result with only the independent
moderate/long/short clocks remaining as parameters. The hprep
hypothesis has been discharged by tagged_deletion_prep_cost. -/
theorem tagged_deletion_expected_without_prep {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat) (N : TripleNativeState n)
    (htriple : TaggedTriple ring i j k a b N)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hmoderate : 2 ≤ b → a ≤ 2 * b →
      ∀ M, TaggedTriple ring i j k a b M →
        TaggedPrepared ring i j a b M → ∀ T,
        costNumerator (nativeE ring) (TaggedDeleted i j k) M T ≤
        n ^ T * (taggedModerateMultiplier b * n *
          (5 * a + 4 * b - 5)))
    (hlong : 2 ≤ b → 2 * b + 1 ≤ a → ∀ T,
      costNumerator (nativeE ring) (TaggedDeleted i j k) N T ≤
        n ^ T * (112 * n * (a + b)))
    (hshort : b = 1 → ∀ T,
      costNumerator (nativeE ring) (TaggedDeleted i j k) N T ≤
        n ^ T * (6 * n * (a + b))) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (nativeE ring) (TaggedDeleted i j k) N
      ((taggedTripleCeiling n a b : Nat) : Rat) := by
  exact tagged_deletion_expected_of_stage_bounds
    hn ring i j k a b N htriple ha hb
    (tagged_deletion_prep_cost_triple hn ring i j k a b N htriple)
    hmoderate hlong hshort

end L3


/-! ## Clean incoming dummy and the D.11 edgewise obstruction

The actual nativeE row yields clean Dummy(0) OR tagged deletion.
The requested edgewise monotonicity of D.11 is false, even for a
peaceful paired-sealed state; D.12 is an aggregate drift inequality.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- A ready responder fires unshielded, even when it is deleted
by a simultaneous incoming live bullet. -/
theorem tagged_incoming_ready_shield_row
    (x y : CertNative) (hyl : y.l = true) (hys : y.sg = true) :
    (certLiteralEPair x y).2.sh = false := by
  rcases x with ⟨xl, xb, xsh, xsg⟩
  cases xl <;> cases xsg <;>
    simp [certLiteralEPair, hyl, hys]

/-- Exact literal OLD-pair row. The deleting alternative is essential. -/
theorem tagged_incoming_ready_dummy_row
    (x y : CertNative) (hyl : y.l = true) (hys : y.sg = true) :
    (certLiteralEPair x y).2.l = false ∨
      ((certLiteralEPair x y).2.b = (1 : Fin 3) ∧
       (certLiteralEPair x y).2.sh = false ∧
       (certLiteralEPair x y).2.sg = false) := by
  rcases sealed_prep_incoming_ready_row x y hyl hys with
    hdead | ⟨hsig, hbullet⟩
  · exact Or.inl hdead
  · exact Or.inr ⟨hbullet,
      tagged_incoming_ready_shield_row x y hyl hys, hsig⟩

/-- Within a sealed sector, a bullet of value 1 at its head forces
the exact phase Dummy(0), including its zero shield and signal. -/
theorem tagged_dummy_zero_of_sealed_head {n : Nat}
    (ring : DirectedRing n) (M : TripleNativeState n)
    (j : Fin n) (b : Nat) (hbpos : 0 < b)
    (hsealed : Sealed ring M j b)
    (hhead : (M j).b = (1 : Fin 3)) :
    SealedPhaseHolds ring M j b (.dummy (sealedZero ring)) := by
  have hzero : (sealedZero ring).val < b := by
    dsimp [sealedZero]
    omega
  have hnotzero : (1 : Fin 3) ≠ 0 := by decide
  have hnottwo : (1 : Fin 3) ≠ 2 := by decide
  obtain ⟨phase, hphase⟩ := hsealed
  cases phase with
  | ready =>
      have hz := hphase.2 (sealedZero ring) hzero
      rw [sealedAt_zero, hhead] at hz
      exact False.elim (hnotzero hz)
  | dummy p =>
      by_cases hpz : p = sealedZero ring
      · simpa only [hpz] using hphase
      · have hz := hphase.1.2.2 (sealedZero ring)
          hzero (Ne.symm hpz)
        rw [sealedAt_zero, hhead] at hz
        exact False.elim (hnotzero hz)
  | live p =>
      by_cases hpz : p = sealedZero ring
      · have hz := hphase.1.2.1
        rw [hpz, sealedAt_zero, hhead] at hz
        exact False.elim (hnottwo hz)
      · have hz := hphase.1.2.2 (sealedZero ring)
          hzero (Ne.symm hpz)
        rw [sealedAt_zero, hhead] at hz
        exact False.elim (hnotzero hz)
  | returning q =>
      have hz := hphase.1 (sealedZero ring) hzero
      rw [sealedAt_zero, hhead] at hz
      exact False.elim (hnotzero hz)

/-- Physical incoming edge e -> j. On survival, SealedClose gives
the target's genuine sealed successor and the head row identifies
it as Dummy(0). No ghost native update or artificial reset occurs. -/
theorem tagged_prepared_incoming_dummy_actual {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n)
    (a b : Nat) (N : TripleNativeState n)
    (e : Fin n) (hne : e ≠ j)
    (hnext : ring.rightNeighbor e = j)
    (htriple : TaggedTriple ring i j k a b N)
    (hprep : TaggedPrepared ring i j a b N) :
    TaggedDeleted i j k (nativeE ring N e) ∨
      TaggedCleanDummy ring i j a b (nativeE ring N e) := by
  let M := nativeE ring N e
  by_cases hdelete : TaggedDeleted i j k M
  · exact Or.inl hdelete
  · have hjl : (N j).l = true := htriple.2.2.2.2.2.1
    have hjs : (N j).sg = true :=
      ((sealedCleanReady_iff ring N j b).1 hprep.2).1
    have hrow :=
      tagged_incoming_ready_dummy_row (N e) (N j) hjl hjs
    have hpair : M j = (certLiteralEPair (N e) (N j)).2 := by
      dsimp [M]
      simp [nativeE, hnext, Ne.symm hne]
    rcases hrow with hdead | ⟨hbullet, _hshield, _hsignal⟩
    · have hd : (M j).l = false := by
        rw [hpair]
        exact hdead
      exact False.elim (hdelete (Or.inr (Or.inl hd)))
    · have hb : (M j).b = (1 : Fin 3) := by
        rw [hpair]
        exact hbullet
      have hs : TaggedSealed ring i j a b M :=
        tagged_sealed_step_of_survival
          ring i j k a b N e htriple
          (tagged_prepared_sealed ring i j a b N hprep)
          hdelete
      have hbpos : 0 < b := by
        have hc : ConsecutiveNative ring N j k b := htriple.2.2
        have hbc : 1 ≤ b := hc.1
        omega
      exact Or.inr ⟨hs.1,
        tagged_dummy_zero_of_sealed_head ring M j b hbpos hs.2 hb⟩

/-- The actual predecessor's clockwise edge enters j, including wraparound. -/
private theorem tagged_right_of_left {n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n) (j : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor j) = j := by
  apply Fin.ext
  change (((j.val + n - 1) % n + 1) % n) = j.val
  by_cases hz : j.val = 0
  · rw [hz]
    simp only [Nat.zero_add]
    rw [Nat.mod_eq_of_lt (by omega : n - 1 < n)]
    have he : n - 1 + 1 = n := by omega
    rw [he, Nat.mod_self]
  · have he : j.val + n - 1 = n + (j.val - 1) := by omega
    rw [he, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega : j.val - 1 < n)]
    have hs : j.val - 1 + 1 = j.val := by omega
    rw [hs, Nat.mod_eq_of_lt j.isLt]

/-- Under Q, a raw outgoing letter at a ready target is the ACTUAL
incoming nativeE service, hence creates Dummy(0) or deletion. -/
theorem tagged_controlled_ready_dummy_actual {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n)
    (a b : Nat) (N : TripleNativeState n)
    (hn : 2 ≤ n) (hports : ring.leftNeighbor j ≠ j)
    (htriple : TaggedTriple ring i j k a b N)
    (hprep : TaggedPrepared ring i j a b N) :
    TaggedDeleted i j k
      (nativeE ring N
        ((taggedRedirection ring j b hn hports).effective N j)) ∨
      TaggedCleanDummy ring i j a b
        (nativeE ring N
          ((taggedRedirection ring j b hn hports).effective N j)) := by
  classical
  have hactual := tagged_prepared_incoming_dummy_actual
    ring i j k a b N (ring.leftNeighbor j)
    hports (tagged_right_of_left hn ring j) htriple hprep
  have heffective :=
    tagged_redirection_ready_right ring j b hn hports N hprep.2
  simpa only [heffective] using hactual

/-! The paper's D.11 Bellman potential. This is different from the
SealedPhaseProgress quota used in SealedClose. -/

def taggedAttackerBellman {n : Nat}
    (population a : Nat) : SealedPhase n → Nat
  | .ready => population * (3 * a - 1)
  | .live p => population * (a - p.val)
  | .dummy p =>
      population * ((2 * a - p.val - 1) + (3 * a - 1))
  | .returning q => population * (q.val + 3 * a - 1)

/-- D.11 has the stated maximum n(5a-2) on valid phases. -/
theorem tagged_attacker_bellman_cap {n : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (i : Fin n) (a : Nat) (ha : 1 ≤ a)
    (phase : SealedPhase n)
    (hphase : SealedPhaseHolds ring N i a phase) :
    taggedAttackerBellman n a phase ≤ n * (5 * a - 2) := by
  cases phase with
  | ready =>
      simp only [taggedAttackerBellman]
      exact Nat.mul_le_mul_left n (by omega)
  | live p =>
      have hp : p.val < a := hphase.1.1
      simp only [taggedAttackerBellman]
      exact Nat.mul_le_mul_left n (by omega)
  | dummy p =>
      have hp : p.val < a := hphase.1.1
      simp only [taggedAttackerBellman]
      exact Nat.mul_le_mul_left n (by omega)
  | returning q =>
      have hq : q.val < a := hphase.2.2.2.1
      simp only [taggedAttackerBellman]
      exact Nat.mul_le_mul_left n (by omega)

/-- Genuine nonready progress from SealedClose. Weak on every edge,
strict on the phase's nominated edge, up to a tagged deletion.
This applies to SealedPhaseProgress, not D.11's Bellman potential. -/
theorem tagged_nonready_attacker_progress_actual {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n)
    (a b : Nat) (N : TripleNativeState n) (e : Fin n)
    (htriple : TaggedTriple ring i j k a b N)
    (phase : SealedPhase n)
    (hphase : SealedPhaseHolds ring N i a phase)
    (hnonready : phase ≠ .ready)
    (hnotdel : ¬ TaggedDeleted i j k (nativeE ring N e)) :
    ∃ nextPhase : SealedPhase n,
      SealedPhaseHolds ring (nativeE ring N e) i a nextPhase ∧
      SealedPhaseProgress a nextPhase ≤ SealedPhaseProgress a phase ∧
      (e = SealedPhaseEdge ring i phase →
        SealedPhaseProgress a nextPhase + 1 ≤
          SealedPhaseProgress a phase) := by
  have hi : (nativeE ring N e i).l = true := by
    cases hx : (nativeE ring N e i).l with
    | false => exact False.elim (hnotdel (Or.inl hx))
    | true => rfl
  have hj : (nativeE ring N e j).l = true := by
    cases hx : (nativeE ring N e j).l with
    | false => exact False.elim (hnotdel (Or.inr (Or.inl hx)))
    | true => rfl
  obtain ⟨q, hq, hprogress⟩ :=
    sealed_close_step_with_progress ring N i j a e phase
      htriple.2.1 hphase hi hj
  exact ⟨q, hq, (hprogress hnonready).1, (hprogress hnonready).2⟩

/-! The n=5 edgewise Bellman counterexample of the D.11 obstruction (leaders 0,2,4, a=b=2, edge 4->0, V 25 -> 40) is recorded in PROGRESS.md; its finite certificate needed Decidable instances that the predicates lack, so it is not compiled here. -/

end L3


/-! ## D.12 summed-drift adversarial certificate

The paper's rate-level Ready compensation is correct.  However, D.12
cannot be quantified over ALL peaceful paired-sealed states without
the extra post-clean-dummy invariant that the target j is unshielded
(and has not performed a live launch).  A literal five-site nativeE
row with both sectors Live(1) defeats the proposed global summed drift.
The bad row is untouched by the Q scheduler because target B is
non-Ready.  This is not an exhibited execution from the paper's
initial Dummy(0); it isolates the extra domain obligation.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- D.11--D.12, the exact arithmetic that compensates a Ready
attacker's incoming dummy by the outgoing live launch.
This is a rate identity; it is not yet a physical Bellman theorem. -/
theorem tagged_ready_two_edge_balance (a : Nat) (ha : 1 ≤ a) :
    1 + (a - 1) + ((2 * a - 1) + (3 * a - 1)) =
      2 * (3 * a - 1) := by
  omega

/-- The corresponding identity after multiplication by the
population size. Both sides are the two distinguished edge values
plus the one-step Bellman cost n. -/
theorem tagged_ready_two_edge_balance_scaled
    (n a : Nat) (ha : 1 ≤ a) :
    n + n * (a - 1) + n * ((2 * a - 1) + (3 * a - 1)) =
      n * (3 * a - 1) + n * (3 * a - 1) := by
  calc
    n + n * (a - 1) + n * ((2 * a - 1) + (3 * a - 1)) =
        n * (1 + (a - 1) + ((2 * a - 1) + (3 * a - 1))) := by
          simp only [Nat.mul_add, Nat.mul_one]
          try ac_rfl
    _ = n * (2 * (3 * a - 1)) := by
          rw [tagged_ready_two_edge_balance a ha]
    _ = n * (3 * a - 1) + n * (3 * a - 1) := by
          have hh : 2 * (3 * a - 1) =
              (3 * a - 1) + (3 * a - 1) := by omega
          rw [hh, Nat.mul_add]

/-- The literal OLD native pair that causes the obstruction:
a live bullet arrives at a non-Ready, shielded leader.
The bullet is consumed, the leader survives, and the initiator
receives the new return signal. -/
theorem tagged_live_into_shielded_leader_row :
    (certLiteralEPair
      ({ l := false, b := 2, sh := false, sg := false } : CertNative)
      ({ l := true, b := 0, sh := true, sg := false } : CertNative)).2.l =
        true ∧
    (certLiteralEPair
      ({ l := false, b := 2, sh := false, sg := false } : CertNative)
      ({ l := true, b := 0, sh := true, sg := false } : CertNative)).1.b =
        (0 : Fin 3) ∧
    (certLiteralEPair
      ({ l := false, b := 2, sh := false, sg := false } : CertNative)
      ({ l := true, b := 0, sh := true, sg := false } : CertNative)).1.sg =
        true := by
  decide +kernel

private def taggedD12BadRing : DirectedRing 5 := ⟨by decide⟩
private def taggedD12BadI : Fin 5 := ⟨0, by decide⟩
private def taggedD12BadJ : Fin 5 := ⟨2, by decide⟩
private def taggedD12BadK : Fin 5 := ⟨4, by decide⟩
private def taggedD12BadEdge : Fin 5 := ⟨1, by decide⟩

/-- Physical ring order:
0 leader (shielded, no signal), 1 live bullet,
2 leader (shielded, no signal), 3 live bullet,
4 leader (shielded, no signal).
Both tagged sectors have gap 2 and are Live(1).
All live bullets have a shielded nearest-left leader and a zero trail. -/
private def taggedD12BadState : TripleNativeState 5 :=
  fun z =>
    if z.val = 0 then
      { l := true, b := 0, sh := true, sg := false }
    else if z.val = 1 then
      { l := false, b := 2, sh := false, sg := false }
    else if z.val = 2 then
      { l := true, b := 0, sh := true, sg := false }
    else if z.val = 3 then
      { l := false, b := 2, sh := false, sg := false }
    else
      { l := true, b := 0, sh := true, sg := false }

/-- The input is an actual peaceful tagged triple and both sectors
are sealed. To make the finite decision procedures visible, unfold
the named predicates rather than ask typeclass search to synthesize
Decidable instances for the opaque wrapper definitions. -/
theorem tagged_d12_bad_paired_sealed :
    TaggedTriple taggedD12BadRing
      taggedD12BadI taggedD12BadJ taggedD12BadK
      2 2 taggedD12BadState ∧
    TaggedSealed taggedD12BadRing
      taggedD12BadI taggedD12BadJ 2 2 taggedD12BadState := by
  constructor
  · unfold TaggedTriple
    refine ⟨?_, ?_, ?_⟩
    · unfold P PeacefulBullet LiveBullet
      decide +kernel
    · unfold ConsecutiveNative
      decide +kernel
    · unfold ConsecutiveNative
      decide +kernel
  · constructor
    · refine ⟨.live (1 : Fin 5), ?_⟩
      unfold SealedPhaseHolds SealedUniqueBullet SealedZeroTrail
      decide +kernel
    · refine ⟨.live (1 : Fin 5), ?_⟩
      unfold SealedPhaseHolds SealedUniqueBullet SealedZeroTrail
      decide +kernel

/-- The target is non-Ready, so the Q gate is closed. -/
private theorem tagged_d12_bad_not_target_ready :
    ¬ SealedCleanReady taggedD12BadRing taggedD12BadState
      taggedD12BadJ 2 := by
  intro h
  have hs : (taggedD12BadState taggedD12BadJ).sg = true :=
    ((sealedCleanReady_iff taggedD12BadRing
      taggedD12BadState taggedD12BadJ 2).1 h).1
  have hf : (taggedD12BadState taggedD12BadJ).sg = false := by
    decide +kernel
  rw [hf] at hs
  cases hs

/-- The auxiliary controlled scheduler is the original tagged
redirection from TripleDeletion: no replacement native row. -/
private noncomputable def taggedD12BadRedirect :
    ControlledSchedulerMass.Redirection (TripleNativeState 5) 5 :=
  taggedRedirection taggedD12BadRing taggedD12BadJ 2
    (by decide +kernel) (by decide +kernel)

private noncomputable def taggedD12BadQ
    (M : TripleNativeState 5) (e : Fin 5) : TripleNativeState 5 :=
  nativeE taggedD12BadRing M (taggedD12BadRedirect.effective M e)

private theorem tagged_d12_bad_gate_closed :
    taggedD12BadRedirect.gate taggedD12BadState = false := by
  classical
  simp [taggedD12BadRedirect, taggedRedirection,
    tagged_d12_bad_not_target_ready]

/-- The problematic edge is untouched by Q because target B is
non-Ready. This is an actual edge 1 -> 2. -/
theorem tagged_d12_bad_q_edge :
    taggedD12BadQ taggedD12BadState taggedD12BadEdge =
      nativeE taggedD12BadRing taggedD12BadState taggedD12BadEdge := by
  unfold taggedD12BadQ
  rw [ControlledSchedulerMass.Redirection.effective_of_gate_false
    taggedD12BadRedirect taggedD12BadState
    tagged_d12_bad_gate_closed taggedD12BadEdge]

/-- On the selected actual edge no leader 0,2,4 is deleted. -/
theorem tagged_d12_bad_edge_survives :
    ¬ TaggedDeleted taggedD12BadI taggedD12BadJ taggedD12BadK
      (taggedD12BadQ taggedD12BadState taggedD12BadEdge) := by
  rw [tagged_d12_bad_q_edge]
  unfold TaggedDeleted
  decide +kernel

/-- Exactly the two paper phase descriptions involved in the bad
edge: Live(1) becomes Return(1), NOT terminal deletion. -/
theorem tagged_d12_bad_phase_change :
    SealedPhaseHolds taggedD12BadRing taggedD12BadState
      taggedD12BadI 2 (.live (1 : Fin 5)) ∧
    SealedPhaseHolds taggedD12BadRing
      (taggedD12BadQ taggedD12BadState taggedD12BadEdge)
      taggedD12BadI 2 (.returning (1 : Fin 5)) := by
  constructor
  · unfold SealedPhaseHolds SealedUniqueBullet SealedZeroTrail
    decide +kernel
  · rw [tagged_d12_bad_q_edge]
    unfold SealedPhaseHolds SealedNoBullet SealedFirstSignal
    decide +kernel

/-- Core-only elementary fact: a natural summand never exceeds
the sum of a finite list containing it. -/
private theorem tagged_nat_le_sum_member
    {x : Nat} {xs : List Nat} (h : x ∈ xs) :
    x ≤ xs.sum := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
      simp only [List.mem_cons] at h
      rcases h with rfl | ht
      · simp
      · have hle := ih ht
        simp only [List.sum_cons]
        omega

/-- No potential agreeing with paper D.11 on these two real sealed
phases can satisfy D.12 at this input. The proof uses only the
single edge 1 -> 2: it has successor potential 30 > 5*5 = 25,
while the other four Nat summands are necessarily nonnegative.
Here Terminal is precisely TaggedDeleted, which is false at the
input and the nominated successor. -/
theorem tagged_d12_bad_for_every_paper_potential
    (V : TripleNativeState 5 → Nat)
    (hbefore : V taggedD12BadState =
      taggedAttackerBellman 5 2 (.live (1 : Fin 5)))
    (hafter :
      V (taggedD12BadQ taggedD12BadState taggedD12BadEdge) =
        taggedAttackerBellman 5 2 (.returning (1 : Fin 5))) :
    ¬ (5 + (List.ofFn (fun e : Fin 5 =>
      V (taggedD12BadQ taggedD12BadState e))).sum ≤
        5 * V taggedD12BadState) := by
  let xs : List Nat :=
    List.ofFn (fun e : Fin 5 =>
      V (taggedD12BadQ taggedD12BadState e))
  have hm :
      V (taggedD12BadQ taggedD12BadState taggedD12BadEdge) ∈ xs := by
    change V (taggedD12BadQ taggedD12BadState taggedD12BadEdge) ∈
      List.ofFn (fun e : Fin 5 =>
        V (taggedD12BadQ taggedD12BadState e))
    exact List.mem_ofFn.mpr ⟨taggedD12BadEdge, rfl⟩
  have hsum :
      V (taggedD12BadQ taggedD12BadState taggedD12BadEdge) ≤
        (List.ofFn (fun e : Fin 5 =>
          V (taggedD12BadQ taggedD12BadState e))).sum :=
    tagged_nat_le_sum_member hm
  have hstrict :
      5 * V taggedD12BadState <
        V (taggedD12BadQ taggedD12BadState taggedD12BadEdge) := by
    rw [hbefore, hafter]
    decide +kernel
  intro hbellman
  omega

/-! The decoded field potential of the D.12 certificate (taggedD12BadFieldPotential) was not kept: its value lemmas used decide on a noncomputable phase extraction. The obstruction itself is tagged_d12_bad_for_every_paper_potential above. -/

end L3


/-! ## Inductive stopped Q-domain and paper-domain invariants

This section treats the actual
Q-controlled nativeE step, not the unrestricted paired-sealed domain
refuted by the D.12 certificate above. D.12's physical drift remains a separate
unsolved obligation. The generic restricted Bellman transfer below
does not assume drift outside the inductively reached states.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

attribute [local instance low] Classical.propDecidable

/-! ### Exact physical Q and its stopped transition -/

/-- One raw Q letter is interpreted by the original redirection. -/
noncomputable def taggedQEffective {n : Nat}
    (ring : DirectedRing n) (j : Fin n) (b : Nat)
    (hn : 2 ≤ n) (hports : ring.leftNeighbor j ≠ j)
    (N : TripleNativeState n) (e : Fin n) : Fin n :=
  (taggedRedirection ring j b hn hports).effective N e

/-- The selected physical state is always updated by nativeE once. -/
noncomputable def taggedQNext {n : Nat}
    (ring : DirectedRing n) (j : Fin n) (b : Nat)
    (hn : 2 ≤ n) (hports : ring.leftNeighbor j ≠ j)
    (N : TripleNativeState n) (e : Fin n) : TripleNativeState n :=
  nativeE ring N (taggedQEffective ring j b hn hports N e)

/-- This is literally the old taggedTrialStep under the Q scheduler.
It has the same absorbing success/failure constructors. -/
noncomputable def taggedQStopped {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (b : Nat)
    (hn : 2 ≤ n) (hports : ring.leftNeighbor j ≠ j)
    (N : TripleNativeState n) (e : Fin n) :
    StopNode (TripleNativeState n) :=
  ControlledSchedulerMass.controlledStep
    (taggedTrialStep ring i j k b)
    (taggedRedirection ring j b hn hports) N e

/-- A ready target cannot serve its outgoing nativeE edge under Q.
Both raw letters L_j and R_j execute L_j. -/
theorem tagged_q_ready_blocks_outgoing {n : Nat}
    (ring : DirectedRing n) (j : Fin n) (b : Nat)
    (hn : 2 ≤ n) (hports : ring.leftNeighbor j ≠ j)
    (N : TripleNativeState n) (e : Fin n)
    (hready : SealedCleanReady ring N j b) :
    taggedQEffective ring j b hn hports N e ≠ j := by
  classical
  have hg :
      (taggedRedirection ring j b hn hports).gate N = true := by
    simp [taggedRedirection, hready]
  have hp := (taggedRedirection ring j b hn hports).effective_ne_B
    N hg e
  simpa [taggedQEffective, taggedRedirection] using hp

/-- The paper's Q redirection eliminates the original vulnerable
trial's Ready-time R_j failure event, for every state, not just
reachable states. Hence Q has only success or active successors. -/
theorem tagged_q_no_failure_guard {n : Nat}
    (ring : DirectedRing n) (j : Fin n) (b : Nat)
    (hn : 2 ≤ n) (hports : ring.leftNeighbor j ≠ j)
    (N : TripleNativeState n) (e : Fin n) :
    ¬ (SealedCleanReady ring N j b ∧
      taggedQEffective ring j b hn hports N e = j) := by
  intro h
  exact (tagged_q_ready_blocks_outgoing
    ring j b hn hports N e h.1) h.2

/-- The controlled StopNode has exactly the paper terminal set:
tagged deletion. The failure constructor is unreachable under Q. -/
theorem tagged_q_stopped_eq {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (b : Nat)
    (hn : 2 ≤ n) (hports : ring.leftNeighbor j ≠ j)
    (N : TripleNativeState n) (e : Fin n) :
    taggedQStopped ring i j k b hn hports N e =
      if TaggedDeleted i j k (taggedQNext ring j b hn hports N e)
      then StopNode.success
      else StopNode.active (taggedQNext ring j b hn hports N e) := by
  classical
  let eff := taggedQEffective ring j b hn hports N e
  have hno : ¬ (SealedCleanReady ring N j b ∧ eff = j) :=
    tagged_q_no_failure_guard ring j b hn hports N e
  change
    (if TaggedDeleted i j k (nativeE ring N eff) then StopNode.success
     else if SealedCleanReady ring N j b ∧ eff = j then StopNode.failure
     else StopNode.active (nativeE ring N eff)) =
    (if TaggedDeleted i j k (nativeE ring N eff) then StopNode.success
     else StopNode.active (nativeE ring N eff))
  simp only [if_neg hno]

/-- Only the active configurations of the stopped Q tree are reached.
No synthetic reset, future-conditioned cut, or post-deletion edge
is allowed. The seed is the physical configuration after the
incoming clean-dummy service, supplied by the actual-entrance lemma. -/
inductive TaggedQActiveReach {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hn : 2 ≤ n) (hports : ring.leftNeighbor j ≠ j)
    (seed : TripleNativeState n) : TripleNativeState n → Prop where
  | start :
      TaggedQActiveReach ring i j k a b hn hports seed seed
  | step {N M : TripleNativeState n}
      (hreach : TaggedQActiveReach ring i j k a b hn hports seed N)
      (e : Fin n)
      (hactive : taggedQStopped ring i j k b hn hports N e =
        .active M) :
      TaggedQActiveReach ring i j k a b hn hports seed M

/-- Every inductive step is one literal Q-selected nativeE row and
not a tagged-deletion terminal. -/
theorem tagged_q_active_successor {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (b : Nat)
    (hn : 2 ≤ n) (hports : ring.leftNeighbor j ≠ j)
    (N M : TripleNativeState n) (e : Fin n)
    (hactive : taggedQStopped ring i j k b hn hports N e = .active M) :
    M = taggedQNext ring j b hn hports N e ∧
    ¬ TaggedDeleted i j k (taggedQNext ring j b hn hports N e) := by
  rw [tagged_q_stopped_eq ring i j k b hn hports N e] at hactive
  by_cases hdel :
      TaggedDeleted i j k (taggedQNext ring j b hn hports N e)
  · simp only [if_pos hdel] at hactive
    cases hactive
  · simp only [if_neg hdel] at hactive
    cases hactive
    exact ⟨rfl, hdel⟩

/-- Equivalently, a surviving actual Q edge extends the inductive
active domain. This is the exact closure premise for stopped costs. -/
theorem tagged_q_reach_surviving_step {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hn : 2 ≤ n) (hports : ring.leftNeighbor j ≠ j)
    (seed N : TripleNativeState n) (e : Fin n)
    (hr : TaggedQActiveReach ring i j k a b hn hports seed N)
    (hnot : ¬ TaggedDeleted i j k
      (taggedQNext ring j b hn hports N e)) :
    TaggedQActiveReach ring i j k a b hn hports seed
      (taggedQNext ring j b hn hports N e) := by
  apply TaggedQActiveReach.step hr e
  rw [tagged_q_stopped_eq ring i j k b hn hports N e]
  simp only [if_neg hnot]

/-! ### Native shield preservation and exclusion of target Live -/

/-- The exact OLD-pair initiator row cannot set a shield when the
source is unshielded and nonsignaling. -/
theorem tagged_q_unshielded_source_row (x y : CertNative)
    (hxsh : x.sh = false) (hxsg : x.sg = false) :
    (certLiteralEPair x y).1.sh = false := by
  simp [certLiteralEPair, hxsh, hxsg]

/-- The exact OLD-pair responder row cannot set its shield from
false to true, regardless of the incoming bullet. -/
theorem tagged_q_unshielded_responder_row (x y : CertNative)
    (hysh : y.sh = false) :
    (certLiteralEPair x y).2.sh = false := by
  simp [certLiteralEPair, hysh]

/-- For the real nativeE, the sole potentially re-shielding case
is selecting the outgoing edge of a signaling target leader. -/
theorem tagged_q_native_unshielded_of_avoided_launch {n : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (j e : Fin n)
    (hsh : (N j).sh = false)
    (havoid : (N j).sg = false ∨ e ≠ j) :
    (nativeE ring N e j).sh = false := by
  by_cases he : e = j
  · subst e
    have hsg : (N j).sg = false := by
      rcases havoid with hz | hn
      · exact hz
      · exact False.elim (hn rfl)
    have hr := tagged_q_unshielded_source_row
      (N j) (N (ring.rightNeighbor j)) hsh hsg
    simpa [nativeE] using hr
  · have hne : j ≠ e := Ne.symm he
    by_cases hj : ring.rightNeighbor e = j
    · have hr := tagged_q_unshielded_responder_row
        (N e) (N j) hsh
      simpa [nativeE, hne, hj] using hr
    · have hj' : j ≠ ring.rightNeighbor e := fun h => hj h.symm
      simpa [nativeE, hne, hj'] using hsh

/-- In a sealed sector, a signaling leader is necessarily in Ready:
the other three phases force the source signal to zero. -/
theorem tagged_q_sealed_signaling_ready {n : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (j : Fin n) (b : Nat)
    (hs : Sealed ring N j b)
    (hsg : (N j).sg = true) :
    SealedCleanReady ring N j b := by
  obtain ⟨phase, hp⟩ := hs
  cases phase with
  | ready => exact hp
  | dummy p =>
      have hz : (N j).sg = false := by
        simpa only [sealedAt_zero] using
          hp.2.2 (sealedZero ring) (Nat.zero_le p.val)
      rw [hz] at hsg
      cases hsg
  | live p =>
      have hz : (N j).sg = false := by
        simpa only [sealedAt_zero] using
          hp.2.2 (sealedZero ring) (Nat.zero_le p.val)
      rw [hz] at hsg
      cases hsg
  | returning q =>
      have hz : (N j).sg = false := by
        simpa only [sealedAt_zero] using hp.2.1
      rw [hz] at hsg
      cases hsg

/-- Every raw Q letter preserves the target's zero shield while its
sector is sealed. If the target signals, it is Ready and Q blocks
its outgoing launch; otherwise an outgoing native service is quiet.
Incoming services can only preserve or clear the shield. -/
theorem tagged_q_unshielded_next {n : Nat}
    (ring : DirectedRing n) (j : Fin n) (b : Nat)
    (hn : 2 ≤ n) (hports : ring.leftNeighbor j ≠ j)
    (N : TripleNativeState n) (e : Fin n)
    (hs : Sealed ring N j b)
    (hsh : (N j).sh = false) :
    ((taggedQNext ring j b hn hports N e) j).sh = false := by
  by_cases hsg : (N j).sg = true
  · have hready := tagged_q_sealed_signaling_ready
      ring N j b hs hsg
    have he := tagged_q_ready_blocks_outgoing
      ring j b hn hports N e hready
    exact tagged_q_native_unshielded_of_avoided_launch
      ring N j (taggedQEffective ring j b hn hports N e)
      hsh (Or.inr he)
  · have hz : (N j).sg = false := by
      cases hh : (N j).sg with
      | false => rfl
      | true => exact False.elim (hsg hh)
    exact tagged_q_native_unshielded_of_avoided_launch
      ring N j (taggedQEffective ring j b hn hports N e)
      hsh (Or.inl hz)

/-! ### Simultaneous inductive closure of all paper-domain invariants -/

/-- The native triple domain, both sealed sectors, and the unshielded
target are invariant along *every active path of the stopped Q tree*.
The only initial hypotheses are exactly the physical clean-dummy
entrance and its surviving peaceful consecutive tagged triple. -/
theorem tagged_q_reachable_invariants {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (seed : TripleNativeState n)
    (hstart : TaggedTriple ring i j k a b seed)
    (hclean : TaggedCleanDummy ring i j a b seed)
    {N : TripleNativeState n}
    (hr : TaggedQActiveReach ring i j k a b
      (by omega : 2 ≤ n) hports seed N) :
    TaggedTriple ring i j k a b N ∧
    TaggedSealed ring i j a b N ∧
    (N j).sh = false := by
  induction hr with
  | start =>
      have hsh : (seed j).sh = false := by
        simpa only [sealedAt_zero] using hclean.2.2.1
      exact ⟨hstart,
        tagged_clean_dummy_sealed ring i j a b seed hclean, hsh⟩
  | step hprior e hactive ih =>
      obtain ⟨htriple, hsealed, hsh⟩ := ih
      obtain ⟨heq, hnot⟩ :=
        tagged_q_active_successor ring i j k b
          (by omega : 2 ≤ n) hports _ _ e hactive
      have htripleNext :
          TaggedTriple ring i j k a b
            (taggedQNext ring j b (by omega : 2 ≤ n) hports _ e) :=
        tagged_triple_step_of_survival hnthree ring
          i j k a b _ (taggedQEffective ring j b
            (by omega : 2 ≤ n) hports _ e) htriple hnot
      have hsealedNext :
          TaggedSealed ring i j a b
            (taggedQNext ring j b (by omega : 2 ≤ n) hports _ e) :=
        tagged_sealed_step_of_survival ring
          i j k a b _ (taggedQEffective ring j b
            (by omega : 2 ≤ n) hports _ e)
          htriple hsealed hnot
      have hshieldNext :
          ((taggedQNext ring j b (by omega : 2 ≤ n) hports _ e) j).sh =
            false :=
        tagged_q_unshielded_next ring j b (by omega : 2 ≤ n)
          hports _ e hsealed.2 hsh
      rw [heq]
      exact ⟨htripleNext, hsealedNext, hshieldNext⟩

/-- The target can never enter the live-bullet family along a
controlled active path: Live requires a true source shield. -/
theorem tagged_q_reachable_target_ne_live {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (seed N : TripleNativeState n)
    (hstart : TaggedTriple ring i j k a b seed)
    (hclean : TaggedCleanDummy ring i j a b seed)
    (hr : TaggedQActiveReach ring i j k a b
      (by omega : 2 ≤ n) hports seed N)
    (p : Fin n) :
    ¬ SealedPhaseHolds ring N j b (.live p) := by
  intro hp
  have hsh : (N j).sh = false :=
    (tagged_q_reachable_invariants hnthree ring i j k a b
      hports seed hstart hclean hr).2.2
  have hlive : (N j).sh = true := by
    simpa only [sealedAt_zero] using hp.2.1
  rw [hsh] at hlive
  cases hlive

/-- Under Q even a Ready target's *raw* outgoing letter executes
an incoming edge, so it never launches a live bullet. -/
theorem tagged_q_reachable_ready_outgoing_redirect {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (seed N : TripleNativeState n)
    (hr : TaggedQActiveReach ring i j k a b
      (by omega : 2 ≤ n) hports seed N)
    (hready : SealedCleanReady ring N j b) :
    taggedQEffective ring j b (by omega : 2 ≤ n)
      hports N j = ring.leftNeighbor j := by
  exact tagged_redirection_ready_right
    ring j b (by omega : 2 ≤ n) hports N hready

/-- The paper's initial state really arises from a *single* nativeE
incoming service on TaggedPrepared. This is not an assumed reset or
additional invariant; both conclusions are already established by
the physical row and surviving-tag lemmas. -/
theorem tagged_q_actual_clean_entrance {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (before : TripleNativeState n) (e : Fin n)
    (hne : e ≠ j) (hnext : ring.rightNeighbor e = j)
    (htriple : TaggedTriple ring i j k a b before)
    (hprep : TaggedPrepared ring i j a b before)
    (hnot : ¬ TaggedDeleted i j k (nativeE ring before e)) :
    TaggedTriple ring i j k a b (nativeE ring before e) ∧
    TaggedCleanDummy ring i j a b (nativeE ring before e) := by
  have htripleNew :=
    tagged_triple_step_of_survival hnthree ring i j k a b
      before e htriple hnot
  have hrow :=
    tagged_prepared_incoming_dummy_actual
      ring i j k a b before e hne hnext htriple hprep
  rcases hrow with hdel | hdummy
  · exact False.elim (hnot hdel)
  · exact ⟨htripleNew, hdummy⟩

/-! ### Canonical proof-only D.11 potential -/

/-- A proof-only phase extracted from the exact sealed predicate.
No agent-field modification; the choice is not evaluated by decide. -/
noncomputable def taggedQAttackerPhase {n : Nat}
    (ring : DirectedRing n) (i : Fin n) (a : Nat)
    (N : TripleNativeState n) : SealedPhase n :=
  if h : Sealed ring N i a then Classical.choose h else .ready

theorem tagged_q_attacker_phase_valid {n : Nat}
    (ring : DirectedRing n) (i : Fin n) (a : Nat)
    (N : TripleNativeState n)
    (hs : Sealed ring N i a) :
    SealedPhaseHolds ring N i a
      (taggedQAttackerPhase ring i a N) := by
  classical
  unfold taggedQAttackerPhase
  rw [dif_pos hs]
  exact Classical.choose_spec hs

/-- D.11's physical potential: zero at tagged deletion, otherwise
taggedAttackerBellman on the extracted sealed attacker phase.
Outside the paper domain, it has an arbitrary harmless fallback. -/
noncomputable def taggedQBellman {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a : Nat)
    (N : TripleNativeState n) : Nat :=
  if TaggedDeleted i j k N then 0
  else taggedAttackerBellman n a (taggedQAttackerPhase ring i a N)

/-- D.11's uniform phase cap holds on the actual active Q-domain. -/
theorem tagged_q_reachable_bellman_cap {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (seed N : TripleNativeState n)
    (hstart : TaggedTriple ring i j k a b seed)
    (hclean : TaggedCleanDummy ring i j a b seed)
    (hr : TaggedQActiveReach ring i j k a b
      (by omega : 2 ≤ n) hports seed N) :
    taggedQBellman ring i j k a N ≤ n * (5 * a - 2) := by
  classical
  by_cases hdel : TaggedDeleted i j k N
  · simp only [taggedQBellman, if_pos hdel]
    exact Nat.zero_le _
  · simp only [taggedQBellman, if_neg hdel]
    have hs : Sealed ring N i a :=
      (tagged_q_reachable_invariants hnthree ring i j k a b
        hports seed hstart hclean hr).2.1.1
    have hp := tagged_q_attacker_phase_valid ring i a N hs
    have ha : 1 ≤ a := hstart.2.1.1
    exact tagged_attacker_bellman_cap ring N i a ha
      (taggedQAttackerPhase ring i a N) hp

/-! ### Algebraic split lemmas and a genuinely reachable-only Bellman API -/

/-- Core Fin-sum spike, as in ProbStages, but available in this
section without referring to that file's private lemma. -/
private theorem tagged_q_sum_spike (n : Nat) :
    ∀ (edge : Fin n) (v : Nat),
      (List.ofFn (fun e : Fin n => if e = edge then v else 0)).sum = v := by
  induction n with
  | zero =>
      intro edge
      exact Fin.elim0 edge
  | succ n ih =>
      intro edge v
      refine Fin.cases ?_ ?_ edge
      · rw [List.ofFn_succ, List.sum_cons]
        have ht :
            (List.ofFn (fun z : Fin n =>
              if z.succ = (0 : Fin (n + 1)) then v else 0)).sum = 0 := by
          have hh := ofFn_sum_eq
            (fun z : Fin n =>
              if z.succ = (0 : Fin (n + 1)) then v else 0)
            (fun _ : Fin n => 0)
            (by
              intro z
              have hz : z.succ ≠ (0 : Fin (n + 1)) := by
                intro he
                have hv := congrArg Fin.val he
                change z.val + 1 = 0 at hv
                omega
              rw [if_neg hz])
          simpa only [ofFn_sum_const, Nat.mul_zero] using hh
        simp [ht]
      · intro edge
        rw [List.ofFn_succ, List.sum_cons]
        have hz : (0 : Fin (n + 1)) ≠ edge.succ := by
          intro he
          have hv := congrArg Fin.val he
          change 0 = edge.val + 1 at hv
          omega
        rw [if_neg hz, Nat.zero_add]
        have hh := ofFn_sum_eq
          (fun z : Fin n => if z.succ = edge.succ then v else 0)
          (fun z : Fin n => if z = edge then v else 0)
          (by intro z; simp only [Fin.succ_inj])
        rw [hh]
        exact ih edge v

/-- If every edge is weakly decreasing and one nominated edge
decreases by n, the D.12 summed inequality follows. The *physical*
premises, not this sum identity, are what must be discharged for
every reachable non-Ready attacker state. -/
theorem tagged_q_drift_from_nominated_edge {n : Nat}
    (V : Nat) (f : Fin n → Nat) (chosen : Fin n)
    (hweak : ∀ e, f e ≤ V)
    (hstrict : f chosen + n ≤ V) :
    n + (List.ofFn f).sum ≤ n * V := by
  have hp : ∀ e : Fin n,
      f e + (if e = chosen then n else 0) ≤ V := by
    intro e
    by_cases he : e = chosen
    · subst e
      simpa using hstrict
    · simpa [he] using hweak e
  have hs := ofFn_sum_le
    (fun e : Fin n => f e + (if e = chosen then n else 0))
    (fun _ : Fin n => V) hp
  rw [ofFn_sum_add, ofFn_sum_const, tagged_q_sum_spike] at hs
  omega

/-- Bellman on a *restricted invariant domain*. Unlike the global
ProbStages.costNumerator_le_of_potential, this theorem requires
the drift premise only on R, and uses closure only for successors
which have not already hit the terminal target. -/
theorem tagged_q_restricted_cost_of_potential
    {S : Type} {n : Nat} (next : S → Fin n → S)
    (Terminal R : S → Prop) (V : S → Nat)
    (hclosed : ∀ x, R x → ∀ e, ¬ Terminal (next x e) → R (next x e))
    (hdrift : ∀ x, R x → ¬ Terminal x →
      n + (List.ofFn (fun e : Fin n => V (next x e))).sum ≤ n * V x) :
    ∀ x, R x → ∀ T,
      costNumerator next Terminal x T ≤ n ^ T * V x := by
  classical
  have hmain : ∀ (T : Nat) (x : S), R x →
      costNumerator next Terminal x T ≤ n ^ T * V x := by
    intro T
    induction T with
    | zero =>
        intro x hx
        simp only [costNumerator_zero]
        exact Nat.zero_le _
    | succ T ih =>
        intro x hx
        by_cases ht : Terminal x
        · rw [costNumerator_terminal next Terminal x ht (T + 1)]
          exact Nat.zero_le _
        · have hs :
              (List.ofFn (fun e : Fin n =>
                costNumerator next Terminal (next x e) T)).sum ≤
              (List.ofFn (fun e : Fin n =>
                n ^ T * V (next x e))).sum := by
            apply ofFn_sum_le
            intro e
            by_cases hterminal : Terminal (next x e)
            · cases T with
              | zero =>
                  simp only [costNumerator_zero]
                  exact Nat.zero_le _
              | succ t =>
                  rw [costNumerator_terminal next Terminal
                    (next x e) hterminal (t + 1)]
                  exact Nat.zero_le _
            · exact ih (next x e) (hclosed x hx e hterminal)
          calc
            costNumerator next Terminal x (T + 1) =
                n ^ (T + 1) +
                  (List.ofFn (fun e : Fin n =>
                    costNumerator next Terminal (next x e) T)).sum := by
                      rw [costNumerator_succ next Terminal x ht T]
            _ ≤ n ^ (T + 1) +
                  (List.ofFn (fun e : Fin n =>
                    n ^ T * V (next x e))).sum :=
                Nat.add_le_add_left hs _
            _ = n ^ T *
                  (n + (List.ofFn (fun e : Fin n =>
                    V (next x e))).sum) := by
                rw [ofFn_sum_mul_left, Nat.mul_add, Nat.pow_succ]
                all_goals ac_rfl
            _ ≤ n ^ T * (n * V x) :=
                Nat.mul_le_mul_left _ (hdrift x hx ht)
            _ = n ^ (T + 1) * V x := by
                rw [Nat.pow_succ]
                ac_rfl
  intro x hx T
  exact hmain T x hx

/-- The exact unfinished D.12 obligation, packaged only on the
inductively reachable Q-domain, is sufficient for finite-horizon
stopped cost. The premise is *not* claimed as proved here. -/
theorem tagged_q_cost_of_reachable_bellman_drift {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hn : 2 ≤ n) (hports : ring.leftNeighbor j ≠ j)
    (seed : TripleNativeState n)
    (hD12 : ∀ N : TripleNativeState n,
      TaggedQActiveReach ring i j k a b hn hports seed N →
      ¬ TaggedDeleted i j k N →
      n + (List.ofFn (fun e : Fin n =>
        taggedQBellman ring i j k a
          (taggedQNext ring j b hn hports N e))).sum ≤
        n * taggedQBellman ring i j k a N) :
    ∀ T,
      costNumerator (taggedQNext ring j b hn hports)
        (TaggedDeleted i j k) seed T ≤
      n ^ T * taggedQBellman ring i j k a seed := by
  have hclosed : ∀ N : TripleNativeState n,
      TaggedQActiveReach ring i j k a b hn hports seed N →
      ∀ e, ¬ TaggedDeleted i j k
        (taggedQNext ring j b hn hports N e) →
        TaggedQActiveReach ring i j k a b hn hports seed
          (taggedQNext ring j b hn hports N e) := by
    intro N hr e hnot
    exact tagged_q_reach_surviving_step
      ring i j k a b hn hports seed N e hr hnot
  exact tagged_q_restricted_cost_of_potential
    (taggedQNext ring j b hn hports)
    (TaggedDeleted i j k)
    (TaggedQActiveReach ring i j k a b hn hports seed)
    (taggedQBellman ring i j k a)
    hclosed hD12 seed (.start)

/-- If the still-open restricted D.12 is supplied, the physical Q
trial's expected tagged-deletion time is at most n(5a-2).
This explicitly records the remaining proof boundary. -/
theorem tagged_q_expected_of_reachable_bellman_drift {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (seed : TripleNativeState n)
    (hstart : TaggedTriple ring i j k a b seed)
    (hclean : TaggedCleanDummy ring i j a b seed)
    (hD12 : ∀ N : TripleNativeState n,
      TaggedQActiveReach ring i j k a b
        (by omega : 2 ≤ n) hports seed N →
      ¬ TaggedDeleted i j k N →
      n + (List.ofFn (fun e : Fin n =>
        taggedQBellman ring i j k a
          (taggedQNext ring j b (by omega : 2 ≤ n)
            hports N e))).sum ≤
        n * taggedQBellman ring i j k a N) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (taggedQNext ring j b (by omega : 2 ≤ n) hports)
      (TaggedDeleted i j k) seed
      ((n * (5 * a - 2) : Nat) : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (taggedQNext ring j b (by omega : 2 ≤ n) hports)
    (TaggedDeleted i j k) (by omega : 0 < n)
    seed (n * (5 * a - 2))).2
  intro T
  have hc := tagged_q_cost_of_reachable_bellman_drift
    ring i j k a b (by omega : 2 ≤ n) hports seed hD12 T
  have hcap := tagged_q_reachable_bellman_cap
    hnthree ring i j k a b hports seed seed hstart hclean
      (TaggedQActiveReach.start)
  exact Nat.le_trans hc
    (Nat.mul_le_mul_left (n ^ T) hcap)

end L3


/-! ## Phase uniqueness and concrete Q-edge Bellman interfaces

D.12's numerical local row case split is not claimed complete.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

attribute [local instance low] Classical.propDecidable

/-! Step (0): unique phase of a sealed native sector. -/

/-- A bullet-free sector cannot also have a uniquely specified
nonzero bullet at an interior offset. -/
private theorem tagged_phase_no_bullet_excludes_unique {n : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (i : Fin n) (a : Nat) (p : Fin n) (v : Fin 3)
    (hz : SealedNoBullet ring N i a)
    (hu : SealedUniqueBullet ring N i a p v)
    (hv : v ≠ 0) : False := by
  have hzero := hz p hu.1
  have hvalue := hu.2.1
  rw [hvalue] at hzero
  exact hv hzero

/-- Unique-bullet phase indices are determined by the actual
bullet location, independently of its kind. -/
private theorem tagged_phase_unique_bullet_index {n : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (i : Fin n) (a : Nat) (p q : Fin n)
    (u v : Fin 3)
    (hp : SealedUniqueBullet ring N i a p u)
    (hq : SealedUniqueBullet ring N i a q v)
    (hu : u ≠ 0) : p = q := by
  by_cases hpq : p = q
  · exact hpq
  · have hz := hq.2.2 p hp.1 hpq
    have hv : u = 0 := by
      calc
        u = (sealedAt ring N i p).b := hp.2.1.symm
        _ = 0 := hz
    exact False.elim (hu hv)

/-- The first positive signal in a returning phase is unique.
A later proposed front would require that earlier true signal
to be simultaneously false. -/
private theorem tagged_phase_unique_return_front {n : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (i : Fin n) (a : Nat) (p q : Fin n)
    (hp : SealedFirstSignal ring N i a p)
    (hq : SealedFirstSignal ring N i a q) : p = q := by
  by_cases he : p.val = q.val
  · exact Fin.ext he
  · by_cases hlt : p.val < q.val
    · have hs := hp.2.2.1
      have hz := hq.2.2.2 p hp.1 hlt
      rw [hs] at hz
      cases hz
    · have hgt : q.val < p.val := by omega
      have hs := hq.2.2.1
      have hz := hp.2.2.2 q hq.1 hgt
      rw [hs] at hz
      cases hz

/-- Phase uniqueness is a structural theorem about the four exact
native sealed predicates, not a reachability assumption. -/
theorem tagged_sealed_phase_unique {n : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (i : Fin n) (a : Nat)
    (p q : SealedPhase n)
    (hp : SealedPhaseHolds ring N i a p)
    (hq : SealedPhaseHolds ring N i a q) : p = q := by
  cases p with
  | ready =>
      cases q with
      | ready => rfl
      | dummy r =>
          exact False.elim
            (tagged_phase_no_bullet_excludes_unique
              ring N i a r 1 hp.2 hq.1 (by decide))
      | live r =>
          exact False.elim
            (tagged_phase_no_bullet_excludes_unique
              ring N i a r 2 hp.2 hq.1 (by decide))
      | returning r =>
          have he : true = false := hp.1.symm.trans hq.2.1
          cases he
  | dummy p =>
      cases q with
      | ready =>
          exact False.elim
            (tagged_phase_no_bullet_excludes_unique
              ring N i a p 1 hq.2 hp.1 (by decide))
      | dummy q =>
          have he : p = q :=
            tagged_phase_unique_bullet_index
              ring N i a p q 1 1 hp.1 hq.1 (by decide)
          cases he
          rfl
      | live q =>
          have he : false = true := hp.2.1.symm.trans hq.2.1
          cases he
      | returning q =>
          exact False.elim
            (tagged_phase_no_bullet_excludes_unique
              ring N i a p 1 hq.1 hp.1 (by decide))
  | live p =>
      cases q with
      | ready =>
          exact False.elim
            (tagged_phase_no_bullet_excludes_unique
              ring N i a p 2 hq.2 hp.1 (by decide))
      | dummy q =>
          have he : true = false := hp.2.1.symm.trans hq.2.1
          cases he
      | live q =>
          have he : p = q :=
            tagged_phase_unique_bullet_index
              ring N i a p q 2 2 hp.1 hq.1 (by decide)
          cases he
          rfl
      | returning q =>
          exact False.elim
            (tagged_phase_no_bullet_excludes_unique
              ring N i a p 2 hq.1 hp.1 (by decide))
  | returning p =>
      cases q with
      | ready =>
          have he : false = true := hp.2.1.symm.trans hq.1
          cases he
      | dummy q =>
          exact False.elim
            (tagged_phase_no_bullet_excludes_unique
              ring N i a q 1 hp.1 hq.1 (by decide))
      | live q =>
          exact False.elim
            (tagged_phase_no_bullet_excludes_unique
              ring N i a q 2 hp.1 hq.1 (by decide))
      | returning q =>
          have he : p = q :=
            tagged_phase_unique_return_front
              ring N i a p q hp.2.2 hq.2.2
          cases he
          rfl

/-- The noncomputable phase choice in the original Bellman
certificate equals EVERY physically valid witness, by uniqueness. -/
theorem tagged_q_attacker_phase_eq {n : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (i : Fin n) (a : Nat) (phase : SealedPhase n)
    (hp : SealedPhaseHolds ring N i a phase) :
    taggedQAttackerPhase ring i a N = phase := by
  have hv := tagged_q_attacker_phase_valid
    ring i a N ⟨phase, hp⟩
  exact tagged_sealed_phase_unique ring N i a
    (taggedQAttackerPhase ring i a N) phase hv hp

/-- The arbitrary choice has disappeared from the D.11 potential
whenever the source is nonterminal and has a concrete valid phase. -/
theorem tagged_q_bellman_eq_phase {n : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (i j k : Fin n) (a : Nat) (phase : SealedPhase n)
    (hnot : ¬ TaggedDeleted i j k N)
    (hp : SealedPhaseHolds ring N i a phase) :
    taggedQBellman ring i j k a N =
      taggedAttackerBellman n a phase := by
  classical
  have hphase := tagged_q_attacker_phase_eq ring N i a phase hp
  unfold taggedQBellman
  rw [if_neg hnot, hphase]

/-- D.11's terminal value is literally zero. -/
theorem tagged_q_bellman_deleted_zero {n : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (i j k : Fin n) (a : Nat)
    (hdel : TaggedDeleted i j k N) :
    taggedQBellman ring i j k a N = 0 := by
  classical
  simp only [taggedQBellman, if_pos hdel]

/-! Step (1): a physical nonready Q step, using SealedClose,
now yields inequalities for the ACTUAL extracted phase.
The subsequent numerical Bellman comparison needs its own row split. -/

/-- Source and successor phases in the real controlled step are
unambiguously identified. On surviving nonready steps, the
SealedPhaseProgress rank is weakly monotone on every edge and
strictly monotone on the nominated physical edge. -/
theorem tagged_q_nonready_phase_progress {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (seed N : TripleNativeState n) (e : Fin n)
    (hstart : TaggedTriple ring i j k a b seed)
    (hclean : TaggedCleanDummy ring i j a b seed)
    (hr : TaggedQActiveReach ring i j k a b
      (by omega : 2 ≤ n) hports seed N)
    (phase : SealedPhase n)
    (hp : SealedPhaseHolds ring N i a phase)
    (hnr : phase ≠ .ready)
    (hnot : ¬ TaggedDeleted i j k
      (taggedQNext ring j b (by omega : 2 ≤ n) hports N e)) :
    SealedPhaseProgress a
      (taggedQAttackerPhase ring i a
        (taggedQNext ring j b (by omega : 2 ≤ n) hports N e)) ≤
      SealedPhaseProgress a phase ∧
    (taggedQEffective ring j b (by omega : 2 ≤ n) hports N e =
      SealedPhaseEdge ring i phase →
      SealedPhaseProgress a
        (taggedQAttackerPhase ring i a
          (taggedQNext ring j b (by omega : 2 ≤ n) hports N e)) + 1 ≤
        SealedPhaseProgress a phase) := by
  let eff := taggedQEffective ring j b (by omega : 2 ≤ n) hports N e
  have ht : TaggedTriple ring i j k a b N :=
    (tagged_q_reachable_invariants hnthree ring i j k a b
      hports seed hstart hclean hr).1
  have hno : ¬ TaggedDeleted i j k (nativeE ring N eff) := by
    exact hnot
  obtain ⟨nextPhase, hnext, hweak, hstrict⟩ :=
    tagged_nonready_attacker_progress_actual
      ring i j k a b N eff ht phase hp hnr hno
  have heq : taggedQAttackerPhase ring i a
      (taggedQNext ring j b (by omega : 2 ≤ n) hports N e) =
      nextPhase :=
    tagged_q_attacker_phase_eq ring
      (taggedQNext ring j b (by omega : 2 ≤ n) hports N e)
      i a nextPhase hnext
  simpa only [heq] using (show
    SealedPhaseProgress a nextPhase ≤
      SealedPhaseProgress a phase ∧
    (eff = SealedPhaseEdge ring i phase →
      SealedPhaseProgress a nextPhase + 1 ≤
        SealedPhaseProgress a phase) from
        ⟨hweak, hstrict⟩)

/-! Step (1ii): exact native terminal collision at the unshielded
target, excluding the shielded-Live counterexample on this
reachable domain. -/

/-- A live bullet striking an unshielded leader deletes that leader
on the literal OLD-pair update, even if the target is signaling. -/
theorem tagged_q_live_unshielded_row
    (x y : CertNative)
    (hxb : x.b = (2 : Fin 3)) (hxsg : x.sg = false)
    (hyl : y.l = true) (hysh : y.sh = false) :
    (certLiteralEPair x y).2.l = false := by
  rcases x with ⟨xl, xb, xsh, xsg⟩
  rcases y with ⟨yl, yb, ysh, ysg⟩
  simp only at hxb hxsg hyl hysh
  subst hxb hxsg hyl hysh
  cases xl <;> cases ysg <;> cases xsh <;>
    simp [certLiteralEPair]

/-- Wraparound-correct physical lift of the terminal live collision. -/
theorem tagged_q_live_unshielded_native {n : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (e j : Fin n)
    (hne : e ≠ j) (hnext : ring.rightNeighbor e = j)
    (hxb : (N e).b = (2 : Fin 3))
    (hxsg : (N e).sg = false)
    (hyl : (N j).l = true)
    (hysh : (N j).sh = false) :
    (nativeE ring N e j).l = false := by
  have hr := tagged_q_live_unshielded_row
    (N e) (N j) hxb hxsg hyl hysh
  have heq :
      nativeE ring N e j = (certLiteralEPair (N e) (N j)).2 := by
    simp [nativeE, hnext, Ne.symm hne]
  rw [heq]
  exact hr

/-- At any Q-reachable active state, a raw edge whose effective
physical service enters j with a live bullet deletes a tagged
leader. Thus it cannot make a surviving Live-to-Return jump. -/
theorem tagged_q_live_terminal_at_target {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (seed N : TripleNativeState n) (e : Fin n)
    (hstart : TaggedTriple ring i j k a b seed)
    (hclean : TaggedCleanDummy ring i j a b seed)
    (hr : TaggedQActiveReach ring i j k a b
      (by omega : 2 ≤ n) hports seed N)
    (heff : taggedQEffective ring j b (by omega : 2 ≤ n)
      hports N e = ring.leftNeighbor j)
    (hbullet : (N (ring.leftNeighbor j)).b = (2 : Fin 3))
    (hsignal : (N (ring.leftNeighbor j)).sg = false) :
    TaggedDeleted i j k
      (taggedQNext ring j b (by omega : 2 ≤ n) hports N e) := by
  have inv := tagged_q_reachable_invariants hnthree ring
    i j k a b hports seed hstart hclean hr
  have hcB : ConsecutiveNative ring N j k b := inv.1.2.2
  have hjl : (N j).l = true := hcB.2.2.2.1
  have hd := tagged_q_live_unshielded_native
    ring N (ring.leftNeighbor j) j hports
    (tagged_right_of_left (by omega : 2 ≤ n) ring j)
    hbullet hsignal hjl inv.2.2
  have he :
      ((taggedQNext ring j b (by omega : 2 ≤ n) hports N e) j).l =
        false := by
    unfold taggedQNext
    rw [heff]
    exact hd
  exact Or.inr (Or.inl he)

/-! Step (2): arithmetic certificates for the cases that D.12
must eventually establish physically. -/

/-- If physical rows separately certify every weak bound and the
strict nominated bound (already scaled by n), the D.12 inequality
follows for all edges without any independence assumption. -/
theorem tagged_q_nonready_sum_of_edge_bounds {n : Nat}
    (value : Nat) (child : Fin n → Nat) (chosen : Fin n)
    (hweak : ∀ e, child e ≤ value)
    (hstrict : child chosen + n ≤ value) :
    n + (List.ofFn child).sum ≤ n * value := by
  exact tagged_q_drift_from_nominated_edge value child chosen hweak hstrict

/-- `List.ofFn` of an injective map has no duplicates (copy of the
private DensityTail lemma). -/
theorem tagged_ofFn_nodup {k : Nat} {X : Type}
    (f : Fin k → X) (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.ofFn_succ, List.nodup_cons]
      constructor
      · intro hmem
        obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
        have h := hf hi
        have hv := congrArg Fin.val h
        change i.val + 1 = 0 at hv
        omega
      · apply ih
        intro i j hij
        exact Fin.succ_inj.mp (hf hij)

/-- Ready's two distinct incident edges are compensated jointly,
not individually. The non-special edges only need weak bounds. -/
theorem tagged_q_ready_sum_of_two_edge_bounds {n : Nat}
    (value : Nat) (child : Fin n → Nat)
    (outgoing incoming : Fin n) (hne : outgoing ≠ incoming)
    (hpair : n + child outgoing + child incoming ≤ 2 * value)
    (hrest : ∀ e, e ≠ outgoing → e ≠ incoming → child e ≤ value) :
    n + (List.ofFn child).sum ≤ n * value := by
  let f : Fin n → Nat := fun e =>
    if e = outgoing then child outgoing
    else if e = incoming then child incoming else value
  have hfg : ∀ e, child e ≤ f e := by
    intro e
    by_cases ho : e = outgoing
    · subst e
      simp [f]
    · by_cases hi : e = incoming
      · subst e
        simp [f, ho]
      · simpa only [f, if_neg ho, if_neg hi] using hrest e ho hi
  let xs : List (Fin n) := List.ofFn (fun e : Fin n => e)
  have hs := sum_two_exceptions xs outgoing incoming f value
    (tagged_ofFn_nodup (fun e : Fin n => e) (by intro a b h; exact h))
    (List.mem_ofFn.mpr ⟨outgoing, rfl⟩)
    (List.mem_ofFn.mpr ⟨incoming, rfl⟩)
    hne (by
      intro z hz hzo hzi
      simp [f, hzo, hzi])
  have hmap : xs.map f = List.ofFn f := by
    simp [xs, List.map_ofFn, Function.comp_def]
  have hlen : xs.length = n := by simp [xs]
  have hfo : f outgoing = child outgoing := by simp [f]
  have hfi : f incoming = child incoming := by
    simp [f, Ne.symm hne]
  have hsum :
      (List.ofFn f).sum =
        child outgoing + child incoming + (n - 2) * value := by
    rw [← hmap, hs, hlen, hfo, hfi]
  have hle := ofFn_sum_le child f hfg
  have hvals : outgoing.val ≠ incoming.val := by
    intro he
    exact hne (Fin.ext he)
  have htwo : 2 ≤ n := by
    have hout := outgoing.isLt
    have hin := incoming.isLt
    omega
  have hidentity : (n - 2) + 2 = n := by omega
  calc
    n + (List.ofFn child).sum ≤ n + (List.ofFn f).sum :=
      Nat.add_le_add_left hle _
    _ = n + (child outgoing + child incoming +
          (n - 2) * value) := by rw [hsum]
    _ ≤ 2 * value + (n - 2) * value := by omega
    _ = n * value := by
      calc
        2 * value + (n - 2) * value =
            ((n - 2) + 2) * value := by
          rw [Nat.add_mul]
          omega
        _ = n * value := by rw [hidentity]

/-! The source and target Q-reachable invariants, the global phase
identification and abstract finite-sum algebra are now separate
certificates. The remaining D.12 physical obligations must control
D.11 (not just SealedPhaseProgress) across all phase transitions. -/

end L3


/-! ## D.11 child potential via exact SealedClose stages.

All results below use the actual Q nativeE edge.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

attribute [local instance low] Classical.propDecidable

/-- Unscaled paper D.11 credit on the Stage representation, including
the distinction between the two bullet kinds. -/
def taggedCloseCredit (a : Nat) : SealedCloseProof.Stage → Nat
  | .ready => 3 * a - 1
  | .bullet false p => (2 * a - p - 1) + (3 * a - 1)
  | .bullet true p => a - p
  | .returning q => q + 3 * a - 1

/-- The credit table agrees literally with taggedAttackerBellman. -/
theorem tagged_close_credit_from_phase {n : Nat}
    (population a : Nat) (phase : SealedPhase n) :
    taggedAttackerBellman population a phase =
      population * taggedCloseCredit a
        (SealedCloseProof.fromPhase phase) := by
  cases phase with
  | ready => rfl
  | dummy p => rfl
  | live p => rfl
  | returning q => rfl

/-- One surviving actual Q edge has exactly the public table stage.
The theorem uses both the old consecutive tagged witnesses and the
literal physical endpoint survival, not an assumed stage transition. -/
theorem tagged_q_surviving_child_stage {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (seed N : TripleNativeState n) (raw : Fin n)
    (hstart : TaggedTriple ring i j k a b seed)
    (hclean : TaggedCleanDummy ring i j a b seed)
    (hreach : TaggedQActiveReach ring i j k a b
      (by omega : 2 ≤ n) hports seed N)
    (phase : SealedPhase n)
    (hphase : SealedPhaseHolds ring N i a phase)
    (hnot : ¬ TaggedDeleted i j k
      (taggedQNext ring j b (by omega : 2 ≤ n)
        hports N raw)) :
    ∃ nextPhase : SealedPhase n,
      SealedPhaseHolds ring
        (taggedQNext ring j b (by omega : 2 ≤ n)
          hports N raw) i a nextPhase ∧
      SealedCloseProof.fromPhase nextPhase =
        sealedCloseTable ring i a
          (taggedQEffective ring j b (by omega : 2 ≤ n)
            hports N raw) phase := by
  let eff :=
    taggedQEffective ring j b (by omega : 2 ≤ n) hports N raw
  have htriple : TaggedTriple ring i j k a b N :=
    (tagged_q_reachable_invariants hnthree ring i j k a b
      hports seed hstart hclean hreach).1
  have hi : (nativeE ring N eff i).l = true := by
    cases hx : (nativeE ring N eff i).l with
    | false => exact False.elim (hnot (Or.inl hx))
    | true => rfl
  have hj : (nativeE ring N eff j).l = true := by
    cases hx : (nativeE ring N eff j).l with
    | false => exact False.elim (hnot (Or.inr (Or.inl hx)))
    | true => rfl
  exact sealed_close_step_stage ring N i j a eff phase
    htriple.2.1 hphase hi hj

/-- The D.11 value of a surviving Q child is the literal credit
of its computed Stage successor, not a new Classical.choose phase. -/
theorem tagged_q_child_bellman_stage {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (seed N : TripleNativeState n) (raw : Fin n)
    (hstart : TaggedTriple ring i j k a b seed)
    (hclean : TaggedCleanDummy ring i j a b seed)
    (hreach : TaggedQActiveReach ring i j k a b
      (by omega : 2 ≤ n) hports seed N)
    (phase : SealedPhase n)
    (hphase : SealedPhaseHolds ring N i a phase)
    (hnot : ¬ TaggedDeleted i j k
      (taggedQNext ring j b (by omega : 2 ≤ n)
        hports N raw)) :
    taggedQBellman ring i j k a
      (taggedQNext ring j b (by omega : 2 ≤ n)
        hports N raw) =
      n * taggedCloseCredit a
        (sealedCloseTable ring i a
          (taggedQEffective ring j b (by omega : 2 ≤ n)
            hports N raw) phase) := by
  obtain ⟨nextPhase, hnext, hstage⟩ :=
    tagged_q_surviving_child_stage
      hnthree ring i j k a b hports
      seed N raw hstart hclean hreach phase hphase hnot
  have hvalue := tagged_q_bellman_eq_phase
    ring (taggedQNext ring j b (by omega : 2 ≤ n)
      hports N raw) i j k a nextPhase hnot hnext
  calc
    taggedQBellman ring i j k a
        (taggedQNext ring j b (by omega : 2 ≤ n)
          hports N raw) =
      taggedAttackerBellman n a nextPhase := hvalue
    _ = n * taggedCloseCredit a
        (SealedCloseProof.fromPhase nextPhase) :=
      tagged_close_credit_from_phase n a nextPhase
    _ = n * taggedCloseCredit a
        (sealedCloseTable ring i a
          (taggedQEffective ring j b (by omega : 2 ≤ n)
            hports N raw) phase) := by
      rw [hstage]

/-- A live bullet at the last occupied site of A is ALWAYS terminal
on its nominated actual edge, using the unshielded target invariant.
This is precisely the exceptional source stage on which the abstract
insideStage would otherwise return a larger-credit Return phase. -/
theorem tagged_q_terminal_live_boundary {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (seed N : TripleNativeState n) (raw p : Fin n)
    (hstart : TaggedTriple ring i j k a b seed)
    (hclean : TaggedCleanDummy ring i j a b seed)
    (hreach : TaggedQActiveReach ring i j k a b
      (by omega : 2 ≤ n) hports seed N)
    (hphase : SealedPhaseHolds ring N i a (.live p))
    (hlast : p.val + 1 = a)
    (heff : taggedQEffective ring j b (by omega : 2 ≤ n)
      hports N raw = SealedPhaseEdge ring i (.live p)) :
    TaggedDeleted i j k
      (taggedQNext ring j b (by omega : 2 ≤ n)
        hports N raw) := by
  have hinv := tagged_q_reachable_invariants
    hnthree ring i j k a b hports seed
      hstart hclean hreach
  have hc : ConsecutiveNative ring N i j a :=
    hinv.1.2.1
  have hne : SealedPhaseEdge ring i (.live p) ≠ j :=
    sealed_close_nominated_ne_right
      ring N i j a (.live p) hc hphase
  have hnext : ring.rightNeighbor
      (SealedPhaseEdge ring i (.live p)) = j :=
    sealed_close_last_bullet_enters_right
      ring N i j a p hc hlast
  have hbullet :
      (N (SealedPhaseEdge ring i (.live p))).b =
        (2 : Fin 3) := hphase.1.2.1
  have hsignal :
      (N (SealedPhaseEdge ring i (.live p))).sg = false :=
    hphase.2.2 p (Nat.le_refl p.val)
  have hjl : (N j).l = true := hc.2.2.2.2.1
  have hkill := tagged_q_live_unshielded_native
    ring N (SealedPhaseEdge ring i (.live p)) j
      hne hnext hbullet hsignal hjl hinv.2.2
  have htarget :
      ((taggedQNext ring j b (by omega : 2 ≤ n)
        hports N raw) j).l = false := by
    unfold taggedQNext
    rw [heff]
    exact hkill
  exact Or.inr (Or.inl htarget)


/-! The exact non-Ready Stage table is a one-credit-decreasing
transition, except for a live bullet at its terminal service.
The latter cannot survive in the reached Q domain (previous lemma). -/

/-- Pure arithmetic of insideStage, with exactly one excluded
transition: final live absorption into a surviving leader. -/
theorem tagged_close_nonready_inside_credit {n : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (i : Fin n) (a r : Nat) (phase : SealedPhase n)
    (hp : SealedPhaseHolds ring N i a phase)
    (hnr : phase ≠ .ready) :
    (∃ p : Fin n,
      phase = .live p ∧ r = p.val ∧ p.val + 1 = a) ∨
    (taggedCloseCredit a
      (SealedCloseProof.insideStage a
        (SealedCloseProof.fromPhase phase) r) ≤
      taggedCloseCredit a (SealedCloseProof.fromPhase phase) ∧
     (r = SealedCloseProof.nominated
        (SealedCloseProof.fromPhase phase) →
      taggedCloseCredit a
        (SealedCloseProof.insideStage a
          (SealedCloseProof.fromPhase phase) r) + 1 ≤
      taggedCloseCredit a (SealedCloseProof.fromPhase phase))) := by
  cases phase with
  | ready =>
      exact False.elim (hnr rfl)
  | dummy p =>
      have hpos : p.val < a := hp.1.1
      right
      by_cases hh : r = p.val
      · by_cases hd : p.val + 1 = a
        · by_cases hz : p.val = 0
          · constructor
            · simp (disch := omega) [SealedCloseProof.fromPhase,
                SealedCloseProof.insideStage, taggedCloseCredit,
                hh, hd, hz, if_pos, if_neg] <;> omega
            · intro hnom
              simp (disch := omega) [SealedCloseProof.fromPhase,
                SealedCloseProof.insideStage, taggedCloseCredit,
                hh, hd, hz, if_pos, if_neg] <;> omega
          · constructor
            · simp [SealedCloseProof.fromPhase,
                SealedCloseProof.insideStage, taggedCloseCredit,
                hh, hd, hz] <;> omega
            · intro hnom
              simp [SealedCloseProof.fromPhase,
                SealedCloseProof.insideStage, taggedCloseCredit,
                hh, hd, hz] <;> omega
        · constructor
          · simp [SealedCloseProof.fromPhase,
              SealedCloseProof.insideStage, taggedCloseCredit,
              hh, hd] <;> omega
          · intro hnom
            simp [SealedCloseProof.fromPhase,
              SealedCloseProof.insideStage, taggedCloseCredit,
              hh, hd] <;> omega
      · constructor
        · simp [SealedCloseProof.fromPhase,
            SealedCloseProof.insideStage, taggedCloseCredit,
            hh]
        · intro hnom
          have heq : r = p.val := hnom
          exact False.elim (hh heq)
  | live p =>
      have hpos : p.val < a := hp.1.1
      by_cases hh : r = p.val
      · by_cases hd : p.val + 1 = a
        · exact Or.inl ⟨p, rfl, hh, hd⟩
        · right
          constructor
          · simp [SealedCloseProof.fromPhase,
              SealedCloseProof.insideStage, taggedCloseCredit,
              hh, hd] <;> omega
          · intro hnom
            simp [SealedCloseProof.fromPhase,
              SealedCloseProof.insideStage, taggedCloseCredit,
              hh, hd] <;> omega
      · right
        constructor
        · simp [SealedCloseProof.fromPhase,
            SealedCloseProof.insideStage, taggedCloseCredit, hh]
        · intro hnom
          have heq : r = p.val := hnom
          exact False.elim (hh heq)
  | returning q =>
      have hqpos : 1 ≤ q.val := hp.2.2.1
      have hqbound : q.val < a := hp.2.2.2.1
      right
      by_cases hh : r + 1 = q.val
      · by_cases hz : r = 0
        · constructor
          · simp (disch := omega) [SealedCloseProof.fromPhase,
              SealedCloseProof.insideStage, taggedCloseCredit,
              hh, hz, if_pos, if_neg] <;> omega
          · intro hnom
            simp (disch := omega) [SealedCloseProof.fromPhase,
              SealedCloseProof.insideStage, taggedCloseCredit,
              hh, hz, if_pos, if_neg] <;> omega
        · constructor
          · simp [SealedCloseProof.fromPhase,
              SealedCloseProof.insideStage, taggedCloseCredit,
              hh, hz] <;> omega
          · intro hnom
            simp [SealedCloseProof.fromPhase,
              SealedCloseProof.insideStage, taggedCloseCredit,
              hh, hz] <;> omega
      · constructor
        · simp [SealedCloseProof.fromPhase,
            SealedCloseProof.insideStage, taggedCloseCredit, hh]
        · intro hnom
          have heq : r = q.val - 1 := hnom
          have hend : r + 1 = q.val := by omega
          exact False.elim (hh hend)

/-- A non-Ready phase is unchanged by the incoming table; no
incoming interaction is charged as its nominated progress edge. -/
theorem tagged_close_nonready_incoming_credit {n : Nat}
    (a : Nat) (phase : SealedPhase n) (hnr : phase ≠ .ready) :
    taggedCloseCredit a
      (SealedCloseProof.incomingStage
        (SealedCloseProof.fromPhase phase)) =
      taggedCloseCredit a (SealedCloseProof.fromPhase phase) := by
  cases phase with
  | ready => exact False.elim (hnr rfl)
  | dummy p => rfl
  | live p => rfl
  | returning q => rfl


/-- The target-only Q redirection does not affect any other raw edge. -/
theorem tagged_q_effective_of_other_raw {n : Nat}
    (ring : DirectedRing n) (j : Fin n) (b : Nat)
    (hn : 2 ≤ n) (hports : ring.leftNeighbor j ≠ j)
    (N : TripleNativeState n) (e : Fin n)
    (hne : e ≠ j) :
    taggedQEffective ring j b hn hports N e = e := by
  classical
  simp [taggedQEffective, taggedRedirection,
    ControlledSchedulerMass.Redirection.effective, hne]

/-- Every physically valid nonready attacker phase has positive
D.11 credit. This is the terminal-success n-unit budget. -/
theorem tagged_close_nonready_credit_positive {n : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (i : Fin n) (a : Nat) (phase : SealedPhase n)
    (ha : 1 ≤ a)
    (hp : SealedPhaseHolds ring N i a phase)
    (hnr : phase ≠ .ready) :
    1 ≤ taggedCloseCredit a
      (SealedCloseProof.fromPhase phase) := by
  cases phase with
  | ready => exact False.elim (hnr rfl)
  | dummy p =>
      have hb : p.val < a := hp.1.1
      simp only [SealedCloseProof.fromPhase, taggedCloseCredit]
      omega
  | live p =>
      have hb : p.val < a := hp.1.1
      simp only [SealedCloseProof.fromPhase, taggedCloseCredit]
      omega
  | returning q =>
      have hq : 1 ≤ q.val := hp.2.2.1
      simp only [SealedCloseProof.fromPhase, taggedCloseCredit]
      omega

/-- Exact weak D.11 nonincrease on every raw Q edge, with an n-unit
strict drop whenever the chosen physical nonready progress edge is
selected. The sole exceptional live-terminal Stage is eliminated by
the literal native collision with unshielded j. -/
theorem tagged_q_nonready_child_bounds {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (seed N : TripleNativeState n) (raw : Fin n)
    (hstart : TaggedTriple ring i j k a b seed)
    (hclean : TaggedCleanDummy ring i j a b seed)
    (hreach : TaggedQActiveReach ring i j k a b
      (by omega : 2 ≤ n) hports seed N)
    (hnotold : ¬ TaggedDeleted i j k N)
    (phase : SealedPhase n)
    (hp : SealedPhaseHolds ring N i a phase)
    (hnr : phase ≠ .ready) :
    taggedQBellman ring i j k a
      (taggedQNext ring j b (by omega : 2 ≤ n)
        hports N raw) ≤
      taggedQBellman ring i j k a N ∧
    (raw = SealedPhaseEdge ring i phase →
      taggedQBellman ring i j k a
        (taggedQNext ring j b (by omega : 2 ≤ n)
          hports N raw) + n ≤
      taggedQBellman ring i j k a N) := by
  let eff := taggedQEffective ring j b
    (by omega : 2 ≤ n) hports N raw
  let r := SealedCloseProof.position ring i eff
  have inv :=
    tagged_q_reachable_invariants hnthree ring
      i j k a b hports seed hstart hclean hreach
  have hc : ConsecutiveNative ring N i j a := inv.1.2.1
  have ha : 1 ≤ a := hc.1
  have hbefore : taggedQBellman ring i j k a N =
      n * taggedCloseCredit a
        (SealedCloseProof.fromPhase phase) := by
    calc
      taggedQBellman ring i j k a N =
        taggedAttackerBellman n a phase :=
          tagged_q_bellman_eq_phase
            ring N i j k a phase hnotold hp
      _ = n * taggedCloseCredit a
          (SealedCloseProof.fromPhase phase) :=
        tagged_close_credit_from_phase n a phase
  by_cases hdel : TaggedDeleted i j k
      (taggedQNext ring j b (by omega : 2 ≤ n)
        hports N raw)
  · have hzero :=
      tagged_q_bellman_deleted_zero ring
        (taggedQNext ring j b (by omega : 2 ≤ n)
          hports N raw) i j k a hdel
    have hpositive : 1 ≤ taggedCloseCredit a
        (SealedCloseProof.fromPhase phase) :=
      tagged_close_nonready_credit_positive
        ring N i a phase ha hp hnr
    constructor
    · rw [hzero]
      exact Nat.zero_le _
    · intro _
      rw [hzero, Nat.zero_add, hbefore]
      calc
        n = n * 1 := (Nat.mul_one n).symm
        _ ≤ n * taggedCloseCredit a
            (SealedCloseProof.fromPhase phase) :=
          Nat.mul_le_mul_left n hpositive
  · have hchild := tagged_q_child_bellman_stage
      hnthree ring i j k a b hports seed N raw
      hstart hclean hreach phase hp hdel
    by_cases hr : r.val < a
    · have htable : sealedCloseTable ring i a eff phase =
          SealedCloseProof.insideStage a
            (SealedCloseProof.fromPhase phase) r.val := by
        change (if r.val < a then
            SealedCloseProof.insideStage a
              (SealedCloseProof.fromPhase phase) r.val
           else if r.val + 1 = n then
             SealedCloseProof.incomingStage
               (SealedCloseProof.fromPhase phase)
           else SealedCloseProof.fromPhase phase) = _
        exact if_pos hr
      rcases tagged_close_nonready_inside_credit
          ring N i a r.val phase hp hnr with
        ⟨p, hphaseEq, hhit, hlast⟩ | ⟨hweak, hstrict⟩
      · have hphaseLive :
            SealedPhaseHolds ring N i a (.live p) := by
          simpa only [hphaseEq] using hp
        have heSite : eff = sealedSite ring i r.val :=
          sealed_close_edge_of_position ring i eff r.val rfl
        have heff :
            eff = SealedPhaseEdge ring i (.live p) := by
          calc
            eff = sealedSite ring i r.val := heSite
            _ = sealedSite ring i p.val := by rw [hhit]
            _ = SealedPhaseEdge ring i (.live p) := rfl
        have hkill := tagged_q_terminal_live_boundary
          hnthree ring i j k a b hports
            seed N raw p hstart hclean hreach
            hphaseLive hlast heff
        exact False.elim (hdel hkill)
      · have hnom : SealedPhaseEdge ring i phase ≠ j :=
          sealed_close_nominated_ne_right
            ring N i j a phase hc hp
        have hnomR : raw = SealedPhaseEdge ring i phase →
            r.val = SealedCloseProof.nominated
              (SealedCloseProof.fromPhase phase) := by
          intro he
          have hE : eff = SealedPhaseEdge ring i phase := by
            dsimp [eff]
            rw [he]
            exact tagged_q_effective_of_other_raw
              ring j b (by omega : 2 ≤ n)
              hports N (SealedPhaseEdge ring i phase) hnom
          change (SealedCloseProof.position ring i eff).val =
            SealedCloseProof.nominated
              (SealedCloseProof.fromPhase phase)
          rw [hE]
          exact sealed_close_nominated_position
            ring N i j a phase hc hp
        constructor
        · calc
            taggedQBellman ring i j k a
                (taggedQNext ring j b
                  (by omega : 2 ≤ n) hports N raw) =
              n * taggedCloseCredit a
                (sealedCloseTable ring i a eff phase) := hchild
            _ = n * taggedCloseCredit a
                (SealedCloseProof.insideStage a
                  (SealedCloseProof.fromPhase phase) r.val) := by
              rw [htable]
            _ ≤ n * taggedCloseCredit a
                (SealedCloseProof.fromPhase phase) :=
              Nat.mul_le_mul_left n hweak
            _ = taggedQBellman ring i j k a N := hbefore.symm
        · intro he
          calc
            taggedQBellman ring i j k a
                (taggedQNext ring j b
                  (by omega : 2 ≤ n) hports N raw) + n =
              n * (taggedCloseCredit a
                (sealedCloseTable ring i a eff phase) + 1) := by
              rw [hchild, Nat.mul_add, Nat.mul_one]
            _ = n * (taggedCloseCredit a
                (SealedCloseProof.insideStage a
                  (SealedCloseProof.fromPhase phase) r.val) + 1) := by
              rw [htable]
            _ ≤ n * taggedCloseCredit a
                (SealedCloseProof.fromPhase phase) :=
              Nat.mul_le_mul_left n (hstrict (hnomR he))
            _ = taggedQBellman ring i j k a N := hbefore.symm
    · have htable : taggedCloseCredit a
          (sealedCloseTable ring i a eff phase) =
          taggedCloseCredit a
            (SealedCloseProof.fromPhase phase) := by
        change taggedCloseCredit a
          (if r.val < a then
            SealedCloseProof.insideStage a
              (SealedCloseProof.fromPhase phase) r.val
           else if r.val + 1 = n then
             SealedCloseProof.incomingStage
               (SealedCloseProof.fromPhase phase)
           else SealedCloseProof.fromPhase phase) =
          taggedCloseCredit a
            (SealedCloseProof.fromPhase phase)
        simp only [if_neg hr]
        by_cases hwrap : r.val + 1 = n
        · simpa only [if_pos hwrap] using
            tagged_close_nonready_incoming_credit a phase hnr
        · simp only [if_neg hwrap]
      constructor
      · apply Nat.le_of_eq
        calc
          taggedQBellman ring i j k a
              (taggedQNext ring j b
                (by omega : 2 ≤ n) hports N raw) =
            n * taggedCloseCredit a
              (sealedCloseTable ring i a eff phase) := hchild
          _ = n * taggedCloseCredit a
              (SealedCloseProof.fromPhase phase) := by rw [htable]
          _ = taggedQBellman ring i j k a N := hbefore.symm
      · intro he
        have hnom : SealedPhaseEdge ring i phase ≠ j :=
          sealed_close_nominated_ne_right
            ring N i j a phase hc hp
        have hE : eff = SealedPhaseEdge ring i phase := by
          dsimp [eff]
          rw [he]
          exact tagged_q_effective_of_other_raw
            ring j b (by omega : 2 ≤ n)
            hports N (SealedPhaseEdge ring i phase) hnom
        have hnomR :
            r.val = SealedCloseProof.nominated
                (SealedCloseProof.fromPhase phase) := by
          change (SealedCloseProof.position ring i eff).val =
            SealedCloseProof.nominated
              (SealedCloseProof.fromPhase phase)
          rw [hE]
          exact sealed_close_nominated_position
            ring N i j a phase hc hp
        have hnomlt := sealed_close_nominated_lt
          ring N i j a phase hc hp
        exact False.elim (hr (by omega))


/-! Ready-stage arithmetic, before physical row classification. -/

/-- Every surviving Ready-stage child has credit at most the
incoming Dummy(0) credit: the largest possible one-edge increase
is 2a-1 unscaled units. -/
theorem tagged_close_ready_stage_upper
    (a pop r : Nat) (ha : 1 ≤ a) :
    taggedCloseCredit a
      (if r < a then
        SealedCloseProof.insideStage a .ready r
       else if r + 1 = pop then
        SealedCloseProof.incomingStage .ready
       else .ready) ≤
    taggedCloseCredit a .ready + (2 * a - 1) := by
  by_cases hr : r < a
  · by_cases hz : r = 0
    · by_cases hshort : a = 1
      · simp [hr, hz, hshort, taggedCloseCredit,
          SealedCloseProof.insideStage] <;> omega
      · simp (disch := omega) [hr, hz, hshort, taggedCloseCredit,
          SealedCloseProof.insideStage, if_pos, if_neg] <;> omega
    · simp [hr, hz, taggedCloseCredit,
        SealedCloseProof.insideStage] <;> omega
  · by_cases hi : r + 1 = pop
    · simp [hr, hi, taggedCloseCredit,
        SealedCloseProof.incomingStage] <;> omega
    · simp [hr, hi, taggedCloseCredit] <;> omega

/-- Except at the true incoming physical service, all surviving
Ready-stage children are nonincreasing. The outgoing Ready
launch has a smaller credit, not a larger one. -/
theorem tagged_close_ready_stage_weak
    (a pop r : Nat) (ha : 1 ≤ a)
    (hnotIncoming : r + 1 ≠ pop) :
    taggedCloseCredit a
      (if r < a then
        SealedCloseProof.insideStage a .ready r
       else if r + 1 = pop then
        SealedCloseProof.incomingStage .ready
       else .ready) ≤
      taggedCloseCredit a .ready := by
  by_cases hr : r < a
  · by_cases hz : r = 0
    · by_cases hshort : a = 1
      · simp [hr, hz, hshort, taggedCloseCredit,
          SealedCloseProof.insideStage] <;> omega
      · simp (disch := omega) [hr, hz, hshort, taggedCloseCredit,
          SealedCloseProof.insideStage, if_pos, if_neg] <;> omega
    · simp [hr, hz, taggedCloseCredit,
        SealedCloseProof.insideStage] <;> omega
  · simp [hr, hnotIncoming, taggedCloseCredit]

/-- Left ports at distinct leader sites are distinct: applying the
clockwise right-neighbor operation recovers the original leaders. -/
theorem tagged_q_left_ports_distinct {n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (i j : Fin n) (hij : i ≠ j) :
    ring.leftNeighbor i ≠ ring.leftNeighbor j := by
  intro he
  have hh := congrArg ring.rightNeighbor he
  rw [tagged_right_of_left hn ring i,
      tagged_right_of_left hn ring j] at hh
  exact hij hh

/-- A redirected raw service cannot create an incoming attacker
service that was not already the raw incoming letter: the new
effective L_j is distinct from L_i because i≠j. -/
theorem tagged_q_no_new_attacker_incoming {n : Nat}
    (ring : DirectedRing n) (i j : Fin n) (b : Nat)
    (hn : 2 ≤ n) (hports : ring.leftNeighbor j ≠ j)
    (hij : i ≠ j)
    (N : TripleNativeState n) (raw : Fin n)
    (hne : raw ≠ ring.leftNeighbor i) :
    taggedQEffective ring j b hn hports N raw ≠
      ring.leftNeighbor i := by
  classical
  have hleft : ring.leftNeighbor j ≠ ring.leftNeighbor i :=
    Ne.symm (tagged_q_left_ports_distinct hn ring i j hij)
  by_cases he : (taggedRedirection ring j b hn hports).gate N = true ∧
      raw = (taggedRedirection ring j b hn hports).portB N
  · have heff : taggedQEffective ring j b hn hports N raw =
        ring.leftNeighbor j := by
      unfold taggedQEffective
      simp only [ControlledSchedulerMass.Redirection.effective,
        if_pos he]
      try rfl
    rw [heff]
    exact hleft
  · have heff : taggedQEffective ring j b hn hports N raw =
        raw := by
      unfold taggedQEffective
      simp only [ControlledSchedulerMass.Redirection.effective,
        if_neg he]
    rw [heff]
    exact hne

/-- If a Q-effective physical service is not the incoming edge of i,
its source-relative offset cannot be n-1. -/
theorem tagged_q_nonincoming_offset {n : Nat}
    (ring : DirectedRing n) (i e : Fin n)
    (hne : e ≠ ring.leftNeighbor i) :
    (SealedCloseProof.position ring i e).val + 1 ≠ n := by
  intro h
  exact hne ((sealed_close_incoming_iff ring i e).1 h)


/-- Every reachable Ready attacker Q child is bounded by the
incoming Dummy credit; if the *raw* service is not its actual
incoming edge, its Bellman value is nonincreasing. -/
theorem tagged_q_ready_child_bounds {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (seed N : TripleNativeState n) (raw : Fin n)
    (hstart : TaggedTriple ring i j k a b seed)
    (hclean : TaggedCleanDummy ring i j a b seed)
    (hreach : TaggedQActiveReach ring i j k a b
      (by omega : 2 ≤ n) hports seed N)
    (hnotOld : ¬ TaggedDeleted i j k N)
    (hready : SealedCleanReady ring N i a) :
    taggedQBellman ring i j k a
      (taggedQNext ring j b (by omega : 2 ≤ n)
        hports N raw) ≤
      taggedQBellman ring i j k a N + n * (2 * a - 1) ∧
    (raw ≠ ring.leftNeighbor i →
      taggedQBellman ring i j k a
        (taggedQNext ring j b (by omega : 2 ≤ n)
          hports N raw) ≤
      taggedQBellman ring i j k a N) := by
  let eff := taggedQEffective ring j b
    (by omega : 2 ≤ n) hports N raw
  let r := SealedCloseProof.position ring i eff
  have hinv := tagged_q_reachable_invariants
    hnthree ring i j k a b hports seed
      hstart hclean hreach
  have hc : ConsecutiveNative ring N i j a := hinv.1.2.1
  have ha : 1 ≤ a := hc.1
  have hij : i ≠ j := sealed_consecutive_endpoints_ne
    ring N i j a hc
  have hbefore :
      taggedQBellman ring i j k a N =
        n * taggedCloseCredit a .ready := by
    calc
      taggedQBellman ring i j k a N =
        taggedAttackerBellman n a .ready :=
          tagged_q_bellman_eq_phase
            ring N i j k a .ready hnotOld hready
      _ = n * taggedCloseCredit a .ready := rfl
  by_cases hdel : TaggedDeleted i j k
      (taggedQNext ring j b (by omega : 2 ≤ n)
        hports N raw)
  · have hzero := tagged_q_bellman_deleted_zero
      ring (taggedQNext ring j b (by omega : 2 ≤ n)
        hports N raw) i j k a hdel
    constructor
    · rw [hzero]
      exact Nat.zero_le _
    · intro _
      rw [hzero]
      exact Nat.zero_le _
  · have hchild := tagged_q_child_bellman_stage
      hnthree ring i j k a b hports
      seed N raw hstart hclean hreach .ready hready hdel
    have htable :
        sealedCloseTable ring i a eff (.ready : SealedPhase n) =
          (if r.val < a then
            SealedCloseProof.insideStage a .ready r.val
           else if r.val + 1 = n then
            SealedCloseProof.incomingStage .ready
           else .ready) := rfl
    have hcreditUpper :=
      tagged_close_ready_stage_upper a n r.val ha
    have hupper : taggedCloseCredit a
        (sealedCloseTable ring i a eff (.ready : SealedPhase n)) ≤
        taggedCloseCredit a .ready + (2 * a - 1) := by
      rw [htable]
      exact hcreditUpper
    constructor
    · calc
        taggedQBellman ring i j k a
            (taggedQNext ring j b
              (by omega : 2 ≤ n) hports N raw) =
          n * taggedCloseCredit a
            (sealedCloseTable ring i a eff .ready) := hchild
        _ ≤ n * (taggedCloseCredit a .ready + (2 * a - 1)) :=
          Nat.mul_le_mul_left n hupper
        _ = taggedQBellman ring i j k a N + n * (2 * a - 1) := by
          rw [Nat.mul_add, hbefore]
    · intro hnotIncoming
      have hnotEff : eff ≠ ring.leftNeighbor i :=
        tagged_q_no_new_attacker_incoming
          ring i j b (by omega : 2 ≤ n)
          hports hij N raw hnotIncoming
      have hnotr : r.val + 1 ≠ n :=
        tagged_q_nonincoming_offset ring i eff hnotEff
      have hweak : taggedCloseCredit a
          (sealedCloseTable ring i a eff (.ready : SealedPhase n)) ≤
          taggedCloseCredit a .ready := by
        rw [htable]
        exact tagged_close_ready_stage_weak a n r.val ha hnotr
      calc
        taggedQBellman ring i j k a
            (taggedQNext ring j b
              (by omega : 2 ≤ n) hports N raw) =
          n * taggedCloseCredit a
            (sealedCloseTable ring i a eff .ready) := hchild
        _ ≤ n * taggedCloseCredit a .ready :=
          Nat.mul_le_mul_left n hweak
        _ = taggedQBellman ring i j k a N := hbefore.symm


/-- A Ready initiator fires live before contacting its responder.
If that responder is an unshielded leader, it is deleted, even
if it simultaneously fires a dummy. -/
theorem tagged_q_ready_unshielded_collision_row
    (x y : CertNative)
    (hxl : x.l = true) (hxsg : x.sg = true)
    (hyl : y.l = true) (hysh : y.sh = false) :
    (certLiteralEPair x y).2.l = false := by
  rcases x with ⟨xl, xb, xsh, xsg⟩
  rcases y with ⟨yl, yb, ysh, ysg⟩
  simp only at hxl hxsg hyl hysh
  subst xl xsg yl ysh
  cases ysg <;> simp [certLiteralEPair]

/-- In gap one, the actual raw outgoing Ready attacker service
immediately deletes j; it cannot survive as Ready. -/
theorem tagged_q_ready_gap_one_deletes {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (seed N : TripleNativeState n)
    (hstart : TaggedTriple ring i j k a b seed)
    (hclean : TaggedCleanDummy ring i j a b seed)
    (hreach : TaggedQActiveReach ring i j k a b
      (by omega : 2 ≤ n) hports seed N)
    (hready : SealedCleanReady ring N i a)
    (hone : a = 1) :
    TaggedDeleted i j k
      (taggedQNext ring j b (by omega : 2 ≤ n)
        hports N i) := by
  have hinv := tagged_q_reachable_invariants
    hnthree ring i j k a b hports seed hstart hclean hreach
  have hc : ConsecutiveNative ring N i j a := hinv.1.2.1
  have hij : i ≠ j := sealed_consecutive_endpoints_ne
    ring N i j a hc
  have heff : taggedQEffective ring j b (by omega : 2 ≤ n)
      hports N i = i :=
    tagged_q_effective_of_other_raw
      ring j b (by omega : 2 ≤ n) hports N i hij
  have hlast : (sealedZero ring).val + 1 = a := by
    dsimp [sealedZero]
    omega
  have hnext : ring.rightNeighbor i = j := by
    have hh := sealed_close_last_bullet_enters_right
      ring N i j a (sealedZero ring) hc hlast
    simpa [SealedPhaseEdge, sealedZero, sealedSite_zero] using hh
  have hi : (N i).l = true := hc.2.2.2.1
  have hj : (N j).l = true := hc.2.2.2.2.1
  have hsignal : (N i).sg = true := by
    simpa only [sealedAt_zero] using hready.1
  have hrow := tagged_q_ready_unshielded_collision_row
    (N i) (N j) hi hsignal hj hinv.2.2
  have hpair : nativeE ring N i j =
      (certLiteralEPair (N i) (N j)).2 := by
    simp [nativeE, hnext, Ne.symm hij]
  have hdeath : (nativeE ring N i j).l = false := by
    rw [hpair]
    exact hrow
  have htarget :
      ((taggedQNext ring j b (by omega : 2 ≤ n)
        hports N i) j).l = false := by
    unfold taggedQNext
    rw [heff]
    exact hdeath
  exact Or.inr (Or.inl htarget)

/-- The raw outgoing Ready service lowers the D.11 Bellman value
by at least 2na, including the gap-one terminal case. -/
theorem tagged_q_ready_outgoing_drop {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (seed N : TripleNativeState n)
    (hstart : TaggedTriple ring i j k a b seed)
    (hclean : TaggedCleanDummy ring i j a b seed)
    (hreach : TaggedQActiveReach ring i j k a b
      (by omega : 2 ≤ n) hports seed N)
    (hnotOld : ¬ TaggedDeleted i j k N)
    (hready : SealedCleanReady ring N i a) :
    taggedQBellman ring i j k a
      (taggedQNext ring j b (by omega : 2 ≤ n)
        hports N i) + n * (2 * a) ≤
      taggedQBellman ring i j k a N := by
  have hinv := tagged_q_reachable_invariants
    hnthree ring i j k a b hports seed hstart hclean hreach
  have hc : ConsecutiveNative ring N i j a := hinv.1.2.1
  have ha : 1 ≤ a := hc.1
  have hij : i ≠ j := sealed_consecutive_endpoints_ne
    ring N i j a hc
  have heff : taggedQEffective ring j b (by omega : 2 ≤ n)
      hports N i = i :=
    tagged_q_effective_of_other_raw
      ring j b (by omega : 2 ≤ n) hports N i hij
  have hbefore : taggedQBellman ring i j k a N =
      n * (3 * a - 1) := by
    exact tagged_q_bellman_eq_phase
      ring N i j k a .ready hnotOld hready
  by_cases hone : a = 1
  · have hdel := tagged_q_ready_gap_one_deletes
      hnthree ring i j k a b hports
        seed N hstart hclean hreach hready hone
    have hzero := tagged_q_bellman_deleted_zero
      ring (taggedQNext ring j b (by omega : 2 ≤ n)
        hports N i) i j k a hdel
    rw [hzero, Nat.zero_add, hbefore]
    exact Nat.mul_le_mul_left n (by omega)
  · have hrzero :
        (SealedCloseProof.position ring i i).val = 0 := by
      have hh := sealed_close_nominated_position
        ring N i j a (.ready : SealedPhase n) hc hready
      simpa [SealedPhaseEdge, SealedCloseProof.fromPhase,
        SealedCloseProof.nominated] using hh
    have htable :
        sealedCloseTable ring i a i (.ready : SealedPhase n) =
          .bullet true 1 := by
      have hapos : 0 < a := by omega
      simp [sealedCloseTable, hrzero, hapos, hone,
        SealedCloseProof.fromPhase,
        SealedCloseProof.insideStage]
    by_cases hdel : TaggedDeleted i j k
        (taggedQNext ring j b (by omega : 2 ≤ n) hports N i)
    · have hzero := tagged_q_bellman_deleted_zero
        ring (taggedQNext ring j b (by omega : 2 ≤ n)
          hports N i) i j k a hdel
      rw [hzero, Nat.zero_add, hbefore]
      exact Nat.mul_le_mul_left n (by omega)
    · have hchild := tagged_q_child_bellman_stage
        hnthree ring i j k a b hports
        seed N i hstart hclean hreach .ready hready hdel
      have hvalue :
          taggedQBellman ring i j k a
            (taggedQNext ring j b (by omega : 2 ≤ n)
              hports N i) = n * (a - 1) := by
        simpa only [heff, htable, taggedCloseCredit] using hchild
      calc
        taggedQBellman ring i j k a
            (taggedQNext ring j b (by omega : 2 ≤ n)
              hports N i) + n * (2 * a) =
          n * (a - 1) + n * (2 * a) := by rw [hvalue]
        _ = n * ((a - 1) + 2 * a) := by rw [Nat.mul_add]
        _ ≤ n * (3 * a - 1) :=
          Nat.mul_le_mul_left n (by omega)
        _ = taggedQBellman ring i j k a N := hbefore.symm


/-- On a ring of at least two sites the outgoing and incoming
physical edges at any attacker are distinct. -/
private theorem tagged_q_incident_edges_distinct {n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n) (i : Fin n) :
    i ≠ ring.leftNeighbor i := by
  intro he
  have hr : ring.rightNeighbor i = i := by
    calc
      ring.rightNeighbor i =
          ring.rightNeighbor (ring.leftNeighbor i) := by rw [← he]
      _ = i := tagged_right_of_left hn ring i
  have hv := congrArg Fin.val hr
  change (i.val + 1) % n = i.val at hv
  by_cases hsmall : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hsmall] at hv
    omega
  · have heq : i.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega

/-- D.12 on precisely the inductively Q-reachable, nondeleted
paired-sealed states; no unproved drift premise is passed here.
Nonready: nominated n-drop plus all-edge nonincrease.
Ready: compensate outgoing Live and incoming Dummy with D.11's
two-edge identity, including raw R_j redirection and two-leader
overlap handled by the actual native stage and terminal rows. -/
theorem tagged_q_reachable_drift {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (seed N : TripleNativeState n)
    (hstart : TaggedTriple ring i j k a b seed)
    (hclean : TaggedCleanDummy ring i j a b seed)
    (hreach : TaggedQActiveReach ring i j k a b
      (by omega : 2 ≤ n) hports seed N)
    (hnot : ¬ TaggedDeleted i j k N) :
    n + (List.ofFn (fun e : Fin n =>
      taggedQBellman ring i j k a
        (taggedQNext ring j b (by omega : 2 ≤ n)
          hports N e))).sum ≤
      n * taggedQBellman ring i j k a N := by
  let V := taggedQBellman ring i j k a
  let Q := taggedQNext ring j b (by omega : 2 ≤ n) hports
  let child : Fin n → Nat := fun e => V (Q N e)
  have hinv := tagged_q_reachable_invariants
    hnthree ring i j k a b hports seed hstart hclean hreach
  let phase := taggedQAttackerPhase ring i a N
  have hp : SealedPhaseHolds ring N i a phase :=
    tagged_q_attacker_phase_valid ring i a N hinv.2.1.1
  by_cases hready : phase = .ready
  · have hphys : SealedCleanReady ring N i a := by
      show SealedPhaseHolds ring N i a .ready
      exact hready ▸ hp
    have ha : 1 ≤ a := hinv.1.2.1.1
    have hbefore : V N = n * (3 * a - 1) := by
      exact tagged_q_bellman_eq_phase
        ring N i j k a .ready hnot hphys
    have hOut : child i + n * (2 * a) ≤ V N :=
      tagged_q_ready_outgoing_drop hnthree ring
        i j k a b hports seed N
        hstart hclean hreach hnot hphys
    have hIn : child (ring.leftNeighbor i) ≤
        V N + n * (2 * a - 1) :=
      (tagged_q_ready_child_bounds hnthree ring
        i j k a b hports seed N (ring.leftNeighbor i)
        hstart hclean hreach hnot hphys).1
    have hOutCredit : child i ≤ n * (a - 1) := by
      have heq : n * (a - 1) + n * (2 * a) =
          n * (3 * a - 1) := by
        have harg : (a - 1) + 2 * a = 3 * a - 1 := by omega
        calc
          n * (a - 1) + n * (2 * a) =
              n * ((a - 1) + 2 * a) := by rw [Nat.mul_add]
          _ = n * (3 * a - 1) := by rw [harg]
      rw [hbefore] at hOut
      omega
    have hInCredit : child (ring.leftNeighbor i) ≤
        n * ((2 * a - 1) + (3 * a - 1)) := by
      have heq :
          n * (3 * a - 1) + n * (2 * a - 1) =
            n * ((2 * a - 1) + (3 * a - 1)) := by
        rw [Nat.mul_add]
        omega
      rw [hbefore] at hIn
      omega
    have hpair :
        n + child i + child (ring.leftNeighbor i) ≤
          2 * V N := by
      have hbalance := tagged_ready_two_edge_balance_scaled n a ha
      rw [hbefore]
      omega
    have hrest : ∀ e, e ≠ i →
        e ≠ ring.leftNeighbor i → child e ≤ V N := by
      intro e heOut heIn
      exact (tagged_q_ready_child_bounds hnthree ring
        i j k a b hports seed N e
        hstart hclean hreach hnot hphys).2 heIn
    have hne : i ≠ ring.leftNeighbor i :=
      tagged_q_incident_edges_distinct
        (by omega : 2 ≤ n) ring i
    exact tagged_q_ready_sum_of_two_edge_bounds
      (V N) child i (ring.leftNeighbor i)
      hne hpair hrest
  · have hweak : ∀ e : Fin n, child e ≤ V N := by
      intro e
      exact (tagged_q_nonready_child_bounds
        hnthree ring i j k a b hports seed N e
        hstart hclean hreach hnot phase hp hready).1
    have hstrict :
        child (SealedPhaseEdge ring i phase) + n ≤ V N :=
      (tagged_q_nonready_child_bounds
        hnthree ring i j k a b hports
        seed N (SealedPhaseEdge ring i phase)
        hstart hclean hreach hnot phase hp hready).2 rfl
    exact tagged_q_nonready_sum_of_edge_bounds
      (V N) child (SealedPhaseEdge ring i phase)
      hweak hstrict

/-- The stopped controlled native process has the paper's
expected duration bound with no hD12 hypothesis. The full one-step
premise is discharged by tagged_q_reachable_drift. -/
theorem tagged_q_expected_drift_bound {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (seed : TripleNativeState n)
    (hstart : TaggedTriple ring i j k a b seed)
    (hclean : TaggedCleanDummy ring i j a b seed) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (taggedQNext ring j b (by omega : 2 ≤ n) hports)
      (TaggedDeleted i j k) seed
      ((n * (5 * a - 2) : Nat) : Rat) := by
  apply tagged_q_expected_of_reachable_bellman_drift
    hnthree ring i j k a b hports seed
      hstart hclean
  intro N hr hnot
  exact tagged_q_reachable_drift
    hnthree ring i j k a b hports
      seed N hstart hclean hr hnot

end L3


/-! ## Target-sector row lift and discrete D.14 arithmetic

The positive theorems in this
section cover:
* an actual Q-surviving step of target sector B through nativeE and
  sealed_close_step_stage;
* the non-Ready nominated-service rank progress at that target;
* two pure exact integer row identities and the non-Jensen secant
  inequality for powers of two.

They DO NOT imply D.10's *word-level* counting inequality by
themselves. Consequently D.13, D.14's probabilistic likelihood lower
bound, D.15's renewal and hmoderate are not asserted here.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

attribute [local instance low] Classical.propDecidable

/-- Physically legal internal stages have exactly the offset bounds
required by the literal SealedCloseProof stage transition. -/
private def taggedTargetStageAdmissible (b : Nat) :
    SealedCloseProof.Stage → Prop
  | .ready => True
  | .bullet _ p => p < b
  | .returning q => 0 < q ∧ q < b

/-- An actual sealed target phase supplies those bounds. -/
private theorem tagged_target_stage_admissible_of_holds {n : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (j : Fin n) (b : Nat) (phase : SealedPhase n)
    (hp : SealedPhaseHolds ring N j b phase) :
    taggedTargetStageAdmissible b
      (SealedCloseProof.fromPhase phase) := by
  cases phase with
  | ready =>
      trivial
  | dummy p =>
      exact hp.1.1
  | live p =>
      exact hp.1.1
  | returning q =>
      have hpos : 0 < q.val := by
        have hh := hp.2.2.1
        omega
      exact ⟨hpos, hp.2.2.2.1⟩

/-- An internal service that is not the current non-Ready nominated
service leaves the exact stage unchanged. This is stronger than the
weak rank monotonicity of sealed_close_step_with_progress. -/
theorem tagged_target_stage_internal_nonhit (b r : Nat)
    (s : SealedCloseProof.Stage)
    (hvalid : taggedTargetStageAdmissible b s)
    (hnr : s ≠ .ready)
    (hmiss : r ≠ SealedCloseProof.nominated s) :
    SealedCloseProof.insideStage b s r = s := by
  cases s with
  | ready =>
      exact False.elim (hnr rfl)
  | bullet live p =>
      have hp : r ≠ p := hmiss
      simp only [SealedCloseProof.insideStage, if_neg hp]
  | returning q =>
      have hq : 0 < q := hvalid.1
      have hr : r + 1 ≠ q := by
        have hm : r ≠ q - 1 := hmiss
        omega
      simp only [SealedCloseProof.insideStage, if_neg hr]

/-- Every successful nominated non-Ready internal stage service
spends EXACTLY one unit of the target rank. Its side conditions
come from the real sealed phase, not from an invented stage. -/
theorem tagged_target_stage_nominated_rank (b : Nat)
    (hb : 2 ≤ b)
    (s : SealedCloseProof.Stage)
    (hvalid : taggedTargetStageAdmissible b s)
    (hnr : s ≠ .ready) :
    SealedCloseProof.rank b
      (SealedCloseProof.insideStage b s
        (SealedCloseProof.nominated s)) + 1 =
      SealedCloseProof.rank b s := by
  cases s with
  | ready =>
      exact False.elim (hnr rfl)
  | bullet live p =>
      have hp : p < b := hvalid
      by_cases htop : p + 1 = b
      · have hpz : p ≠ 0 := by omega
        simp [SealedCloseProof.rank, SealedCloseProof.insideStage,
          SealedCloseProof.nominated, htop, hpz] <;> omega
      · simp [SealedCloseProof.rank, SealedCloseProof.insideStage,
          SealedCloseProof.nominated, htop] <;> omega
  | returning q =>
      have hq : 0 < q := hvalid.1
      have he : q - 1 + 1 = q := by omega
      by_cases hz : q - 1 = 0
      · simp (disch := omega) [SealedCloseProof.rank, SealedCloseProof.insideStage,
          SealedCloseProof.nominated, he, hz, if_pos, if_neg] <;> omega
      · simp (disch := omega) [SealedCloseProof.rank, SealedCloseProof.insideStage,
          SealedCloseProof.nominated, he, hz, if_pos, if_neg] <;> omega

/-- The clean-dummy entrance has precisely 2b-1 remaining
nominated target hits. This is the initial value in D.10. -/
theorem tagged_target_clean_dummy_rank (b : Nat) (hb : 1 ≤ b) :
    SealedCloseProof.rank b (.bullet false 0) = 2 * b - 1 := by
  simp only [SealedCloseProof.rank, Nat.sub_zero]

/-- The exact physical target-sector version of the established
attacker stage lift. On a surviving Q edge it is the REAL
nativeE step at the effective edge, never a synthetic table step. -/
theorem tagged_q_surviving_target_stage {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (seed N : TripleNativeState n) (raw : Fin n)
    (hstart : TaggedTriple ring i j k a b seed)
    (hclean : TaggedCleanDummy ring i j a b seed)
    (hreach : TaggedQActiveReach ring i j k a b
      (by omega : 2 ≤ n) hports seed N)
    (phase : SealedPhase n)
    (hphase : SealedPhaseHolds ring N j b phase)
    (hnot : ¬ TaggedDeleted i j k
      (taggedQNext ring j b (by omega : 2 ≤ n)
        hports N raw)) :
    ∃ nextPhase : SealedPhase n,
      SealedPhaseHolds ring
        (taggedQNext ring j b (by omega : 2 ≤ n)
          hports N raw) j b nextPhase ∧
      SealedCloseProof.fromPhase nextPhase =
        sealedCloseTable ring j b
          (taggedQEffective ring j b (by omega : 2 ≤ n)
            hports N raw) phase := by
  let eff :=
    taggedQEffective ring j b (by omega : 2 ≤ n) hports N raw
  have htriple : TaggedTriple ring i j k a b N :=
    (tagged_q_reachable_invariants hnthree ring i j k a b
      hports seed hstart hclean hreach).1
  have hj : (nativeE ring N eff j).l = true := by
    cases hx : (nativeE ring N eff j).l with
    | false => exact False.elim (hnot (Or.inr (Or.inl hx)))
    | true => rfl
  have hk : (nativeE ring N eff k).l = true := by
    cases hx : (nativeE ring N eff k).l with
    | false => exact False.elim (hnot (Or.inr (Or.inr hx)))
    | true => rfl
  exact sealed_close_step_stage ring N j k b eff phase
    htriple.2.2 hphase hj hk

/-- For a non-Ready target, the real Q step has nonincreasing
target rank and a strict unit drop at its nominated physical edge.
These are one-step premises for D.10, not its word-count conclusion. -/
theorem tagged_q_target_nonready_progress {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (seed N : TripleNativeState n) (raw : Fin n)
    (hstart : TaggedTriple ring i j k a b seed)
    (hclean : TaggedCleanDummy ring i j a b seed)
    (hreach : TaggedQActiveReach ring i j k a b
      (by omega : 2 ≤ n) hports seed N)
    (phase : SealedPhase n)
    (hphase : SealedPhaseHolds ring N j b phase)
    (hnr : phase ≠ .ready)
    (hnot : ¬ TaggedDeleted i j k
      (taggedQNext ring j b (by omega : 2 ≤ n)
        hports N raw)) :
    ∃ nextPhase : SealedPhase n,
      SealedPhaseHolds ring
        (taggedQNext ring j b (by omega : 2 ≤ n)
          hports N raw) j b nextPhase ∧
      SealedPhaseProgress b nextPhase ≤
        SealedPhaseProgress b phase ∧
      (taggedQEffective ring j b (by omega : 2 ≤ n)
          hports N raw = SealedPhaseEdge ring j phase →
        SealedPhaseProgress b nextPhase + 1 ≤
          SealedPhaseProgress b phase) := by
  let eff :=
    taggedQEffective ring j b (by omega : 2 ≤ n) hports N raw
  have htriple : TaggedTriple ring i j k a b N :=
    (tagged_q_reachable_invariants hnthree ring i j k a b
      hports seed hstart hclean hreach).1
  have hj : (nativeE ring N eff j).l = true := by
    cases hx : (nativeE ring N eff j).l with
    | false => exact False.elim (hnot (Or.inr (Or.inl hx)))
    | true => rfl
  have hk : (nativeE ring N eff k).l = true := by
    cases hx : (nativeE ring N eff k).l with
    | false => exact False.elim (hnot (Or.inr (Or.inr hx)))
    | true => rfl
  obtain ⟨nextPhase, hnext, hprogress⟩ :=
    sealed_close_step_with_progress ring N j k b eff phase
      htriple.2.2 hphase hj hk
  exact ⟨nextPhase, hnext, (hprogress hnr).1,
    (hprogress hnr).2⟩

/-! ### D.14's exact discrete non-Jensen arithmetic. -/

/-- The elementary inequality 1+d ≤ 2^d, in pure Nat. -/
private theorem tagged_pow_two_covers_successor :
    ∀ d : Nat, d + 1 ≤ 2 ^ d := by
  intro d
  induction d with
  | zero =>
      decide
  | succ d ih =>
      rw [Nat.pow_succ]
      omega

/-- Globally valid integer support line through m and m+1,
with no reals and no probabilistic independence:
  (m+2-N) / 2^(m+1) ≤ 1 / 2^N.
Nat subtraction makes the negative-affine case trivially true.
This is the exact denominator-cleared secant statement. -/
theorem tagged_discrete_pow_two_secant (m N : Nat) :
    (m + 2 - N) * 2 ^ N ≤ 2 ^ (m + 1) := by
  by_cases hle : N ≤ m + 1
  · let d := m + 1 - N
    have hsum : m + 1 = N + d := by
      dsimp [d]
      omega
    have hshift : m + 2 - N = d + 1 := by
      dsimp [d]
      omega
    have hb : d + 1 ≤ 2 ^ d :=
      tagged_pow_two_covers_successor d
    calc
      (m + 2 - N) * 2 ^ N = 2 ^ N * (d + 1) := by
        rw [hshift]
        ac_rfl
      _ ≤ 2 ^ N * 2 ^ d :=
        Nat.mul_le_mul_left (2 ^ N) hb
      _ = 2 ^ (m + 1) := by
        rw [hsum, Nat.pow_add]
  · have hz : m + 2 - N = 0 := by omega
    simp only [hz, Nat.zero_mul]
    exact Nat.zero_le _

/-- Finite sums preserve the secant bound, so the deterministic
averaging step never needs a real Jensen theorem. The remaining
Q-word likelihood/compensation weights must still be constructed. -/
theorem tagged_discrete_pow_two_secant_sum
    (m K : Nat) (N : Fin K → Nat) :
    (List.ofFn (fun i : Fin K =>
      (m + 2 - N i) * 2 ^ (N i))).sum ≤
      K * 2 ^ (m + 1) := by
  calc
    (List.ofFn (fun i : Fin K =>
        (m + 2 - N i) * 2 ^ (N i))).sum ≤
      (List.ofFn (fun _ : Fin K => 2 ^ (m + 1))).sum :=
        ofFn_sum_le _ _
          (fun i => tagged_discrete_pow_two_secant m (N i))
    _ = K * 2 ^ (m + 1) := by rw [ofFn_sum_const]

/-- Numerical bound behind D.13/D.14 when b=2:
(5a-2)/(2b-1) ≤ 6. This is arithmetic only; E_Q N itself
has not been bounded by the Q-word count. -/
theorem tagged_moderate_q_two_arithmetic
    (a b : Nat) (hb : b = 2) (ha : a ≤ 2 * b) :
    5 * a - 2 ≤ 6 * (2 * b - 1) := by
  omega

/-- For b≥3, (5a-2)/(2b-1) ≤ 28/5.
The integer bound is 5(5a-2) ≤ 28(2b-1). -/
theorem tagged_moderate_q_large_arithmetic
    (a b : Nat) (hb : 3 ≤ b) (ha : a ≤ 2 * b) :
    5 * (5 * a - 2) ≤ 28 * (2 * b - 1) := by
  omega

/-- The integer numerator comparison behind 7/320 ≥ 1/52. -/
theorem tagged_moderate_q_secant_multiplier :
    320 ≤ 7 * 52 := by
  decide

end L3

/-! ## Exact stopped counting bridges -/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

attribute [local instance low] Classical.propDecidable

/-! D.13: predictable edge charge and stopped time. -/

/-- Full raw-word numerator of the total selected-edge charge. -/
noncomputable def taggedWeightedCost {S : Type} {n : Nat}
    (next : S → Fin n → S) (Terminal : S → Prop)
    (c : S → Fin n → Nat) (x : S) : Nat → Nat
  | 0 => 0
  | T + 1 =>
      if Terminal x then 0 else
        (List.ofFn (fun e : Fin n =>
          n ^ T * c x e +
            taggedWeightedCost next Terminal c (next x e) T)).sum

/-- Per-state charge, with n possible raw letters at every live step. -/
noncomputable def taggedNodeCost {S : Type} {n : Nat}
    (next : S → Fin n → S) (Terminal : S → Prop)
    (k : S → Nat) (x : S) : Nat → Nat
  | 0 => 0
  | T + 1 =>
      if Terminal x then 0 else
        n ^ (T + 1) * k x +
          (List.ofFn (fun e : Fin n =>
            taggedNodeCost next Terminal k (next x e) T)).sum

/-- General edge-vs-state comparison. No occupancy limit or
independence between time steps is used. -/
theorem tagged_weighted_le_node
    {S : Type} {n : Nat}
    (next : S → Fin n → S) (Terminal : S → Prop)
    (c : S → Fin n → Nat) (k : S → Nat)
    (hbudget : ∀ x, ¬ Terminal x →
      (List.ofFn (fun e : Fin n => c x e)).sum ≤ n * k x) :
    ∀ T x, taggedWeightedCost next Terminal c x T ≤
      taggedNodeCost next Terminal k x T := by
  classical
  intro T
  induction T with
  | zero =>
      intro x
      exact Nat.le_refl 0
  | succ T ih =>
      intro x
      by_cases ht : Terminal x
      · simp [taggedWeightedCost, taggedNodeCost, ht]
      · have hfirst :
            n ^ T * (List.ofFn (fun e : Fin n => c x e)).sum ≤
              n ^ (T + 1) * k x := by
          calc
            _ ≤ n ^ T * (n * k x) :=
              Nat.mul_le_mul_left _ (hbudget x ht)
            _ = n ^ (T + 1) * k x := by
              rw [Nat.pow_succ]
              ac_rfl
        have hchildren :
            (List.ofFn (fun e : Fin n =>
              taggedWeightedCost next Terminal c (next x e) T)).sum ≤
            (List.ofFn (fun e : Fin n =>
              taggedNodeCost next Terminal k (next x e) T)).sum := by
          apply ofFn_sum_le
          intro e
          exact ih (next x e)
        simp only [taggedWeightedCost, taggedNodeCost, if_neg ht]
        calc
          (List.ofFn (fun e : Fin n =>
            n ^ T * c x e +
              taggedWeightedCost next Terminal c (next x e) T)).sum =
              n ^ T * (List.ofFn (fun e : Fin n => c x e)).sum +
                (List.ofFn (fun e : Fin n =>
                  taggedWeightedCost next Terminal c (next x e) T)).sum := by
            rw [ofFn_sum_add, ofFn_sum_mul_left]
          _ ≤ n ^ (T + 1) * k x +
                (List.ofFn (fun e : Fin n =>
                  taggedNodeCost next Terminal k (next x e) T)).sum :=
            Nat.add_le_add hfirst hchildren

/-- Unit node charge is the existing stopping-time numerator. -/
theorem tagged_node_one_eq_cost
    {S : Type} {n : Nat}
    (next : S → Fin n → S) (Terminal : S → Prop) :
    ∀ T x, taggedNodeCost next Terminal (fun _ => 1) x T =
      costNumerator next Terminal x T := by
  classical
  intro T
  induction T with
  | zero =>
      intro x
      simp only [taggedNodeCost, costNumerator_zero]
  | succ T ih =>
      intro x
      by_cases ht : Terminal x
      · rw [costNumerator_terminal next Terminal x ht (T + 1)]
        simp [taggedNodeCost, ht]
      · calc
          taggedNodeCost next Terminal (fun _ => 1) x (T + 1) =
              n ^ (T + 1) +
                (List.ofFn (fun e : Fin n =>
                  taggedNodeCost next Terminal (fun _ => 1)
                    (next x e) T)).sum := by
              simp only [taggedNodeCost, if_neg ht, Nat.mul_one]
          _ = n ^ (T + 1) +
                (List.ofFn (fun e : Fin n =>
                  costNumerator next Terminal (next x e) T)).sum := by
              congr 1
              exact ofFn_sum_eq _ _ (fun e => ih (next x e))
          _ = costNumerator next Terminal x (T + 1) :=
            (costNumerator_succ next Terminal x ht T).symm

theorem tagged_weighted_le_cost
    {S : Type} {n : Nat}
    (next : S → Fin n → S) (Terminal : S → Prop)
    (c : S → Fin n → Nat)
    (hbudget : ∀ x, ¬ Terminal x →
      (List.ofFn (fun e : Fin n => c x e)).sum ≤ n) :
    ∀ T x, taggedWeightedCost next Terminal c x T ≤
      costNumerator next Terminal x T := by
  intro T x
  calc
    _ ≤ taggedNodeCost next Terminal (fun _ => 1) x T :=
      tagged_weighted_le_node next Terminal c (fun _ => 1)
        (by intro s hs; simpa only [Nat.mul_one] using hbudget s hs) T x
    _ = costNumerator next Terminal x T :=
      tagged_node_one_eq_cost next Terminal T x

/-- Scaling a per-edge charge commutes with the whole word sum. -/
theorem tagged_weighted_scale
    {S : Type} {n : Nat}
    (next : S → Fin n → S) (Terminal : S → Prop)
    (c : S → Fin n → Nat) (k : Nat) :
    ∀ T x, taggedWeightedCost next Terminal
        (fun s e => k * c s e) x T =
      k * taggedWeightedCost next Terminal c x T := by
  classical
  intro T
  induction T with
  | zero =>
      intro x
      simp [taggedWeightedCost]
  | succ T ih =>
      intro x
      by_cases ht : Terminal x
      · simp [taggedWeightedCost, ht]
      · simp only [taggedWeightedCost, if_neg ht]
        calc
          (List.ofFn (fun e : Fin n =>
            n ^ T * (k * c x e) +
              taggedWeightedCost next Terminal
                (fun s q => k * c s q) (next x e) T)).sum =
              (List.ofFn (fun e : Fin n =>
                k * (n ^ T * c x e +
                  taggedWeightedCost next Terminal c (next x e) T))).sum := by
                apply ofFn_sum_eq
                intro e
                rw [ih (next x e), Nat.mul_add]
                ac_rfl
          _ = k * (List.ofFn (fun e : Fin n =>
                n ^ T * c x e +
                  taggedWeightedCost next Terminal c (next x e) T)).sum :=
            ofFn_sum_mul_left k _

/-- A non-Ready Q target has exactly one nominated raw letter. -/
noncomputable def taggedQTargetHit {n : Nat}
    (ring : DirectedRing n) (j : Fin n) (b : Nat)
    (N : TripleNativeState n) (e : Fin n) : Nat :=
  if ¬ SealedCleanReady ring N j b ∧
      e = SealedPhaseEdge ring j
        (taggedQAttackerPhase ring j b N)
  then 1 else 0

theorem tagged_q_target_hit_one_edge {n : Nat}
    (ring : DirectedRing n) (j : Fin n) (b : Nat)
    (N : TripleNativeState n) :
    (List.ofFn (fun e : Fin n =>
      n * taggedQTargetHit ring j b N e)).sum ≤ n := by
  classical
  by_cases hready : SealedCleanReady ring N j b
  · simp [taggedQTargetHit, hready, ofFn_sum_const]
  · let required := SealedPhaseEdge ring j
        (taggedQAttackerPhase ring j b N)
    calc
      (List.ofFn (fun e : Fin n =>
          n * taggedQTargetHit ring j b N e)).sum =
        (List.ofFn (fun e : Fin n =>
          if e = required then n else 0)).sum := by
            apply ofFn_sum_eq
            intro e
            by_cases he : e = required
            · simp [taggedQTargetHit, required, hready, he]
            · simp [taggedQTargetHit, required, hready, he]
      _ = n := tagged_q_sum_spike n required n
      _ ≤ n := Nat.le_refl n

/-- D.13: exact n-times nominated-target hits versus Q stopped cost. -/
theorem tagged_q_target_hit_compensator {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (b : Nat)
    (hn : 2 ≤ n) (hports : ring.leftNeighbor j ≠ j)
    (seed : TripleNativeState n) (T : Nat) :
    n * taggedWeightedCost
      (taggedQNext ring j b hn hports)
      (TaggedDeleted i j k)
      (taggedQTargetHit ring j b) seed T ≤
    costNumerator
      (taggedQNext ring j b hn hports)
      (TaggedDeleted i j k) seed T := by
  let next := taggedQNext ring j b hn hports
  let Terminal := TaggedDeleted i j k
  calc
    n * taggedWeightedCost next Terminal
        (taggedQTargetHit ring j b) seed T =
      taggedWeightedCost next Terminal
        (fun s e => n * taggedQTargetHit ring j b s e) seed T := by
          exact (tagged_weighted_scale next Terminal
            (taggedQTargetHit ring j b) n T seed).symm
    _ ≤ costNumerator next Terminal seed T :=
      tagged_weighted_le_cost next Terminal
        (fun s e => n * taggedQTargetHit ring j b s e)
        (by intro s _; exact tagged_q_target_hit_one_edge ring j b s)
        T seed

/-- D.12 directly bounds this same Q charge, with no new premise. -/
theorem tagged_q_target_hit_drift_bound {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (seed : TripleNativeState n)
    (hstart : TaggedTriple ring i j k a b seed)
    (hclean : TaggedCleanDummy ring i j a b seed) :
    ∀ T, n * taggedWeightedCost
        (taggedQNext ring j b (by omega : 2 ≤ n) hports)
        (TaggedDeleted i j k)
        (taggedQTargetHit ring j b) seed T ≤
      n ^ T * (n * (5 * a - 2)) := by
  have hclock :
      ∀ T, costNumerator
        (taggedQNext ring j b (by omega : 2 ≤ n) hports)
        (TaggedDeleted i j k) seed T ≤
        n ^ T * (n * (5 * a - 2)) :=
    (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (taggedQNext ring j b (by omega : 2 ≤ n) hports)
      (TaggedDeleted i j k) (by omega : 0 < n)
      seed (n * (5 * a - 2))).1
        (tagged_q_expected_drift_bound hnthree ring i j k a b
          hports seed hstart hclean)
  intro T
  exact Nat.le_trans
    (tagged_q_target_hit_compensator ring i j k b
      (by omega : 2 ≤ n) hports seed T)
    (hclock T)

/-! D.10: exact abstract stopped rank ledger.
A physical local-slot balance is still required. -/

private def taggedLedgerCreditNode {S : Type}
    (credit : S → Nat) : StopNode S → Nat
  | .active x => credit x
  | .success => 0
  | .failure => 0

/-- The exact stopped pathwise ledger, conditional only on a
one-edge balance and reachability closure. Not a physical D.10 claim. -/
theorem tagged_ledger_word_bound {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S)
    (r : ControlledSchedulerMass.Redirection S n)
    (R : S → Prop) (credit : S → Nat)
    (charge : S → Fin n → Nat) (m : Nat)
    (hlocal : ∀ s, R s → ∀ e,
      m * ControlledSchedulerMass.eventCost r (.active s) e +
        taggedLedgerCreditNode credit (step s e) ≤
          charge s e + credit s)
    (hclosed : ∀ s, R s → ∀ e t,
      step s e = .active t → R t) :
    ∀ x : StopNode S, (∀ s, x = .active s → R s) →
      ∀ w : List (Fin n),
        m * ControlledSchedulerMass.eventCount step r x w ≤
          wordCharge step charge x w +
            taggedLedgerCreditNode credit x := by
  have hmain : ∀ (w : List (Fin n)) (x : StopNode S),
      (∀ s, x = .active s → R s) →
      m * ControlledSchedulerMass.eventCount step r x w ≤
        wordCharge step charge x w +
          taggedLedgerCreditNode credit x := by
    intro w
    induction w with
    | nil =>
        intro x hx
        cases x <;> simp [ControlledSchedulerMass.eventCount,
          wordCharge, taggedLedgerCreditNode]
    | cons e es ih =>
        intro x hx
        cases x with
        | success =>
            simp [ControlledSchedulerMass.eventCount_success,
              ControlledSchedulerMass.eventCost, stepNode,
              wordCharge, taggedLedgerCreditNode]
        | failure =>
            simp [ControlledSchedulerMass.eventCount_failure,
              ControlledSchedulerMass.eventCost, stepNode,
              wordCharge, taggedLedgerCreditNode]
        | active s =>
            have hs : R s := hx s rfl
            have hnext : ∀ t, step s e = .active t → R t := by
              intro t ht
              exact hclosed s hs e t ht
            have hi := ih (step s e) hnext
            have hl := hlocal s hs e
            change
              m * (ControlledSchedulerMass.eventCost r (.active s) e +
                ControlledSchedulerMass.eventCount step r
                  (step s e) es) ≤
              charge s e + wordCharge step charge (step s e) es +
                credit s
            rw [Nat.mul_add]
            omega
  intro x hx w
  exact hmain w x hx

theorem tagged_ledger_clean_cycle {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S)
    (r : ControlledSchedulerMass.Redirection S n)
    (R : S → Prop) (credit : S → Nat)
    (charge : S → Fin n → Nat) (m : Nat)
    (hlocal : ∀ s, R s → ∀ e,
      m * ControlledSchedulerMass.eventCost r (.active s) e +
        taggedLedgerCreditNode credit (step s e) ≤
          charge s e + credit s)
    (hclosed : ∀ s, R s → ∀ e t,
      step s e = .active t → R t)
    (seed : S) (hr : R seed) (hz : credit seed = 0)
    (w : List (Fin n)) :
    m * ControlledSchedulerMass.eventCount step r (.active seed) w ≤
      wordCharge step charge (.active seed) w := by
  have h := tagged_ledger_word_bound step r R credit charge m
    hlocal hclosed (.active seed) (by
      intro s hs
      cases hs
      exact hr) w
  simpa only [taggedLedgerCreditNode, hz, Nat.add_zero] using h

/-! D.14: finite-word affine secant with no real Jensen lemma. -/

private theorem tagged_q_event_cost_le_one
    {S : Type} {n : Nat}
    (r : ControlledSchedulerMass.Redirection S n)
    (x : StopNode S) (e : Fin n) :
    ControlledSchedulerMass.eventCost r x e ≤ 1 := by
  cases x with
  | active s =>
      simp [ControlledSchedulerMass.eventCost]
      split <;> omega
  | success => simp [ControlledSchedulerMass.eventCost]
  | failure => simp [ControlledSchedulerMass.eventCost]

private theorem tagged_q_event_count_le_length
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S)
    (r : ControlledSchedulerMass.Redirection S n)
    (x : StopNode S) (w : List (Fin n)) :
    ControlledSchedulerMass.eventCount step r x w ≤ w.length := by
  induction w generalizing x with
  | nil => simp [ControlledSchedulerMass.eventCount]
  | cons e es ih =>
      simp only [ControlledSchedulerMass.eventCount, List.length_cons]
      have hc := tagged_q_event_cost_le_one r x e
      have ht := ih (stepNode step x e)
      omega

/-- Globally valid denominator-cleared secant, even N>m+1. -/
theorem tagged_q_secant_scaled (m T N : Nat) (hNT : N ≤ T) :
    (m + 2) * 2 ^ T ≤
      2 ^ (m + 1) * 2 ^ (T - N) + N * 2 ^ T := by
  by_cases hsmall : N ≤ m + 1
  · have hsplit : T = N + (T - N) := by omega
    have hpow : 2 ^ T = 2 ^ N * 2 ^ (T - N) := by
      calc
        2 ^ T = 2 ^ (N + (T - N)) :=
          congrArg (fun k : Nat => 2 ^ k) hsplit
        _ = 2 ^ N * 2 ^ (T - N) := by rw [Nat.pow_add]
    have hsec :
        (m + 2) * 2 ^ N ≤
          2 ^ (m + 1) + N * 2 ^ N := by
      have heq : (m + 2 - N) + N = m + 2 := by omega
      calc
        _ = ((m + 2 - N) + N) * 2 ^ N := by rw [heq]
        _ = (m + 2 - N) * 2 ^ N + N * 2 ^ N := by
          rw [Nat.add_mul]
        _ ≤ 2 ^ (m + 1) + N * 2 ^ N :=
          Nat.add_le_add_right (tagged_discrete_pow_two_secant m N) _
    calc
      (m + 2) * 2 ^ T =
          ((m + 2) * 2 ^ N) * 2 ^ (T - N) := by
            rw [hpow]
            ac_rfl
      _ ≤ (2 ^ (m + 1) + N * 2 ^ N) * 2 ^ (T - N) :=
        Nat.mul_le_mul_right _ hsec
      _ = 2 ^ (m + 1) * 2 ^ (T - N) + N * 2 ^ T := by
        rw [Nat.add_mul, hpow]
        ac_rfl
  · have hlarge : m + 2 ≤ N := by omega
    have hs := Nat.mul_le_mul_right (2 ^ T) hlarge
    omega

private theorem tagged_q_sum_map_le {X : Type}
    (xs : List X) (f g : X → Nat)
    (hfg : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      apply Nat.add_le_add
      · exact hfg x (by simp)
      · apply ih
        intro y hy
        exact hfg y (by simp [hy])

private theorem tagged_q_sum_map_mul {X : Type}
    (xs : List X) (k : Nat) (f : X → Nat) :
    (xs.map (fun x => k * f x)).sum =
      k * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.mul_add]

private theorem tagged_q_sum_map_add {X : Type}
    (xs : List X) (f g : X → Nat) :
    (xs.map (fun x => f x + g x)).sum =
      (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_assoc, Nat.add_left_comm]

private theorem tagged_q_word_sum_le {n : Nat} (T : Nat)
    (f g : List (Fin n) → Nat)
    (hfg : ∀ w, w.length = T → f w ≤ g w) :
    FixedSpanRenewalPayload.wordSum n T f ≤
      FixedSpanRenewalPayload.wordSum n T g := by
  unfold FixedSpanRenewalPayload.wordSum
  apply tagged_q_sum_map_le
  intro w hw
  have hlen := allSchedules_schedule_length n T w hw
  exact hfg w.reverse (by simpa [hlen])

private theorem tagged_q_word_sum_mul {n : Nat} (T k : Nat)
    (f : List (Fin n) → Nat) :
    FixedSpanRenewalPayload.wordSum n T (fun w => k * f w) =
      k * FixedSpanRenewalPayload.wordSum n T f := by
  unfold FixedSpanRenewalPayload.wordSum
  exact tagged_q_sum_map_mul _ k
    (fun (w : List (Fin n)) => f w.reverse)

private theorem tagged_q_word_sum_add {n : Nat} (T : Nat)
    (f g : List (Fin n) → Nat) :
    FixedSpanRenewalPayload.wordSum n T (fun w => f w + g w) =
      FixedSpanRenewalPayload.wordSum n T f +
        FixedSpanRenewalPayload.wordSum n T g := by
  unfold FixedSpanRenewalPayload.wordSum
  exact tagged_q_sum_map_add _
    (fun (w : List (Fin n)) => f w.reverse)
    (fun (w : List (Fin n)) => g w.reverse)

private theorem tagged_q_word_success_eq_count
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (x : StopNode S) (T : Nat) :
    FixedSpanRenewalPayload.wordSum n T
      (fun w => successWeight (ControlledSchedulerMass.runWord step x w)) =
        successCount step x T := by
  induction T generalizing x with
  | zero =>
      simp [FixedSpanRenewalPayload.wordSum, allSchedules,
        ControlledSchedulerMass.runWord, successCount, treeWeight] <;>
        cases x <;> rfl
  | succ T ih =>
      rw [FixedSpanRenewalPayload.wordSum_succ]
      simp only [ControlledSchedulerMass.runWord, treeWeight]
      exact ofFn_sum_eq _ _ (fun e => ih (stepNode step x e))

/-- D.14: all finite-horizon successful Q words, with their actual N. -/
theorem tagged_q_secant_weighted
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S)
    (r : ControlledSchedulerMass.Redirection S n)
    (x : StopNode S) (T m : Nat) :
    (m + 2) * 2 ^ T *
        successCount (ControlledSchedulerMass.controlledStep step r) x T ≤
      2 ^ (m + 1) * weightedQSuccessNumerator step r x T +
        2 ^ T * collapseCountNumerator step r x T := by
  let Q := ControlledSchedulerMass.controlledStep step r
  have hword : ∀ w : List (Fin n), w.length = T →
      (m + 2) * 2 ^ T *
          successWeight (ControlledSchedulerMass.runWord Q x w) ≤
        2 ^ (m + 1) *
          powSuccessOnly
            (ControlledSchedulerMass.runWord Q x w)
            (T - ControlledSchedulerMass.eventCount Q r x w) +
        2 ^ T * ControlledSchedulerMass.eventCount Q r x w := by
    intro w hlen
    have hN : ControlledSchedulerMass.eventCount Q r x w ≤ T := by
      have hc := tagged_q_event_count_le_length Q r x w
      omega
    cases hy : ControlledSchedulerMass.runWord Q x w with
    | success =>
        simpa [hy, successWeight, powSuccessOnly, Nat.mul_comm] using
          tagged_q_secant_scaled m T
            (ControlledSchedulerMass.eventCount Q r x w) hN
    | failure => simp [hy, successWeight, powSuccessOnly]
    | active s => simp [hy, successWeight, powSuccessOnly]
  have hs :
      FixedSpanRenewalPayload.wordSum n T (fun w =>
        (m + 2) * 2 ^ T *
          successWeight (ControlledSchedulerMass.runWord Q x w)) ≤
      FixedSpanRenewalPayload.wordSum n T (fun w =>
        2 ^ (m + 1) *
          powSuccessOnly
            (ControlledSchedulerMass.runWord Q x w)
            (T - ControlledSchedulerMass.eventCount Q r x w) +
        2 ^ T * ControlledSchedulerMass.eventCount Q r x w) := by
    apply tagged_q_word_sum_le
    intro w hw
    exact hword w hw
  simp only [tagged_q_word_sum_mul, tagged_q_word_sum_add] at hs
  rw [tagged_q_word_success_eq_count Q x T] at hs
  simpa only [weightedQSuccessNumerator, collapseCountNumerator] using hs

/-- Exact original-scheduler success lower bound, cleared of 2^T. -/
theorem tagged_q_secant_raw
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S)
    (r : ControlledSchedulerMass.Redirection S n)
    (x : StopNode S) (T m : Nat) :
    (m + 2) *
        successCount (ControlledSchedulerMass.controlledStep step r) x T ≤
      2 ^ (m + 1) * successCount step x T +
        collapseCountNumerator step r x T := by
  have hsec := tagged_q_secant_weighted step r x T m
  have hmeasure := weighted_changeOfMeasure_success step r x T
  have hscaled :
      2 ^ T * ((m + 2) *
        successCount (ControlledSchedulerMass.controlledStep step r) x T) ≤
      2 ^ T * (2 ^ (m + 1) * successCount step x T +
        collapseCountNumerator step r x T) := by
    calc
      _ = (m + 2) * 2 ^ T *
          successCount (ControlledSchedulerMass.controlledStep step r) x T := by
            ac_rfl
      _ ≤ 2 ^ (m + 1) * weightedQSuccessNumerator step r x T +
            2 ^ T * collapseCountNumerator step r x T := hsec
      _ ≤ 2 ^ (m + 1) * (2 ^ T * successCount step x T) +
            2 ^ T * collapseCountNumerator step r x T :=
          Nat.add_le_add_right
            (Nat.mul_le_mul_left _ hmeasure) _
      _ = 2 ^ T * (2 ^ (m + 1) * successCount step x T +
            collapseCountNumerator step r x T) := by
          rw [Nat.mul_add]
          ac_rfl
  exact Nat.le_of_mul_le_mul_left hscaled
    (Nat.pow_pos (by decide : 0 < 2))

/-- Actual physical tagged deletion Q-vs-original finite-horizon count. -/
theorem tagged_q_physical_secant_raw {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (b : Nat)
    (hn : 2 ≤ n) (hports : ring.leftNeighbor j ≠ j)
    (seed : TripleNativeState n) (T m : Nat) :
    (m + 2) *
      successCount (taggedQStopped ring i j k b hn hports)
        (.active seed) T ≤
      2 ^ (m + 1) *
        successCount (taggedTrialStep ring i j k b)
          (.active seed) T +
      collapseCountNumerator
        (taggedTrialStep ring i j k b)
        (taggedRedirection ring j b hn hports)
        (.active seed) T := by
  change
    (m + 2) *
      successCount
        (ControlledSchedulerMass.controlledStep
          (taggedTrialStep ring i j k b)
          (taggedRedirection ring j b hn hports))
        (.active seed) T ≤
    2 ^ (m + 1) *
      successCount (taggedTrialStep ring i j k b)
        (.active seed) T +
    collapseCountNumerator
      (taggedTrialStep ring i j k b)
      (taggedRedirection ring j b hn hports)
      (.active seed) T
  exact tagged_q_secant_raw
    (taggedTrialStep ring i j k b)
    (taggedRedirection ring j b hn hports)
    (.active seed) T m

end L3


/-! ## Physical target quota, stopped Q rows

This section uses the
literal SealedClose stage table and the current Q redirection.
The target's credit is the elapsed portion of the current
2b-1 nominated-service cycle. No global occupancy theorem. -/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

attribute [local instance low] Classical.propDecidable

/-- Every valid stage has its nominated offset inside the sector. -/
private theorem tagged_target_nominated_valid
    (b : Nat) (s : SealedCloseProof.Stage)
    (hvalid : taggedTargetStageAdmissible b s) (hb : 0 < b) :
    SealedCloseProof.nominated s < b := by
  cases s with
  | ready =>
      simp only [SealedCloseProof.nominated]
      omega
  | bullet live p =>
      exact hvalid
  | returning q =>
      have hq : q < b := hvalid.2
      simp only [SealedCloseProof.nominated]
      omega

/-- Non-Ready incoming receipt does not alter the stage. -/
private theorem tagged_target_nonready_incoming
    (s : SealedCloseProof.Stage) (hnr : s ≠ .ready) :
    SealedCloseProof.incomingStage s = s := by
  cases s with
  | ready => exact False.elim (hnr rfl)
  | bullet live p => rfl
  | returning q => rfl

/-- Exact slot accounting for an internal non-Ready stage.
The equality, rather than weak monotonicity, is essential. -/
theorem tagged_target_nonready_inside_exact
    (b r : Nat) (hb : 2 ≤ b)
    (s : SealedCloseProof.Stage)
    (hvalid : taggedTargetStageAdmissible b s)
    (hnr : s ≠ .ready) :
    SealedCloseProof.rank b (SealedCloseProof.insideStage b s r) +
      (if r = SealedCloseProof.nominated s then 1 else 0) =
        SealedCloseProof.rank b s := by
  by_cases hh : r = SealedCloseProof.nominated s
  · subst r
    simpa only [if_pos rfl, ite_true] using
      tagged_target_stage_nominated_rank b hb s hvalid hnr
  · have hsame :=
      tagged_target_stage_internal_nonhit b r s hvalid hnr hh
    simp only [hsame, if_neg hh, Nat.add_zero]

/-- The source-relative table spends precisely one target slot iff
the selected PHYSICAL edge is the non-Ready nominated edge. -/
theorem tagged_target_nonready_table_exact {n : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (j k : Fin n) (b : Nat) (hb : 2 ≤ b)
    (phase : SealedPhase n) (raw : Fin n)
    (hc : ConsecutiveNative ring N j k b)
    (hphase : SealedPhaseHolds ring N j b phase)
    (hnr : phase ≠ .ready) :
    SealedCloseProof.rank b (sealedCloseTable ring j b raw phase) +
      (if raw = SealedPhaseEdge ring j phase then 1 else 0) =
        SealedCloseProof.rank b (SealedCloseProof.fromPhase phase) := by
  let s := SealedCloseProof.fromPhase phase
  let pos := SealedCloseProof.position ring j raw
  have hvalid : taggedTargetStageAdmissible b s :=
    tagged_target_stage_admissible_of_holds ring N j b phase hphase
  have hnrS : s ≠ .ready := by
    dsimp [s]
    cases phase with
    | ready => exact False.elim (hnr rfl)
    | dummy p => intro hh; cases hh
    | live p => intro hh; cases hh
    | returning q => intro hh; cases hh
  have hnomlt : SealedCloseProof.nominated s < b :=
    tagged_target_nominated_valid b s hvalid (by omega)
  have hnomPos :
      (SealedCloseProof.position ring j
        (SealedPhaseEdge ring j phase)).val =
          SealedCloseProof.nominated s :=
    sealed_close_nominated_position ring N j k b phase hc hphase
  by_cases hhit : raw = SealedPhaseEdge ring j phase
  · have hindex : pos.val = SealedCloseProof.nominated s := by
      dsimp [pos]
      simpa only [hhit] using hnomPos
    have hlt : pos.val < b := by omega
    have htable :
        sealedCloseTable ring j b raw phase =
          SealedCloseProof.insideStage b s pos.val := by
      change (if pos.val < b then
        SealedCloseProof.insideStage b s pos.val
        else if pos.val + 1 = n then
          SealedCloseProof.incomingStage s else s) =
        SealedCloseProof.insideStage b s pos.val
      exact if_pos hlt
    calc
      SealedCloseProof.rank b (sealedCloseTable ring j b raw phase) +
          (if raw = SealedPhaseEdge ring j phase then 1 else 0) =
          SealedCloseProof.rank b
            (SealedCloseProof.insideStage b s
              (SealedCloseProof.nominated s)) + 1 := by
            rw [htable, hindex, if_pos hhit]
      _ = SealedCloseProof.rank b s :=
        tagged_target_stage_nominated_rank b hb s hvalid hnrS
  · have hmiss : pos.val ≠ SealedCloseProof.nominated s := by
      intro heq
      have hraw :=
        sealed_close_edge_of_position ring j raw
          (SealedCloseProof.nominated s) heq
      have hedge :=
        sealed_close_edge_of_position ring j
          (SealedPhaseEdge ring j phase)
          (SealedCloseProof.nominated s) hnomPos
      exact hhit (hraw.trans hedge.symm)
    have htable :
        sealedCloseTable ring j b raw phase = s := by
      change (if pos.val < b then
        SealedCloseProof.insideStage b s pos.val
        else if pos.val + 1 = n then
          SealedCloseProof.incomingStage s else s) = s
      by_cases hinside : pos.val < b
      · simp only [if_pos hinside]
        exact tagged_target_stage_internal_nonhit
          b pos.val s hvalid hnrS hmiss
      · simp only [if_neg hinside]
        by_cases hwrap : pos.val + 1 = n
        · simp only [if_pos hwrap]
          exact tagged_target_nonready_incoming s hnrS
        · simp only [if_neg hwrap]
    simp only [htable, if_neg hhit, Nat.add_zero]
    rfl

/-- A SURVIVING actual Q step, from any inductively reached
non-Ready target stage, obeys the exact rank debit in its RAW
letter. This removes the occupancy-bound obstruction. -/
theorem tagged_q_target_surviving_nonready_exact {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat) (hb : 2 ≤ b)
    (hports : ring.leftNeighbor j ≠ j)
    (seed N : TripleNativeState n) (raw : Fin n)
    (hstart : TaggedTriple ring i j k a b seed)
    (hclean : TaggedCleanDummy ring i j a b seed)
    (hreach : TaggedQActiveReach ring i j k a b
      (by omega : 2 ≤ n) hports seed N)
    (phase : SealedPhase n)
    (hphase : SealedPhaseHolds ring N j b phase)
    (hnr : phase ≠ .ready)
    (hnot : ¬ TaggedDeleted i j k
      (taggedQNext ring j b (by omega : 2 ≤ n)
        hports N raw)) :
    ∃ nextPhase : SealedPhase n,
      SealedPhaseHolds ring
        (taggedQNext ring j b (by omega : 2 ≤ n)
          hports N raw) j b nextPhase ∧
      SealedPhaseProgress b nextPhase +
        (if raw = SealedPhaseEdge ring j phase then 1 else 0) =
        SealedPhaseProgress b phase := by
  have hnotReady : ¬ SealedCleanReady ring N j b := by
    intro hr
    exact hnr (tagged_sealed_phase_unique
      ring N j b phase .ready hphase hr)
  have hgate :
      (taggedRedirection ring j b
        (by omega : 2 ≤ n) hports).gate N = false := by
    simp [taggedRedirection, hnotReady]
  have heff : taggedQEffective ring j b
      (by omega : 2 ≤ n) hports N raw = raw := by
    unfold taggedQEffective
    exact (taggedRedirection ring j b
      (by omega : 2 ≤ n) hports).effective_of_gate_false N hgate raw
  obtain ⟨nextPhase, hnext, hstage⟩ :=
    tagged_q_surviving_target_stage hnthree ring i j k a b
      hports seed N raw hstart hclean hreach phase hphase hnot
  have hc : ConsecutiveNative ring N j k b :=
    (tagged_q_reachable_invariants
      hnthree ring i j k a b hports seed
        hstart hclean hreach).1.2.2
  have htable :=
    tagged_target_nonready_table_exact ring N j k b hb
      phase raw hc hphase hnr
  rw [heff] at hstage
  rw [← hstage] at htable
  have hnorm : ∀ p : SealedPhase n,
      SealedCloseProof.rank b (SealedCloseProof.fromPhase p) =
        SealedPhaseProgress b p := by
    intro p
    cases p <;> rfl
  rw [hnorm nextPhase, hnorm phase] at htable
  exact ⟨nextPhase, hnext, htable⟩

/-- On a surviving Ready-time collapsed service, both raw Q
letters execute the same actual incoming L_j row, and the target
returns to clean Dummy(0). -/
theorem tagged_q_target_ready_collapsed_reset {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (seed N : TripleNativeState n) (raw : Fin n)
    (hstart : TaggedTriple ring i j k a b seed)
    (hclean : TaggedCleanDummy ring i j a b seed)
    (hreach : TaggedQActiveReach ring i j k a b
      (by omega : 2 ≤ n) hports seed N)
    (hready : SealedCleanReady ring N j b)
    (hcollapse : (taggedRedirection ring j b
      (by omega : 2 ≤ n) hports).Collapses N raw)
    (hnot : ¬ TaggedDeleted i j k
      (taggedQNext ring j b (by omega : 2 ≤ n)
        hports N raw)) :
    TaggedCleanDummy ring i j a b
      (taggedQNext ring j b (by omega : 2 ≤ n)
        hports N raw) := by
  have hinv := tagged_q_reachable_invariants
    hnthree ring i j k a b hports seed
      hstart hclean hreach
  have hprepared : TaggedPrepared ring i j a b N :=
    ⟨hinv.2.1.1, hready⟩
  have heff : taggedQEffective ring j b
      (by omega : 2 ≤ n) hports N raw =
        ring.leftNeighbor j := by
    have hh :=
      ((taggedRedirection ring j b
        (by omega : 2 ≤ n) hports).collapses_iff_effective
          N raw).mp hcollapse
    change (taggedRedirection ring j b
      (by omega : 2 ≤ n) hports).effective N raw =
        ring.leftNeighbor j
    simpa [taggedRedirection] using hh.2
  have hphys : ¬ TaggedDeleted i j k
      (nativeE ring N (ring.leftNeighbor j)) := by
    simpa only [taggedQNext, heff] using hnot
  have hrow :=
    tagged_prepared_incoming_dummy_actual ring i j k a b N
      (ring.leftNeighbor j) hports
      (tagged_right_of_left (by omega : 2 ≤ n) ring j)
      hinv.1 hprepared
  rcases hrow with hdead | hdummy
  · exact False.elim (hphys hdead)
  · simpa only [taggedQNext, heff] using hdummy

/-- Partial-cycle credit in the current target governorship. -/
noncomputable def taggedQTargetLedgerCredit {n : Nat}
    (ring : DirectedRing n) (j : Fin n) (b : Nat)
    (N : TripleNativeState n) : Nat :=
  (2 * b - 1) -
    SealedPhaseProgress b (taggedQAttackerPhase ring j b N)

/-- Physical D.10 one-edge slot balance. Terminal deletion
discards all unfinished credit; a Ready collapse spends one
whole completed cycle. -/
theorem tagged_q_target_physical_slot {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat) (hb : 2 ≤ b)
    (hports : ring.leftNeighbor j ≠ j)
    (seed N : TripleNativeState n) (raw : Fin n)
    (hstart : TaggedTriple ring i j k a b seed)
    (hclean : TaggedCleanDummy ring i j a b seed)
    (hreach : TaggedQActiveReach ring i j k a b
      (by omega : 2 ≤ n) hports seed N) :
    (2 * b - 1) *
      ControlledSchedulerMass.eventCost
        (taggedRedirection ring j b (by omega : 2 ≤ n) hports)
        (.active N) raw +
      taggedLedgerCreditNode
        (taggedQTargetLedgerCredit ring j b)
        (taggedQStopped ring i j k b (by omega : 2 ≤ n)
          hports N raw) ≤
      taggedQTargetHit ring j b N raw +
        taggedQTargetLedgerCredit ring j b N := by
  let hn : 2 ≤ n := by omega
  let r := taggedRedirection ring j b hn hports
  let next := taggedQNext ring j b hn hports N raw
  let step := taggedQStopped ring i j k b hn hports N raw
  let credit := taggedQTargetLedgerCredit ring j b
  let m := 2 * b - 1
  have hinv := tagged_q_reachable_invariants
    hnthree ring i j k a b hports seed
      hstart hclean hreach
  obtain ⟨phase, hphase⟩ := hinv.2.1.2
  by_cases hready : SealedCleanReady ring N j b
  · have hold : credit N = m := by
      have hh := tagged_q_attacker_phase_eq ring N j b
        (.ready : SealedPhase n) hready
      simp [credit, taggedQTargetLedgerCredit, hh,
        SealedPhaseProgress, m]
    have hhit : taggedQTargetHit ring j b N raw = 0 := by
      simp [taggedQTargetHit, hready]
    by_cases hcollapse : r.Collapses N raw
    · have hevent :
          ControlledSchedulerMass.eventCost r (.active N) raw = 1 := by
        simp [ControlledSchedulerMass.eventCost, hcollapse]
      have hnode : taggedLedgerCreditNode credit step = 0 := by
        change taggedLedgerCreditNode credit
          (taggedQStopped ring i j k b hn hports N raw) = 0
        rw [tagged_q_stopped_eq ring i j k b hn hports N raw]
        by_cases hdel : TaggedDeleted i j k next
        · change taggedLedgerCreditNode credit
            (if TaggedDeleted i j k next then StopNode.success
              else StopNode.active next) = 0
          rw [if_pos hdel]
          rfl
        · have hcleanNext :=
            tagged_q_target_ready_collapsed_reset hnthree
              ring i j k a b hports seed N raw
              hstart hclean hreach hready hcollapse hdel
          have hph := tagged_q_attacker_phase_eq ring next j b
            (.dummy (sealedZero ring)) hcleanNext.2
          change taggedLedgerCreditNode credit
            (if TaggedDeleted i j k next then StopNode.success
              else StopNode.active next) = 0
          rw [if_neg hdel]
          change credit next = 0
          simp [credit, taggedQTargetLedgerCredit, hph,
            SealedPhaseProgress, sealedZero]
      change m * ControlledSchedulerMass.eventCost r (.active N) raw +
          taggedLedgerCreditNode credit step ≤
        taggedQTargetHit ring j b N raw + credit N
      simp [hevent, hnode, hhit, hold]
    · have hevent :
          ControlledSchedulerMass.eventCost r (.active N) raw = 0 := by
        simp [ControlledSchedulerMass.eventCost, hcollapse]
      have hnode : taggedLedgerCreditNode credit step ≤ m := by
        change taggedLedgerCreditNode credit
          (taggedQStopped ring i j k b hn hports N raw) ≤ m
        rw [tagged_q_stopped_eq ring i j k b hn hports N raw]
        by_cases hdel : TaggedDeleted i j k next
        · change taggedLedgerCreditNode credit
            (if TaggedDeleted i j k next then StopNode.success
              else StopNode.active next) ≤ m
          rw [if_pos hdel]
          exact Nat.zero_le m
        · change taggedLedgerCreditNode credit
            (if TaggedDeleted i j k next then StopNode.success
              else StopNode.active next) ≤ m
          rw [if_neg hdel]
          change credit next ≤ m
          change (2 * b - 1) - SealedPhaseProgress b
            (taggedQAttackerPhase ring j b next) ≤ m
          dsimp [m]
          exact Nat.sub_le _ _
      change m * ControlledSchedulerMass.eventCost r (.active N) raw +
          taggedLedgerCreditNode credit step ≤
        taggedQTargetHit ring j b N raw + credit N
      simpa [hevent, hhit, hold] using hnode
  · have hnr : phase ≠ .ready := by
      intro he
      cases he
      exact hready hphase
    have hphaseOld :=
      tagged_q_attacker_phase_eq ring N j b phase hphase
    have hgate : r.gate N = false := by
      simp [r, taggedRedirection, hready]
    have hcollapse : ¬ r.Collapses N raw := by
      intro hh
      have hg : r.gate N = true := hh.1
      rw [hgate] at hg
      cases hg
    have hevent :
        ControlledSchedulerMass.eventCost r (.active N) raw = 0 := by
      simp [ControlledSchedulerMass.eventCost, hcollapse]
    by_cases hdel : TaggedDeleted i j k next
    · have hnode : taggedLedgerCreditNode credit step = 0 := by
        change taggedLedgerCreditNode credit
          (taggedQStopped ring i j k b hn hports N raw) = 0
        rw [tagged_q_stopped_eq ring i j k b hn hports N raw]
        change taggedLedgerCreditNode credit
          (if TaggedDeleted i j k next then StopNode.success
            else StopNode.active next) = 0
        rw [if_pos hdel]
        rfl
      change m * ControlledSchedulerMass.eventCost r (.active N) raw +
          taggedLedgerCreditNode credit step ≤
        taggedQTargetHit ring j b N raw + credit N
      simp [hevent, hnode]
    · obtain ⟨after, hafter, hprogress⟩ :=
        tagged_q_target_surviving_nonready_exact hnthree
          ring i j k a b hb hports seed N raw
          hstart hclean hreach phase hphase hnr hdel
      have hphaseAfter :=
        tagged_q_attacker_phase_eq ring next j b after hafter
      have hrank := sealed_phase_progress_bound
        ring N j b phase hphase
      have hold : credit N =
          m - SealedPhaseProgress b phase := by
        simp only [credit, taggedQTargetLedgerCredit, hphaseOld]
        dsimp [m]
      have hnew : credit next =
          m - SealedPhaseProgress b after := by
        simp only [credit, taggedQTargetLedgerCredit, hphaseAfter]
        dsimp [m]
      have hhit :
          taggedQTargetHit ring j b N raw =
            (if raw = SealedPhaseEdge ring j phase then 1 else 0) := by
        simp [taggedQTargetHit, hready, hphaseOld]
      have hnode :
          taggedLedgerCreditNode credit step = credit next := by
        change taggedLedgerCreditNode credit
          (taggedQStopped ring i j k b hn hports N raw) =
            credit next
        rw [tagged_q_stopped_eq ring i j k b hn hports N raw]
        change taggedLedgerCreditNode credit
          (if TaggedDeleted i j k next then StopNode.success
            else StopNode.active next) = credit next
        rw [if_neg hdel]
        rfl
      change m * ControlledSchedulerMass.eventCost r (.active N) raw +
          taggedLedgerCreditNode credit step ≤
        taggedQTargetHit ring j b N raw + credit N
      simp only [hevent, hnode, hhit, hold, hnew,
        Nat.mul_zero, Nat.zero_add]
      dsimp [m] at hrank ⊢
      by_cases he : raw = SealedPhaseEdge ring j phase
      · simp only [if_pos he] at hprogress ⊢
        omega
      · simp only [if_neg he] at hprogress ⊢
        omega

/-- D.10 pathwise physical word bound: EVERY Ready-time collapsed
raw letter is paid for by 2b-1 nominated target services on
the same stopped Q word, without a future last-Ready cut. -/
theorem tagged_q_target_physical_cycle {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat) (hb : 2 ≤ b)
    (hports : ring.leftNeighbor j ≠ j)
    (seed : TripleNativeState n)
    (hstart : TaggedTriple ring i j k a b seed)
    (hclean : TaggedCleanDummy ring i j a b seed)
    (w : List (Fin n)) :
    (2 * b - 1) *
      ControlledSchedulerMass.eventCount
        (taggedQStopped ring i j k b (by omega : 2 ≤ n) hports)
        (taggedRedirection ring j b (by omega : 2 ≤ n) hports)
        (.active seed) w ≤
      wordCharge
        (taggedQStopped ring i j k b (by omega : 2 ≤ n) hports)
        (taggedQTargetHit ring j b) (.active seed) w := by
  let hn : 2 ≤ n := by omega
  have hlocal :
      ∀ N : TripleNativeState n,
        TaggedQActiveReach ring i j k a b hn hports seed N →
        ∀ e : Fin n,
          (2 * b - 1) *
            ControlledSchedulerMass.eventCost
              (taggedRedirection ring j b hn hports)
              (.active N) e +
            taggedLedgerCreditNode
              (taggedQTargetLedgerCredit ring j b)
              (taggedQStopped ring i j k b hn hports N e) ≤
            taggedQTargetHit ring j b N e +
              taggedQTargetLedgerCredit ring j b N := by
    intro N hr e
    exact tagged_q_target_physical_slot hnthree ring
      i j k a b hb hports seed N e hstart hclean hr
  have hclosed :
      ∀ N : TripleNativeState n,
        TaggedQActiveReach ring i j k a b hn hports seed N →
        ∀ e M,
          taggedQStopped ring i j k b hn hports N e = .active M →
          TaggedQActiveReach ring i j k a b hn hports seed M := by
    intro N hr e M hactive
    exact TaggedQActiveReach.step hr e hactive
  have hz : taggedQTargetLedgerCredit ring j b seed = 0 := by
    have hphase :=
      tagged_q_attacker_phase_eq ring seed j b
        (.dummy (sealedZero ring)) hclean.2
    have hrank :
        SealedPhaseProgress b (.dummy (sealedZero ring)) =
          2 * b - 1 := by
      simp [SealedPhaseProgress, sealedZero]
    simp [taggedQTargetLedgerCredit, hphase, hrank]
  exact tagged_ledger_clean_cycle
    (taggedQStopped ring i j k b hn hports)
    (taggedRedirection ring j b hn hports)
    (TaggedQActiveReach ring i j k a b hn hports seed)
    (taggedQTargetLedgerCredit ring j b)
    (taggedQTargetHit ring j b) (2 * b - 1)
    hlocal hclosed seed TaggedQActiveReach.start hz w


/-- D.10 complete-word numerator: the physical slot ledger summed
over all length-T Q raw words. The endpoint padding contributes
zero in both numerator conventions. -/
theorem tagged_q_target_physical_count {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat) (hb : 2 ≤ b)
    (hports : ring.leftNeighbor j ≠ j)
    (seed : TripleNativeState n)
    (hstart : TaggedTriple ring i j k a b seed)
    (hclean : TaggedCleanDummy ring i j a b seed)
    (T : Nat) :
    (2 * b - 1) *
      collapseCountNumerator
        (taggedTrialStep ring i j k b)
        (taggedRedirection ring j b (by omega : 2 ≤ n) hports)
        (.active seed) T ≤
      edgeChargeNumerator
        (taggedQStopped ring i j k b (by omega : 2 ≤ n) hports)
        (taggedQTargetHit ring j b) (.active seed) T := by
  let hn : 2 ≤ n := by omega
  let Q := taggedQStopped ring i j k b hn hports
  let r := taggedRedirection ring j b hn hports
  let x : StopNode (TripleNativeState n) := .active seed
  calc
    (2 * b - 1) *
        collapseCountNumerator
          (taggedTrialStep ring i j k b) r x T =
      FixedSpanRenewalPayload.wordSum n T
        (fun w => (2 * b - 1) *
          ControlledSchedulerMass.eventCount Q r x w) := by
            unfold collapseCountNumerator
            rw [tagged_q_word_sum_mul]
            rfl
    _ ≤ FixedSpanRenewalPayload.wordSum n T
          (wordCharge Q (taggedQTargetHit ring j b) x) := by
            apply tagged_q_word_sum_le
            intro w hw
            exact tagged_q_target_physical_cycle
              hnthree ring i j k a b hb hports
              seed hstart hclean w
    _ = edgeChargeNumerator Q
          (taggedQTargetHit ring j b) x T :=
      wordSum_charge_eq_edgeChargeNumerator Q
        (taggedQTargetHit ring j b) x T

end L3


/-! ## Physical target-collapse budget and moderate retry frontier

No modified physical step.
This section isolates the real D.10/D.12 collapse budget and
the 64/52 factor at the clean-dummy vulnerable entrance.
The complete physical D.15 Ready stage and retry splice remain open.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

attribute [local instance low] Classical.propDecidable

/-! ### D.15 two-port arithmetic and physical incoming endpoint. -/

theorem tagged_d15_prepared_incoming {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat) (N : TripleNativeState n)
    (hstart : TaggedTriple ring i j k a b N)
    (hprep : TaggedPrepared ring i j a b N) :
    TaggedDeleted i j k
        (nativeE ring N (ring.leftNeighbor j)) ∨
      TaggedCleanDummy ring i j a b
        (nativeE ring N (ring.leftNeighbor j)) := by
  have hport : ring.leftNeighbor j ≠ j :=
    Ne.symm (tagged_q_incident_edges_distinct
      (by omega : 2 ≤ n) ring j)
  exact tagged_prepared_incoming_dummy_actual
    ring i j k a b N (ring.leftNeighbor j)
    hport (tagged_right_of_left (by omega : 2 ≤ n) ring j)
    hstart hprep

/-- D.15's exact ready-cut Bellman sum, conditional on the three
literal endpoint classes. Establishing these bounds for all
reachable nativeE successors is the still-open physical lift. -/
theorem tagged_d15_ready_two_port
    {n : Nat} (b : Nat) (hb : 2 ≤ b)
    (child : Fin n → Nat)
    (outgoing incoming : Fin n) (hne : outgoing ≠ incoming)
    (hout : child outgoing ≤ n * (4 * b - 3))
    (hin : child incoming = 0)
    (hrest : ∀ e, e ≠ outgoing → e ≠ incoming →
      child e ≤ n * (2 * b - 1)) :
    n + (List.ofFn child).sum ≤
      n * (n * (2 * b - 1)) := by
  have hcoeff :
      1 + (4 * b - 3) = 2 * (2 * b - 1) := by
    omega
  have hpair :
      n + child outgoing + child incoming ≤
        2 * (n * (2 * b - 1)) := by
    calc
      n + child outgoing + child incoming ≤
          n + n * (4 * b - 3) + 0 := by
        omega
      _ = n * (1 + (4 * b - 3)) := by
        simp only [Nat.add_zero, Nat.mul_one, Nat.mul_add]
      _ = n * (2 * (2 * b - 1)) := by rw [hcoeff]
      _ = 2 * (n * (2 * b - 1)) := by ac_rfl
  exact tagged_q_ready_sum_of_two_edge_bounds
    (n * (2 * b - 1)) child outgoing incoming hne
    hpair hrest

theorem tagged_d15_attempt_budget
    (n a b : Nat) (ha : 1 ≤ a) (hb : 2 ≤ b) :
    n * (2 * b - 1) + n * (5 * a - 2) +
        n * (2 * b - 2) =
      n * (5 * a + 4 * b - 5) := by
  have hcoeff :
      (2 * b - 1) + (5 * a - 2) + (2 * b - 2) =
        5 * a + 4 * b - 5 := by
    omega
  calc
    n * (2 * b - 1) + n * (5 * a - 2) +
        n * (2 * b - 2) =
      n * ((2 * b - 1) + (5 * a - 2) + (2 * b - 2)) := by
        rw [Nat.mul_add, Nat.mul_add]
    _ = n * (5 * a + 4 * b - 5) := by rw [hcoeff]

/-! ### QStopped physical cost from the restricted D.12 drift. -/

private theorem tagged_d15_triple_not_deleted {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n)
    (a b : Nat) (N : TripleNativeState n)
    (h : TaggedTriple ring i j k a b N) :
    ¬ TaggedDeleted i j k N := by
  have hi : (N i).l = true := h.2.1.2.2.2.1
  have hj : (N j).l = true := h.2.1.2.2.2.2.1
  have hk : (N k).l = true := h.2.2.2.2.2.2.1
  intro hd
  rcases hd with hi' | hj' | hk'
  · rw [hi] at hi'
    cases hi'
  · rw [hj] at hj'
    cases hj'
  · rw [hk] at hk'
    cases hk'

/-- The actual controlled StopNode Q tree has D.12's expected
cost bound, charging no more after a tagged deletion. -/
theorem tagged_d15_q_stopped_cost {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (seed : TripleNativeState n)
    (hstart : TaggedTriple ring i j k a b seed)
    (hclean : TaggedCleanDummy ring i j a b seed) :
    ∀ T,
      truncatedActiveCostNumerator
        (taggedQStopped ring i j k b (by omega : 2 ≤ n) hports)
        (.active seed) T ≤
      n ^ T * (n * (5 * a - 2)) := by
  let hn : 2 ≤ n := by omega
  let Q := taggedQStopped ring i j k b hn hports
  let next := taggedQNext ring j b hn hports
  let V := taggedQBellman ring i j k a
  have hmain : ∀ (T : Nat) (N : TripleNativeState n),
      TaggedQActiveReach ring i j k a b hn hports seed N →
      truncatedActiveCostNumerator Q (.active N) T ≤
        n ^ T * V N := by
    intro T
    induction T with
    | zero =>
        intro N hreach
        simp [truncatedActiveCostNumerator]
    | succ T ih =>
        intro N hreach
        have htriple : TaggedTriple ring i j k a b N :=
          (tagged_q_reachable_invariants hnthree
            ring i j k a b hports seed hstart hclean hreach).1
        have hnot : ¬ TaggedDeleted i j k N :=
          tagged_d15_triple_not_deleted ring i j k a b N htriple
        have hdrift :
            n + (List.ofFn (fun e : Fin n =>
              V (next N e))).sum ≤ n * V N :=
          tagged_q_reachable_drift hnthree ring i j k a b
            hports seed N hstart hclean hreach hnot
        have hchild (e : Fin n) :
            truncatedActiveCostNumerator Q (Q N e) T ≤
              n ^ T * V (next N e) := by
          change truncatedActiveCostNumerator Q
            (taggedQStopped ring i j k b hn hports N e) T ≤
            n ^ T * V (next N e)
          rw [tagged_q_stopped_eq ring i j k b hn hports N e]
          by_cases hdel : TaggedDeleted i j k (next N e)
          · rw [if_pos hdel]
            cases T <;> simp [truncatedActiveCostNumerator]
          · rw [if_neg hdel]
            exact ih (next N e)
              (tagged_q_reach_surviving_step ring i j k a b
                hn hports seed N e hreach hdel)
        have hsum :
            (List.ofFn (fun e : Fin n =>
              truncatedActiveCostNumerator Q (Q N e) T)).sum ≤
            n ^ T *
              (List.ofFn (fun e : Fin n => V (next N e))).sum := by
          calc
            _ ≤ (List.ofFn (fun e : Fin n =>
                  n ^ T * V (next N e))).sum :=
              ofFn_sum_le _ _ hchild
            _ = n ^ T *
                (List.ofFn (fun e : Fin n => V (next N e))).sum :=
              ofFn_sum_mul_left (n ^ T) _
        change n ^ (T + 1) +
            (List.ofFn (fun e : Fin n =>
              truncatedActiveCostNumerator Q (Q N e) T)).sum ≤
          n ^ (T + 1) * V N
        calc
          _ ≤ n ^ (T + 1) +
              n ^ T *
                (List.ofFn (fun e : Fin n =>
                  V (next N e))).sum :=
            Nat.add_le_add_left hsum _
          _ = n ^ T *
              (n + (List.ofFn (fun e : Fin n =>
                V (next N e))).sum) := by
            rw [Nat.pow_succ, Nat.mul_add]
          _ ≤ n ^ T * (n * V N) :=
            Nat.mul_le_mul_left (n ^ T) hdrift
          _ = n ^ (T + 1) * V N := by
            rw [Nat.pow_succ]
            ac_rfl
  intro T
  have hseed := hmain T seed TaggedQActiveReach.start
  have hcap := tagged_q_reachable_bellman_cap
    hnthree ring i j k a b hports seed seed
    hstart hclean TaggedQActiveReach.start
  exact Nat.le_trans hseed
    (Nat.mul_le_mul_left (n ^ T) hcap)

/-! ### Physical D.10 slot ledger to D.13 compensator. -/

noncomputable def taggedD15TargetActive {n : Nat}
    (ring : DirectedRing n) (j : Fin n) (b : Nat)
    (N : TripleNativeState n) : Bool :=
  decide (¬ SealedCleanReady ring N j b)

private theorem tagged_d15_charge_is_service {n : Nat}
    (ring : DirectedRing n) (j : Fin n) (b : Nat)
    (N : TripleNativeState n) (e : Fin n) :
    taggedQTargetHit ring j b N e =
      serviceCharge (taggedD15TargetActive ring j b)
        (fun M => SealedPhaseEdge ring j
          (taggedQAttackerPhase ring j b M)) N e := by
  classical
  by_cases hready : SealedCleanReady ring N j b
  · simp [taggedQTargetHit, serviceCharge,
      taggedD15TargetActive, hready]
  · by_cases he :
        e = SealedPhaseEdge ring j (taggedQAttackerPhase ring j b N)
    · simp [taggedQTargetHit, serviceCharge,
        taggedD15TargetActive, hready, he]
    · simp [taggedQTargetHit, serviceCharge,
        taggedD15TargetActive, hready, he]

/-- Every physical Q collapse is paid from the actual D.10
ledger. D.12 bounds the resulting stopped Q clock. -/
theorem tagged_d15_physical_collapse_moment {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat) (hb : 2 ≤ b)
    (hports : ring.leftNeighbor j ≠ j)
    (seed : TripleNativeState n)
    (hstart : TaggedTriple ring i j k a b seed)
    (hclean : TaggedCleanDummy ring i j a b seed)
    (T : Nat) :
    (2 * b - 1) *
      collapseCountNumerator
        (taggedTrialStep ring i j k b)
        (taggedRedirection ring j b (by omega : 2 ≤ n) hports)
        (.active seed) T ≤
      n ^ T * (5 * a - 2) := by
  let hn : 2 ≤ n := by omega
  let Q := taggedQStopped ring i j k b hn hports
  let r := taggedRedirection ring j b hn hports
  let active := taggedD15TargetActive ring j b
  let required : TripleNativeState n → Fin n :=
    fun N => SealedPhaseEdge ring j
      (taggedQAttackerPhase ring j b N)
  have hcharge :
      taggedQTargetHit ring j b =
        serviceCharge active required := by
    funext N e
    exact tagged_d15_charge_is_service ring j b N e
  have hcycle :
      (2 * b - 1) *
        collapseCountNumerator (taggedTrialStep ring i j k b)
          r (.active seed) T ≤
      edgeChargeNumerator Q (serviceCharge active required)
        (.active seed) T := by
    have h := tagged_q_target_physical_count
      hnthree ring i j k a b hb hports seed hstart hclean T
    rw [hcharge] at h
    exact h
  have hscaled := compensator_cleared Q active required
    (collapseCountNumerator (taggedTrialStep ring i j k b) r)
    (2 * b - 1) (.active seed) T hcycle
  have hcost := tagged_d15_q_stopped_cost
    hnthree ring i j k a b hports seed hstart hclean T
  have hh :
      n * ((2 * b - 1) *
        collapseCountNumerator (taggedTrialStep ring i j k b)
          r (.active seed) T) ≤
      n * (n ^ T * (5 * a - 2)) := by
    calc
      _ ≤ truncatedActiveCostNumerator Q (.active seed) T :=
        hscaled
      _ ≤ n ^ T * (n * (5 * a - 2)) := hcost
      _ = n * (n ^ T * (5 * a - 2)) := by ac_rfl
  exact Nat.le_of_mul_le_mul_left hh (by omega : 0 < n)


/-! ### D.14, original-scheduler nonretry counting. -/

/-- No controlled failure can appear in a controlled word if
every active one-letter child is free of failure. -/
private theorem tagged_d15_safe_word
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S)
    (hs : ∀ s e, step s e ≠ .failure)
    (z : StopNode S) (hz : z ≠ .failure)
    (w : List (Fin n)) :
    ControlledSchedulerMass.runWord step z w ≠ .failure := by
  induction w generalizing z with
  | nil =>
      exact hz
  | cons e es ih =>
      apply ih
      cases z with
      | active s =>
          exact hs s e
      | success =>
          simp [stepNode]
      | failure =>
          exact False.elim (hz rfl)

/-- The m=5 affine secant gives a sharp nonretry estimate across
all controlled words, including active (not just success) leaves. -/
theorem tagged_d15_secant_nonretry
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S)
    (r : ControlledSchedulerMass.Redirection S n)
    (z : StopNode S) (hz : z ≠ .failure)
    (hcontrolled : ∀ s e,
      ControlledSchedulerMass.controlledStep step r s e ≠ .failure)
    (T : Nat) :
    7 * (2 ^ T * n ^ T) ≤
      64 * weightedQNonRetryNumerator step r z T +
        2 ^ T * collapseCountNumerator step r z T := by
  let q := ControlledSchedulerMass.controlledStep step r
  have hpoint : ∀ idx : Fin (n ^ T),
      7 * 2 ^ T ≤
        64 * powSuccessOrActive
          (ControlledSchedulerMass.runWord q z
            (FixedSpanRenewalPayload.rawWord n T idx))
          (T - ControlledSchedulerMass.eventCount
            q r z (FixedSpanRenewalPayload.rawWord n T idx)) +
        2 ^ T * ControlledSchedulerMass.eventCount
          q r z (FixedSpanRenewalPayload.rawWord n T idx) := by
    intro idx
    let w := FixedSpanRenewalPayload.rawWord n T idx
    let N := ControlledSchedulerMass.eventCount q r z w
    have hNT : N ≤ T := by
      have hh := tagged_q_event_count_le_length q r z w
      simpa [N, w,
        FixedSpanRenewalPayload.rawWord_length] using hh
    have hsec : 7 * 2 ^ T ≤
        64 * 2 ^ (T - N) + N * 2 ^ T := by
      simpa using tagged_q_secant_scaled 5 T N hNT
    have hnf : ControlledSchedulerMass.runWord q z w ≠
        .failure :=
      tagged_d15_safe_word q hcontrolled z hz w
    cases hr : ControlledSchedulerMass.runWord q z w with
    | active y =>
        simpa [powSuccessOrActive, hr, N, w,
          Nat.mul_comm] using hsec
    | success =>
        simpa [powSuccessOrActive, hr, N, w,
          Nat.mul_comm] using hsec
    | failure =>
        exact False.elim (hnf hr)
  have hsum :=
    ofFn_sum_le
      (fun _ : Fin (n ^ T) => 7 * 2 ^ T)
      (fun idx : Fin (n ^ T) =>
        64 * powSuccessOrActive
          (ControlledSchedulerMass.runWord q z
            (FixedSpanRenewalPayload.rawWord n T idx))
          (T - ControlledSchedulerMass.eventCount q r z
            (FixedSpanRenewalPayload.rawWord n T idx)) +
        2 ^ T * ControlledSchedulerMass.eventCount q r z
          (FixedSpanRenewalPayload.rawWord n T idx))
      hpoint
  rw [ofFn_sum_const, ofFn_sum_add,
    ofFn_sum_mul_left, ofFn_sum_mul_left] at hsum
  rw [
    FixedSpanRenewalPayload.rawWord_sum n T
      (fun w =>
        powSuccessOrActive
          (ControlledSchedulerMass.runWord q z w)
          (T - ControlledSchedulerMass.eventCount q r z w)),
    FixedSpanRenewalPayload.rawWord_sum n T
      (fun w => ControlledSchedulerMass.eventCount q r z w)
  ] at hsum
  have hword :
      n ^ T * (7 * 2 ^ T) ≤
        64 * weightedQNonRetryNumerator step r z T +
          2 ^ T * collapseCountNumerator step r z T := by
    simpa [q, weightedQNonRetryNumerator,
      collapseCountNumerator] using hsum
  calc
    7 * (2 ^ T * n ^ T) =
        n ^ T * (7 * 2 ^ T) := by
      ac_rfl
    _ ≤ 64 * weightedQNonRetryNumerator step r z T +
        2 ^ T * collapseCountNumerator step r z T := hword

/-- If E_Q[N] <= 6 (in numerator form), the raw process
has at least 1/64 probability of non-failure by any horizon. -/
theorem tagged_d15_nonretry_small
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S)
    (r : ControlledSchedulerMass.Redirection S n)
    (z : StopNode S) (hz : z ≠ .failure)
    (hcontrolled : ∀ s e,
      ControlledSchedulerMass.controlledStep step r s e ≠ .failure)
    (T : Nat)
    (hcollapse :
      collapseCountNumerator step r z T ≤ 6 * n ^ T) :
    n ^ T ≤ 64 * (activeCount step z T +
      successCount step z T) := by
  let P := 2 ^ T * n ^ T
  let W := weightedQNonRetryNumerator step r z T
  let C := 2 ^ T * collapseCountNumerator step r z T
  have hsec : 7 * P ≤ 64 * W + C := by
    simpa [P, W, C] using
      tagged_d15_secant_nonretry step r z hz hcontrolled T
  have hc : C ≤ 6 * P := by
    calc
      C = 2 ^ T * collapseCountNumerator step r z T := rfl
      _ ≤ 2 ^ T * (6 * n ^ T) :=
        Nat.mul_le_mul_left (2 ^ T) hcollapse
      _ = 6 * P := by
        dsimp [P]
        ac_rfl
  have hp : P ≤ 64 * W := by omega
  have hchange := weighted_changeOfMeasure_nonretry step r z T
  have hscaled : 2 ^ T * n ^ T ≤
      2 ^ T * (64 * (activeCount step z T +
        successCount step z T)) := by
    calc
      2 ^ T * n ^ T = P := rfl
      _ ≤ 64 * W := hp
      _ ≤ 64 * (2 ^ T *
          (activeCount step z T + successCount step z T)) :=
        Nat.mul_le_mul_left 64 hchange
      _ = 2 ^ T * (64 *
          (activeCount step z T + successCount step z T)) := by
        ac_rfl
  exact Nat.le_of_mul_le_mul_left hscaled
    (Nat.pow_pos (by decide : 0 < 2))

/-- At b>=3, the collapse bound 5 E_Q[N] <= 28 and
7/320 >= 1/52 imply raw nonretry mass at least 1/52. -/
theorem tagged_d15_nonretry_large
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S)
    (r : ControlledSchedulerMass.Redirection S n)
    (z : StopNode S) (hz : z ≠ .failure)
    (hcontrolled : ∀ s e,
      ControlledSchedulerMass.controlledStep step r s e ≠ .failure)
    (T : Nat)
    (hcollapse :
      5 * collapseCountNumerator step r z T ≤ 28 * n ^ T) :
    n ^ T ≤ 52 * (activeCount step z T +
      successCount step z T) := by
  let P := 2 ^ T * n ^ T
  let W := weightedQNonRetryNumerator step r z T
  let C := 2 ^ T * collapseCountNumerator step r z T
  have hsec : 7 * P ≤ 64 * W + C := by
    simpa [P, W, C] using
      tagged_d15_secant_nonretry step r z hz hcontrolled T
  have hc : 5 * C ≤ 28 * P := by
    calc
      5 * C = 2 ^ T *
          (5 * collapseCountNumerator step r z T) := by
        dsimp [C]
        ac_rfl
      _ ≤ 2 ^ T * (28 * n ^ T) :=
        Nat.mul_le_mul_left (2 ^ T) hcollapse
      _ = 28 * P := by
        dsimp [P]
        ac_rfl
  have hfive := Nat.mul_le_mul_left 5 hsec
  have hseven : 7 * P ≤ 320 * W := by omega
  have hprod : 7 * P ≤ 7 * (52 * W) := by
    calc
      _ ≤ 320 * W := hseven
      _ ≤ (7 * 52) * W :=
        Nat.mul_le_mul_right W tagged_moderate_q_secant_multiplier
      _ = 7 * (52 * W) := by ac_rfl
  have hp : P ≤ 52 * W :=
    Nat.le_of_mul_le_mul_left hprod (by decide : 0 < 7)
  have hchange := weighted_changeOfMeasure_nonretry step r z T
  have hscaled : 2 ^ T * n ^ T ≤
      2 ^ T * (52 * (activeCount step z T +
        successCount step z T)) := by
    calc
      2 ^ T * n ^ T = P := rfl
      _ ≤ 52 * W := hp
      _ ≤ 52 * (2 ^ T *
          (activeCount step z T + successCount step z T)) :=
        Nat.mul_le_mul_left 52 hchange
      _ = 2 ^ T * (52 *
          (activeCount step z T + successCount step z T)) := by
        ac_rfl
  exact Nat.le_of_mul_le_mul_left hscaled
    (Nat.pow_pos (by decide : 0 < 2))

/-- Physical D.10+D.12+D.14, raw vulnerable FAILURE count at
a genuine clean-dummy entrance: <=63/64 at b=2 and
<=51/52 at b>=3. The result is NOT a full per-attempt retry
bound for arbitrary Prepared scratch. -/
theorem tagged_d15_physical_vulnerable_failure_mass {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hb : 2 ≤ b) (hab : a ≤ 2 * b)
    (hports : ring.leftNeighbor j ≠ j)
    (seed : TripleNativeState n)
    (hstart : TaggedTriple ring i j k a b seed)
    (hclean : TaggedCleanDummy ring i j a b seed) :
    ∀ T,
      taggedModerateMultiplier b *
        failureCount (taggedTrialStep ring i j k b)
          (.active seed) T ≤
      (taggedModerateMultiplier b - 1) * n ^ T := by
  let step := taggedTrialStep ring i j k b
  let r := taggedRedirection ring j b
    (by omega : 2 ≤ n) hports
  have hq : ∀ s e,
      ControlledSchedulerMass.controlledStep step r s e ≠
        .failure := by
    intro s e
    change taggedQStopped ring i j k b
      (by omega : 2 ≤ n) hports s e ≠ .failure
    rw [tagged_q_stopped_eq ring i j k b
      (by omega : 2 ≤ n) hports s e]
    split <;> simp
  intro T
  have hcollapse := tagged_d15_physical_collapse_moment
    hnthree ring i j k a b hb hports
    seed hstart hclean T
  have hpart := node_count_partition step (.active seed) T
  by_cases htwo : b = 2
  · have hcoeff : 5 * a - 2 ≤ 18 := by
      simpa [htwo] using
        (tagged_moderate_q_two_arithmetic a b htwo hab)
    have hc :
        collapseCountNumerator step r (.active seed) T ≤
          6 * n ^ T := by
      have hleft : 3 *
          collapseCountNumerator step r (.active seed) T ≤
          (5 * a - 2) * n ^ T := by
        have h := hcollapse
        subst htwo
        rw [Nat.mul_comm (n ^ T)] at h
        exact h
      have hright : (5 * a - 2) * n ^ T ≤
          18 * n ^ T :=
        Nat.mul_le_mul_right (n ^ T) hcoeff
      omega
    have hnonretry := tagged_d15_nonretry_small
      step r (.active seed) (by simp) hq T hc
    have hfail :
        64 * failureCount step (.active seed) T ≤
          63 * n ^ T := by
      omega
    simpa [step, taggedModerateMultiplier, htwo] using hfail
  · have hthree : 3 ≤ b := by omega
    have hc :
        5 * collapseCountNumerator step r (.active seed) T ≤
          28 * n ^ T := by
      let C := collapseCountNumerator step r (.active seed) T
      let P := n ^ T
      let m := 2 * b - 1
      let v := 5 * a - 2
      have hcv : m * C ≤ v * P := by
        have h := hcollapse
        rw [Nat.mul_comm (n ^ T)] at h
        exact h
      have hbound : 5 * v ≤ 28 * m :=
        tagged_moderate_q_large_arithmetic a b hthree hab
      have hprod : m * (5 * C) ≤ m * (28 * P) := by
        calc
          m * (5 * C) = 5 * (m * C) := by ac_rfl
          _ ≤ 5 * (v * P) :=
            Nat.mul_le_mul_left 5 hcv
          _ = (5 * v) * P := by ac_rfl
          _ ≤ (28 * m) * P :=
            Nat.mul_le_mul_right P hbound
          _ = m * (28 * P) := by ac_rfl
      have hm : 0 < m := by
        dsimp [m]
        omega
      exact Nat.le_of_mul_le_mul_left hprod hm
    have hnonretry := tagged_d15_nonretry_large
      step r (.active seed) (by simp) hq T hc
    have hfail :
        52 * failureCount step (.active seed) T ≤
          51 * n ^ T := by
      omega
    simpa [step, taggedModerateMultiplier, if_neg htwo] using hfail

end L3

/-! ## D.15 Ready closure on the physical prepared triple

This uses nativeE and the literal
SealedClose source-relative table, without changing any machine row.
A Ready excursion needs the full Ready continuation potential: the
two-port drift below accounts for outgoing Live and incoming Dummy.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

attribute [local instance low] Classical.propDecidable

/-- Ready preparation exits on the actual incoming clean dummy or
a physical deletion of one of the three tagged leaders. -/
private def taggedD15ReadyStop {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n)
    (a b : Nat) (N : TripleNativeState n) : Prop :=
  TaggedDeleted i j k N ∨ TaggedCleanDummy ring i j a b N

/-- The Ready-restart term remains present during the entire
non-Ready excursion, whose target rank is charged separately. -/
noncomputable def taggedD15ReadyPotential {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n)
    (a b : Nat) (N : TripleNativeState n) : Nat :=
  if taggedD15ReadyStop ring i j k a b N then 0
  else n * ((2 * b - 1) +
    SealedPhaseProgress b (taggedQAttackerPhase ring j b N))

private theorem tagged_d15_ready_phase_value {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n)
    (a b : Nat) (N : TripleNativeState n)
    (phase : SealedPhase n)
    (hp : SealedPhaseHolds ring N j b phase)
    (ht : ¬ taggedD15ReadyStop ring i j k a b N) :
    taggedD15ReadyPotential ring i j k a b N =
      n * ((2 * b - 1) +
        SealedCloseProof.rank b (SealedCloseProof.fromPhase phase)) := by
  unfold taggedD15ReadyPotential
  rw [if_neg ht]
  rw [tagged_q_attacker_phase_eq ring N j b phase hp]
  cases phase <;> rfl

/-- The killed child value is bounded by the literal successor
table, including children deleted before a stage is extracted. -/
private theorem tagged_d15_ready_child_rank {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n)
    (a b : Nat) (N : TripleNativeState n) (e : Fin n)
    (ht : TaggedTriple ring i j k a b N)
    (phase : SealedPhase n)
    (hp : SealedPhaseHolds ring N j b phase) :
    taggedD15ReadyPotential ring i j k a b (nativeE ring N e) ≤
      n * ((2 * b - 1) +
        SealedCloseProof.rank b (sealedCloseTable ring j b e phase)) := by
  classical
  by_cases hstop :
      taggedD15ReadyStop ring i j k a b (nativeE ring N e)
  · simp only [taggedD15ReadyPotential, if_pos hstop]
    exact Nat.zero_le _
  · have hsurvive :
        ¬ TaggedDeleted i j k (nativeE ring N e) := by
      intro hd
      exact hstop (Or.inl hd)
    have hj : (nativeE ring N e j).l = true := by
      cases hx : (nativeE ring N e j).l with
      | false => exact False.elim (hsurvive (Or.inr (Or.inl hx)))
      | true => rfl
    have hk : (nativeE ring N e k).l = true := by
      cases hx : (nativeE ring N e k).l with
      | false => exact False.elim (hsurvive (Or.inr (Or.inr hx)))
      | true => rfl
    obtain ⟨after, hafter, hstage⟩ :=
      sealed_close_step_stage ring N j k b e phase
        ht.2.2 hp hj hk
    have hvalue :=
      tagged_d15_ready_phase_value ring i j k a b
        (nativeE ring N e) after hafter hstop
    calc
      taggedD15ReadyPotential ring i j k a b (nativeE ring N e) ≤
          n * ((2 * b - 1) +
            SealedCloseProof.rank b
              (SealedCloseProof.fromPhase after)) :=
        Nat.le_of_eq hvalue
      _ = n * ((2 * b - 1) +
            SealedCloseProof.rank b
              (sealedCloseTable ring j b e phase)) := by
        rw [hstage]

/-- Real source-j outgoing edge has target offset zero. -/
private theorem tagged_d15_ready_out_table {n : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (j k : Fin n) (b : Nat) (hb : 2 ≤ b)
    (hc : ConsecutiveNative ring N j k b)
    (hp : SealedCleanReady ring N j b) :
    sealedCloseTable ring j b j (.ready : SealedPhase n) =
      SealedCloseProof.Stage.bullet true 1 := by
  have hnom :=
    sealed_close_nominated_position ring N j k b
      (.ready : SealedPhase n) hc hp
  have hpos : (SealedCloseProof.position ring j j).val = 0 := by
    simpa only [SealedPhaseEdge, SealedCloseProof.fromPhase,
      SealedCloseProof.nominated] using hnom
  have hzero : 0 < b := by omega
  have hone : b ≠ 1 := by omega
  change
    (if (SealedCloseProof.position ring j j).val < b then
      SealedCloseProof.insideStage b .ready
        (SealedCloseProof.position ring j j).val
     else if (SealedCloseProof.position ring j j).val + 1 = n then
      SealedCloseProof.incomingStage .ready
     else .ready) = .bullet true 1
  rw [hpos]
  simp [hzero, hone, SealedCloseProof.insideStage]

/-- Except for outgoing j and incoming L_j, a physical Ready service
leaves the target's literal source-relative stage unchanged. -/
private theorem tagged_d15_ready_quiet_table {n : Nat}
    (ring : DirectedRing n) (j e : Fin n) (b : Nat)
    (hout : e ≠ j) (hin : e ≠ ring.leftNeighbor j) :
    sealedCloseTable ring j b e (.ready : SealedPhase n) =
      SealedCloseProof.Stage.ready := by
  let pos := SealedCloseProof.position ring j e
  have hnonzero : pos.val ≠ 0 := by
    intro hz
    have hsite :=
      sealed_close_edge_of_position ring j e 0 hz
    have he : e = j := by
      simpa only [sealedSite_zero] using hsite
    exact hout he
  have hnotIncoming : pos.val + 1 ≠ n := by
    intro hh
    exact hin ((sealed_close_incoming_iff ring j e).1 hh)
  change
    (if pos.val < b then
      SealedCloseProof.insideStage b .ready pos.val
     else if pos.val + 1 = n then
       SealedCloseProof.incomingStage .ready
     else .ready) = .ready
  by_cases hins : pos.val < b
  · simp [hins, hnonzero, SealedCloseProof.insideStage]
  · simp [hins, hnotIncoming]

/-- D.15 physical Ready closure, with repeated Live/Returning cycles
paid by a single finite Bellman supersolution. The state is not
restarted or changed between cycles. -/
theorem tagged_d15_ready_closure_cost {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat) (hb : 2 ≤ b)
    (N : TripleNativeState n)
    (htriple : TaggedTriple ring i j k a b N)
    (hprep : TaggedPrepared ring i j a b N) :
    ∀ T,
      costNumerator (nativeE ring)
        (taggedD15ReadyStop ring i j k a b) N T ≤
        n ^ T * (n * (2 * b - 1)) := by
  classical
  let target := taggedD15ReadyStop ring i j k a b
  let potential := taggedD15ReadyPotential ring i j k a b
  let Inv : TripleNativeState n → Prop :=
    fun M => TaggedTriple ring i j k a b M ∧
      TaggedSealed ring i j a b M
  have hclosed :
      ∀ M : TripleNativeState n, Inv M → ∀ e,
        ¬ target (nativeE ring M e) →
          Inv (nativeE ring M e) := by
    intro M hg e hnottarget
    have hsurvive :
        ¬ TaggedDeleted i j k (nativeE ring M e) := by
      intro hd
      exact hnottarget (Or.inl hd)
    have htr : TaggedTriple ring i j k a b (nativeE ring M e) :=
      tagged_triple_step_of_survival hnthree
        ring i j k a b M e hg.1 hsurvive
    have hs : TaggedSealed ring i j a b (nativeE ring M e) :=
      tagged_sealed_step_of_survival ring i j k a b
        M e hg.1 hg.2 hsurvive
    exact ⟨htr, hs⟩
  have hdrift :
      ∀ M : TripleNativeState n, Inv M → ¬ target M →
        n + (List.ofFn (fun e : Fin n =>
          potential (nativeE ring M e))).sum ≤
          n * potential M := by
    intro M hg hnot
    obtain ⟨phase, hp⟩ := hg.2.2
    have hOld :
        potential M =
          n * ((2 * b - 1) +
            SealedCloseProof.rank b
              (SealedCloseProof.fromPhase phase)) :=
      tagged_d15_ready_phase_value ring i j k a b M phase hp hnot
    by_cases hready : phase = .ready
    · subst phase
      have hports : j ≠ ring.leftNeighbor j :=
        tagged_q_incident_edges_distinct
          (by omega : 2 ≤ n) ring j
      have hprepM : TaggedPrepared ring i j a b M :=
        ⟨hg.2.1, hp⟩
      have hcap :
          ∀ e : Fin n,
            potential (nativeE ring M e) ≤
              n * ((2 * b - 1) +
                SealedCloseProof.rank b
                  (sealedCloseTable ring j b e
                    (.ready : SealedPhase n))) := by
        intro e
        exact tagged_d15_ready_child_rank
          ring i j k a b M e hg.1 .ready hp
      have hout :
          potential (nativeE ring M j) ≤ n * (4 * b - 3) := by
        have htable := tagged_d15_ready_out_table
          ring M j k b hb hg.1.2.2 hp
        have hh := hcap j
        rw [htable] at hh
        have hcoef :
            (2 * b - 1) +
              SealedCloseProof.rank b (.bullet true 1) =
              4 * b - 3 := by
          simp only [SealedCloseProof.rank]
          omega
        simpa only [hcoef] using hh
      have hin :
          potential (nativeE ring M (ring.leftNeighbor j)) = 0 := by
        have htarget :
            target (nativeE ring M (ring.leftNeighbor j)) :=
          tagged_d15_prepared_incoming hnthree
            ring i j k a b M hg.1 hprepM
        change
          (if taggedD15ReadyStop ring i j k a b
                (nativeE ring M (ring.leftNeighbor j))
           then 0
           else n * ((2 * b - 1) +
             SealedPhaseProgress b
               (taggedQAttackerPhase ring j b
                 (nativeE ring M (ring.leftNeighbor j))))) = 0
        rw [if_pos htarget]
      have hrest :
          ∀ e : Fin n, e ≠ j →
            e ≠ ring.leftNeighbor j →
              potential (nativeE ring M e) ≤
                n * (2 * b - 1) := by
        intro e he hi
        have htable :=
          tagged_d15_ready_quiet_table ring j e b he hi
        have hh := hcap e
        rw [htable] at hh
        simpa only [SealedCloseProof.rank, Nat.add_zero] using hh
      have hreadyValue : potential M = n * (2 * b - 1) := by
        simpa only [SealedCloseProof.fromPhase,
          SealedCloseProof.rank, Nat.add_zero] using hOld
      have hrow := tagged_d15_ready_two_port b hb
        (fun e : Fin n => potential (nativeE ring M e))
        j (ring.leftNeighbor j) hports hout hin hrest
      rw [hreadyValue]
      exact hrow
    · let port := SealedPhaseEdge ring j phase
      have hcap :
          ∀ e : Fin n,
            potential (nativeE ring M e) ≤
              n * ((2 * b - 1) +
                SealedCloseProof.rank b
                  (sealedCloseTable ring j b e phase)) := by
        intro e
        exact tagged_d15_ready_child_rank
          ring i j k a b M e hg.1 phase hp
      have htable (e : Fin n) :=
        tagged_target_nonready_table_exact ring M j k b
          hb phase e hg.1.2.2 hp hready
      have hweak :
          ∀ e : Fin n,
            potential (nativeE ring M e) ≤ potential M := by
        intro e
        have hh := htable e
        have hrank :
            SealedCloseProof.rank b
                (sealedCloseTable ring j b e phase) ≤
              SealedCloseProof.rank b
                (SealedCloseProof.fromPhase phase) := by
          omega
        calc
          potential (nativeE ring M e) ≤
              n * ((2 * b - 1) +
                SealedCloseProof.rank b
                  (sealedCloseTable ring j b e phase)) := hcap e
          _ ≤ n * ((2 * b - 1) +
                SealedCloseProof.rank b
                  (SealedCloseProof.fromPhase phase)) :=
            Nat.mul_le_mul_left n
              (Nat.add_le_add_left hrank (2 * b - 1))
          _ = potential M := hOld.symm
      have hnom := htable port
      have hrank :
          SealedCloseProof.rank b
            (sealedCloseTable ring j b port phase) + 1 =
          SealedCloseProof.rank b
            (SealedCloseProof.fromPhase phase) := by
        simpa only [port, ↓reduceIte] using hnom
      have hcoef :
          ((2 * b - 1) + SealedCloseProof.rank b
            (sealedCloseTable ring j b port phase)) + 1 =
          (2 * b - 1) + SealedCloseProof.rank b
            (SealedCloseProof.fromPhase phase) := by
        omega
      have hstrict :
          potential (nativeE ring M port) + n ≤
            potential M := by
        calc
          potential (nativeE ring M port) + n ≤
              n * ((2 * b - 1) +
                SealedCloseProof.rank b
                  (sealedCloseTable ring j b port phase)) + n :=
            Nat.add_le_add_right (hcap port) n
          _ = n * (((2 * b - 1) +
                SealedCloseProof.rank b
                  (sealedCloseTable ring j b port phase)) + 1) :=
            (Nat.mul_succ _ _).symm
          _ = n * ((2 * b - 1) +
                SealedCloseProof.rank b
                  (SealedCloseProof.fromPhase phase)) := by
            rw [hcoef]
          _ = potential M := hOld.symm
      exact tagged_q_drift_from_nominated_edge
        (potential M)
        (fun e : Fin n => potential (nativeE ring M e))
        port hweak hstrict
  have hinitial : ¬ target N := by
    intro hd
    rcases hd with hdel | hclean
    · exact (tagged_d15_triple_not_deleted
        ring i j k a b N htriple) hdel
    · have hh := tagged_sealed_phase_unique
        ring N j b (.ready : SealedPhase n)
        (.dummy (sealedZero ring)) hprep.2 hclean.2
      cases hh
  have hstartValue : potential N = n * (2 * b - 1) := by
    have hh := tagged_d15_ready_phase_value
      ring i j k a b N (.ready : SealedPhase n)
      hprep.2 hinitial
    simpa only [SealedCloseProof.fromPhase,
      SealedCloseProof.rank, Nat.add_zero] using hh
  have hcost := tagged_q_restricted_cost_of_potential
    (nativeE ring) target Inv potential
    hclosed hdrift N
    ⟨htriple, tagged_prepared_sealed ring i j a b N hprep⟩
  intro T
  have hh := hcost T
  simpa only [hstartValue] using hh

end L3

/-! ## Physical attempt-phase alias obstruction

Certificate. These proofs use the original nativeE row.
A physical state can revisit exactly the same Ready configuration
after a clean-Dummy vulnerable entrance; an attempt-history bit
cannot be recovered from SealedPhaseHolds on that state alone.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

/-- Regardless of the attempt mode, the physical two-sector sealed
domain is genuinely closed under every surviving nativeE row. -/
theorem tagged_d15_sealed_domain_step {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n) (e : Fin n)
    (htriple : TaggedTriple ring i j k a b N)
    (hsealed : TaggedSealed ring i j a b N) :
    TaggedDeleted i j k (nativeE ring N e) ∨
      (TaggedTriple ring i j k a b (nativeE ring N e) ∧
        TaggedSealed ring i j a b (nativeE ring N e)) := by
  by_cases hdel : TaggedDeleted i j k (nativeE ring N e)
  · exact Or.inl hdel
  · exact Or.inr
      ⟨tagged_triple_step_of_survival
          hn ring i j k a b N e htriple hdel,
        tagged_sealed_step_of_survival
          ring i j k a b N e htriple hsealed hdel⟩

/-- Five-site ring with three physical leaders at 0,2,4. -/
private def taggedD15AliasRing : DirectedRing 5 := ⟨by decide⟩

/-- Both sectors are Ready, with the two predecessor signals already
present. K is a leader whose signal is zero. Every bullet is empty. -/
private def taggedD15AliasSeed : TripleNativeState 5 :=
  fun z =>
    if z.val = 0 then
      { l := true, b := 0, sh := false, sg := true }
    else if z.val = 1 then
      { l := false, b := 0, sh := false, sg := true }
    else if z.val = 2 then
      { l := true, b := 0, sh := false, sg := true }
    else if z.val = 3 then
      { l := false, b := 0, sh := false, sg := true }
    else
      { l := true, b := 0, sh := false, sg := false }

/-- Incoming edge 1 first creates physical clean Dummy(0) at B. -/
private def taggedD15AliasDummy : TripleNativeState 5 :=
  nativeE taggedD15AliasRing taggedD15AliasSeed (1 : Fin 5)

/-- Outgoing edge 2 advances this dummy to offset one. -/
private def taggedD15AliasMoved : TripleNativeState 5 :=
  nativeE taggedD15AliasRing taggedD15AliasDummy (2 : Fin 5)

/-- Edge 3 absorbs the dummy at leader K and starts the return. -/
private def taggedD15AliasReturning : TripleNativeState 5 :=
  nativeE taggedD15AliasRing taggedD15AliasMoved (3 : Fin 5)

/-- Edge 2 completes the incoming signal, restoring Ready at B. -/
private def taggedD15AliasReturned : TripleNativeState 5 :=
  nativeE taggedD15AliasRing taggedD15AliasReturning (2 : Fin 5)

theorem tagged_d15_alias_initial_triple :
    TaggedTriple taggedD15AliasRing
      (0 : Fin 5) (2 : Fin 5) (4 : Fin 5)
      2 2 taggedD15AliasSeed := by
  have hzero : ∀ v : Fin 5,
      (taggedD15AliasSeed v).b = (0 : Fin 3) := by
    decide +kernel
  refine ⟨?_, ?_, ?_⟩
  · intro v hlive
    change (taggedD15AliasSeed v).b = (2 : Fin 3) at hlive
    rw [hzero v] at hlive
    cases hlive
  · dsimp only [ConsecutiveNative]
    decide +kernel
  · dsimp only [ConsecutiveNative]
    decide +kernel

theorem tagged_d15_alias_initial_prepared :
    TaggedPrepared taggedD15AliasRing
      (0 : Fin 5) (2 : Fin 5) 2 2
      taggedD15AliasSeed := by
  refine ⟨⟨.ready, ?_⟩, ?_⟩
  · dsimp only [SealedPhaseHolds, SealedNoBullet]
    decide +kernel
  · dsimp only [SealedCleanReady, SealedPhaseHolds,
      SealedNoBullet]
    decide +kernel

theorem tagged_d15_alias_clean_dummy :
    TaggedCleanDummy taggedD15AliasRing
      (0 : Fin 5) (2 : Fin 5) 2 2
      taggedD15AliasDummy := by
  refine ⟨⟨.ready, ?_⟩, ?_⟩
  · dsimp only [SealedPhaseHolds, SealedNoBullet]
    decide +kernel
  · dsimp only [SealedPhaseHolds, SealedUniqueBullet,
      SealedZeroTrail]
    decide +kernel

/-- The outgoing service of clean Dummy(0) is not a retry cut:
the real successor has a moving Dummy(1), not Ready/Live(1). -/
theorem tagged_d15_alias_dummy_moves :
    SealedPhaseHolds taggedD15AliasRing
      taggedD15AliasMoved (2 : Fin 5) 2
      (.dummy (1 : Fin 5)) := by
  dsimp only [SealedPhaseHolds, SealedUniqueBullet,
    SealedZeroTrail]
  decide +kernel

theorem tagged_d15_alias_returning_phase :
    SealedPhaseHolds taggedD15AliasRing
      taggedD15AliasReturning (2 : Fin 5) 2
      (.returning (1 : Fin 5)) := by
  dsimp only [SealedPhaseHolds, SealedNoBullet,
    SealedFirstSignal]
  decide +kernel

/-- No tag has been deleted anywhere on the four-service loop,
nor on the alternate outgoing Ready service. -/
theorem tagged_d15_alias_survives :
    ¬ TaggedDeleted (0 : Fin 5) (2 : Fin 5) (4 : Fin 5)
        taggedD15AliasDummy ∧
    ¬ TaggedDeleted (0 : Fin 5) (2 : Fin 5) (4 : Fin 5)
        taggedD15AliasMoved ∧
    ¬ TaggedDeleted (0 : Fin 5) (2 : Fin 5) (4 : Fin 5)
        taggedD15AliasReturning ∧
    ¬ TaggedDeleted (0 : Fin 5) (2 : Fin 5) (4 : Fin 5)
        taggedD15AliasReturned ∧
    ¬ TaggedDeleted (0 : Fin 5) (2 : Fin 5) (4 : Fin 5)
        (nativeE taggedD15AliasRing taggedD15AliasSeed
          (2 : Fin 5)) := by
  dsimp only [TaggedDeleted]
  decide +kernel

/-- The exact complete physical native state returns, not merely
its sealed-phase label or the three leader flags. -/
theorem tagged_d15_alias_exact_return :
    taggedD15AliasReturned = taggedD15AliasSeed := by
  have hall :
      ∀ z : Fin 5,
        taggedD15AliasReturned z = taggedD15AliasSeed z := by
    decide +kernel
  exact funext hall

theorem tagged_d15_alias_returned_prepared :
    TaggedPrepared taggedD15AliasRing
      (0 : Fin 5) (2 : Fin 5) 2 2
      taggedD15AliasReturned := by
  rw [tagged_d15_alias_exact_return]
  exact tagged_d15_alias_initial_prepared

/-- On the identical Ready state, outgoing edge 2 launches Live(1).
It is part of the Ready preparation stage before a clean dummy,
but a vulnerable-trial failure after the clean-Dummy entrance. -/
theorem tagged_d15_alias_ready_outgoing_live :
    SealedPhaseHolds taggedD15AliasRing
      (nativeE taggedD15AliasRing taggedD15AliasSeed (2 : Fin 5))
      (2 : Fin 5) 2 (.live (1 : Fin 5)) := by
  dsimp only [SealedPhaseHolds, SealedUniqueBullet,
    SealedZeroTrail]
  decide +kernel

/-- No state-only observer can assign distinct attempt-history modes
to the same physical state before and after this genuine loop. -/
theorem tagged_d15_no_memoryless_attempt_phase
    (Phase : Type)
    (attemptPhase : TripleNativeState 5 → Option Phase)
    (ready vulnerable : Phase)
    (hne : ready ≠ vulnerable)
    (hentry : attemptPhase taggedD15AliasSeed = some ready)
    (hpost : attemptPhase taggedD15AliasReturned = some vulnerable) :
    False := by
  rw [tagged_d15_alias_exact_return] at hpost
  have hh : (some ready : Option Phase) = some vulnerable :=
    hentry.symm.trans hpost
  exact hne (Option.some.inj hh)

end L3


/-! ## Real history-carrying D.15 attempt and recovery

No machine or nativeE row is
modified. The attempt mode is an independent historical coordinate:
two runs with exactly the same physical Native state can have
different modes. The stage's phase is a witness about the CURRENT
physical state, not a stored replacement native state.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

inductive TaggedD15AttemptMode where
  | readyWait
  | vulnerable
  | recovery
  deriving DecidableEq, Repr

/-- In recovery the actual B sector has not yet returned to Ready.
The Live(1) entry is certified by the outgoing-stage table below. -/
def TaggedD15ModeValid {n : Nat}
    (mode : TaggedD15AttemptMode) (phase : SealedPhase n) : Prop :=
  match mode with
  | .readyWait => True
  | .vulnerable => True
  | .recovery => phase ≠ .ready

/-- The phase/history observer is separate from N. All physical fields
are still exactly the original TripleNativeState, never overwritten by
the monitor. The stored proofs enforce the real triple and two sectors. -/
structure TaggedD15AttemptState {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat) where
  N : TripleNativeState n
  mode : TaggedD15AttemptMode
  targetPhase : SealedPhase n
  triple : TaggedTriple ring i j k a b N
  attackerSealed : Sealed ring N i a
  targetHolds : SealedPhaseHolds ring N j b targetPhase
  modeValid : TaggedD15ModeValid mode targetPhase

/-- A retry carries its actual reached Ready cut and the genuine
native-domain certificate; there is no canonical reset state. -/
structure TaggedD15AttemptSeed {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat) where
  N : TripleNativeState n
  triple : TaggedTriple ring i j k a b N
  prepared : TaggedPrepared ring i j a b N

def tagged_d15_attempt_start {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (seed : TaggedD15AttemptSeed ring i j k a b) :
    TaggedD15AttemptState ring i j k a b :=
  { N := seed.N
    mode := .readyWait
    targetPhase := .ready
    triple := seed.triple
    attackerSealed := seed.prepared.1
    targetHolds := seed.prepared.2
    modeValid := True.intro }

/-- This dependent node predicate ties EVERY continuation and retry
to the literal nativeE successor. A success node must mean an actual
tagged deletion, rather than the observer's choice to terminate. -/
private def taggedD15NodeMatches {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (M : TripleNativeState n) :
    AttemptNode (TaggedD15AttemptState ring i j k a b)
      (TaggedD15AttemptSeed ring i j k a b) → Prop
  | .success => TaggedDeleted i j k M
  | .active z => z.N = M
  | .retry seed => seed.N = M

/- One nativeE step from a valid physical triple with its historical
stage. The subtype certificate proves that the observer cannot
silently change or restart N. -/

/-- Local per-mode domain for the history observer. Moved here
because the certified step now proves active-good closure. -/
def TaggedD15AttemptGood {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (z : TaggedD15AttemptState ring i j k a b) : Prop :=
  (z.mode = .readyWait →
    ¬ TaggedCleanDummy ring i j a b z.N) ∧
  (z.mode = .vulnerable → (z.N j).sh = false)

/-- The two terminal node kinds have no active invariant to preserve. -/
private def taggedD15NodeGood {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat) :
    AttemptNode (TaggedD15AttemptState ring i j k a b)
      (TaggedD15AttemptSeed ring i j k a b) → Prop
  | .success => True
  | .retry _ => True
  | .active z => TaggedD15AttemptGood ring i j k a b z

noncomputable def tagged_d15_attempt_step_certified {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat) (hb : 2 ≤ b)
    (z : TaggedD15AttemptState ring i j k a b)
    (e : Fin n) :
    { out : AttemptNode (TaggedD15AttemptState ring i j k a b)
        (TaggedD15AttemptSeed ring i j k a b) //
      taggedD15NodeMatches ring i j k a b
        (nativeE ring z.N e) out ∧
      (TaggedD15AttemptGood ring i j k a b z →
        taggedD15NodeGood ring i j k a b out) ∧
      (∀ z', out = .active z' →
        (z.mode = .readyWait →
          (TaggedCleanDummy ring i j a b (nativeE ring z.N e) →
            z'.mode = .vulnerable) ∧
          (¬ TaggedCleanDummy ring i j a b (nativeE ring z.N e) →
            z'.mode = .readyWait)) ∧
        (z.mode = .vulnerable →
          ((z.targetPhase = .ready ∧ e = j) →
            z'.mode = .recovery ∧
              SealedCloseProof.fromPhase z'.targetPhase =
                SealedCloseProof.Stage.bullet true 1) ∧
          (¬ (z.targetPhase = .ready ∧ e = j) →
            z'.mode = .vulnerable)) ∧
        (z.mode = .recovery → z'.mode = .recovery)) ∧
      (∀ seed, out = .retry seed → z.mode = .recovery) } := by
  classical
  let M := nativeE ring z.N e
  by_cases hdeleted : TaggedDeleted i j k M
  · exact ⟨.success, ⟨hdeleted, fun _ => True.intro,
        (by intro z' h; cases h),
        (by intro seed h; cases h)⟩⟩
  · have htriple : TaggedTriple ring i j k a b M :=
      tagged_triple_step_of_survival hn ring i j k a b
        z.N e z.triple hdeleted
    have hsealed : TaggedSealed ring i j a b M :=
      tagged_sealed_step_of_survival ring i j k a b
        z.N e z.triple
        ⟨z.attackerSealed, ⟨z.targetPhase, z.targetHolds⟩⟩
        hdeleted
    have hj : (M j).l = true := by
      cases hx : (M j).l with
      | false => exact False.elim (hdeleted (Or.inr (Or.inl hx)))
      | true => rfl
    have hk : (M k).l = true := by
      cases hx : (M k).l with
      | false => exact False.elim (hdeleted (Or.inr (Or.inr hx)))
      | true => rfl
    have hstep :=
      sealed_close_step_stage ring z.N j k b e z.targetPhase
        z.triple.2.2 z.targetHolds hj hk
    obtain ⟨nextPhase, hnextPhase, hstage⟩ :=
      Classical.indefiniteDescription _ hstep
    cases hmode : z.mode with
    | readyWait =>
        by_cases hclean : TaggedCleanDummy ring i j a b M
        · have hsh : (M j).sh = false := by
            have hs := hclean.2.2.1
            rw [sealedAt_zero] at hs
            exact hs
          refine ⟨.active
            { N := M
              mode := .vulnerable
              targetPhase := nextPhase
              triple := htriple
              attackerSealed := hsealed.1
              targetHolds := hnextPhase
              modeValid := True.intro }, ⟨rfl, ?_, ?_, ?_⟩⟩
          · intro _
            change
              (TaggedD15AttemptMode.vulnerable = .readyWait →
                ¬ TaggedCleanDummy ring i j a b M) ∧
              (TaggedD15AttemptMode.vulnerable = .vulnerable →
                (M j).sh = false)
            constructor
            · intro hbad
              cases hbad
            · intro _
              exact hsh
          · intro z' hz
            cases hz
            constructor
            · intro _
              constructor
              · intro _
                rfl
              · intro hno
                exact False.elim (hno hclean)
            constructor
            · intro hbad
              cases hbad
            · intro hbad
              cases hbad
          · intro seed hs
            cases hs
        · refine ⟨.active
            { N := M
              mode := .readyWait
              targetPhase := nextPhase
              triple := htriple
              attackerSealed := hsealed.1
              targetHolds := hnextPhase
              modeValid := True.intro }, ⟨rfl, ?_, ?_, ?_⟩⟩
          · intro _
            change
              (TaggedD15AttemptMode.readyWait = .readyWait →
                ¬ TaggedCleanDummy ring i j a b M) ∧
              (TaggedD15AttemptMode.readyWait = .vulnerable →
                (M j).sh = false)
            constructor
            · intro _
              exact hclean
            · intro hbad
              cases hbad
          · intro z' hz
            cases hz
            constructor
            · intro _
              constructor
              · intro hc
                exact False.elim (hclean hc)
              · intro _
                rfl
            constructor
            · intro hbad
              cases hbad
            · intro hbad
              cases hbad
          · intro seed hs
            cases hs
    | vulnerable =>
        by_cases hfail : z.targetPhase = .ready ∧ e = j
        · have hready : SealedCleanReady ring z.N j b := by
            change SealedPhaseHolds ring z.N j b .ready
            rw [← hfail.1]
            exact z.targetHolds
          have htable : sealedCloseTable ring j b e z.targetPhase =
              SealedCloseProof.Stage.bullet true 1 := by
            rw [hfail.1, hfail.2]
            exact tagged_d15_ready_out_table ring z.N j k b
              hb z.triple.2.2 hready
          have hrealLive :
              SealedCloseProof.fromPhase nextPhase =
                SealedCloseProof.Stage.bullet true 1 :=
            hstage.trans htable
          have hnonready : nextPhase ≠ .ready := by
            intro heq
            rw [heq] at hrealLive
            cases hrealLive
          refine ⟨.active
            { N := M
              mode := .recovery
              targetPhase := nextPhase
              triple := htriple
              attackerSealed := hsealed.1
              targetHolds := hnextPhase
              modeValid := hnonready }, ⟨rfl, ?_, ?_, ?_⟩⟩
          · intro _
            change
              (TaggedD15AttemptMode.recovery = .readyWait →
                ¬ TaggedCleanDummy ring i j a b M) ∧
              (TaggedD15AttemptMode.recovery = .vulnerable →
                (M j).sh = false)
            constructor
            · intro hbad
              cases hbad
            · intro hbad
              cases hbad
          · intro z' hz
            cases hz
            constructor
            · intro hbad
              cases hbad
            constructor
            · intro _
              constructor
              · intro _
                exact ⟨rfl, hrealLive⟩
              · intro hno
                exact False.elim (hno hfail)
            · intro hbad
              cases hbad
          · intro seed hs
            cases hs
        · refine ⟨.active
            { N := M
              mode := .vulnerable
              targetPhase := nextPhase
              triple := htriple
              attackerSealed := hsealed.1
              targetHolds := hnextPhase
              modeValid := True.intro }, ⟨rfl, ?_, ?_, ?_⟩⟩
          · intro hg
            have hsh : (z.N j).sh = false := hg.2 hmode
            have hshM : (M j).sh = false := by
              change (nativeE ring z.N e j).sh = false
              by_cases hsig : (z.N j).sg = true
              · have hready : SealedCleanReady ring z.N j b :=
                  tagged_q_sealed_signaling_ready
                    ring z.N j b
                    ⟨z.targetPhase, z.targetHolds⟩ hsig
                have hphase : z.targetPhase = .ready :=
                  tagged_sealed_phase_unique ring z.N j b
                    z.targetPhase .ready z.targetHolds hready
                have he : e ≠ j := by
                  intro hej
                  exact hfail ⟨hphase, hej⟩
                exact tagged_q_native_unshielded_of_avoided_launch
                  ring z.N j e hsh (Or.inr he)
              · have hzero : (z.N j).sg = false := by
                  cases hz : (z.N j).sg with
                  | false => rfl
                  | true => exact False.elim (hsig hz)
                exact tagged_q_native_unshielded_of_avoided_launch
                  ring z.N j e hsh (Or.inl hzero)
            change
              (TaggedD15AttemptMode.vulnerable = .readyWait →
                ¬ TaggedCleanDummy ring i j a b M) ∧
              (TaggedD15AttemptMode.vulnerable = .vulnerable →
                (M j).sh = false)
            constructor
            · intro hbad
              cases hbad
            · intro _
              exact hshM
          · intro z' hz
            cases hz
            constructor
            · intro hbad
              cases hbad
            constructor
            · intro _
              constructor
              · intro hf
                exact False.elim (hfail hf)
              · intro _
                rfl
            · intro hbad
              cases hbad
          · intro seed hs
            cases hs
    | recovery =>
        by_cases hready : nextPhase = .ready
        · have hphysicalReady : SealedCleanReady ring M j b := by
            rw [hready] at hnextPhase
            exact hnextPhase
          exact ⟨.retry
            { N := M
              triple := htriple
              prepared := ⟨hsealed.1, hphysicalReady⟩ },
                ⟨rfl, fun _ => True.intro,
                  (by intro z' hz; cases hz),
                  (by intro seed hs; cases hs; rfl)⟩⟩
        · refine ⟨.active
            { N := M
              mode := .recovery
              targetPhase := nextPhase
              triple := htriple
              attackerSealed := hsealed.1
              targetHolds := hnextPhase
              modeValid := hready }, ⟨rfl, ?_, ?_, ?_⟩⟩
          · intro _
            change
              (TaggedD15AttemptMode.recovery = .readyWait →
                ¬ TaggedCleanDummy ring i j a b M) ∧
              (TaggedD15AttemptMode.recovery = .vulnerable →
                (M j).sh = false)
            constructor
            · intro hbad
              cases hbad
            · intro hbad
              cases hbad
          · intro z' hz
            cases hz
            constructor
            · intro hbad
              cases hbad
            constructor
            · intro hbad
              cases hbad
            · intro _
              rfl
          · intro seed hs
            cases hs

noncomputable def tagged_d15_attempt_step {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat) (hb : 2 ≤ b)
    (z : TaggedD15AttemptState ring i j k a b)
    (e : Fin n) :
    AttemptNode (TaggedD15AttemptState ring i j k a b)
      (TaggedD15AttemptSeed ring i j k a b) :=
  (tagged_d15_attempt_step_certified hn ring i j k a b hb z e).val

/-- Physical all-edge closure, including tagged deletion, all survivors
and actual Ready retry payloads. The active successor is a well-typed
history state with its preserved TaggedTriple and A-sealed proofs. -/
theorem tagged_d15_attempt_all_edge_closed {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat) (hb : 2 ≤ b)
    (z : TaggedD15AttemptState ring i j k a b)
    (e : Fin n) :
    taggedD15NodeMatches ring i j k a b
      (nativeE ring z.N e)
      (tagged_d15_attempt_step hn ring i j k a b hb z e) :=
  (tagged_d15_attempt_step_certified hn ring i j k a b hb z e).property.1


/-- No active descendant of a good attempt can lose the per-mode
history invariant. This is projection of the certified subtype. -/
theorem tagged_d15_attempt_good_closed {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat) (hb : 2 ≤ b)
    (z z' : TaggedD15AttemptState ring i j k a b)
    (e : Fin n)
    (hg : TaggedD15AttemptGood ring i j k a b z)
    (hstep : tagged_d15_attempt_step hn ring i j k a b hb z e =
      .active z') :
    TaggedD15AttemptGood ring i j k a b z' := by
  have hc :=
    (tagged_d15_attempt_step_certified
      hn ring i j k a b hb z e).property.2.1 hg
  unfold tagged_d15_attempt_step at hstep
  rw [hstep] at hc
  exact hc

/-- The library's real attempt interface: a retry is an actual native
Ready state, not a synthetic clock or refreshed bit-field snapshot. -/
noncomputable def tagged_d15_retry_kernel {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat) (hb : 2 ≤ b) :
    RetryKernel (TaggedD15AttemptState ring i j k a b)
      (TaggedD15AttemptSeed ring i j k a b) n where
  start := tagged_d15_attempt_start ring i j k a b
  step := tagged_d15_attempt_step hn ring i j k a b hb
  valid := fun _ => True
  retry_valid := by
    intro _ _ _ _
    trivial

/-! A separate recovery clock uses non-Ready B's exact nominated
rank. It neither assumes the other sector is Ready nor conditions on
the future success of the vulnerable trial. -/

private def taggedD15RecoveryStop {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (b : Nat)
    (N : TripleNativeState n) : Prop :=
  TaggedDeleted i j k N ∨ SealedCleanReady ring N j b

open Classical in
noncomputable def taggedD15RecoveryPotential {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (b : Nat)
    (N : TripleNativeState n) : Nat :=
  if taggedD15RecoveryStop ring i j k b N then 0
  else n * SealedPhaseProgress b
    (taggedQAttackerPhase ring j b N)

private theorem tagged_d15_recovery_phase_value {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (b : Nat)
    (N : TripleNativeState n) (phase : SealedPhase n)
    (hphase : SealedPhaseHolds ring N j b phase)
    (hnot : ¬ taggedD15RecoveryStop ring i j k b N) :
    taggedD15RecoveryPotential ring i j k b N =
      n * SealedPhaseProgress b phase := by
  unfold taggedD15RecoveryPotential
  rw [if_neg hnot]
  rw [tagged_q_attacker_phase_eq ring N j b phase hphase]

private theorem tagged_d15_recovery_rank_positive {n : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (j : Fin n) (b : Nat) (phase : SealedPhase n)
    (hphase : SealedPhaseHolds ring N j b phase)
    (hnon : phase ≠ .ready) :
    1 ≤ SealedPhaseProgress b phase := by
  cases phase with
  | ready => exact False.elim (hnon rfl)
  | dummy p =>
      have hp : p.val < b := hphase.1.1
      simp only [SealedPhaseProgress]
      omega
  | live p =>
      have hp : p.val < b := hphase.1.1
      simp only [SealedPhaseProgress]
      omega
  | returning q =>
      have hq : 1 ≤ q.val := hphase.2.2.1
      simpa only [SealedPhaseProgress] using hq

/-- Exact stopped cost of B returning from ANY surviving non-Ready
sealed phase. At the actual Live(1) failure entry this rank is
2b-2, giving n(2b-2), including all intervening unrelated services. -/
theorem tagged_d15_recovery_cost_of_phase {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (htriple : TaggedTriple ring i j k a b N)
    (hsealed : TaggedSealed ring i j a b N)
    (phase : SealedPhase n)
    (hphase : SealedPhaseHolds ring N j b phase)
    (hnon : phase ≠ .ready) :
    ∀ T,
      costNumerator (nativeE ring)
        (taggedD15RecoveryStop ring i j k b) N T ≤
      n ^ T * (n * SealedPhaseProgress b phase) := by
  classical
  let stop := taggedD15RecoveryStop ring i j k b
  let V := taggedD15RecoveryPotential ring i j k b
  let Inv : TripleNativeState n → Prop :=
    fun M => TaggedTriple ring i j k a b M ∧
      TaggedSealed ring i j a b M
  have hclosed :
      ∀ M : TripleNativeState n, Inv M → ∀ e,
        ¬ stop (nativeE ring M e) → Inv (nativeE ring M e) := by
    intro M hgood e hnot
    have hnodelete :
        ¬ TaggedDeleted i j k (nativeE ring M e) := by
      intro hd
      exact hnot (Or.inl hd)
    exact ⟨tagged_triple_step_of_survival
        hn ring i j k a b M e hgood.1 hnodelete,
      tagged_sealed_step_of_survival
        ring i j k a b M e hgood.1 hgood.2 hnodelete⟩
  have hdrift :
      ∀ M : TripleNativeState n, Inv M → ¬ stop M →
        n + (List.ofFn (fun e : Fin n =>
          V (nativeE ring M e))).sum ≤ n * V M := by
    intro M hgood hnot
    obtain ⟨p, hp⟩ := hgood.2.2
    have hnonready : p ≠ .ready := by
      intro he
      apply hnot
      exact Or.inr (by
        change SealedCleanReady ring M j b
        subst he
        exact hp)
    have hOld : V M = n * SealedPhaseProgress b p :=
      tagged_d15_recovery_phase_value
        ring i j k b M p hp hnot
    have hpositive : 1 ≤ SealedPhaseProgress b p :=
      tagged_d15_recovery_rank_positive ring M j b p hp hnonready
    have hchild (e : Fin n) :
        V (nativeE ring M e) ≤ V M ∧
          (e = SealedPhaseEdge ring j p →
            V (nativeE ring M e) + n ≤ V M) := by
      let M' := nativeE ring M e
      by_cases hterminal : stop M'
      · have hzero : V M' = 0 := by
          unfold V taggedD15RecoveryPotential
          rw [if_pos hterminal]
        have hscaled : n ≤ n * SealedPhaseProgress b p := by
          have hh := Nat.mul_le_mul_left n hpositive
          simpa only [Nat.mul_one] using hh
        constructor
        · rw [hzero]
          exact Nat.zero_le _
        · intro _
          rw [hzero, Nat.zero_add, hOld]
          exact hscaled
      · have hnodelete : ¬ TaggedDeleted i j k M' := by
          intro hd
          exact hterminal (Or.inl hd)
        have hj : (M' j).l = true := by
          cases hx : (M' j).l with
          | false =>
              exact False.elim (hnodelete (Or.inr (Or.inl hx)))
          | true => rfl
        have hk : (M' k).l = true := by
          cases hx : (M' k).l with
          | false =>
              exact False.elim (hnodelete (Or.inr (Or.inr hx)))
          | true => rfl
        obtain ⟨nextPhase, hnext, hprogress⟩ :=
          sealed_close_step_with_progress
            ring M j k b e p hgood.1.2.2 hp hj hk
        have hNextValue : V M' =
            n * SealedPhaseProgress b nextPhase :=
          tagged_d15_recovery_phase_value
            ring i j k b M' nextPhase hnext hterminal
        have hweak := (hprogress hnonready).1
        have hstrong := (hprogress hnonready).2
        constructor
        · calc
            V M' = n * SealedPhaseProgress b nextPhase :=
              hNextValue
            _ ≤ n * SealedPhaseProgress b p :=
              Nat.mul_le_mul_left n hweak
            _ = V M := hOld.symm
        · intro he
          have hh := Nat.mul_le_mul_left n (hstrong he)
          calc
            V M' + n =
                n * SealedPhaseProgress b nextPhase + n := by
              rw [hNextValue]
            _ = n * (SealedPhaseProgress b nextPhase + 1) :=
              (Nat.mul_succ n _).symm
            _ ≤ n * SealedPhaseProgress b p := hh
            _ = V M := hOld.symm
    exact tagged_q_drift_from_nominated_edge
      (V M)
      (fun e : Fin n => V (nativeE ring M e))
      (SealedPhaseEdge ring j p)
      (fun e => (hchild e).1)
      ((hchild (SealedPhaseEdge ring j p)).2 rfl)
  have hnotInitial :
      ¬ taggedD15RecoveryStop ring i j k b N := by
    intro hd
    rcases hd with hdel | hready
    · exact (tagged_d15_triple_not_deleted
        ring i j k a b N htriple) hdel
    · have heq := tagged_sealed_phase_unique
        ring N j b phase .ready hphase hready
      exact hnon heq
  have hInitValue : V N = n * SealedPhaseProgress b phase :=
    tagged_d15_recovery_phase_value
      ring i j k b N phase hphase hnotInitial
  have hc := tagged_q_restricted_cost_of_potential
    (nativeE ring) stop Inv V
    hclosed hdrift N ⟨htriple, hsealed⟩
  intro T
  calc
    costNumerator (nativeE ring)
        (taggedD15RecoveryStop ring i j k b) N T ≤
      n ^ T * V N := hc T
    _ = n ^ T * (n * SealedPhaseProgress b phase) := by
      rw [hInitValue]

/-- The source-relative Live(1) stage, produced by a real vulnerable
Ready-outgoing failure, has exactly the advertised recovery quota. -/
theorem tagged_d15_recovery_live_stage_cost {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hb : 2 ≤ b) (N : TripleNativeState n)
    (htriple : TaggedTriple ring i j k a b N)
    (hsealed : TaggedSealed ring i j a b N)
    (phase : SealedPhase n)
    (hphase : SealedPhaseHolds ring N j b phase)
    (hlive :
      SealedCloseProof.fromPhase phase =
        SealedCloseProof.Stage.bullet true 1) :
    ∀ T,
      costNumerator (nativeE ring)
        (taggedD15RecoveryStop ring i j k b) N T ≤
      n ^ T * (n * (2 * b - 2)) := by
  have hnonready : phase ≠ .ready := by
    intro he
    rw [he] at hlive
    cases hlive
  have hrank :
      SealedPhaseProgress b phase = 2 * b - 2 := by
    have hEq : SealedCloseProof.rank b
        (SealedCloseProof.fromPhase phase) =
          SealedPhaseProgress b phase := by
      cases phase <;> rfl
    rw [hlive] at hEq
    simp only [SealedCloseProof.rank] at hEq
    omega
  intro T
  have hh := tagged_d15_recovery_cost_of_phase
    hn ring i j k a b N htriple hsealed phase
    hphase hnonready T
  simpa only [hrank] using hh

end L3
/-! ## D.11 without a synthetic Q-reachability seed

The standing Q trial's proof used only three current-state physical
invariants: TaggedTriple, both Sealed sectors, and an unshielded B.
The following eight row proofs are the source-level same calculations
with that invariant explicitly supplied at the CURRENT full cut.
No new native state, scheduler, or weak future hypothesis is introduced.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false
attribute [local instance low] Classical.propDecidable

/-- The entire local D.11 domain is a current physical predicate,
not inductive future reachability. This is exactly the triple/seal/shield
conjunction used at Q-active cuts. -/
def TaggedD15QStructural {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n)
    (a b : Nat) (N : TripleNativeState n) : Prop :=
  TaggedTriple ring i j k a b N ∧
  TaggedSealed ring i j a b N ∧
  (N j).sh = false

theorem tagged_d15_surviving_child_stage_structural {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (N : TripleNativeState n) (raw : Fin n)
    (hs : TaggedD15QStructural ring i j k a b N)
    (phase : SealedPhase n)
    (hphase : SealedPhaseHolds ring N i a phase)
    (hnot : ¬ TaggedDeleted i j k
      (taggedQNext ring j b (by omega : 2 ≤ n)
        hports N raw)) :
    ∃ nextPhase : SealedPhase n,
      SealedPhaseHolds ring
        (taggedQNext ring j b (by omega : 2 ≤ n)
          hports N raw) i a nextPhase ∧
      SealedCloseProof.fromPhase nextPhase =
        sealedCloseTable ring i a
          (taggedQEffective ring j b (by omega : 2 ≤ n)
            hports N raw) phase := by
  let eff :=
    taggedQEffective ring j b (by omega : 2 ≤ n) hports N raw
  have htriple : TaggedTriple ring i j k a b N := hs.1
  have hi : (nativeE ring N eff i).l = true := by
    cases hx : (nativeE ring N eff i).l with
    | false => exact False.elim (hnot (Or.inl hx))
    | true => rfl
  have hj : (nativeE ring N eff j).l = true := by
    cases hx : (nativeE ring N eff j).l with
    | false => exact False.elim (hnot (Or.inr (Or.inl hx)))
    | true => rfl
  exact sealed_close_step_stage ring N i j a eff phase
    htriple.2.1 hphase hi hj

theorem tagged_d15_child_bellman_stage_structural {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (N : TripleNativeState n) (raw : Fin n)
    (hs : TaggedD15QStructural ring i j k a b N)
    (phase : SealedPhase n)
    (hphase : SealedPhaseHolds ring N i a phase)
    (hnot : ¬ TaggedDeleted i j k
      (taggedQNext ring j b (by omega : 2 ≤ n)
        hports N raw)) :
    taggedQBellman ring i j k a
      (taggedQNext ring j b (by omega : 2 ≤ n)
        hports N raw) =
      n * taggedCloseCredit a
        (sealedCloseTable ring i a
          (taggedQEffective ring j b (by omega : 2 ≤ n)
            hports N raw) phase) := by
  obtain ⟨nextPhase, hnext, hstage⟩ :=
    tagged_d15_surviving_child_stage_structural
      hnthree ring i j k a b hports
      N raw hs phase hphase hnot
  have hvalue := tagged_q_bellman_eq_phase
    ring (taggedQNext ring j b (by omega : 2 ≤ n)
      hports N raw) i j k a nextPhase hnot hnext
  calc
    taggedQBellman ring i j k a
        (taggedQNext ring j b (by omega : 2 ≤ n)
          hports N raw) =
      taggedAttackerBellman n a nextPhase := hvalue
    _ = n * taggedCloseCredit a
        (SealedCloseProof.fromPhase nextPhase) :=
      tagged_close_credit_from_phase n a nextPhase
    _ = n * taggedCloseCredit a
        (sealedCloseTable ring i a
          (taggedQEffective ring j b (by omega : 2 ≤ n)
            hports N raw) phase) := by
      rw [hstage]

theorem tagged_d15_terminal_live_boundary_structural {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (N : TripleNativeState n) (raw p : Fin n)
    (hs : TaggedD15QStructural ring i j k a b N)
    (hphase : SealedPhaseHolds ring N i a (.live p))
    (hlast : p.val + 1 = a)
    (heff : taggedQEffective ring j b (by omega : 2 ≤ n)
      hports N raw = SealedPhaseEdge ring i (.live p)) :
    TaggedDeleted i j k
      (taggedQNext ring j b (by omega : 2 ≤ n)
        hports N raw) := by
  have hinv := hs
  have hc : ConsecutiveNative ring N i j a :=
    hinv.1.2.1
  have hne : SealedPhaseEdge ring i (.live p) ≠ j :=
    sealed_close_nominated_ne_right
      ring N i j a (.live p) hc hphase
  have hnext : ring.rightNeighbor
      (SealedPhaseEdge ring i (.live p)) = j :=
    sealed_close_last_bullet_enters_right
      ring N i j a p hc hlast
  have hbullet :
      (N (SealedPhaseEdge ring i (.live p))).b =
        (2 : Fin 3) := hphase.1.2.1
  have hsignal :
      (N (SealedPhaseEdge ring i (.live p))).sg = false :=
    hphase.2.2 p (Nat.le_refl p.val)
  have hjl : (N j).l = true := hc.2.2.2.2.1
  have hkill := tagged_q_live_unshielded_native
    ring N (SealedPhaseEdge ring i (.live p)) j
      hne hnext hbullet hsignal hjl hinv.2.2
  have htarget :
      ((taggedQNext ring j b (by omega : 2 ≤ n)
        hports N raw) j).l = false := by
    unfold taggedQNext
    rw [heff]
    exact hkill
  exact Or.inr (Or.inl htarget)

theorem tagged_d15_nonready_child_bounds_structural {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (N : TripleNativeState n) (raw : Fin n)
    (hs : TaggedD15QStructural ring i j k a b N)
    (hnotold : ¬ TaggedDeleted i j k N)
    (phase : SealedPhase n)
    (hp : SealedPhaseHolds ring N i a phase)
    (hnr : phase ≠ .ready) :
    taggedQBellman ring i j k a
      (taggedQNext ring j b (by omega : 2 ≤ n)
        hports N raw) ≤
      taggedQBellman ring i j k a N ∧
    (raw = SealedPhaseEdge ring i phase →
      taggedQBellman ring i j k a
        (taggedQNext ring j b (by omega : 2 ≤ n)
          hports N raw) + n ≤
      taggedQBellman ring i j k a N) := by
  let eff := taggedQEffective ring j b
    (by omega : 2 ≤ n) hports N raw
  let r := SealedCloseProof.position ring i eff
  have inv := hs
  have hc : ConsecutiveNative ring N i j a := inv.1.2.1
  have ha : 1 ≤ a := hc.1
  have hbefore : taggedQBellman ring i j k a N =
      n * taggedCloseCredit a
        (SealedCloseProof.fromPhase phase) := by
    calc
      taggedQBellman ring i j k a N =
        taggedAttackerBellman n a phase :=
          tagged_q_bellman_eq_phase
            ring N i j k a phase hnotold hp
      _ = n * taggedCloseCredit a
          (SealedCloseProof.fromPhase phase) :=
        tagged_close_credit_from_phase n a phase
  by_cases hdel : TaggedDeleted i j k
      (taggedQNext ring j b (by omega : 2 ≤ n)
        hports N raw)
  · have hzero :=
      tagged_q_bellman_deleted_zero ring
        (taggedQNext ring j b (by omega : 2 ≤ n)
          hports N raw) i j k a hdel
    have hpositive : 1 ≤ taggedCloseCredit a
        (SealedCloseProof.fromPhase phase) :=
      tagged_close_nonready_credit_positive
        ring N i a phase ha hp hnr
    constructor
    · rw [hzero]
      exact Nat.zero_le _
    · intro _
      rw [hzero, Nat.zero_add, hbefore]
      calc
        n = n * 1 := (Nat.mul_one n).symm
        _ ≤ n * taggedCloseCredit a
            (SealedCloseProof.fromPhase phase) :=
          Nat.mul_le_mul_left n hpositive
  · have hchild := tagged_d15_child_bellman_stage_structural
      hnthree ring i j k a b hports N raw
      hs phase hp hdel
    by_cases hr : r.val < a
    · have htable : sealedCloseTable ring i a eff phase =
          SealedCloseProof.insideStage a
            (SealedCloseProof.fromPhase phase) r.val := by
        change (if r.val < a then
            SealedCloseProof.insideStage a
              (SealedCloseProof.fromPhase phase) r.val
           else if r.val + 1 = n then
             SealedCloseProof.incomingStage
               (SealedCloseProof.fromPhase phase)
           else SealedCloseProof.fromPhase phase) = _
        exact if_pos hr
      rcases tagged_close_nonready_inside_credit
          ring N i a r.val phase hp hnr with
        ⟨p, hphaseEq, hhit, hlast⟩ | ⟨hweak, hstrict⟩
      · have hphaseLive :
            SealedPhaseHolds ring N i a (.live p) := by
          simpa only [hphaseEq] using hp
        have heSite : eff = sealedSite ring i r.val :=
          sealed_close_edge_of_position ring i eff r.val rfl
        have heff :
            eff = SealedPhaseEdge ring i (.live p) := by
          calc
            eff = sealedSite ring i r.val := heSite
            _ = sealedSite ring i p.val := by rw [hhit]
            _ = SealedPhaseEdge ring i (.live p) := rfl
        have hkill := tagged_d15_terminal_live_boundary_structural
          hnthree ring i j k a b hports
            N raw p hs
            hphaseLive hlast heff
        exact False.elim (hdel hkill)
      · have hnom : SealedPhaseEdge ring i phase ≠ j :=
          sealed_close_nominated_ne_right
            ring N i j a phase hc hp
        have hnomR : raw = SealedPhaseEdge ring i phase →
            r.val = SealedCloseProof.nominated
              (SealedCloseProof.fromPhase phase) := by
          intro he
          have hE : eff = SealedPhaseEdge ring i phase := by
            dsimp [eff]
            rw [he]
            exact tagged_q_effective_of_other_raw
              ring j b (by omega : 2 ≤ n)
              hports N (SealedPhaseEdge ring i phase) hnom
          change (SealedCloseProof.position ring i eff).val =
            SealedCloseProof.nominated
              (SealedCloseProof.fromPhase phase)
          rw [hE]
          exact sealed_close_nominated_position
            ring N i j a phase hc hp
        constructor
        · calc
            taggedQBellman ring i j k a
                (taggedQNext ring j b
                  (by omega : 2 ≤ n) hports N raw) =
              n * taggedCloseCredit a
                (sealedCloseTable ring i a eff phase) := hchild
            _ = n * taggedCloseCredit a
                (SealedCloseProof.insideStage a
                  (SealedCloseProof.fromPhase phase) r.val) := by
              rw [htable]
            _ ≤ n * taggedCloseCredit a
                (SealedCloseProof.fromPhase phase) :=
              Nat.mul_le_mul_left n hweak
            _ = taggedQBellman ring i j k a N := hbefore.symm
        · intro he
          calc
            taggedQBellman ring i j k a
                (taggedQNext ring j b
                  (by omega : 2 ≤ n) hports N raw) + n =
              n * (taggedCloseCredit a
                (sealedCloseTable ring i a eff phase) + 1) := by
              rw [hchild, Nat.mul_add, Nat.mul_one]
            _ = n * (taggedCloseCredit a
                (SealedCloseProof.insideStage a
                  (SealedCloseProof.fromPhase phase) r.val) + 1) := by
              rw [htable]
            _ ≤ n * taggedCloseCredit a
                (SealedCloseProof.fromPhase phase) :=
              Nat.mul_le_mul_left n (hstrict (hnomR he))
            _ = taggedQBellman ring i j k a N := hbefore.symm
    · have htable : taggedCloseCredit a
          (sealedCloseTable ring i a eff phase) =
          taggedCloseCredit a
            (SealedCloseProof.fromPhase phase) := by
        change taggedCloseCredit a
          (if r.val < a then
            SealedCloseProof.insideStage a
              (SealedCloseProof.fromPhase phase) r.val
           else if r.val + 1 = n then
             SealedCloseProof.incomingStage
               (SealedCloseProof.fromPhase phase)
           else SealedCloseProof.fromPhase phase) =
          taggedCloseCredit a
            (SealedCloseProof.fromPhase phase)
        simp only [if_neg hr]
        by_cases hwrap : r.val + 1 = n
        · simpa only [if_pos hwrap] using
            tagged_close_nonready_incoming_credit a phase hnr
        · simp only [if_neg hwrap]
      constructor
      · apply Nat.le_of_eq
        calc
          taggedQBellman ring i j k a
              (taggedQNext ring j b
                (by omega : 2 ≤ n) hports N raw) =
            n * taggedCloseCredit a
              (sealedCloseTable ring i a eff phase) := hchild
          _ = n * taggedCloseCredit a
              (SealedCloseProof.fromPhase phase) := by rw [htable]
          _ = taggedQBellman ring i j k a N := hbefore.symm
      · intro he
        have hnom : SealedPhaseEdge ring i phase ≠ j :=
          sealed_close_nominated_ne_right
            ring N i j a phase hc hp
        have hE : eff = SealedPhaseEdge ring i phase := by
          dsimp [eff]
          rw [he]
          exact tagged_q_effective_of_other_raw
            ring j b (by omega : 2 ≤ n)
            hports N (SealedPhaseEdge ring i phase) hnom
        have hnomR :
            r.val = SealedCloseProof.nominated
                (SealedCloseProof.fromPhase phase) := by
          change (SealedCloseProof.position ring i eff).val =
            SealedCloseProof.nominated
              (SealedCloseProof.fromPhase phase)
          rw [hE]
          exact sealed_close_nominated_position
            ring N i j a phase hc hp
        have hnomlt := sealed_close_nominated_lt
          ring N i j a phase hc hp
        exact False.elim (hr (by omega))

theorem tagged_d15_ready_child_bounds_structural {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (N : TripleNativeState n) (raw : Fin n)
    (hs : TaggedD15QStructural ring i j k a b N)
    (hnotOld : ¬ TaggedDeleted i j k N)
    (hready : SealedCleanReady ring N i a) :
    taggedQBellman ring i j k a
      (taggedQNext ring j b (by omega : 2 ≤ n)
        hports N raw) ≤
      taggedQBellman ring i j k a N + n * (2 * a - 1) ∧
    (raw ≠ ring.leftNeighbor i →
      taggedQBellman ring i j k a
        (taggedQNext ring j b (by omega : 2 ≤ n)
          hports N raw) ≤
      taggedQBellman ring i j k a N) := by
  let eff := taggedQEffective ring j b
    (by omega : 2 ≤ n) hports N raw
  let r := SealedCloseProof.position ring i eff
  have hinv := hs
  have hc : ConsecutiveNative ring N i j a := hinv.1.2.1
  have ha : 1 ≤ a := hc.1
  have hij : i ≠ j := sealed_consecutive_endpoints_ne
    ring N i j a hc
  have hbefore :
      taggedQBellman ring i j k a N =
        n * taggedCloseCredit a .ready := by
    calc
      taggedQBellman ring i j k a N =
        taggedAttackerBellman n a .ready :=
          tagged_q_bellman_eq_phase
            ring N i j k a .ready hnotOld hready
      _ = n * taggedCloseCredit a .ready := rfl
  by_cases hdel : TaggedDeleted i j k
      (taggedQNext ring j b (by omega : 2 ≤ n)
        hports N raw)
  · have hzero := tagged_q_bellman_deleted_zero
      ring (taggedQNext ring j b (by omega : 2 ≤ n)
        hports N raw) i j k a hdel
    constructor
    · rw [hzero]
      exact Nat.zero_le _
    · intro _
      rw [hzero]
      exact Nat.zero_le _
  · have hchild := tagged_d15_child_bellman_stage_structural
      hnthree ring i j k a b hports
      N raw hs .ready hready hdel
    have htable :
        sealedCloseTable ring i a eff (.ready : SealedPhase n) =
          (if r.val < a then
            SealedCloseProof.insideStage a .ready r.val
           else if r.val + 1 = n then
            SealedCloseProof.incomingStage .ready
           else .ready) := rfl
    have hcreditUpper :=
      tagged_close_ready_stage_upper a n r.val ha
    have hupper : taggedCloseCredit a
        (sealedCloseTable ring i a eff (.ready : SealedPhase n)) ≤
        taggedCloseCredit a .ready + (2 * a - 1) := by
      rw [htable]
      exact hcreditUpper
    constructor
    · calc
        taggedQBellman ring i j k a
            (taggedQNext ring j b
              (by omega : 2 ≤ n) hports N raw) =
          n * taggedCloseCredit a
            (sealedCloseTable ring i a eff .ready) := hchild
        _ ≤ n * (taggedCloseCredit a .ready + (2 * a - 1)) :=
          Nat.mul_le_mul_left n hupper
        _ = taggedQBellman ring i j k a N + n * (2 * a - 1) := by
          rw [Nat.mul_add, hbefore]
    · intro hnotIncoming
      have hnotEff : eff ≠ ring.leftNeighbor i :=
        tagged_q_no_new_attacker_incoming
          ring i j b (by omega : 2 ≤ n)
          hports hij N raw hnotIncoming
      have hnotr : r.val + 1 ≠ n :=
        tagged_q_nonincoming_offset ring i eff hnotEff
      have hweak : taggedCloseCredit a
          (sealedCloseTable ring i a eff (.ready : SealedPhase n)) ≤
          taggedCloseCredit a .ready := by
        rw [htable]
        exact tagged_close_ready_stage_weak a n r.val ha hnotr
      calc
        taggedQBellman ring i j k a
            (taggedQNext ring j b
              (by omega : 2 ≤ n) hports N raw) =
          n * taggedCloseCredit a
            (sealedCloseTable ring i a eff .ready) := hchild
        _ ≤ n * taggedCloseCredit a .ready :=
          Nat.mul_le_mul_left n hweak
        _ = taggedQBellman ring i j k a N := hbefore.symm

theorem tagged_d15_ready_gap_one_deletes_structural {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (N : TripleNativeState n)
    (hs : TaggedD15QStructural ring i j k a b N)
    (hready : SealedCleanReady ring N i a)
    (hone : a = 1) :
    TaggedDeleted i j k
      (taggedQNext ring j b (by omega : 2 ≤ n)
        hports N i) := by
  have hinv := hs
  have hc : ConsecutiveNative ring N i j a := hinv.1.2.1
  have hij : i ≠ j := sealed_consecutive_endpoints_ne
    ring N i j a hc
  have heff : taggedQEffective ring j b (by omega : 2 ≤ n)
      hports N i = i :=
    tagged_q_effective_of_other_raw
      ring j b (by omega : 2 ≤ n) hports N i hij
  have hlast : (sealedZero ring).val + 1 = a := by
    dsimp [sealedZero]
    omega
  have hnext : ring.rightNeighbor i = j := by
    have hh := sealed_close_last_bullet_enters_right
      ring N i j a (sealedZero ring) hc hlast
    simpa [SealedPhaseEdge, sealedZero, sealedSite_zero] using hh
  have hi : (N i).l = true := hc.2.2.2.1
  have hj : (N j).l = true := hc.2.2.2.2.1
  have hsignal : (N i).sg = true := by
    simpa only [sealedAt_zero] using hready.1
  have hrow := tagged_q_ready_unshielded_collision_row
    (N i) (N j) hi hsignal hj hinv.2.2
  have hpair : nativeE ring N i j =
      (certLiteralEPair (N i) (N j)).2 := by
    simp [nativeE, hnext, Ne.symm hij]
  have hdeath : (nativeE ring N i j).l = false := by
    rw [hpair]
    exact hrow
  have htarget :
      ((taggedQNext ring j b (by omega : 2 ≤ n)
        hports N i) j).l = false := by
    unfold taggedQNext
    rw [heff]
    exact hdeath
  exact Or.inr (Or.inl htarget)

theorem tagged_d15_ready_outgoing_drop_structural {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (N : TripleNativeState n)
    (hs : TaggedD15QStructural ring i j k a b N)
    (hnotOld : ¬ TaggedDeleted i j k N)
    (hready : SealedCleanReady ring N i a) :
    taggedQBellman ring i j k a
      (taggedQNext ring j b (by omega : 2 ≤ n)
        hports N i) + n * (2 * a) ≤
      taggedQBellman ring i j k a N := by
  have hinv := hs
  have hc : ConsecutiveNative ring N i j a := hinv.1.2.1
  have ha : 1 ≤ a := hc.1
  have hij : i ≠ j := sealed_consecutive_endpoints_ne
    ring N i j a hc
  have heff : taggedQEffective ring j b (by omega : 2 ≤ n)
      hports N i = i :=
    tagged_q_effective_of_other_raw
      ring j b (by omega : 2 ≤ n) hports N i hij
  have hbefore : taggedQBellman ring i j k a N =
      n * (3 * a - 1) := by
    exact tagged_q_bellman_eq_phase
      ring N i j k a .ready hnotOld hready
  by_cases hone : a = 1
  · have hdel := tagged_d15_ready_gap_one_deletes_structural
      hnthree ring i j k a b hports
        N hs hready hone
    have hzero := tagged_q_bellman_deleted_zero
      ring (taggedQNext ring j b (by omega : 2 ≤ n)
        hports N i) i j k a hdel
    rw [hzero, Nat.zero_add, hbefore]
    exact Nat.mul_le_mul_left n (by omega)
  · have hrzero :
        (SealedCloseProof.position ring i i).val = 0 := by
      have hh := sealed_close_nominated_position
        ring N i j a (.ready : SealedPhase n) hc hready
      simpa [SealedPhaseEdge, SealedCloseProof.fromPhase,
        SealedCloseProof.nominated] using hh
    have htable :
        sealedCloseTable ring i a i (.ready : SealedPhase n) =
          .bullet true 1 := by
      have hapos : 0 < a := by omega
      simp [sealedCloseTable, hrzero, hapos, hone,
        SealedCloseProof.fromPhase,
        SealedCloseProof.insideStage]
    by_cases hdel : TaggedDeleted i j k
        (taggedQNext ring j b (by omega : 2 ≤ n) hports N i)
    · have hzero := tagged_q_bellman_deleted_zero
        ring (taggedQNext ring j b (by omega : 2 ≤ n)
          hports N i) i j k a hdel
      rw [hzero, Nat.zero_add, hbefore]
      exact Nat.mul_le_mul_left n (by omega)
    · have hchild := tagged_d15_child_bellman_stage_structural
        hnthree ring i j k a b hports
        N i hs .ready hready hdel
      have hvalue :
          taggedQBellman ring i j k a
            (taggedQNext ring j b (by omega : 2 ≤ n)
              hports N i) = n * (a - 1) := by
        simpa only [heff, htable, taggedCloseCredit] using hchild
      calc
        taggedQBellman ring i j k a
            (taggedQNext ring j b (by omega : 2 ≤ n)
              hports N i) + n * (2 * a) =
          n * (a - 1) + n * (2 * a) := by rw [hvalue]
        _ = n * ((a - 1) + 2 * a) := by rw [Nat.mul_add]
        _ ≤ n * (3 * a - 1) :=
          Nat.mul_le_mul_left n (by omega)
        _ = taggedQBellman ring i j k a N := hbefore.symm

theorem tagged_d15_reachable_drift_structural {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (N : TripleNativeState n)
    (hs : TaggedD15QStructural ring i j k a b N)
    (hnot : ¬ TaggedDeleted i j k N) :
    n + (List.ofFn (fun e : Fin n =>
      taggedQBellman ring i j k a
        (taggedQNext ring j b (by omega : 2 ≤ n)
          hports N e))).sum ≤
      n * taggedQBellman ring i j k a N := by
  let V := taggedQBellman ring i j k a
  let Q := taggedQNext ring j b (by omega : 2 ≤ n) hports
  let child : Fin n → Nat := fun e => V (Q N e)
  have hinv := hs
  let phase := taggedQAttackerPhase ring i a N
  have hp : SealedPhaseHolds ring N i a phase :=
    tagged_q_attacker_phase_valid ring i a N hinv.2.1.1
  by_cases hready : phase = .ready
  · have hphys : SealedCleanReady ring N i a := by
      show SealedPhaseHolds ring N i a .ready
      exact hready ▸ hp
    have ha : 1 ≤ a := hinv.1.2.1.1
    have hbefore : V N = n * (3 * a - 1) := by
      exact tagged_q_bellman_eq_phase
        ring N i j k a .ready hnot hphys
    have hOut : child i + n * (2 * a) ≤ V N :=
      tagged_d15_ready_outgoing_drop_structural hnthree ring
        i j k a b hports N
        hs hnot hphys
    have hIn : child (ring.leftNeighbor i) ≤
        V N + n * (2 * a - 1) :=
      (tagged_d15_ready_child_bounds_structural hnthree ring
        i j k a b hports N (ring.leftNeighbor i)
        hs hnot hphys).1
    have hOutCredit : child i ≤ n * (a - 1) := by
      have heq : n * (a - 1) + n * (2 * a) =
          n * (3 * a - 1) := by
        have harg : (a - 1) + 2 * a = 3 * a - 1 := by omega
        calc
          n * (a - 1) + n * (2 * a) =
              n * ((a - 1) + 2 * a) := by rw [Nat.mul_add]
          _ = n * (3 * a - 1) := by rw [harg]
      rw [hbefore] at hOut
      omega
    have hInCredit : child (ring.leftNeighbor i) ≤
        n * ((2 * a - 1) + (3 * a - 1)) := by
      have heq :
          n * (3 * a - 1) + n * (2 * a - 1) =
            n * ((2 * a - 1) + (3 * a - 1)) := by
        rw [Nat.mul_add]
        omega
      rw [hbefore] at hIn
      omega
    have hpair :
        n + child i + child (ring.leftNeighbor i) ≤
          2 * V N := by
      have hbalance := tagged_ready_two_edge_balance_scaled n a ha
      rw [hbefore]
      omega
    have hrest : ∀ e, e ≠ i →
        e ≠ ring.leftNeighbor i → child e ≤ V N := by
      intro e heOut heIn
      exact (tagged_d15_ready_child_bounds_structural hnthree ring
        i j k a b hports N e
        hs hnot hphys).2 heIn
    have hne : i ≠ ring.leftNeighbor i :=
      tagged_q_incident_edges_distinct
        (by omega : 2 ≤ n) ring i
    exact tagged_q_ready_sum_of_two_edge_bounds
      (V N) child i (ring.leftNeighbor i)
      hne hpair hrest
  · have hweak : ∀ e : Fin n, child e ≤ V N := by
      intro e
      exact (tagged_d15_nonready_child_bounds_structural
        hnthree ring i j k a b hports N e
        hs hnot phase hp hready).1
    have hstrict :
        child (SealedPhaseEdge ring i phase) + n ≤ V N :=
      (tagged_d15_nonready_child_bounds_structural
        hnthree ring i j k a b hports
        N (SealedPhaseEdge ring i phase)
        hs hnot phase hp hready).2 rfl
    exact tagged_q_nonready_sum_of_edge_bounds
      (V N) child (SealedPhaseEdge ring i phase)
      hweak hstrict


/-- Structural D.11 needs no Q-reachability constructor at all.
Every surviving Q letter transports the same physical triple/sealed
state; Q prevents a signaling unshielded B from launching. -/
theorem tagged_d15_q_structural_step {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (N : TripleNativeState n)
    (hs : TaggedD15QStructural ring i j k a b N)
    (e : Fin n) :
    TaggedDeleted i j k
      (taggedQNext ring j b (by omega : 2 ≤ n) hports N e) ∨
    TaggedD15QStructural ring i j k a b
      (taggedQNext ring j b (by omega : 2 ≤ n) hports N e) := by
  let M := taggedQNext ring j b (by omega : 2 ≤ n) hports N e
  by_cases hdel : TaggedDeleted i j k M
  · exact Or.inl hdel
  · have htr : TaggedTriple ring i j k a b M :=
      tagged_triple_step_of_survival hn ring i j k a b
        N (taggedQEffective ring j b (by omega : 2 ≤ n)
          hports N e) hs.1 hdel
    have hseal : TaggedSealed ring i j a b M :=
      tagged_sealed_step_of_survival ring i j k a b
        N (taggedQEffective ring j b (by omega : 2 ≤ n)
          hports N e) hs.1 hs.2.1 hdel
    have hsh : (M j).sh = false :=
      tagged_q_unshielded_next ring j b (by omega : 2 ≤ n)
        hports N e hs.2.1.2 hs.2.2
    exact Or.inr ⟨htr, hseal, hsh⟩

/-- The new pointwise D.11 drift has no seed or future-reachability
parameter. The eight physical source proofs above pay all Q edges. -/
theorem tagged_d15_q_structural_bellman_drift {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (N : TripleNativeState n)
    (hs : TaggedD15QStructural ring i j k a b N) :
    n + (List.ofFn (fun e : Fin n =>
      taggedQBellman ring i j k a
        (taggedQNext ring j b (by omega : 2 ≤ n)
          hports N e))).sum ≤
    n * taggedQBellman ring i j k a N := by
  exact tagged_d15_reachable_drift_structural
    hn ring i j k a b hports N hs
    (tagged_d15_triple_not_deleted ring i j k a b N hs.1)

/-- The killed attacker potential has its uniform 5a-2 cap on any
structural Q state. -/
theorem tagged_d15_q_structural_cap {n : Nat}
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (hs : TaggedD15QStructural ring i j k a b N) :
    taggedQBellman ring i j k a N ≤ n * (5 * a - 2) := by
  have hnot := tagged_d15_triple_not_deleted
    ring i j k a b N hs.1
  have hp := tagged_q_attacker_phase_valid
    ring i a N hs.2.1.1
  have hh := tagged_attacker_bellman_cap
    ring N i a hs.1.2.1.1
    (taggedQAttackerPhase ring i a N) hp
  unfold taggedQBellman
  rw [if_neg hnot]
  exact hh

/-- The complete Q trial is now bounded from EVERY structural
full cut, without declaring the cut to be an inductively reached
descendant of an earlier clean dummy. -/
theorem tagged_d15_q_structural_cost {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (N : TripleNativeState n)
    (hs : TaggedD15QStructural ring i j k a b N) :
    ∀ T,
      costNumerator
        (taggedQNext ring j b (by omega : 2 ≤ n) hports)
        (TaggedDeleted i j k) N T ≤
      n ^ T * taggedQBellman ring i j k a N := by
  have hclosed :
      ∀ M : TripleNativeState n,
        TaggedD15QStructural ring i j k a b M →
        ∀ e, ¬ TaggedDeleted i j k
          (taggedQNext ring j b (by omega : 2 ≤ n)
            hports M e) →
          TaggedD15QStructural ring i j k a b
            (taggedQNext ring j b (by omega : 2 ≤ n)
              hports M e) := by
    intro M hg e hnot
    rcases tagged_d15_q_structural_step
        hn ring i j k a b hports M hg e with hdel | hgood
    · exact False.elim (hnot hdel)
    · exact hgood
  have hdrift :
      ∀ M : TripleNativeState n,
        TaggedD15QStructural ring i j k a b M →
        ¬ TaggedDeleted i j k M →
        n + (List.ofFn (fun e : Fin n =>
          taggedQBellman ring i j k a
            (taggedQNext ring j b (by omega : 2 ≤ n)
              hports M e))).sum ≤
          n * taggedQBellman ring i j k a M := by
    intro M hg _
    exact tagged_d15_q_structural_bellman_drift
      hn ring i j k a b hports M hg
  exact tagged_q_restricted_cost_of_potential
    (taggedQNext ring j b (by omega : 2 ≤ n) hports)
    (TaggedDeleted i j k)
    (TaggedD15QStructural ring i j k a b)
    (taggedQBellman ring i j k a)
    hclosed hdrift N hs

/-- Raw and controlled Q execute exactly the same nativeE edge
unless the raw letter is B's outgoing edge at a B-Ready cut. -/
theorem tagged_d15_raw_q_same_other_edge {n : Nat}
    (ring : DirectedRing n) (j : Fin n) (b : Nat)
    (hn : 2 ≤ n) (hports : ring.leftNeighbor j ≠ j)
    (N : TripleNativeState n) (e : Fin n)
    (hne : e ≠ j) :
    taggedQNext ring j b hn hports N e =
      nativeE ring N e := by
  unfold taggedQNext
  rw [tagged_q_effective_of_other_raw
    ring j b hn hports N e hne]

theorem tagged_d15_raw_q_same_nonready {n : Nat}
    (ring : DirectedRing n) (j : Fin n) (b : Nat)
    (hn : 2 ≤ n) (hports : ring.leftNeighbor j ≠ j)
    (N : TripleNativeState n)
    (hnot : ¬ SealedCleanReady ring N j b) :
    taggedQNext ring j b hn hports N j =
      nativeE ring N j := by
  classical
  unfold taggedQNext taggedQEffective
  simp [taggedRedirection,
    ControlledSchedulerMass.Redirection.effective, hnot]

theorem tagged_d15_raw_q_ready_redirect {n : Nat}
    (ring : DirectedRing n) (j : Fin n) (b : Nat)
    (hn : 2 ≤ n) (hports : ring.leftNeighbor j ≠ j)
    (N : TripleNativeState n)
    (hready : SealedCleanReady ring N j b) :
    taggedQNext ring j b hn hports N j =
      nativeE ring N (ring.leftNeighbor j) := by
  unfold taggedQNext taggedQEffective
  rw [tagged_redirection_ready_right
    ring j b hn hports N hready]

/-- A raw vulnerable continuation with zero B shield remains unshielded
on EVERY physical edge except its own ready-time outgoing failure.
No assertion about future Q encounters is needed. -/
theorem tagged_d15_raw_vulnerable_shield_step {n : Nat}
    (ring : DirectedRing n) (j : Fin n) (b : Nat)
    (N : TripleNativeState n) (e : Fin n)
    (hsealed : Sealed ring N j b)
    (hsh : (N j).sh = false)
    (hnotfail : ¬ (SealedCleanReady ring N j b ∧ e = j)) :
    (nativeE ring N e j).sh = false := by
  by_cases hsig : (N j).sg = true
  · have hready := tagged_q_sealed_signaling_ready
      ring N j b hsealed hsig
    have he : e ≠ j := by
      intro hj
      exact hnotfail ⟨hready, hj⟩
    exact tagged_q_native_unshielded_of_avoided_launch
      ring N j e hsh (Or.inr he)
  · have hz : (N j).sg = false := by
      cases hx : (N j).sg with
      | false => rfl
      | true => exact False.elim (hsig hx)
    exact tagged_q_native_unshielded_of_avoided_launch
      ring N j e hsh (Or.inl hz)

/-- Local good predicate, independent of a Q reachability tree.
Ready-wait must not have already reached the clean dummy; vulnerability
requires the actual B shield to be zero. Recovery has its phase debt in
the already kernel-checked state and requires no shield premise. -/
theorem tagged_d15_attempt_good_start {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (seed : TaggedD15AttemptSeed ring i j k a b) :
    TaggedD15AttemptGood ring i j k a b
      (tagged_d15_attempt_start ring i j k a b seed) := by
  have hnodummy : ¬ TaggedCleanDummy ring i j a b seed.N := by
    intro hclean
    have heq := tagged_sealed_phase_unique ring seed.N j b
      (.ready : SealedPhase n) (.dummy (sealedZero ring))
      seed.prepared.2 hclean.2
    cases heq
  constructor
  · intro _
    exact hnodummy
  · intro he
    change TaggedD15AttemptMode.readyWait =
      TaggedD15AttemptMode.vulnerable at he
    cases he

theorem tagged_d15_structural_of_vulnerable_good {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (z : TaggedD15AttemptState ring i j k a b)
    (hg : TaggedD15AttemptGood ring i j k a b z)
    (hv : z.mode = .vulnerable) :
    TaggedD15QStructural ring i j k a b z.N :=
  ⟨z.triple, ⟨z.attackerSealed,
      ⟨z.targetPhase, z.targetHolds⟩⟩, hg.2 hv⟩


/-- The raw vulnerable process has exactly the same structural
invariant on a surviving NON-failure edge, including a physical
incoming/outgoing merge in either sector. -/
theorem tagged_d15_raw_vulnerable_structural_step {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n) (e : Fin n)
    (hs : TaggedD15QStructural ring i j k a b N)
    (hnotdel : ¬ TaggedDeleted i j k (nativeE ring N e))
    (hnotfail : ¬ (SealedCleanReady ring N j b ∧ e = j)) :
    TaggedD15QStructural ring i j k a b (nativeE ring N e) := by
  have htriple := tagged_triple_step_of_survival
    hn ring i j k a b N e hs.1 hnotdel
  have hsealed := tagged_sealed_step_of_survival
    ring i j k a b N e hs.1 hs.2.1 hnotdel
  have hsh := tagged_d15_raw_vulnerable_shield_step
    ring j b N e hs.2.1.2 hs.2.2 hnotfail
  exact ⟨htriple, hsealed, hsh⟩

/-- The entire vulnerable-stage Bellman comparison reduces to an
ordinary pointwise comparison of physical attempt-child values
against Q's attacker credit plus the recovery budget. No fake
expectation, future-conditioned scheduler, or reset enters. -/
theorem tagged_d15_vulnerable_bellman_of_pointwise {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hports : ring.leftNeighbor j ≠ j)
    (N : TripleNativeState n)
    (hs : TaggedD15QStructural ring i j k a b N)
    (R : Nat) (child : Fin n → Nat)
    (hchild : ∀ e,
      child e ≤ taggedQBellman ring i j k a
        (taggedQNext ring j b (by omega : 2 ≤ n) hports N e)
          + R) :
    n + (List.ofFn child).sum ≤
      n * (taggedQBellman ring i j k a N + R) := by
  have hsum :
      (List.ofFn child).sum ≤
        (List.ofFn (fun e : Fin n =>
          taggedQBellman ring i j k a
            (taggedQNext ring j b (by omega : 2 ≤ n)
              hports N e) + R)).sum :=
    ofFn_sum_le _ _ hchild
  have hsplit :
      (List.ofFn (fun e : Fin n =>
        taggedQBellman ring i j k a
          (taggedQNext ring j b (by omega : 2 ≤ n)
            hports N e) + R)).sum =
        (List.ofFn (fun e : Fin n =>
          taggedQBellman ring i j k a
            (taggedQNext ring j b (by omega : 2 ≤ n)
              hports N e))).sum + n * R := by
    rw [ofFn_sum_add, ofFn_sum_const]
  have hQ := tagged_d15_q_structural_bellman_drift
    hn ring i j k a b hports N hs
  calc
    n + (List.ofFn child).sum ≤
        n + (List.ofFn (fun e : Fin n =>
          taggedQBellman ring i j k a
            (taggedQNext ring j b (by omega : 2 ≤ n)
              hports N e) + R)).sum :=
      Nat.add_le_add_left hsum n
    _ = (n + (List.ofFn (fun e : Fin n =>
          taggedQBellman ring i j k a
            (taggedQNext ring j b (by omega : 2 ≤ n)
              hports N e))).sum) + n * R := by
      rw [hsplit]
      omega
    _ ≤ n * taggedQBellman ring i j k a N + n * R :=
      Nat.add_le_add_right hQ (n * R)
    _ = n * (taggedQBellman ring i j k a N + R) := by
      rw [Nat.mul_add]



/-! ## Source-local stopped Ready and recovery drifts

These two lemmas extract already proved *one-step* inequalities from
the stopped-clock certificates; unlike finite-horizon cost bounds,
they are suitable for the AttemptCostSuperSolutionOn one-letter rule.
-/

/-- Current-state Ready-wait drift with no initial deletion/dummy
terminal. There is no future phase or scheduler hypothesis. -/
theorem tagged_d15_ready_local_drift {n : Nat}
    (hnthree : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat) (hb : 2 ≤ b)
    (N : TripleNativeState n)
    (hg : TaggedTriple ring i j k a b N ∧
      TaggedSealed ring i j a b N)
    (hnot : ¬ taggedD15ReadyStop ring i j k a b N) :
    n + (List.ofFn (fun e : Fin n =>
      taggedD15ReadyPotential ring i j k a b
        (nativeE ring N e))).sum ≤
    n * taggedD15ReadyPotential ring i j k a b N := by
  let target := taggedD15ReadyStop ring i j k a b
  let potential := taggedD15ReadyPotential ring i j k a b
  obtain ⟨phase, hp⟩ := hg.2.2
  have hOld :
      potential N =
        n * ((2 * b - 1) +
          SealedCloseProof.rank b
            (SealedCloseProof.fromPhase phase)) :=
    tagged_d15_ready_phase_value ring i j k a b N phase hp hnot
  by_cases hready : phase = .ready
  · subst phase
    have hports : j ≠ ring.leftNeighbor j :=
      tagged_q_incident_edges_distinct
        (by omega : 2 ≤ n) ring j
    have hprepM : TaggedPrepared ring i j a b N :=
      ⟨hg.2.1, hp⟩
    have hcap :
        ∀ e : Fin n,
          potential (nativeE ring N e) ≤
            n * ((2 * b - 1) +
              SealedCloseProof.rank b
                (sealedCloseTable ring j b e
                  (.ready : SealedPhase n))) := by
      intro e
      exact tagged_d15_ready_child_rank
        ring i j k a b N e hg.1 .ready hp
    have hout :
        potential (nativeE ring N j) ≤ n * (4 * b - 3) := by
      have htable := tagged_d15_ready_out_table
        ring N j k b hb hg.1.2.2 hp
      have hh := hcap j
      rw [htable] at hh
      have hcoef :
          (2 * b - 1) +
            SealedCloseProof.rank b (.bullet true 1) =
            4 * b - 3 := by
        simp only [SealedCloseProof.rank]
        omega
      simpa only [hcoef] using hh
    have hin :
        potential (nativeE ring N (ring.leftNeighbor j)) = 0 := by
      have htarget :
          target (nativeE ring N (ring.leftNeighbor j)) :=
        tagged_d15_prepared_incoming hnthree
          ring i j k a b N hg.1 hprepM
      change
        (if taggedD15ReadyStop ring i j k a b
              (nativeE ring N (ring.leftNeighbor j))
         then 0
         else n * ((2 * b - 1) +
           SealedPhaseProgress b
             (taggedQAttackerPhase ring j b
               (nativeE ring N (ring.leftNeighbor j))))) = 0
      rw [if_pos htarget]
    have hrest :
        ∀ e : Fin n, e ≠ j →
          e ≠ ring.leftNeighbor j →
            potential (nativeE ring N e) ≤
              n * (2 * b - 1) := by
      intro e he hi
      have htable :=
        tagged_d15_ready_quiet_table ring j e b he hi
      have hh := hcap e
      rw [htable] at hh
      simpa only [SealedCloseProof.rank, Nat.add_zero] using hh
    have hreadyValue : potential N = n * (2 * b - 1) := by
      simpa only [SealedCloseProof.fromPhase,
        SealedCloseProof.rank, Nat.add_zero] using hOld
    have hrow := tagged_d15_ready_two_port b hb
      (fun e : Fin n => potential (nativeE ring N e))
      j (ring.leftNeighbor j) hports hout hin hrest
    show n + (List.ofFn (fun e : Fin n =>
        potential (nativeE ring N e))).sum ≤ n * potential N
    rw [hreadyValue]
    exact hrow
  · let port := SealedPhaseEdge ring j phase
    have hcap :
        ∀ e : Fin n,
          potential (nativeE ring N e) ≤
            n * ((2 * b - 1) +
              SealedCloseProof.rank b
                (sealedCloseTable ring j b e phase)) := by
      intro e
      exact tagged_d15_ready_child_rank
        ring i j k a b N e hg.1 phase hp
    have htable (e : Fin n) :=
      tagged_target_nonready_table_exact ring N j k b
        hb phase e hg.1.2.2 hp hready
    have hweak :
        ∀ e : Fin n,
          potential (nativeE ring N e) ≤ potential N := by
      intro e
      have hh := htable e
      have hrank :
          SealedCloseProof.rank b
              (sealedCloseTable ring j b e phase) ≤
            SealedCloseProof.rank b
              (SealedCloseProof.fromPhase phase) := by
        omega
      calc
        potential (nativeE ring N e) ≤
            n * ((2 * b - 1) +
              SealedCloseProof.rank b
                (sealedCloseTable ring j b e phase)) := hcap e
        _ ≤ n * ((2 * b - 1) +
              SealedCloseProof.rank b
                (SealedCloseProof.fromPhase phase)) :=
          Nat.mul_le_mul_left n
            (Nat.add_le_add_left hrank (2 * b - 1))
        _ = potential N := hOld.symm
    have hnom := htable port
    have hrank :
        SealedCloseProof.rank b
          (sealedCloseTable ring j b port phase) + 1 =
        SealedCloseProof.rank b
          (SealedCloseProof.fromPhase phase) := by
      simpa only [port, ↓reduceIte] using hnom
    have hcoef :
        ((2 * b - 1) + SealedCloseProof.rank b
          (sealedCloseTable ring j b port phase)) + 1 =
        (2 * b - 1) + SealedCloseProof.rank b
          (SealedCloseProof.fromPhase phase) := by
      omega
    have hstrict :
        potential (nativeE ring N port) + n ≤
          potential N := by
      calc
        potential (nativeE ring N port) + n ≤
            n * ((2 * b - 1) +
              SealedCloseProof.rank b
                (sealedCloseTable ring j b port phase)) + n :=
          Nat.add_le_add_right (hcap port) n
        _ = n * (((2 * b - 1) +
              SealedCloseProof.rank b
                (sealedCloseTable ring j b port phase)) + 1) :=
          (Nat.mul_succ _ _).symm
        _ = n * ((2 * b - 1) +
              SealedCloseProof.rank b
                (SealedCloseProof.fromPhase phase)) := by
          rw [hcoef]
        _ = potential N := hOld.symm
    exact tagged_q_drift_from_nominated_edge
      (potential N)
      (fun e : Fin n => potential (nativeE ring N e))
      port hweak hstrict

/-- Current-state non-Ready recovery drift until actual Ready or
deletion. Every physical edge is charged once. -/
theorem tagged_d15_recovery_local_drift {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (hgood : TaggedTriple ring i j k a b N ∧
      TaggedSealed ring i j a b N)
    (hnot : ¬ taggedD15RecoveryStop ring i j k b N) :
    n + (List.ofFn (fun e : Fin n =>
      taggedD15RecoveryPotential ring i j k b
        (nativeE ring N e))).sum ≤
    n * taggedD15RecoveryPotential ring i j k b N := by
  let stop := taggedD15RecoveryStop ring i j k b
  let V := taggedD15RecoveryPotential ring i j k b
  obtain ⟨p, hp⟩ := hgood.2.2
  have hnonready : p ≠ .ready := by
    intro he
    apply hnot
    exact Or.inr (by
      change SealedCleanReady ring N j b
      subst he
      exact hp)
  have hOld : V N = n * SealedPhaseProgress b p :=
    tagged_d15_recovery_phase_value
      ring i j k b N p hp hnot
  have hpositive : 1 ≤ SealedPhaseProgress b p :=
    tagged_d15_recovery_rank_positive ring N j b p hp hnonready
  have hchild (e : Fin n) :
      V (nativeE ring N e) ≤ V N ∧
        (e = SealedPhaseEdge ring j p →
          V (nativeE ring N e) + n ≤ V N) := by
    let N' := nativeE ring N e
    by_cases hterminal : stop N'
    · have hzero : V N' = 0 := by
        unfold V taggedD15RecoveryPotential
        rw [if_pos hterminal]
      have hscaled : n ≤ n * SealedPhaseProgress b p := by
        have hh := Nat.mul_le_mul_left n hpositive
        simpa only [Nat.mul_one] using hh
      constructor
      · rw [hzero]
        exact Nat.zero_le _
      · intro _
        rw [hzero, Nat.zero_add, hOld]
        exact hscaled
    · have hnodelete : ¬ TaggedDeleted i j k N' := by
        intro hd
        exact hterminal (Or.inl hd)
      have hj : (N' j).l = true := by
        cases hx : (N' j).l with
        | false =>
            exact False.elim (hnodelete (Or.inr (Or.inl hx)))
        | true => rfl
      have hk : (N' k).l = true := by
        cases hx : (N' k).l with
        | false =>
            exact False.elim (hnodelete (Or.inr (Or.inr hx)))
        | true => rfl
      obtain ⟨nextPhase, hnext, hprogress⟩ :=
        sealed_close_step_with_progress
          ring N j k b e p hgood.1.2.2 hp hj hk
      have hNextValue : V N' =
          n * SealedPhaseProgress b nextPhase :=
        tagged_d15_recovery_phase_value
          ring i j k b N' nextPhase hnext hterminal
      have hweak := (hprogress hnonready).1
      have hstrong := (hprogress hnonready).2
      constructor
      · calc
          V N' = n * SealedPhaseProgress b nextPhase :=
            hNextValue
          _ ≤ n * SealedPhaseProgress b p :=
            Nat.mul_le_mul_left n hweak
          _ = V N := hOld.symm
      · intro he
        have hh := Nat.mul_le_mul_left n (hstrong he)
        calc
          V N' + n =
              n * SealedPhaseProgress b nextPhase + n := by
            rw [hNextValue]
          _ = n * (SealedPhaseProgress b nextPhase + 1) :=
            (Nat.mul_succ n _).symm
          _ ≤ n * SealedPhaseProgress b p := hh
          _ = V N := hOld.symm
  exact tagged_q_drift_from_nominated_edge
    (V N)
    (fun e : Fin n => V (nativeE ring N e))
    (SealedPhaseEdge ring j p)
    (fun e => (hchild e).1)
    ((hchild (SealedPhaseEdge ring j p)).2 rfl)

/-- The Ready-wait stage's finite Bellman comparison needs only
pointwise bound of each actual kernel child by its physical killed
B-stage value plus the reserved A-vulnerable/recovery continuation.
The paper Ready two-port calculation is already in
tagged_d15_ready_local_drift. -/
theorem tagged_d15_ready_bellman_of_pointwise {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat) (hb : 2 ≤ b)
    (N : TripleNativeState n)
    (hg : TaggedTriple ring i j k a b N ∧
      TaggedSealed ring i j a b N)
    (hnot : ¬ taggedD15ReadyStop ring i j k a b N)
    (R : Nat) (child : Fin n → Nat)
    (hchild : ∀ e,
      child e ≤ taggedD15ReadyPotential ring i j k a b
        (nativeE ring N e) + R) :
    n + (List.ofFn child).sum ≤
      n * (taggedD15ReadyPotential ring i j k a b N + R) := by
  have hsum : (List.ofFn child).sum ≤
      (List.ofFn (fun e : Fin n =>
        taggedD15ReadyPotential ring i j k a b
          (nativeE ring N e) + R)).sum :=
    ofFn_sum_le _ _ hchild
  have hsplit :
      (List.ofFn (fun e : Fin n =>
        taggedD15ReadyPotential ring i j k a b
          (nativeE ring N e) + R)).sum =
        (List.ofFn (fun e : Fin n =>
          taggedD15ReadyPotential ring i j k a b
            (nativeE ring N e))).sum + n * R := by
    rw [ofFn_sum_add, ofFn_sum_const]
  have hready := tagged_d15_ready_local_drift
    hn ring i j k a b hb N hg hnot
  calc
    n + (List.ofFn child).sum ≤
        n + (List.ofFn (fun e : Fin n =>
          taggedD15ReadyPotential ring i j k a b
            (nativeE ring N e) + R)).sum :=
      Nat.add_le_add_left hsum n
    _ = (n + (List.ofFn (fun e : Fin n =>
          taggedD15ReadyPotential ring i j k a b
            (nativeE ring N e))).sum) + n * R := by
      rw [hsplit]
      omega
    _ ≤ n * taggedD15ReadyPotential ring i j k a b N + n * R :=
      Nat.add_le_add_right hready (n * R)
    _ = n * (taggedD15ReadyPotential ring i j k a b N + R) := by
      rw [Nat.mul_add]



/-! ## D.15 exact whole-attempt candidate potential

This assigns the paper's three concrete stage debts to the actual
history carrying state, with no synthetic native state or status bit.
Only the LOCAL kernel-step inequalities and good-closure remain to
complete its supersolution.
-/

/-- Potential of an attempt node, zero at both terminal kinds. Same
definition as PPL.Convergence.LDLocal.attemptNodePotential, restated
here because that module's import chain is not in this build. -/
def taggedAttemptNodePotential
    {A S : Type} (P : A → Nat) :
    AttemptNode A S → Nat
  | .active a => P a
  | .success => 0
  | .retry _ => 0

noncomputable def tagged_d15_attempt_potential {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (z : TaggedD15AttemptState ring i j k a b) : Nat :=
  match z.mode with
  | .readyWait =>
      taggedD15ReadyPotential ring i j k a b z.N +
        n * (5 * a - 2) + n * (2 * b - 2)
  | .vulnerable =>
      taggedQBellman ring i j k a z.N + n * (2 * b - 2)
  | .recovery => taggedD15RecoveryPotential ring i j k b z.N

/-- The initial Ready physical cut has precisely the D.15 paper
attempt budget, not an inflated ad-hoc stage constant. -/
theorem tagged_d15_attempt_potential_start {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (ha : 1 ≤ a) (hb : 2 ≤ b)
    (seed : TaggedD15AttemptSeed ring i j k a b) :
    tagged_d15_attempt_potential ring i j k a b
      (tagged_d15_attempt_start ring i j k a b seed) =
        n * (5 * a + 4 * b - 5) := by
  have hnoDelete : ¬ TaggedDeleted i j k seed.N :=
    tagged_d15_triple_not_deleted
      ring i j k a b seed.N seed.triple
  have hnoDummy : ¬ TaggedCleanDummy ring i j a b seed.N := by
    intro hclean
    have hphase := tagged_sealed_phase_unique ring seed.N j b
      (.ready : SealedPhase n) (.dummy (sealedZero ring))
      seed.prepared.2 hclean.2
    cases hphase
  have hnot : ¬ taggedD15ReadyStop ring i j k a b seed.N := by
    intro ht
    rcases ht with hd | hc
    · exact hnoDelete hd
    · exact hnoDummy hc
  have hvalue :
      taggedD15ReadyPotential ring i j k a b seed.N =
        n * (2 * b - 1) := by
    have hh := tagged_d15_ready_phase_value ring i j k a b
      seed.N (.ready : SealedPhase n) seed.prepared.2 hnot
    simpa only [SealedCloseProof.fromPhase,
      SealedCloseProof.rank, Nat.add_zero] using hh
  change
    taggedD15ReadyPotential ring i j k a b seed.N +
      n * (5 * a - 2) + n * (2 * b - 2) =
        n * (5 * a + 4 * b - 5)
  rw [hvalue]
  exact tagged_d15_attempt_budget n a b ha hb


end L3

/-!
Local pointwise comparisons. The first is a mode-independent
upper bound for every GOOD active child, eliminating the need for a
mode-case analysis in the Ready parent.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

theorem tagged_d15_recovery_uniform_cap {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (z : TaggedD15AttemptState ring i j k a b) :
    taggedD15RecoveryPotential ring i j k b z.N ≤
      n * (2 * b - 1) := by
  classical
  by_cases hstop : taggedD15RecoveryStop ring i j k b z.N
  · unfold taggedD15RecoveryPotential
    rw [if_pos hstop]
    exact Nat.zero_le _
  · have hval := tagged_d15_recovery_phase_value
      ring i j k b z.N z.targetPhase z.targetHolds hstop
    have hcap := sealed_phase_progress_bound
      ring z.N j b z.targetPhase z.targetHolds
    calc
      taggedD15RecoveryPotential ring i j k b z.N =
          n * SealedPhaseProgress b z.targetPhase := hval
      _ ≤ n * (2 * b - 1) := Nat.mul_le_mul_left n hcap

theorem tagged_d15_recovery_live_pointwise {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (b : Nat)
    (N : TripleNativeState n)
    (phase : SealedPhase n)
    (hp : SealedPhaseHolds ring N j b phase)
    (hlive : SealedCloseProof.fromPhase phase =
      SealedCloseProof.Stage.bullet true 1) :
    taggedD15RecoveryPotential ring i j k b N ≤
      n * (2 * b - 2) := by
  classical
  by_cases hstop : taggedD15RecoveryStop ring i j k b N
  · unfold taggedD15RecoveryPotential
    rw [if_pos hstop]
    exact Nat.zero_le _
  · have hval := tagged_d15_recovery_phase_value
      ring i j k b N phase hp hstop
    have heq :
        SealedCloseProof.rank b
            (SealedCloseProof.fromPhase phase) =
          SealedPhaseProgress b phase := by
      cases phase <;> rfl
    rw [hlive] at heq
    simp only [SealedCloseProof.rank] at heq
    have hrank :
        SealedPhaseProgress b phase = 2 * b - 2 := by
      omega
    rw [hval, hrank]
    exact Nat.le_refl _

/-- For an arbitrary GOOD active child whose physical native
configuration is M, even the largest of the three mode values is
below the killed Ready potential of M plus the two reserves. -/
theorem tagged_d15_ready_any_active_pointwise {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (ha : 1 ≤ a)
    (z : TaggedD15AttemptState ring i j k a b)
    (hg : TaggedD15AttemptGood ring i j k a b z) :
    tagged_d15_attempt_potential ring i j k a b z ≤
      taggedD15ReadyPotential ring i j k a b z.N +
        n * (5 * a - 2) + n * (2 * b - 2) := by
  unfold tagged_d15_attempt_potential
  cases hm : z.mode with
  | readyWait =>
      change
        taggedD15ReadyPotential ring i j k a b z.N +
          n * (5 * a - 2) + n * (2 * b - 2) ≤
        taggedD15ReadyPotential ring i j k a b z.N +
          n * (5 * a - 2) + n * (2 * b - 2)
      exact Nat.le_refl _
  | vulnerable =>
      have hs :=
        tagged_d15_structural_of_vulnerable_good
          ring i j k a b z hg hm
      have hcap :=
        tagged_d15_q_structural_cap
          ring i j k a b z.N hs
      change
        taggedQBellman ring i j k a z.N + n * (2 * b - 2) ≤
        taggedD15ReadyPotential ring i j k a b z.N +
          n * (5 * a - 2) + n * (2 * b - 2)
      omega
  | recovery =>
      have hcap :=
        tagged_d15_recovery_uniform_cap ring i j k a b z
      have hcoeff :
          2 * b - 1 ≤ (5 * a - 2) + (2 * b - 2) := by
        omega
      have hscale :
          n * (2 * b - 1) ≤
            n * (5 * a - 2) + n * (2 * b - 2) := by
        calc
          n * (2 * b - 1) ≤
              n * ((5 * a - 2) + (2 * b - 2)) :=
            Nat.mul_le_mul_left n hcoeff
          _ = n * (5 * a - 2) + n * (2 * b - 2) :=
            Nat.mul_add n _ _
      change
        taggedD15RecoveryPotential ring i j k b z.N ≤
        taggedD15ReadyPotential ring i j k a b z.N +
          n * (5 * a - 2) + n * (2 * b - 2)
      omega

/-- This Ready-child comparison uses only the actual nativeE
projection and good-closure of the certificate, not the mode
decision tree hidden in tagged_d15_attempt_step_certified. -/
theorem tagged_d15_ready_attempt_child_pointwise {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (ha : 1 ≤ a) (hb : 2 ≤ b)
    (z : TaggedD15AttemptState ring i j k a b)
    (hg : TaggedD15AttemptGood ring i j k a b z)
    (e : Fin n) :
    taggedAttemptNodePotential
        (tagged_d15_attempt_potential ring i j k a b)
        (tagged_d15_attempt_step hn ring i j k a b hb z e) ≤
      taggedD15ReadyPotential ring i j k a b
          (nativeE ring z.N e) +
        n * (5 * a - 2) + n * (2 * b - 2) := by
  cases hnode : tagged_d15_attempt_step
      hn ring i j k a b hb z e with
  | success =>
      simp only [taggedAttemptNodePotential]
      exact Nat.zero_le _
  | retry seed =>
      simp only [taggedAttemptNodePotential]
      exact Nat.zero_le _
  | active z' =>
      have hmatch := tagged_d15_attempt_all_edge_closed
        hn ring i j k a b hb z e
      rw [hnode] at hmatch
      have hgood' := tagged_d15_attempt_good_closed
        hn ring i j k a b hb z z' e hg hnode
      have hpoint := tagged_d15_ready_any_active_pointwise
        ring i j k a b ha z' hgood'
      rw [hmatch] at hpoint
      simpa only [taggedAttemptNodePotential] using hpoint

/-- The complete pointwise Ready comparison closes the Ready
branch of the attempt supersolution, using the physical
Ready-wait drift and actual good/closed child observer. -/
theorem tagged_d15_ready_attempt_bellman {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (ha : 1 ≤ a) (hb : 2 ≤ b)
    (z : TaggedD15AttemptState ring i j k a b)
    (hg : TaggedD15AttemptGood ring i j k a b z)
    (hm : z.mode = .readyWait) :
    n + (List.ofFn (fun e : Fin n =>
      taggedAttemptNodePotential
        (tagged_d15_attempt_potential ring i j k a b)
        (tagged_d15_attempt_step hn ring i j k a b hb z e))).sum ≤
      n * tagged_d15_attempt_potential ring i j k a b z := by
  have hnotDeleted : ¬ TaggedDeleted i j k z.N :=
    tagged_d15_triple_not_deleted
      ring i j k a b z.N z.triple
  have hnot : ¬ taggedD15ReadyStop ring i j k a b z.N := by
    intro h
    rcases h with hd | hc
    · exact hnotDeleted hd
    · exact (hg.1 hm) hc
  have hsealed : TaggedSealed ring i j a b z.N :=
    ⟨z.attackerSealed, ⟨z.targetPhase, z.targetHolds⟩⟩
  have hbound : ∀ e : Fin n,
      taggedAttemptNodePotential
          (tagged_d15_attempt_potential ring i j k a b)
          (tagged_d15_attempt_step hn ring i j k a b hb z e) ≤
        taggedD15ReadyPotential ring i j k a b
          (nativeE ring z.N e) +
          (n * (5 * a - 2) + n * (2 * b - 2)) := by
    intro e
    have h := tagged_d15_ready_attempt_child_pointwise
      hn ring i j k a b ha hb z hg e
    omega
  have hbell := tagged_d15_ready_bellman_of_pointwise
    hn ring i j k a b hb z.N
    ⟨z.triple, hsealed⟩ hnot
    (n * (5 * a - 2) + n * (2 * b - 2))
    (fun e : Fin n =>
      taggedAttemptNodePotential
        (tagged_d15_attempt_potential ring i j k a b)
        (tagged_d15_attempt_step hn ring i j k a b hb z e))
    hbound
  have hval :
      tagged_d15_attempt_potential ring i j k a b z =
        taggedD15ReadyPotential ring i j k a b z.N +
          (n * (5 * a - 2) + n * (2 * b - 2)) := by
    unfold tagged_d15_attempt_potential
    rw [hm]
    exact Nat.add_assoc _ _ _
  rw [hval]
  exact hbell

end L3


/-!
The two remaining physical-child inequalities can be discharged
without looking at the observer's hidden choice, provided its
active successor mode and native projection have been identified.
The missing result is the mode classification of that choice.
-/

namespace L3

open PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

/-- A vulnerable nonfailure raw edge is the same literal physical
edge as the controlled Q sampler, even when e=j in a non-Ready
target phase. This needs no global reachability certificate. -/
theorem tagged_d15_vulnerable_nonfailure_raw_eq {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (z : TaggedD15AttemptState ring i j k a b)
    (e : Fin n)
    (hnotfail : ¬ (z.targetPhase = .ready ∧ e = j)) :
    taggedQNext ring j b (by omega : 2 ≤ n)
        (by
          exact Ne.symm (tagged_q_incident_edges_distinct
            (by omega : 2 ≤ n) ring j))
        z.N e =
      nativeE ring z.N e := by
  have hports : ring.leftNeighbor j ≠ j :=
    Ne.symm (tagged_q_incident_edges_distinct
      (by omega : 2 ≤ n) ring j)
  by_cases he : e = j
  · have hnready : ¬ SealedCleanReady ring z.N j b := by
      intro hready
      have hphase := tagged_sealed_phase_unique
        ring z.N j b z.targetPhase (.ready : SealedPhase n)
        z.targetHolds hready
      exact hnotfail ⟨hphase, he⟩
    subst e
    exact tagged_d15_raw_q_same_nonready
      ring j b (by omega : 2 ≤ n) hports z.N hnready
  · exact tagged_d15_raw_q_same_other_edge
      ring j b (by omega : 2 ≤ n) hports z.N e he

theorem tagged_d15_vulnerable_nonfailure_pointwise {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (z z' : TaggedD15AttemptState ring i j k a b)
    (e : Fin n)
    (hnotfail : ¬ (z.targetPhase = .ready ∧ e = j))
    (hmode : z'.mode = .vulnerable)
    (hphysical : z'.N = nativeE ring z.N e) :
    taggedAttemptNodePotential
        (tagged_d15_attempt_potential ring i j k a b)
        (AttemptNode.active (S := TaggedD15AttemptSeed ring i j k a b) z') ≤
      taggedQBellman ring i j k a
        (taggedQNext ring j b (by omega : 2 ≤ n)
          (by
            exact Ne.symm (tagged_q_incident_edges_distinct
              (by omega : 2 ≤ n) ring j))
          z.N e) +
        n * (2 * b - 2) := by
  have hraw := tagged_d15_vulnerable_nonfailure_raw_eq
    hn ring i j k a b z e hnotfail
  have hval :
      tagged_d15_attempt_potential ring i j k a b z' =
        taggedQBellman ring i j k a z'.N + n * (2 * b - 2) := by
    unfold tagged_d15_attempt_potential
    rw [hmode]
  change
    tagged_d15_attempt_potential ring i j k a b z' ≤
      taggedQBellman ring i j k a
        (taggedQNext ring j b (by omega : 2 ≤ n)
          (by
            exact Ne.symm (tagged_q_incident_edges_distinct
              (by omega : 2 ≤ n) ring j))
          z.N e) + n * (2 * b - 2)
  rw [hval, hphysical, hraw]
  exact Nat.le_refl _

theorem tagged_d15_vulnerable_failure_pointwise {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (z z' : TaggedD15AttemptState ring i j k a b)
    (e : Fin n)
    (hmode : z'.mode = .recovery)
    (hlive : SealedCloseProof.fromPhase z'.targetPhase =
      SealedCloseProof.Stage.bullet true 1) :
    taggedAttemptNodePotential
        (tagged_d15_attempt_potential ring i j k a b)
        (AttemptNode.active (S := TaggedD15AttemptSeed ring i j k a b) z') ≤
      taggedQBellman ring i j k a
        (taggedQNext ring j b (by omega : 2 ≤ n)
          (by
            exact Ne.symm (tagged_q_incident_edges_distinct
              (by omega : 2 ≤ n) ring j))
          z.N e) +
        n * (2 * b - 2) := by
  have hval :
      tagged_d15_attempt_potential ring i j k a b z' =
        taggedD15RecoveryPotential ring i j k b z'.N := by
    unfold tagged_d15_attempt_potential
    rw [hmode]
  have hcap := tagged_d15_recovery_live_pointwise
    ring i j k b z'.N z'.targetPhase z'.targetHolds hlive
  change tagged_d15_attempt_potential ring i j k a b z' ≤
    taggedQBellman ring i j k a
      (taggedQNext ring j b (by omega : 2 ≤ n)
        (by
          exact Ne.symm (tagged_q_incident_edges_distinct
            (by omega : 2 ≤ n) ring j))
        z.N e) + n * (2 * b - 2)
  rw [hval]
  omega

theorem tagged_d15_recovery_mode_pointwise {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (z' : TaggedD15AttemptState ring i j k a b)
    (hmode : z'.mode = .recovery) :
    taggedAttemptNodePotential
        (tagged_d15_attempt_potential ring i j k a b)
        (AttemptNode.active (S := TaggedD15AttemptSeed ring i j k a b) z') ≤
      taggedD15RecoveryPotential ring i j k b z'.N := by
  have hval :
      tagged_d15_attempt_potential ring i j k a b z' =
        taggedD15RecoveryPotential ring i j k b z'.N := by
    unfold tagged_d15_attempt_potential
    rw [hmode]
  change tagged_d15_attempt_potential ring i j k a b z' ≤
      taggedD15RecoveryPotential ring i j k b z'.N
  rw [hval]
  exact Nat.le_refl _

end L3


/-!
Certified per-mode outcomes and live Bellman supersolution.
Includes the tagged_d15_attempt_step_certified certificate and its
tagged_d15_attempt_good_closed projection.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

/-- Projection of the per-mode data carried by the certified transition. -/
theorem tagged_d15_step_active_outcomes {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hb : 2 ≤ b)
    (z z' : TaggedD15AttemptState ring i j k a b)
    (e : Fin n)
    (hstep : tagged_d15_attempt_step hn ring i j k a b hb z e =
      .active z') :
    (z.mode = .readyWait →
      (TaggedCleanDummy ring i j a b (nativeE ring z.N e) →
        z'.mode = .vulnerable) ∧
      (¬ TaggedCleanDummy ring i j a b (nativeE ring z.N e) →
        z'.mode = .readyWait)) ∧
    (z.mode = .vulnerable →
      ((z.targetPhase = .ready ∧ e = j) →
        z'.mode = .recovery ∧
          SealedCloseProof.fromPhase z'.targetPhase =
            SealedCloseProof.Stage.bullet true 1) ∧
      (¬ (z.targetPhase = .ready ∧ e = j) →
        z'.mode = .vulnerable)) ∧
    (z.mode = .recovery → z'.mode = .recovery) := by
  change (tagged_d15_attempt_step_certified
    hn ring i j k a b hb z e).val = .active z' at hstep
  exact (tagged_d15_attempt_step_certified
    hn ring i j k a b hb z e).property.2.2.1 z' hstep

theorem tagged_d15_step_retry_only_recovery {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hb : 2 ≤ b)
    (z : TaggedD15AttemptState ring i j k a b)
    (seed : TaggedD15AttemptSeed ring i j k a b)
    (e : Fin n)
    (hstep : tagged_d15_attempt_step hn ring i j k a b hb z e =
      .retry seed) :
    z.mode = .recovery := by
  change (tagged_d15_attempt_step_certified
    hn ring i j k a b hb z e).val = .retry seed at hstep
  exact (tagged_d15_attempt_step_certified
    hn ring i j k a b hb z e).property.2.2.2 seed hstep

theorem tagged_d15_step_active_native {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hb : 2 ≤ b)
    (z z' : TaggedD15AttemptState ring i j k a b)
    (e : Fin n)
    (hstep : tagged_d15_attempt_step hn ring i j k a b hb z e =
      .active z') :
    z'.N = nativeE ring z.N e := by
  have h := tagged_d15_attempt_all_edge_closed
    hn ring i j k a b hb z e
  rw [hstep] at h
  exact h

theorem tagged_d15_step_success_deletes {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hb : 2 ≤ b)
    (z : TaggedD15AttemptState ring i j k a b)
    (e : Fin n)
    (hstep : tagged_d15_attempt_step hn ring i j k a b hb z e =
      .success) :
    TaggedDeleted i j k (nativeE ring z.N e) := by
  have h := tagged_d15_attempt_all_edge_closed
    hn ring i j k a b hb z e
  rw [hstep] at h
  exact h

theorem tagged_d15_step_retry_native {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hb : 2 ≤ b)
    (z : TaggedD15AttemptState ring i j k a b)
    (seed : TaggedD15AttemptSeed ring i j k a b)
    (e : Fin n)
    (hstep : tagged_d15_attempt_step hn ring i j k a b hb z e =
      .retry seed) :
    seed.N = nativeE ring z.N e := by
  have h := tagged_d15_attempt_all_edge_closed
    hn ring i j k a b hb z e
  rw [hstep] at h
  exact h

/-- Nonfailure vulnerable continuation is active and physically identical
to the actual native edge. The deleted alternative is success. -/
theorem tagged_d15_vulnerable_surviving_nonfailure {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hb : 2 ≤ b)
    (z : TaggedD15AttemptState ring i j k a b)
    (e : Fin n)
    (hv : z.mode = .vulnerable)
    (hnotdel : ¬ TaggedDeleted i j k (nativeE ring z.N e))
    (hnotfail : ¬ (z.targetPhase = .ready ∧ e = j)) :
    ∃ z', tagged_d15_attempt_step hn ring i j k a b hb z e =
        .active z' ∧
      z'.mode = .vulnerable ∧ z'.N = nativeE ring z.N e := by
  cases hnode : tagged_d15_attempt_step
      hn ring i j k a b hb z e with
  | success =>
      exact False.elim (hnotdel
        (tagged_d15_step_success_deletes
          hn ring i j k a b hb z e hnode))
  | retry seed =>
      have hr := tagged_d15_step_retry_only_recovery
        hn ring i j k a b hb z seed e hnode
      rw [hv] at hr
      cases hr
  | active z' =>
      have hm := (tagged_d15_step_active_outcomes
        hn ring i j k a b hb z z' e hnode).2.1 hv
      exact ⟨z', rfl, hm.2 hnotfail,
        tagged_d15_step_active_native
          hn ring i j k a b hb z z' e hnode⟩

/-- The Ready outgoing vulnerable failure is active Recovery with
the actual one-bullet Live phase. -/
theorem tagged_d15_vulnerable_surviving_failure {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hb : 2 ≤ b)
    (z : TaggedD15AttemptState ring i j k a b)
    (e : Fin n)
    (hv : z.mode = .vulnerable)
    (hnotdel : ¬ TaggedDeleted i j k (nativeE ring z.N e))
    (hfail : z.targetPhase = .ready ∧ e = j) :
    ∃ z', tagged_d15_attempt_step hn ring i j k a b hb z e =
        .active z' ∧
      z'.mode = .recovery ∧
      SealedCloseProof.fromPhase z'.targetPhase =
        SealedCloseProof.Stage.bullet true 1 ∧
      z'.N = nativeE ring z.N e := by
  cases hnode : tagged_d15_attempt_step
      hn ring i j k a b hb z e with
  | success =>
      exact False.elim (hnotdel
        (tagged_d15_step_success_deletes
          hn ring i j k a b hb z e hnode))
  | retry seed =>
      have hr := tagged_d15_step_retry_only_recovery
        hn ring i j k a b hb z seed e hnode
      rw [hv] at hr
      cases hr
  | active z' =>
      have hm := (tagged_d15_step_active_outcomes
        hn ring i j k a b hb z z' e hnode).2.1 hv
      have hml := hm.1 hfail
      exact ⟨z', rfl, hml.1, hml.2,
        tagged_d15_step_active_native
          hn ring i j k a b hb z z' e hnode⟩

/-- Every surviving recovery step not yet reaching Ready stays active
Recovery, while a surviving Ready-reaching step produces the actual
native retry seed. -/
theorem tagged_d15_recovery_surviving_nonready {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hb : 2 ≤ b)
    (z : TaggedD15AttemptState ring i j k a b)
    (e : Fin n)
    (hv : z.mode = .recovery)
    (hnotdel : ¬ TaggedDeleted i j k (nativeE ring z.N e))
    (hnready : ¬ SealedCleanReady ring (nativeE ring z.N e) j b) :
    ∃ z', tagged_d15_attempt_step hn ring i j k a b hb z e =
        .active z' ∧
      z'.mode = .recovery ∧ z'.N = nativeE ring z.N e := by
  cases hnode : tagged_d15_attempt_step
      hn ring i j k a b hb z e with
  | success =>
      exact False.elim (hnotdel
        (tagged_d15_step_success_deletes
          hn ring i j k a b hb z e hnode))
  | retry seed =>
      have hN := tagged_d15_step_retry_native
        hn ring i j k a b hb z seed e hnode
      apply False.elim
      apply hnready
      rw [← hN]
      exact seed.prepared.2
  | active z' =>
      have hm := (tagged_d15_step_active_outcomes
        hn ring i j k a b hb z z' e hnode).2.2 hv
      exact ⟨z', rfl, hm,
        tagged_d15_step_active_native
          hn ring i j k a b hb z z' e hnode⟩

theorem tagged_d15_recovery_surviving_ready {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hb : 2 ≤ b)
    (z : TaggedD15AttemptState ring i j k a b)
    (e : Fin n)
    (hv : z.mode = .recovery)
    (hnotdel : ¬ TaggedDeleted i j k (nativeE ring z.N e))
    (hready : SealedCleanReady ring (nativeE ring z.N e) j b) :
    ∃ seed, tagged_d15_attempt_step hn ring i j k a b hb z e =
        .retry seed ∧ seed.N = nativeE ring z.N e := by
  cases hnode : tagged_d15_attempt_step
      hn ring i j k a b hb z e with
  | success =>
      exact False.elim (hnotdel
        (tagged_d15_step_success_deletes
          hn ring i j k a b hb z e hnode))
  | retry seed =>
      exact ⟨seed, rfl, tagged_d15_step_retry_native
        hn ring i j k a b hb z seed e hnode⟩
  | active z' =>
      have hm := (tagged_d15_step_active_outcomes
        hn ring i j k a b hb z z' e hnode).2.2 hv
      have hnonready : z'.targetPhase ≠ .ready := by
        have h := z'.modeValid
        rw [hm] at h
        exact h
      have hN := tagged_d15_step_active_native
        hn ring i j k a b hb z z' e hnode
      have hnow : SealedCleanReady ring z'.N j b := by
        rw [hN]
        exact hready
      have hphase := tagged_sealed_phase_unique
        ring z'.N j b z'.targetPhase (.ready : SealedPhase n)
        z'.targetHolds hnow
      exact False.elim (hnonready hphase)

/-! The two Bellman branches use exactly the accepted physical pointwise
comparisons; they do not unfold the dependent step. -/

theorem tagged_d15_vulnerable_attempt_bellman {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (ha : 1 ≤ a) (hb : 2 ≤ b)
    (z : TaggedD15AttemptState ring i j k a b)
    (hg : TaggedD15AttemptGood ring i j k a b z)
    (hv : z.mode = .vulnerable) :
    n + (List.ofFn (fun e : Fin n =>
      taggedAttemptNodePotential
        (tagged_d15_attempt_potential ring i j k a b)
        (tagged_d15_attempt_step hn ring i j k a b hb z e))).sum ≤
      n * tagged_d15_attempt_potential ring i j k a b z := by
  let P := tagged_d15_attempt_potential ring i j k a b
  let child : Fin n → Nat := fun e =>
    taggedAttemptNodePotential P
      (tagged_d15_attempt_step hn ring i j k a b hb z e)
  have hs : TaggedD15QStructural ring i j k a b z.N :=
    tagged_d15_structural_of_vulnerable_good
      ring i j k a b z hg hv
  have hports : ring.leftNeighbor j ≠ j :=
    Ne.symm (tagged_q_incident_edges_distinct
      (by omega : 2 ≤ n) ring j)
  have hchild : ∀ e : Fin n,
      child e ≤
        taggedQBellman ring i j k a
          (taggedQNext ring j b (by omega : 2 ≤ n) hports z.N e) +
        n * (2 * b - 2) := by
    intro e
    cases hnode : tagged_d15_attempt_step
        hn ring i j k a b hb z e with
    | success =>
        simp [child, taggedAttemptNodePotential, hnode]
    | retry seed =>
        simp [child, taggedAttemptNodePotential, hnode]
    | active z' =>
        by_cases hfail : z.targetPhase = .ready ∧ e = j
        · have hm := (tagged_d15_step_active_outcomes
            hn ring i j k a b hb z z' e hnode).2.1 hv
          have hml := hm.1 hfail
          have hh := tagged_d15_vulnerable_failure_pointwise
            hn ring i j k a b z z' e hml.1 hml.2
          simpa only [child, P, hnode] using hh
        · have hm := (tagged_d15_step_active_outcomes
            hn ring i j k a b hb z z' e hnode).2.1 hv
          have hmode : z'.mode = .vulnerable := hm.2 hfail
          have hphys := tagged_d15_step_active_native
            hn ring i j k a b hb z z' e hnode
          have hh := tagged_d15_vulnerable_nonfailure_pointwise
            hn ring i j k a b z z' e hfail hmode hphys
          simpa only [child, P, hnode] using hh
  have hbell := tagged_d15_vulnerable_bellman_of_pointwise
    hn ring i j k a b hports z.N hs
    (n * (2 * b - 2)) child hchild
  have hvalue :
      P z = taggedQBellman ring i j k a z.N +
        n * (2 * b - 2) := by
    unfold P tagged_d15_attempt_potential
    rw [hv]
  change n + (List.ofFn child).sum ≤ n * P z
  rw [hvalue]
  exact hbell

theorem tagged_d15_recovery_attempt_bellman {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hb : 2 ≤ b)
    (z : TaggedD15AttemptState ring i j k a b)
    (hv : z.mode = .recovery) :
    n + (List.ofFn (fun e : Fin n =>
      taggedAttemptNodePotential
        (tagged_d15_attempt_potential ring i j k a b)
        (tagged_d15_attempt_step hn ring i j k a b hb z e))).sum ≤
      n * tagged_d15_attempt_potential ring i j k a b z := by
  let P := tagged_d15_attempt_potential ring i j k a b
  let V := taggedD15RecoveryPotential ring i j k b
  let child : Fin n → Nat := fun e =>
    taggedAttemptNodePotential P
      (tagged_d15_attempt_step hn ring i j k a b hb z e)
  have hnotdel : ¬ TaggedDeleted i j k z.N :=
    tagged_d15_triple_not_deleted
      ring i j k a b z.N z.triple
  have hnready : z.targetPhase ≠ .ready := by
    have hh := z.modeValid
    rw [hv] at hh
    exact hh
  have hnot : ¬ taggedD15RecoveryStop ring i j k b z.N := by
    intro hs
    rcases hs with hd | hr
    · exact hnotdel hd
    · exact hnready (tagged_sealed_phase_unique
        ring z.N j b z.targetPhase (.ready : SealedPhase n)
        z.targetHolds hr)
  have hgood : TaggedTriple ring i j k a b z.N ∧
      TaggedSealed ring i j a b z.N :=
    ⟨z.triple, ⟨z.attackerSealed, ⟨z.targetPhase, z.targetHolds⟩⟩⟩
  have hchild : ∀ e : Fin n,
      child e ≤ V (nativeE ring z.N e) := by
    intro e
    cases hnode : tagged_d15_attempt_step
        hn ring i j k a b hb z e with
    | success =>
        simp [child, taggedAttemptNodePotential, hnode]
    | retry seed =>
        simp [child, taggedAttemptNodePotential, hnode]
    | active z' =>
        have hmode : z'.mode = .recovery :=
          (tagged_d15_step_active_outcomes
            hn ring i j k a b hb z z' e hnode).2.2 hv
        have hphys := tagged_d15_step_active_native
          hn ring i j k a b hb z z' e hnode
        have hh := tagged_d15_recovery_mode_pointwise
          ring i j k a b z' hmode
        rw [hphys] at hh
        simpa only [child, P, V, hnode] using hh
  have hsum : (List.ofFn child).sum ≤
      (List.ofFn (fun e : Fin n =>
        V (nativeE ring z.N e))).sum :=
    ofFn_sum_le _ _ hchild
  have hlocal := tagged_d15_recovery_local_drift
    hn ring i j k a b z.N hgood hnot
  have hvalue : P z = V z.N := by
    unfold P tagged_d15_attempt_potential
    rw [hv]
  change n + (List.ofFn child).sum ≤ n * P z
  rw [hvalue]
  calc
    n + (List.ofFn child).sum ≤
        n + (List.ofFn (fun e : Fin n =>
          V (nativeE ring z.N e))).sum :=
      Nat.add_le_add_left hsum n
    _ ≤ n * V z.N := hlocal

/-- A name local to this importable file, not the unbuilt moderate chain. -/
def TaggedAttemptCostSuper
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n)
    (good : A → Prop) (P : A → Nat) : Prop :=
  ∀ z, good z →
    n + (List.ofFn (fun e : Fin n =>
      taggedAttemptNodePotential P (K.step z e))).sum ≤ n * P z

theorem tagged_d15_attempt_super {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (ha : 1 ≤ a) (hb : 2 ≤ b) :
    TaggedAttemptCostSuper
      (tagged_d15_retry_kernel hn ring i j k a b hb)
      (TaggedD15AttemptGood ring i j k a b)
      (tagged_d15_attempt_potential ring i j k a b) := by
  intro z hg
  cases hm : z.mode with
  | readyWait =>
      exact tagged_d15_ready_attempt_bellman
        hn ring i j k a b ha hb z hg hm
  | vulnerable =>
      exact tagged_d15_vulnerable_attempt_bellman
        hn ring i j k a b ha hb z hg hm
  | recovery =>
      exact tagged_d15_recovery_attempt_bellman
        hn ring i j k a b hb z hm

private theorem tagged_attempt_success_cost_zero
    {A S : Type} {n : Nat} (K : RetryKernel A S n)
    (T : Nat) :
    attemptCostNumerator K (.success) T = 0 := by
  cases T <;> rfl

private theorem tagged_attempt_retry_cost_zero
    {A S : Type} {n : Nat} (K : RetryKernel A S n)
    (s : S) (T : Nat) :
    attemptCostNumerator K (.retry s) T = 0 := by
  cases T <;> rfl

/-- Local finite-horizon Bellman induction, using importable
attemptCostNumerator and List.ofFn helpers. -/
theorem tagged_attempt_cost_numerator_le_of_super
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n)
    (good : A → Prop) (P : A → Nat)
    (hclosed : ∀ z e z', good z →
      K.step z e = .active z' → good z')
    (hsuper : TaggedAttemptCostSuper K good P) :
    ∀ z, good z → ∀ T,
      attemptCostNumerator K (.active z) T ≤ n ^ T * P z := by
  intro z hz T
  induction T generalizing z with
  | zero =>
      simp [attemptCostNumerator]
  | succ T ih =>
      change n ^ (T + 1) +
          (List.ofFn (fun e : Fin n =>
            attemptCostNumerator K (K.step z e) T)).sum ≤
        n ^ (T + 1) * P z
      have hchild : ∀ e : Fin n,
          attemptCostNumerator K (K.step z e) T ≤
            n ^ T * taggedAttemptNodePotential P (K.step z e) := by
        intro e
        cases hstep : K.step z e with
        | active z' =>
            have hz' : good z' := hclosed z e z' hz hstep
            have hh := ih z' hz'
            simpa [hstep, taggedAttemptNodePotential] using hh
        | success =>
            simp [hstep, taggedAttemptNodePotential,
              tagged_attempt_success_cost_zero]
        | retry s =>
            simp [hstep, taggedAttemptNodePotential,
              tagged_attempt_retry_cost_zero]
      have hsum :
          (List.ofFn (fun e : Fin n =>
            attemptCostNumerator K (K.step z e) T)).sum ≤
          n ^ T *
            (List.ofFn (fun e : Fin n =>
              taggedAttemptNodePotential P (K.step z e))).sum := by
        calc
          (List.ofFn (fun e : Fin n =>
              attemptCostNumerator K (K.step z e) T)).sum ≤
            (List.ofFn (fun e : Fin n =>
              n ^ T * taggedAttemptNodePotential P
                (K.step z e))).sum :=
              ofFn_sum_le _ _ hchild
          _ = n ^ T *
              (List.ofFn (fun e : Fin n =>
                taggedAttemptNodePotential P (K.step z e))).sum :=
              ofFn_sum_mul_left (n ^ T) _
      calc
        n ^ (T + 1) +
          (List.ofFn (fun e : Fin n =>
            attemptCostNumerator K (K.step z e) T)).sum ≤
          n ^ (T + 1) +
            n ^ T * (List.ofFn (fun e : Fin n =>
              taggedAttemptNodePotential P (K.step z e))).sum :=
          Nat.add_le_add_left hsum _
        _ = n ^ T *
            (n + (List.ofFn (fun e : Fin n =>
              taggedAttemptNodePotential P (K.step z e))).sum) := by
          simp [Nat.pow_succ, Nat.mul_add,
            Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        _ ≤ n ^ T * (n * P z) :=
          Nat.mul_le_mul_left (n ^ T) (hsuper z hz)
        _ = n ^ (T + 1) * P z := by
          simp [Nat.pow_succ, Nat.mul_assoc,
            Nat.mul_left_comm, Nat.mul_comm]

/-- The actual history kernel's one-attempt cost starts at the
paper coefficient n(5a+4b-5), without importing the unbuilt
moderate-attempt module. -/
theorem tagged_d15_attempt_finite_cost {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (ha : 1 ≤ a) (hb : 2 ≤ b)
    (seed : TaggedD15AttemptSeed ring i j k a b) (T : Nat) :
    attemptCostNumerator
      (tagged_d15_retry_kernel hn ring i j k a b hb)
      (.active ((tagged_d15_retry_kernel hn ring i j k a b hb).start seed))
      T ≤
      n ^ T * (n * (5 * a + 4 * b - 5)) := by
  let K := tagged_d15_retry_kernel hn ring i j k a b hb
  let P := tagged_d15_attempt_potential ring i j k a b
  have hclosed :
      ∀ z e z', TaggedD15AttemptGood ring i j k a b z →
        K.step z e = .active z' →
          TaggedD15AttemptGood ring i j k a b z' := by
    intro z e z' hz hs
    exact tagged_d15_attempt_good_closed
      hn ring i j k a b hb z z' e hz hs
  have hcost := tagged_attempt_cost_numerator_le_of_super
    K (TaggedD15AttemptGood ring i j k a b) P
    hclosed
    (tagged_d15_attempt_super hn ring i j k a b ha hb)
    (tagged_d15_attempt_start ring i j k a b seed)
    (tagged_d15_attempt_good_start ring i j k a b seed) T
  have hvalue := tagged_d15_attempt_potential_start
    ring i j k a b ha hb seed
  change attemptCostNumerator K
    (.active (tagged_d15_attempt_start ring i j k a b seed)) T ≤
      n ^ T * (n * (5 * a + 4 * b - 5))
  calc
    _ ≤ n ^ T * P
        (tagged_d15_attempt_start ring i j k a b seed) := hcost
    _ = n ^ T * (n * (5 * a + 4 * b - 5)) := by
      exact congrArg (fun x => n ^ T * x) hvalue


/-! Retry-count splice: every retry follows a genuine vulnerable
Ready-outgoing failure; the return phase is counted without resetting
the physical native state. -/

theorem tagged_d15_deleted_step_success {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hb : 2 ≤ b)
    (z : TaggedD15AttemptState ring i j k a b)
    (e : Fin n)
    (hd : TaggedDeleted i j k (nativeE ring z.N e)) :
    tagged_d15_attempt_step hn ring i j k a b hb z e = .success := by
  cases hnode : tagged_d15_attempt_step
      hn ring i j k a b hb z e with
  | success => rfl
  | active z' =>
      have hN := tagged_d15_step_active_native
        hn ring i j k a b hb z z' e hnode
      have hdeleted : TaggedDeleted i j k z'.N := by
        rw [hN]
        exact hd
      exact False.elim
        ((tagged_d15_triple_not_deleted
          ring i j k a b z'.N z'.triple) hdeleted)
  | retry seed =>
      have hN := tagged_d15_step_retry_native
        hn ring i j k a b hb z seed e hnode
      have hdeleted : TaggedDeleted i j k seed.N := by
        rw [hN]
        exact hd
      exact False.elim
        ((tagged_d15_triple_not_deleted
          ring i j k a b seed.N seed.triple) hdeleted)

private theorem tagged_retry_count_le_pow
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n) :
    ∀ x T, retryCount K x T ≤ n ^ T := by
  intro x T
  induction T generalizing x with
  | zero =>
      cases x <;> simp [retryCount]
  | succ T ih =>
      cases x with
      | success => simp [retryCount]
      | retry s => simp [retryCount]
      | active z =>
          change
            (List.ofFn (fun e : Fin n =>
              retryCount K (K.step z e) T)).sum ≤ n ^ (T + 1)
          calc
            (List.ofFn (fun e : Fin n =>
                retryCount K (K.step z e) T)).sum ≤
              (List.ofFn (fun _ : Fin n => n ^ T)).sum :=
                ofFn_sum_le _ _ (fun e => ih (K.step z e))
            _ = n * n ^ T := ofFn_sum_const n (n ^ T)
            _ = n ^ (T + 1) := by
              rw [Nat.pow_succ]
              ac_rfl

private theorem tagged_failure_count_success_zero
    {V : Type} {n : Nat}
    (step : V → Fin n → StopNode V) :
    ∀ T, failureCount step (.success) T = 0 := by
  intro T
  induction T with
  | zero => rfl
  | succ T ih =>
      change
        (List.ofFn (fun _ : Fin n =>
          failureCount step (.success) T)).sum = 0
      rw [ofFn_sum_eq _ (fun _ : Fin n => 0) (fun _ => ih),
        ofFn_sum_const]
      simp

private theorem tagged_failure_count_failure_eq_pow
    {V : Type} {n : Nat}
    (step : V → Fin n → StopNode V) :
    ∀ T, failureCount step (.failure) T = n ^ T := by
  intro T
  induction T with
  | zero => rfl
  | succ T ih =>
      change
        (List.ofFn (fun _ : Fin n =>
          failureCount step (.failure) T)).sum = n ^ (T + 1)
      rw [ofFn_sum_eq _ (fun _ : Fin n => n ^ T) (fun _ => ih),
        ofFn_sum_const, Nat.pow_succ]
      ac_rfl

/-- The vulnerable attempt has no more retry cylinders than the
genuine native stopped trial has failure cylinders, at every horizon.
The latter charges all later recovery work to its failure leaf. -/
theorem tagged_d15_vulnerable_retry_le_failure {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hb : 2 ≤ b) (T : Nat) :
    ∀ (z : TaggedD15AttemptState ring i j k a b)
      (M : TripleNativeState n),
      z.mode = .vulnerable →
      z.N = M →
      TaggedD15AttemptGood ring i j k a b z →
      retryCount (tagged_d15_retry_kernel hn ring i j k a b hb)
        (.active z) T ≤
      failureCount (taggedTrialStep ring i j k b)
        (.active M) T := by
  classical
  let K := tagged_d15_retry_kernel hn ring i j k a b hb
  let trial := taggedTrialStep ring i j k b
  induction T with
  | zero =>
      intro z M _ _ _
      exact Nat.le_of_eq rfl
  | succ T ih =>
      intro z M hv hphys hg
      change
        (List.ofFn (fun e : Fin n =>
          retryCount K (K.step z e) T)).sum ≤
        (List.ofFn (fun e : Fin n =>
          failureCount trial (trial M e) T)).sum
      apply ofFn_sum_le
      intro e
      by_cases hd : TaggedDeleted i j k (nativeE ring M e)
      · have hdZ : TaggedDeleted i j k (nativeE ring z.N e) := by
          rw [hphys]
          exact hd
        have hnode := tagged_d15_deleted_step_success
          hn ring i j k a b hb z e hdZ
        have htrial :
            trial M e = .success := by
          simp [trial, taggedTrialStep, hd]
        change retryCount K
            (tagged_d15_attempt_step hn ring i j k a b hb z e) T ≤
          failureCount trial (trial M e) T
        rw [hnode, htrial, tagged_failure_count_success_zero]
        cases T <;> exact Nat.le_of_eq rfl
      · by_cases hf : SealedCleanReady ring M j b ∧ e = j
        · have htrial :
              trial M e = .failure := by
            simp [trial, taggedTrialStep, (hf.2 ▸ hd : ¬ TaggedDeleted i j k (nativeE ring M j)), hf]
          rw [htrial, tagged_failure_count_failure_eq_pow]
          exact tagged_retry_count_le_pow K (K.step z e) T
        · have hnotdelZ :
              ¬ TaggedDeleted i j k (nativeE ring z.N e) := by
            rw [hphys]
            exact hd
          have hnotfail :
              ¬ (z.targetPhase = .ready ∧ e = j) := by
            intro hfail
            have hready : SealedCleanReady ring M j b := by
              have hh := z.targetHolds
              rw [hfail.1] at hh
              rw [← hphys]
              exact hh
            exact hf ⟨hready, hfail.2⟩
          obtain ⟨z', hnode, hmode, hN⟩ :=
            tagged_d15_vulnerable_surviving_nonfailure
              hn ring i j k a b hb z e hv hnotdelZ hnotfail
          have hnext : TaggedD15AttemptGood ring i j k a b z' :=
            tagged_d15_attempt_good_closed
              hn ring i j k a b hb z z' e hg hnode
          have hnextN : z'.N = nativeE ring M e := by
            rw [hphys] at hN
            exact hN
          have htrial :
              trial M e = .active (nativeE ring M e) := by
            simp [trial, taggedTrialStep, hd, hf]
          change retryCount K
              (tagged_d15_attempt_step hn ring i j k a b hb z e) T ≤
            failureCount trial (trial M e) T
          rw [hnode, htrial]
          exact ih z' (nativeE ring M e) hmode hnextN hnext

/-- A uniformly valid first-Ready attempt has retry mass no greater
than the original vulnerable failure fraction. No independence of
consecutive attempts is used. -/
theorem tagged_d15_attempt_retry_mass {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (ha : 1 ≤ a) (hb : 2 ≤ b) (hab : a ≤ 2 * b)
    (seed : TaggedD15AttemptSeed ring i j k a b)
    (T : Nat) :
    taggedModerateMultiplier b *
      retryCount (tagged_d15_retry_kernel hn ring i j k a b hb)
        (.active ((tagged_d15_retry_kernel hn ring i j k a b hb).start seed))
        T ≤
      (taggedModerateMultiplier b - 1) * n ^ T := by
  classical
  let K := tagged_d15_retry_kernel hn ring i j k a b hb
  let q := taggedModerateMultiplier b
  have hports : ring.leftNeighbor j ≠ j :=
    Ne.symm (tagged_q_incident_edges_distinct
      (by omega : 2 ≤ n) ring j)
  have hentry :
      ∀ z : TaggedD15AttemptState ring i j k a b,
        TaggedD15AttemptGood ring i j k a b z →
        z.mode = .vulnerable →
        TaggedCleanDummy ring i j a b z.N →
        ∀ U, q * retryCount K (.active z) U ≤
          (q - 1) * n ^ U := by
    intro z hg hv hc U
    have hdom := tagged_d15_vulnerable_retry_le_failure
      hn ring i j k a b hb U z z.N hv rfl hg
    have hmass := tagged_d15_physical_vulnerable_failure_mass
      hn ring i j k a b hb hab hports
      z.N z.triple hc U
    exact Nat.le_trans (Nat.mul_le_mul_left q hdom)
      (by simpa only [q] using hmass)
  have hpre :
      ∀ U, ∀ z : TaggedD15AttemptState ring i j k a b,
        z.mode = .readyWait →
        TaggedD15AttemptGood ring i j k a b z →
        q * retryCount K (.active z) U ≤
          (q - 1) * n ^ U := by
    intro U
    induction U with
    | zero =>
        intro z _ _
        simp [retryCount]
    | succ U ih =>
        intro z hm hg
        change
          q * (List.ofFn (fun e : Fin n =>
            retryCount K (K.step z e) U)).sum ≤
          (q - 1) * n ^ (U + 1)
        have hchild : ∀ e : Fin n,
            q * retryCount K (K.step z e) U ≤
              (q - 1) * n ^ U := by
          intro e
          cases hnode : K.step z e with
          | success =>
              simp [retryCount]
          | retry seed' =>
              have hr := tagged_d15_step_retry_only_recovery
                hn ring i j k a b hb z seed' e hnode
              rw [hm] at hr
              cases hr
          | active z' =>
              have hs :
                  tagged_d15_attempt_step hn ring i j k a b hb z e =
                    .active z' := hnode
              have hg' : TaggedD15AttemptGood ring i j k a b z' :=
                tagged_d15_attempt_good_closed
                  hn ring i j k a b hb z z' e hg hs
              have hN := tagged_d15_step_active_native
                hn ring i j k a b hb z z' e hs
              have hclass := (tagged_d15_step_active_outcomes
                hn ring i j k a b hb z z' e hs).1 hm
              by_cases hclean : TaggedCleanDummy ring i j a b z'.N
              · have hcN :
                    TaggedCleanDummy ring i j a b
                      (nativeE ring z.N e) := by
                    rw [← hN]
                    exact hclean
                have hv' : z'.mode = .vulnerable := hclass.1 hcN
                exact hentry z' hg' hv' hclean U
              · have hnN :
                    ¬ TaggedCleanDummy ring i j a b
                      (nativeE ring z.N e) := by
                    intro hcN
                    apply hclean
                    rw [hN]
                    exact hcN
                have hm' : z'.mode = .readyWait := hclass.2 hnN
                exact ih z' hm' hg'
        calc
          q * (List.ofFn (fun e : Fin n =>
              retryCount K (K.step z e) U)).sum =
            (List.ofFn (fun e : Fin n =>
              q * retryCount K (K.step z e) U)).sum :=
                (ofFn_sum_mul_left q _).symm
          _ ≤ (List.ofFn (fun _ : Fin n =>
              (q - 1) * n ^ U)).sum :=
                ofFn_sum_le _ _ hchild
          _ = n * ((q - 1) * n ^ U) :=
                ofFn_sum_const n ((q - 1) * n ^ U)
          _ = (q - 1) * n ^ (U + 1) := by
                rw [Nat.pow_succ]
                ac_rfl
  have hstart : TaggedD15AttemptGood ring i j k a b
      (K.start seed) :=
    tagged_d15_attempt_good_start ring i j k a b seed
  have hbound := hpre T (K.start seed) (by rfl) hstart
  exact hbound

/-- The entire native history is simulated edge-for-edge, including
the actual Ready retry seed and success only on real tag deletion. -/
theorem tagged_d15_retry_native_simulation {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hb : 2 ≤ b) :
    Prob.RetrySimulation
      (tagged_d15_retry_kernel hn ring i j k a b hb)
      (nativeE ring)
      (TaggedDeleted i j k)
      (fun M z => z.N = M) := by
  intro M z hrel _ e
  cases hnode :
      (tagged_d15_retry_kernel hn ring i j k a b hb).step z e with
  | success =>
      have hs :
          tagged_d15_attempt_step hn ring i j k a b hb z e =
            .success := hnode
      have hd := tagged_d15_step_success_deletes
        hn ring i j k a b hb z e hs
      rw [hrel] at hd
      exact hd
  | active z' =>
      have hs :
          tagged_d15_attempt_step hn ring i j k a b hb z e =
            .active z' := hnode
      have hN := tagged_d15_step_active_native
        hn ring i j k a b hb z z' e hs
      rw [hrel] at hN
      exact hN
  | retry seed =>
      have hs :
          tagged_d15_attempt_step hn ring i j k a b hb z e =
            .retry seed := hnode
      have hN := tagged_d15_step_retry_native
        hn ring i j k a b hb z seed e hs
      rw [hrel] at hN
      exact hN

/-- D.15's full moderate native first-deletion cost, with the
96-era universal factor replaced by the sharp 64/52 bound already
proved for the actual tagged vulnerable trial. -/
theorem tagged_d15_moderate_native_cost {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (ha : 1 ≤ a) (hb : 2 ≤ b) (hab : a ≤ 2 * b)
    (M : TripleNativeState n)
    (htriple : TaggedTriple ring i j k a b M)
    (hprepared : TaggedPrepared ring i j a b M) :
    ∀ T, costNumerator (nativeE ring) (TaggedDeleted i j k) M T ≤
      n ^ T * (taggedModerateMultiplier b * n *
        (5 * a + 4 * b - 5)) := by
  classical
  let K := tagged_d15_retry_kernel hn ring i j k a b hb
  let B := n * (5 * a + 4 * b - 5)
  let q := taggedModerateMultiplier b
  have hqpos : 0 < q := by
    unfold q taggedModerateMultiplier
    split <;> omega
  have hnum : q - 1 < q := by omega
  have hcost :
      ∀ seed : TaggedD15AttemptSeed ring i j k a b,
        K.valid seed → ∀ T,
          costNumerator (Prob.attemptStepper K)
            (fun x => Prob.attemptGood x ∨ Prob.attemptFail x)
            (.active (K.start seed)) T ≤ n ^ T * B := by
    intro seed _ T
    simpa only [Prob.attempt_costNumerator_eq] using
      (tagged_d15_attempt_finite_cost
        hn ring i j k a b ha hb seed T)
  have hretry :
      ∀ seed : TaggedD15AttemptSeed ring i j k a b,
        K.valid seed → ∀ T,
          q * retryCount K (.active (K.start seed)) T ≤
            (q - 1) * n ^ T := by
    intro seed _ T
    exact tagged_d15_attempt_retry_mass
      hn ring i j k a b ha hb hab seed T
  have hsim :=
    tagged_d15_retry_native_simulation hn ring i j k a b hb
  let seed : TaggedD15AttemptSeed ring i j k a b :=
    { N := M
      triple := htriple
      prepared := hprepared }
  have hceil :
      Prob.renewalCeiling B (q - 1) q = q * B := by
    have hdiff : q - (q - 1) = 1 := by omega
    simp [Prob.renewalCeiling, Prob.ceilNat, hdiff, Nat.mod_one, Nat.mul_comm]
  have hresult := Prob.costNumerator_renewal_le
    (nativeE ring) (TaggedDeleted i j k)
    K (fun M z => z.N = M) hsim
    B (q - 1) q hnum hcost hretry
    M seed (by trivial) (by rfl)
  intro T
  calc
    costNumerator (nativeE ring) (TaggedDeleted i j k) M T ≤
        n ^ T * Prob.renewalCeiling B (q - 1) q :=
      hresult T
    _ = n ^ T * (taggedModerateMultiplier b * n *
          (5 * a + 4 * b - 5)) := by
      rw [hceil]
      dsimp [B, q]
      ac_rfl


/-- Exactly the higher-order hmoderate hypothesis appearing in the
D.9 stage-assembly theorem (TripleDeletion.lean original line 296). -/
theorem tagged_d15_hmoderate {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (ha : 1 ≤ a) :
    2 ≤ b → a ≤ 2 * b →
      ∀ M, TaggedTriple ring i j k a b M →
        TaggedPrepared ring i j a b M → ∀ T,
        costNumerator (nativeE ring) (TaggedDeleted i j k) M T ≤
          n ^ T * (taggedModerateMultiplier b * n *
            (5 * a + 4 * b - 5)) := by
  intro hb hab M htriple hprepared T
  exact tagged_d15_moderate_native_cost
    hn ring i j k a b ha hb hab M htriple hprepared T

end L3


/-!
Source-local consequence of the D.15 and preparation
certificates.

The first missing physical obligation remains the long regime:
a genuine retained attacker live bullet at 2*b outstanding hops,
the target/attacker progress race, a stopped 1/16 successful
native attempt, and its 7*n*(a+b) per-attempt budget. No such
proof is assumed below. The one-edge hshort is also not asserted.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- Fully unconditional within the moderate range: the two prepared
sectors and the actual history-dependent D.15 renewal are paid on
the same native scheduler. This does not use hlong or hshort. -/
theorem tagged_deletion_moderate_cost {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (htriple : TaggedTriple ring i j k a b N)
    (hb : 2 ≤ b) (hab : a ≤ 2 * b) :
    ∀ T,
      costNumerator (nativeE ring)
        (TaggedDeleted i j k) N T ≤
      n ^ T * taggedTripleCeiling n a b := by
  have ha : 1 ≤ a := htriple.2.1.1
  have hprep := tagged_deletion_prep_cost_triple
    hn ring i j k a b N htriple
  have hmoderate := tagged_d15_hmoderate
    hn ring i j k a b ha hb hab
  have hcombined := Prob.costNumerator_stage_le
    (nativeE ring) N
    (fun M => TaggedTriple ring i j k a b M ∧
      TaggedPrepared ring i j a b M)
    (TaggedDeleted i j k)
    (3 * n * (a + b))
    (taggedModerateMultiplier b * n * (5 * a + 4 * b - 5))
    hprep
    (fun M hm T => hmoderate M hm.1 hm.2 T)
  intro T
  calc
    costNumerator (nativeE ring) (TaggedDeleted i j k) N T ≤
        n ^ T * (3 * n * (a + b) +
          taggedModerateMultiplier b * n *
            (5 * a + 4 * b - 5)) :=
      hcombined T
    _ ≤ n ^ T * taggedTripleCeiling n a b :=
      Nat.mul_le_mul_left (n ^ T)
        (tagged_moderate_rate_le_ceiling n a b ha hb hab)

/-- The moderate range also gives the expected first-deletion bound.
The target is actual deletion of one of the distinct tagged leaders. -/
theorem tagged_deletion_moderate_expected {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (htriple : TaggedTriple ring i j k a b N)
    (hb : 2 ≤ b) (hab : a ≤ 2 * b) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (nativeE ring) (TaggedDeleted i j k) N
      ((taggedTripleCeiling n a b : Nat) : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (nativeE ring) (TaggedDeleted i j k)
    (by omega : 0 < n) N (taggedTripleCeiling n a b)).2
  exact tagged_deletion_moderate_cost
    hn ring i j k a b N htriple hb hab

/-- Precise remaining all-regime interface. The preparation and
moderate hypotheses have disappeared, as have the redundant
positivity premises (they follow from the consecutive tags).
The two physical hypotheses below are intentionally not defined
as axioms or claimed proved. -/
theorem tagged_deletion_cost_of_long_short {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (htriple : TaggedTriple ring i j k a b N)
    (hlong : 2 ≤ b → 2 * b + 1 ≤ a → ∀ T,
      costNumerator (nativeE ring)
        (TaggedDeleted i j k) N T ≤
        n ^ T * (112 * n * (a + b)))
    (hshort : b = 1 → ∀ T,
      costNumerator (nativeE ring)
        (TaggedDeleted i j k) N T ≤
        n ^ T * (6 * n * (a + b))) :
    ∀ T,
      costNumerator (nativeE ring)
        (TaggedDeleted i j k) N T ≤
      n ^ T * taggedTripleCeiling n a b := by
  have ha : 1 ≤ a := htriple.2.1.1
  have hb : 1 ≤ b := htriple.2.2.1
  exact tagged_deletion_cost_of_stage_bounds
    ring i j k a b N htriple ha hb
    (tagged_deletion_prep_cost_triple
      hn ring i j k a b N htriple)
    (tagged_d15_hmoderate hn ring i j k a b ha)
    hlong hshort

theorem tagged_deletion_expected_of_long_short {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (htriple : TaggedTriple ring i j k a b N)
    (hlong : 2 ≤ b → 2 * b + 1 ≤ a → ∀ T,
      costNumerator (nativeE ring)
        (TaggedDeleted i j k) N T ≤
        n ^ T * (112 * n * (a + b)))
    (hshort : b = 1 → ∀ T,
      costNumerator (nativeE ring)
        (TaggedDeleted i j k) N T ≤
        n ^ T * (6 * n * (a + b))) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (nativeE ring) (TaggedDeleted i j k) N
      ((taggedTripleCeiling n a b : Nat) : Rat) := by
  have ha : 1 ≤ a := htriple.2.1.1
  have hb : 1 ≤ b := htriple.2.2.1
  exact tagged_deletion_expected_without_prep
    hn ring i j k a b N htriple ha hb
    (tagged_d15_hmoderate hn ring i j k a b ha)
    hlong hshort

end L3



/-!
One-edge target source lemmas.
No LDLocalAttempt module is imported.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal
  (AttemptNode RetryKernel attemptCostNumerator retryCount)

set_option autoImplicit false
set_option Elab.async false

/-- A gap-one B sector that has once reached Ready has only Ready
and the one-site Dummy(0), until a tagged endpoint is deleted. -/
def TaggedShortBPhase {n : Nat}
    (ring : DirectedRing n) (j : Fin n)
    (N : TripleNativeState n) : Prop :=
  SealedCleanReady ring N j 1 ∨
    SealedPhaseHolds ring N j 1 (.dummy (sealedZero ring))

private theorem tagged_short_stage_to_phase {n : Nat}
    (ring : DirectedRing n) (phase : SealedPhase n)
    (h :
      SealedCloseProof.fromPhase phase = .ready ∨
      SealedCloseProof.fromPhase phase = .bullet false 0) :
    phase = .ready ∨ phase = .dummy (sealedZero ring) := by
  cases phase with
  | ready =>
      exact Or.inl rfl
  | dummy p =>
      rcases h with hr | hb
      · cases hr
      · have hval : p.val = 0 := by
          have hnom := congrArg SealedCloseProof.nominated hb
          simpa only [SealedCloseProof.fromPhase,
            SealedCloseProof.nominated] using hnom
        have hp : p = sealedZero ring := Fin.ext (by
          simpa [sealedZero] using hval)
        exact Or.inr (congrArg SealedPhase.dummy hp)
  | live p =>
      rcases h with hr | hb
      · cases hr
      · cases hb
  | returning q =>
      rcases h with hr | hb
      · cases hr
      · cases hb

/-- Pure literal stage table at d=1; there is no surviving Live
or Return phase reachable from Ready/Dummy(0). -/
private theorem tagged_short_stage_table {n : Nat}
    (ring : DirectedRing n) (j e : Fin n)
    (phase : SealedPhase n)
    (hphase : phase = .ready ∨
      phase = .dummy (sealedZero ring)) :
    sealedCloseTable ring j 1 e phase = .ready ∨
      sealedCloseTable ring j 1 e phase = .bullet false 0 := by
  rcases hphase with hp | hp
  · subst phase
    let r := SealedCloseProof.position ring j e
    change
      (if r.val < 1 then
        SealedCloseProof.insideStage 1 .ready r.val
       else if r.val + 1 = n then
        SealedCloseProof.incomingStage .ready
       else .ready) = .ready ∨
      (if r.val < 1 then
        SealedCloseProof.insideStage 1 .ready r.val
       else if r.val + 1 = n then
        SealedCloseProof.incomingStage .ready
       else .ready) = .bullet false 0
    by_cases hr : r.val < 1
    · have hz : r.val = 0 := by omega
      simp [hr, hz, SealedCloseProof.insideStage]
    · by_cases hin : r.val + 1 = n
      · simp [hr, hin, SealedCloseProof.incomingStage]
      · simp [hr, hin]
  · subst phase
    let r := SealedCloseProof.position ring j e
    change
      (if r.val < 1 then
        SealedCloseProof.insideStage 1
          (.bullet false 0) r.val
       else if r.val + 1 = n then
        SealedCloseProof.incomingStage (.bullet false 0)
       else .bullet false 0) = .ready ∨
      (if r.val < 1 then
        SealedCloseProof.insideStage 1
          (.bullet false 0) r.val
       else if r.val + 1 = n then
        SealedCloseProof.incomingStage (.bullet false 0)
       else .bullet false 0) = .bullet false 0
    by_cases hr : r.val < 1
    · have hz : r.val = 0 := by omega
      simp [hr, hz, SealedCloseProof.insideStage]
    · by_cases hin : r.val + 1 = n
      · simp [hr, hin, SealedCloseProof.incomingStage]
      · simp [hr, hin]

/-- The genuine native edge closes the B-gap-one phase invariant,
including the repeated physical tag i=k. -/
theorem tagged_short_b_phase_step {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a : Nat)
    (N : TripleNativeState n)
    (ht : TaggedTriple ring i j k a 1 N)
    (hB : TaggedShortBPhase ring j N)
    (e : Fin n) :
    TaggedDeleted i j k (nativeE ring N e) ∨
      TaggedShortBPhase ring j (nativeE ring N e) := by
  let M := nativeE ring N e
  by_cases hdel : TaggedDeleted i j k M
  · exact Or.inl hdel
  · have hj : (M j).l = true := by
      cases hx : (M j).l with
      | false => exact False.elim (hdel (Or.inr (Or.inl hx)))
      | true => rfl
    have hk : (M k).l = true := by
      cases hx : (M k).l with
      | false => exact False.elim (hdel (Or.inr (Or.inr hx)))
      | true => rfl
    rcases hB with hr | hd
    · obtain ⟨nextPhase, hnext, hstage⟩ :=
        sealed_close_step_stage ring N j k 1 e
          (.ready : SealedPhase n) ht.2.2 hr hj hk
      have htable := tagged_short_stage_table ring j e
        (.ready : SealedPhase n) (Or.inl rfl)
      have hcases := tagged_short_stage_to_phase
        ring nextPhase (by
          rw [hstage]
          exact htable)
      rcases hcases with hready | hdummy
      · rw [hready] at hnext
        exact Or.inr (Or.inl hnext)
      · rw [hdummy] at hnext
        exact Or.inr (Or.inr hnext)
    · obtain ⟨nextPhase, hnext, hstage⟩ :=
        sealed_close_step_stage ring N j k 1 e
          (.dummy (sealedZero ring)) ht.2.2 hd hj hk
      have htable := tagged_short_stage_table ring j e
        (.dummy (sealedZero ring)) (Or.inr rfl)
      have hcases := tagged_short_stage_to_phase
        ring nextPhase (by
          rw [hstage]
          exact htable)
      rcases hcases with hready | hdummy
      · rw [hready] at hnext
        exact Or.inr (Or.inl hnext)
      · rw [hdummy] at hnext
        exact Or.inr (Or.inr hnext)

/-- At one-edge B, j is either ready to dummy-fire (hence will
clear shield before collision), or already a shield-zero dummy. -/
theorem tagged_short_b_vulnerable {n : Nat}
    (ring : DirectedRing n) (j : Fin n)
    (N : TripleNativeState n)
    (hB : TaggedShortBPhase ring j N) :
    (N j).sg = true ∨
      ((N j).sg = false ∧ (N j).sh = false) := by
  rcases hB with hready | hdummy
  · exact Or.inl ((sealedCleanReady_iff ring N j 1).1 hready).1
  · have hshield : (N j).sh = false := by
      simpa only [sealedAt_zero] using hdummy.2.1
    have hsignal : (N j).sg = false := by
      have hz := hdummy.2.2 (sealedZero ring)
        (Nat.le_refl (sealedZero ring).val)
      simpa only [sealedAt_zero] using hz
    exact Or.inr ⟨hsignal, hshield⟩

/-- The exact old-pair collision: an incoming live bullet, or an
initiator that fires live on this interaction, deletes a ready
dummy-firing responder or an already-unshielded responder.
No assumption on the responder's pre-interaction shield is made
in the Ready case. -/
theorem tagged_short_live_hit_row (x y : CertNative)
    (hattack : x.b = (2 : Fin 3) ∨
      (x.l = true ∧ x.sg = true))
    (hyl : y.l = true)
    (hvul : y.sg = true ∨
      (y.sg = false ∧ y.sh = false)) :
    (certLiteralEPair x y).2.l = false := by
  rcases x with ⟨xl, xb, xsh, xsg⟩
  rcases y with ⟨yl, yb, ysh, ysg⟩
  simp only at hattack hyl hvul
  subst yl
  rcases hattack with hb | hready
  · subst xb
    rcases hvul with hs | ⟨hs, hh⟩
    · subst ysg
      cases xl <;> cases xsg <;> cases ysh <;>
        simp [certLiteralEPair]
    · subst ysg
      subst ysh
      cases xl <;> cases xsg <;>
        simp [certLiteralEPair]
  · rcases hready with ⟨hl, hs⟩
    subst xl
    subst xsg
    rcases hvul with hy | ⟨hy, hh⟩
    · subst ysg
      cases ysh <;> simp [certLiteralEPair]
    · subst ysg
      subst ysh
      simp [certLiteralEPair]

/-- Source-level soundness of the terminal clean-live-hit edge.
The collision uses nativeE (not a controlled/redirected edge),
and makes no distinctness assumption on i and k. -/
theorem tagged_short_live_hit_kills {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a : Nat)
    (N : TripleNativeState n)
    (ht : TaggedTriple ring i j k a 1 N)
    (hB : TaggedShortBPhase ring j N)
    (e : Fin n) (hne : e ≠ j)
    (hnext : ring.rightNeighbor e = j)
    (hattack : (N e).b = (2 : Fin 3) ∨
      ((N e).l = true ∧ (N e).sg = true)) :
    TaggedDeleted i j k (nativeE ring N e) := by
  have hj : (N j).l = true := ht.2.2.2.2.2.1
  have hrow := tagged_short_live_hit_row (N e) (N j)
    hattack hj (tagged_short_b_vulnerable ring j N hB)
  have hpair :
      nativeE ring N e j = (certLiteralEPair (N e) (N j)).2 := by
    simp [nativeE, hnext, Ne.symm hne]
  have hdead : (nativeE ring N e j).l = false := by
    rw [hpair]
    exact hrow
  exact Or.inr (Or.inl hdead)

/-- Terminal service of a genuine sealed live attacker must delete
j, even when B is Ready with pre-existing shield. -/
theorem tagged_short_terminal_live_deletes {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a : Nat)
    (N : TripleNativeState n)
    (ht : TaggedTriple ring i j k a 1 N)
    (hB : TaggedShortBPhase ring j N)
    (p : Fin n)
    (hphase : SealedPhaseHolds ring N i a (.live p))
    (hlast : p.val + 1 = a) :
    TaggedDeleted i j k
      (nativeE ring N (SealedPhaseEdge ring i (.live p))) := by
  have hne : SealedPhaseEdge ring i (.live p) ≠ j :=
    sealed_close_nominated_ne_right ring N i j a
      (.live p) ht.2.1 hphase
  have hnxt :
      ring.rightNeighbor (SealedPhaseEdge ring i (.live p)) = j :=
    sealed_close_last_bullet_enters_right
      ring N i j a p ht.2.1 hlast
  exact tagged_short_live_hit_kills ring i j k a
    N ht hB (SealedPhaseEdge ring i (.live p))
    hne hnxt (Or.inl hphase.1.2.1)

/-- A clean Ready attacker at gap one directly kills j on its
outgoing service, because j dummy-fires before collision. -/
theorem tagged_short_ready_gap_one_deletes {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a : Nat)
    (N : TripleNativeState n)
    (ht : TaggedTriple ring i j k a 1 N)
    (hB : TaggedShortBPhase ring j N)
    (hready : SealedCleanReady ring N i a)
    (hone : a = 1) :
    TaggedDeleted i j k (nativeE ring N i) := by
  have hne : i ≠ j :=
    sealed_consecutive_endpoints_ne ring N i j a ht.2.1
  have hlast : (sealedZero ring).val + 1 = a := by
    dsimp [sealedZero]
    omega
  have hnxt : ring.rightNeighbor i = j := by
    have hh := sealed_close_last_bullet_enters_right
      ring N i j a (sealedZero ring) ht.2.1 hlast
    simpa [SealedPhaseEdge, sealedZero, sealedSite_zero] using hh
  have hi : (N i).l = true := ht.2.1.2.2.2.1
  have hsig : (N i).sg = true := by
    simpa only [sealedAt_zero] using hready.1
  exact tagged_short_live_hit_kills ring i j k a N ht hB
    i hne hnxt (Or.inr ⟨hi, hsig⟩)


/-! ## The raw native attacker credit, with B's one-edge promise -/

def TaggedShortAttackGood {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a : Nat)
    (N : TripleNativeState n) : Prop :=
  TaggedTriple ring i j k a 1 N ∧
    Sealed ring N i a ∧ TaggedShortBPhase ring j N

theorem tagged_short_attack_good_closed {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a : Nat)
    (N : TripleNativeState n)
    (hs : TaggedShortAttackGood ring i j k a N)
    (e : Fin n)
    (hnot : ¬ TaggedDeleted i j k (nativeE ring N e)) :
    TaggedShortAttackGood ring i j k a (nativeE ring N e) := by
  have hBsealed : Sealed ring N j 1 := by
    rcases hs.2.2 with hr | hd
    · exact sealed_of_clean_ready ring N j 1 hr
    · exact ⟨.dummy (sealedZero ring), hd⟩
  have htriple := tagged_triple_step_of_survival
    hn ring i j k a 1 N e hs.1 hnot
  have hsealed := tagged_sealed_step_of_survival
    ring i j k a 1 N e hs.1
    ⟨hs.2.1, hBsealed⟩ hnot
  have hBstep := tagged_short_b_phase_step
    ring i j k a N hs.1 hs.2.2 e
  rcases hBstep with hd | hb
  · exact False.elim (hnot hd)
  · exact ⟨htriple, hsealed.1, hb⟩

/-- The exact raw native successor stage of A is selected by the
sealed stage table as long as neither tagged endpoint is deleted. -/
theorem tagged_short_attacker_child_stage {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a : Nat)
    (N : TripleNativeState n) (e : Fin n)
    (ht : TaggedTriple ring i j k a 1 N)
    (phase : SealedPhase n)
    (hp : SealedPhaseHolds ring N i a phase)
    (hnot : ¬ TaggedDeleted i j k (nativeE ring N e)) :
    ∃ nextPhase : SealedPhase n,
      SealedPhaseHolds ring (nativeE ring N e) i a nextPhase ∧
      SealedCloseProof.fromPhase nextPhase =
        sealedCloseTable ring i a e phase := by
  have hi : (nativeE ring N e i).l = true := by
    cases hx : (nativeE ring N e i).l with
    | false => exact False.elim (hnot (Or.inl hx))
    | true => rfl
  have hj : (nativeE ring N e j).l = true := by
    cases hx : (nativeE ring N e j).l with
    | false => exact False.elim (hnot (Or.inr (Or.inl hx)))
    | true => rfl
  exact sealed_close_step_stage
    ring N i j a e phase ht.2.1 hp hi hj

theorem tagged_short_attacker_child_credit {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a : Nat)
    (N : TripleNativeState n) (e : Fin n)
    (ht : TaggedTriple ring i j k a 1 N)
    (phase : SealedPhase n)
    (hp : SealedPhaseHolds ring N i a phase)
    (hnot : ¬ TaggedDeleted i j k (nativeE ring N e)) :
    taggedQBellman ring i j k a (nativeE ring N e) =
      n * taggedCloseCredit a
        (sealedCloseTable ring i a e phase) := by
  obtain ⟨nextPhase, hnext, hstage⟩ :=
    tagged_short_attacker_child_stage
      ring i j k a N e ht phase hp hnot
  calc
    taggedQBellman ring i j k a (nativeE ring N e) =
        taggedAttackerBellman n a nextPhase :=
      tagged_q_bellman_eq_phase
        ring (nativeE ring N e) i j k a
        nextPhase hnot hnext
    _ = n * taggedCloseCredit a
          (SealedCloseProof.fromPhase nextPhase) :=
      tagged_close_credit_from_phase n a nextPhase
    _ = n * taggedCloseCredit a
          (sealedCloseTable ring i a e phase) := by
      rw [hstage]

/-- Nonready A: all raw edges weakly decrease the D.11 credit,
and the nominated edge lowers it by n. The one exception in the
stage table—surviving final Live absorption—is impossible by the
literal b=1 kill lemma. -/
theorem tagged_short_nonready_child_bounds {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a : Nat)
    (N : TripleNativeState n) (e : Fin n)
    (hs : TaggedShortAttackGood ring i j k a N)
    (phase : SealedPhase n)
    (hp : SealedPhaseHolds ring N i a phase)
    (hnr : phase ≠ .ready) :
    taggedQBellman ring i j k a (nativeE ring N e) ≤
      taggedQBellman ring i j k a N ∧
    (e = SealedPhaseEdge ring i phase →
      taggedQBellman ring i j k a (nativeE ring N e) + n ≤
        taggedQBellman ring i j k a N) := by
  let r := SealedCloseProof.position ring i e
  have hc : ConsecutiveNative ring N i j a := hs.1.2.1
  have ha : 1 ≤ a := hc.1
  have hnotold : ¬ TaggedDeleted i j k N :=
    tagged_d15_triple_not_deleted ring i j k a 1 N hs.1
  have hbefore : taggedQBellman ring i j k a N =
      n * taggedCloseCredit a
        (SealedCloseProof.fromPhase phase) := by
    calc
      taggedQBellman ring i j k a N =
          taggedAttackerBellman n a phase :=
        tagged_q_bellman_eq_phase ring N i j k a
          phase hnotold hp
      _ = n * taggedCloseCredit a
          (SealedCloseProof.fromPhase phase) :=
        tagged_close_credit_from_phase n a phase
  by_cases hdel : TaggedDeleted i j k (nativeE ring N e)
  · have hzero := tagged_q_bellman_deleted_zero
      ring (nativeE ring N e) i j k a hdel
    have hpositive :=
      tagged_close_nonready_credit_positive
        ring N i a phase ha hp hnr
    constructor
    · rw [hzero]
      exact Nat.zero_le _
    · intro _
      rw [hzero, Nat.zero_add, hbefore]
      calc
        n = n * 1 := (Nat.mul_one n).symm
        _ ≤ n * taggedCloseCredit a
            (SealedCloseProof.fromPhase phase) :=
          Nat.mul_le_mul_left n hpositive
  · have hchild := tagged_short_attacker_child_credit
      ring i j k a N e hs.1 phase hp hdel
    by_cases hr : r.val < a
    · have htable : sealedCloseTable ring i a e phase =
          SealedCloseProof.insideStage a
            (SealedCloseProof.fromPhase phase) r.val := by
        change (if r.val < a then
            SealedCloseProof.insideStage a
              (SealedCloseProof.fromPhase phase) r.val
           else if r.val + 1 = n then
             SealedCloseProof.incomingStage
               (SealedCloseProof.fromPhase phase)
           else SealedCloseProof.fromPhase phase) = _
        exact if_pos hr
      rcases tagged_close_nonready_inside_credit
          ring N i a r.val phase hp hnr with
        ⟨p, hphaseEq, hhit, hlast⟩ | ⟨hweak, hstrict⟩
      · have hphaseLive :
            SealedPhaseHolds ring N i a (.live p) := by
          simpa only [hphaseEq] using hp
        have heSite : e = sealedSite ring i r.val :=
          sealed_close_edge_of_position ring i e r.val rfl
        have heff :
            e = SealedPhaseEdge ring i (.live p) := by
          calc
            e = sealedSite ring i r.val := heSite
            _ = sealedSite ring i p.val := by rw [hhit]
            _ = SealedPhaseEdge ring i (.live p) := rfl
        have hkill :=
          tagged_short_terminal_live_deletes
            ring i j k a N hs.1 hs.2.2 p hphaseLive hlast
        exact False.elim (hdel (by rw [heff]; exact hkill))
      · have hnomR : e = SealedPhaseEdge ring i phase →
            r.val = SealedCloseProof.nominated
              (SealedCloseProof.fromPhase phase) := by
          intro he
          change (SealedCloseProof.position ring i e).val =
            SealedCloseProof.nominated
              (SealedCloseProof.fromPhase phase)
          rw [he]
          exact sealed_close_nominated_position
            ring N i j a phase hc hp
        constructor
        · calc
            taggedQBellman ring i j k a (nativeE ring N e) =
                n * taggedCloseCredit a
                  (sealedCloseTable ring i a e phase) := hchild
            _ = n * taggedCloseCredit a
                  (SealedCloseProof.insideStage a
                    (SealedCloseProof.fromPhase phase) r.val) := by
              rw [htable]
            _ ≤ n * taggedCloseCredit a
                  (SealedCloseProof.fromPhase phase) :=
              Nat.mul_le_mul_left n hweak
            _ = taggedQBellman ring i j k a N := hbefore.symm
        · intro he
          calc
            taggedQBellman ring i j k a (nativeE ring N e) + n =
                n * (taggedCloseCredit a
                  (sealedCloseTable ring i a e phase) + 1) := by
              rw [hchild, Nat.mul_add, Nat.mul_one]
            _ = n * (taggedCloseCredit a
                  (SealedCloseProof.insideStage a
                    (SealedCloseProof.fromPhase phase) r.val) + 1) := by
              rw [htable]
            _ ≤ n * taggedCloseCredit a
                  (SealedCloseProof.fromPhase phase) :=
              Nat.mul_le_mul_left n (hstrict (hnomR he))
            _ = taggedQBellman ring i j k a N := hbefore.symm
    · have htable : taggedCloseCredit a
          (sealedCloseTable ring i a e phase) =
          taggedCloseCredit a
            (SealedCloseProof.fromPhase phase) := by
        change taggedCloseCredit a
          (if r.val < a then
            SealedCloseProof.insideStage a
              (SealedCloseProof.fromPhase phase) r.val
           else if r.val + 1 = n then
             SealedCloseProof.incomingStage
               (SealedCloseProof.fromPhase phase)
           else SealedCloseProof.fromPhase phase) =
          taggedCloseCredit a
            (SealedCloseProof.fromPhase phase)
        simp only [if_neg hr]
        by_cases hwrap : r.val + 1 = n
        · simpa only [if_pos hwrap] using
            tagged_close_nonready_incoming_credit a phase hnr
        · simp only [if_neg hwrap]
      constructor
      · apply Nat.le_of_eq
        calc
          taggedQBellman ring i j k a (nativeE ring N e) =
              n * taggedCloseCredit a
                (sealedCloseTable ring i a e phase) := hchild
          _ = n * taggedCloseCredit a
                (SealedCloseProof.fromPhase phase) := by rw [htable]
          _ = taggedQBellman ring i j k a N := hbefore.symm
      · intro he
        have hnomR :
            r.val = SealedCloseProof.nominated
              (SealedCloseProof.fromPhase phase) := by
          change (SealedCloseProof.position ring i e).val =
            SealedCloseProof.nominated
              (SealedCloseProof.fromPhase phase)
          rw [he]
          exact sealed_close_nominated_position
            ring N i j a phase hc hp
        have hnomlt :=
          sealed_close_nominated_lt ring N i j a phase hc hp
        exact False.elim (hr (by omega))

/-- Ready A: its only possibly increasing physical child is the
incoming incident edge. Every other edge is weakly nonincreasing. -/
theorem tagged_short_ready_child_bounds {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a : Nat)
    (N : TripleNativeState n) (e : Fin n)
    (ht : TaggedTriple ring i j k a 1 N)
    (hready : SealedCleanReady ring N i a) :
    taggedQBellman ring i j k a (nativeE ring N e) ≤
      taggedQBellman ring i j k a N + n * (2 * a - 1) ∧
    (e ≠ ring.leftNeighbor i →
      taggedQBellman ring i j k a (nativeE ring N e) ≤
        taggedQBellman ring i j k a N) := by
  let r := SealedCloseProof.position ring i e
  have ha : 1 ≤ a := ht.2.1.1
  have hnotold : ¬ TaggedDeleted i j k N :=
    tagged_d15_triple_not_deleted ring i j k a 1 N ht
  have hbefore : taggedQBellman ring i j k a N =
      n * taggedCloseCredit a .ready := by
    calc
      taggedQBellman ring i j k a N =
          taggedAttackerBellman n a (.ready : SealedPhase n) :=
        tagged_q_bellman_eq_phase
          ring N i j k a .ready hnotold hready
      _ = n * taggedCloseCredit a .ready :=
        tagged_close_credit_from_phase n a (.ready : SealedPhase n)
  by_cases hdel : TaggedDeleted i j k (nativeE ring N e)
  · have hzero := tagged_q_bellman_deleted_zero
      ring (nativeE ring N e) i j k a hdel
    constructor
    · rw [hzero]
      exact Nat.zero_le _
    · intro _
      rw [hzero]
      exact Nat.zero_le _
  · have hchild := tagged_short_attacker_child_credit
      ring i j k a N e ht .ready hready hdel
    have htable : sealedCloseTable ring i a e
        (.ready : SealedPhase n) =
        (if r.val < a then
          SealedCloseProof.insideStage a .ready r.val
         else if r.val + 1 = n then
           SealedCloseProof.incomingStage .ready
         else .ready) := by
      rfl
    have hupper :=
      tagged_close_ready_stage_upper a n r.val ha
    constructor
    · calc
        taggedQBellman ring i j k a (nativeE ring N e) =
            n * taggedCloseCredit a
              (sealedCloseTable ring i a e .ready) := hchild
        _ ≤ n * (taggedCloseCredit a .ready + (2 * a - 1)) := by
          rw [htable]
          exact Nat.mul_le_mul_left n hupper
        _ = taggedQBellman ring i j k a N +
            n * (2 * a - 1) := by
          rw [Nat.mul_add, hbefore]
    · intro hnotIncoming
      have hnotr : r.val + 1 ≠ n :=
        tagged_q_nonincoming_offset ring i e hnotIncoming
      have hweak :=
        tagged_close_ready_stage_weak a n r.val ha hnotr
      calc
        taggedQBellman ring i j k a (nativeE ring N e) =
            n * taggedCloseCredit a
              (sealedCloseTable ring i a e .ready) := hchild
        _ ≤ n * taggedCloseCredit a .ready := by
          rw [htable]
          exact Nat.mul_le_mul_left n hweak
        _ = taggedQBellman ring i j k a N := hbefore.symm

/-- At a Ready A, the outgoing native edge lowers attacker credit
by at least 2*n*a; at gap a=1 it deletes j immediately. -/
theorem tagged_short_ready_outgoing_drop {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a : Nat)
    (N : TripleNativeState n)
    (hs : TaggedShortAttackGood ring i j k a N)
    (hready : SealedCleanReady ring N i a) :
    taggedQBellman ring i j k a (nativeE ring N i) + n * (2 * a) ≤
      taggedQBellman ring i j k a N := by
  have ht := hs.1
  have hnotold : ¬ TaggedDeleted i j k N :=
    tagged_d15_triple_not_deleted ring i j k a 1 N ht
  have hbefore : taggedQBellman ring i j k a N =
      n * (3 * a - 1) := by
    simpa only [taggedAttackerBellman] using
      (tagged_q_bellman_eq_phase
        ring N i j k a .ready hnotold hready)
  by_cases hone : a = 1
  · have hdel := tagged_short_ready_gap_one_deletes
      ring i j k a N ht hs.2.2 hready hone
    have hzero := tagged_q_bellman_deleted_zero
      ring (nativeE ring N i) i j k a hdel
    rw [hzero, Nat.zero_add, hbefore]
    exact Nat.mul_le_mul_left n (by omega)
  · have hrzero :
        (SealedCloseProof.position ring i i).val = 0 := by
      have hh := sealed_close_nominated_position
        ring N i j a (.ready : SealedPhase n) ht.2.1 hready
      simpa [SealedPhaseEdge, SealedCloseProof.fromPhase,
        SealedCloseProof.nominated] using hh
    have htable :
        sealedCloseTable ring i a i (.ready : SealedPhase n) =
          .bullet true 1 := by
      have hapos : 0 < a := by
        have ha : 1 ≤ a := ht.2.1.1
        omega
      simp [sealedCloseTable, hrzero, hapos, hone,
        SealedCloseProof.fromPhase, SealedCloseProof.insideStage]
    by_cases hdel : TaggedDeleted i j k (nativeE ring N i)
    · have hzero := tagged_q_bellman_deleted_zero
        ring (nativeE ring N i) i j k a hdel
      rw [hzero, Nat.zero_add, hbefore]
      exact Nat.mul_le_mul_left n (by omega)
    · have hchild := tagged_short_attacker_child_credit
        ring i j k a N i ht .ready hready hdel
      have hvalue :
          taggedQBellman ring i j k a (nativeE ring N i) =
            n * (a - 1) := by
        simpa only [htable, taggedCloseCredit] using hchild
      calc
        taggedQBellman ring i j k a (nativeE ring N i) +
            n * (2 * a) =
          n * (a - 1) + n * (2 * a) := by rw [hvalue]
        _ = n * ((a - 1) + 2 * a) := by rw [Nat.mul_add]
        _ ≤ n * (3 * a - 1) :=
          Nat.mul_le_mul_left n (by omega)
        _ = taggedQBellman ring i j k a N := hbefore.symm

/-- The short-target restricted D.11 Bellman inequality is on the
real raw nativeE scheduler. There is no target-Q redirection. -/
theorem tagged_short_attack_bellman {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a : Nat)
    (N : TripleNativeState n)
    (hs : TaggedShortAttackGood ring i j k a N) :
    n + (List.ofFn (fun e : Fin n =>
        taggedQBellman ring i j k a (nativeE ring N e))).sum ≤
      n * taggedQBellman ring i j k a N := by
  let V := taggedQBellman ring i j k a
  let child : Fin n → Nat := fun e => V (nativeE ring N e)
  let phase := taggedQAttackerPhase ring i a N
  have hp : SealedPhaseHolds ring N i a phase :=
    tagged_q_attacker_phase_valid ring i a N hs.2.1
  by_cases hready : phase = .ready
  · have hphys : SealedCleanReady ring N i a := by
      show SealedPhaseHolds ring N i a .ready
      exact hready ▸ hp
    have ha : 1 ≤ a := hs.1.2.1.1
    have hOut : child i + n * (2 * a) ≤ V N :=
      tagged_short_ready_outgoing_drop
        ring i j k a N hs hphys
    have hIn : child (ring.leftNeighbor i) ≤
        V N + n * (2 * a - 1) :=
      (tagged_short_ready_child_bounds
        ring i j k a N (ring.leftNeighbor i)
        hs.1 hphys).1
    have hrest : ∀ e, e ≠ i →
        e ≠ ring.leftNeighbor i → child e ≤ V N := by
      intro e _ he
      exact (tagged_short_ready_child_bounds
        ring i j k a N e hs.1 hphys).2 he
    have hcoef : n + n * (2 * a - 1) ≤ n * (2 * a) := by
      have hh : (2 * a - 1) + 1 = 2 * a := by omega
      calc
        n + n * (2 * a - 1) =
          n * ((2 * a - 1) + 1) := by
            rw [Nat.mul_add]
            omega
        _ ≤ n * (2 * a) :=
          Nat.mul_le_mul_left n (Nat.le_of_eq hh)
    have hpair :
        n + child i + child (ring.leftNeighbor i) ≤
          2 * V N := by
      omega
    have hne : i ≠ ring.leftNeighbor i :=
      tagged_q_incident_edges_distinct
        (by omega : 2 ≤ n) ring i
    exact tagged_q_ready_sum_of_two_edge_bounds
      (V N) child i (ring.leftNeighbor i) hne
      hpair hrest
  · have hweak : ∀ e : Fin n, child e ≤ V N := by
      intro e
      exact (tagged_short_nonready_child_bounds
        ring i j k a N e hs phase hp hready).1
    have hstrict :
        child (SealedPhaseEdge ring i phase) + n ≤ V N :=
      (tagged_short_nonready_child_bounds
        ring i j k a N (SealedPhaseEdge ring i phase)
        hs phase hp hready).2 rfl
    exact tagged_q_drift_from_nominated_edge
      (V N) child (SealedPhaseEdge ring i phase)
      hweak hstrict

/-- A-Ready to actual tagged deletion costs at most n(3a-1),
without retries. This is the second half of the D.20 A clock. -/
theorem tagged_short_ready_attack_cost {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a : Nat)
    (N : TripleNativeState n)
    (ht : TaggedTriple ring i j k a 1 N)
    (hB : TaggedShortBPhase ring j N)
    (hA : SealedCleanReady ring N i a) :
    ∀ T,
      costNumerator (nativeE ring)
        (TaggedDeleted i j k) N T ≤
      n ^ T * (n * (3 * a - 1)) := by
  let Inv := TaggedShortAttackGood ring i j k a
  let V := taggedQBellman ring i j k a
  have hclosed :
      ∀ M, Inv M → ∀ e,
        ¬ TaggedDeleted i j k (nativeE ring M e) →
          Inv (nativeE ring M e) := by
    intro M hm e hnot
    exact tagged_short_attack_good_closed
      hn ring i j k a M hm e hnot
  have hdrift :
      ∀ M, Inv M → ¬ TaggedDeleted i j k M →
        n + (List.ofFn (fun e : Fin n =>
          V (nativeE ring M e))).sum ≤ n * V M := by
    intro M hm _
    exact tagged_short_attack_bellman
      hn ring i j k a M hm
  have hnot : ¬ TaggedDeleted i j k N :=
    tagged_d15_triple_not_deleted
      ring i j k a 1 N ht
  have hvalue : V N = n * (3 * a - 1) := by
    exact tagged_q_bellman_eq_phase
      ring N i j k a .ready hnot hA
  have hcost := tagged_q_restricted_cost_of_potential
    (nativeE ring) (TaggedDeleted i j k) Inv V
    hclosed hdrift N ⟨ht, sealed_of_clean_ready ring N i a hA, hB⟩
  intro T
  calc
    costNumerator (nativeE ring)
        (TaggedDeleted i j k) N T ≤ n ^ T * V N := hcost T
    _ = n ^ T * (n * (3 * a - 1)) := by rw [hvalue]




/-! ## Two actual first-hit preparations and one nonretry attack clock -/

/-- Independently prepare B from an arbitrary peaceful tagged triple
to Ready, preserving the native triple on the surviving branch.
For b=1 this costs 3*n, not 3*n*(a+1). -/
theorem tagged_short_target_prep_cost {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a : Nat)
    (N : TripleNativeState n)
    (ht : TaggedTriple ring i j k a 1 N) :
    ∀ T,
      costNumerator (nativeE ring)
        (fun M => (TaggedTriple ring i j k a 1 M ∧
          TaggedShortBPhase ring j M) ∨
          TaggedDeleted i j k M) N T ≤
      n ^ T * (3 * n) := by
  let Good : TripleNativeState n → Prop :=
    fun M => (TaggedTriple ring i j k a 1 M ∧
      TaggedShortBPhase ring j M) ∨
      TaggedDeleted i j k M
  have hclosed :
      ∀ M, TaggedTriple ring i j k a 1 M → ∀ e,
        ¬ Good (nativeE ring M e) →
          TaggedTriple ring i j k a 1 (nativeE ring M e) := by
    intro M hm e hnot
    have hsurvive : ¬ TaggedDeleted i j k (nativeE ring M e) := by
      intro hd
      exact hnot (Or.inr hd)
    exact tagged_triple_step_of_survival
      hn ring i j k a 1 M e hm hsurvive
  have htarget :
      ∀ M, TaggedTriple ring i j k a 1 M →
        SealedPrepTarget ring j k 1 M → Good M := by
    intro M hm hprep
    change (M j).l = false ∨ (M k).l = false ∨
      SealedCleanReady ring M j 1 at hprep
    rcases hprep with hj | hk | hr
    · exact Or.inr (Or.inr (Or.inl hj))
    · exact Or.inr (Or.inr (Or.inr hk))
    · exact Or.inl ⟨hm, Or.inl hr⟩
  have hcomp := tagged_cost_invariant_target_le
    (nativeE ring)
    (TaggedTriple ring i j k a 1)
    Good (SealedPrepTarget ring j k 1)
    hclosed htarget N ht
  have hclock :=
    (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (nativeE ring) (SealedPrepTarget ring j k 1)
      (by omega : 0 < n) N (3 * n * 1)).1
      (tagged_sealed_prep_expected_three
        hn ring j k 1
        (by omega : 0 < 1)
        (by omega : 1 < n)
        N ht.1 ht.2.2)
  intro T
  have hh := Nat.le_trans (hcomp T) (hclock T)
  simpa [Good, Nat.mul_one] using hh

/-- While B remains in its one-edge Ready/Dummy(0) family,
prepare A to Ready. Every selected edge retains B's actual
history state and the current triple unless a tagged leader dies. -/
theorem tagged_short_attacker_prep_cost {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a : Nat)
    (N : TripleNativeState n)
    (ht : TaggedTriple ring i j k a 1 N)
    (hB : TaggedShortBPhase ring j N) :
    ∀ T,
      costNumerator (nativeE ring)
        (fun M => (TaggedTriple ring i j k a 1 M ∧
          TaggedShortBPhase ring j M ∧
          SealedCleanReady ring M i a) ∨
          TaggedDeleted i j k M) N T ≤
      n ^ T * (3 * n * a) := by
  let Inv : TripleNativeState n → Prop :=
    fun M => TaggedTriple ring i j k a 1 M ∧
      TaggedShortBPhase ring j M
  let Good : TripleNativeState n → Prop :=
    fun M => (TaggedTriple ring i j k a 1 M ∧
      TaggedShortBPhase ring j M ∧
      SealedCleanReady ring M i a) ∨
      TaggedDeleted i j k M
  have hclosed : ∀ M, Inv M → ∀ e,
      ¬ Good (nativeE ring M e) →
        Inv (nativeE ring M e) := by
    intro M hm e hnot
    have hsurvive : ¬ TaggedDeleted i j k (nativeE ring M e) := by
      intro hd
      exact hnot (Or.inr hd)
    have ht' := tagged_triple_step_of_survival
      hn ring i j k a 1 M e hm.1 hsurvive
    have hB' := tagged_short_b_phase_step
      ring i j k a M hm.1 hm.2 e
    rcases hB' with hd | hgood
    · exact False.elim (hsurvive hd)
    · exact ⟨ht', hgood⟩
  have htarget : ∀ M, Inv M →
      SealedPrepTarget ring i j a M → Good M := by
    intro M hm hprep
    change (M i).l = false ∨ (M j).l = false ∨
      SealedCleanReady ring M i a at hprep
    rcases hprep with hi | hj | hready
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr (Or.inl hj))
    · exact Or.inl ⟨hm.1, hm.2, hready⟩
  have hcomp := tagged_cost_invariant_target_le
    (nativeE ring) Inv Good
    (SealedPrepTarget ring i j a)
    hclosed htarget N ⟨ht, hB⟩
  have hc : ConsecutiveNative ring N i j a := ht.2.1
  have hapos : 0 < a := by
    have ha : 1 ≤ a := hc.1
    omega
  have halt : a < n := hc.2.1
  have hclock :=
    (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (nativeE ring) (SealedPrepTarget ring i j a)
      (by omega : 0 < n) N (3 * n * a)).1
      (tagged_sealed_prep_expected_three
        hn ring i j a hapos halt N ht.1 hc)
  intro T
  exact Nat.le_trans (hcomp T) (hclock T)

/-- From an already prepared B=1, first prepare A (3*n*a),
then pay the exact A-Ready raw live-hit potential n(3a-1).
There are no geometric retries. -/
theorem tagged_short_after_target_cost {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a : Nat)
    (N : TripleNativeState n)
    (ht : TaggedTriple ring i j k a 1 N)
    (hB : TaggedShortBPhase ring j N) :
    ∀ T,
      costNumerator (nativeE ring)
        (TaggedDeleted i j k) N T ≤
      n ^ T * (3 * n * a + n * (3 * a - 1)) := by
  have hfirst :=
    tagged_short_attacker_prep_cost
      hn ring i j k a N ht hB
  have hsecond :
      ∀ M : TripleNativeState n,
        (TaggedTriple ring i j k a 1 M ∧
         TaggedShortBPhase ring j M ∧
         SealedCleanReady ring M i a) →
        ∀ T,
          costNumerator (nativeE ring)
            (TaggedDeleted i j k) M T ≤
          n ^ T * (n * (3 * a - 1)) := by
    intro M hm T
    exact tagged_short_ready_attack_cost
      hn ring i j k a M hm.1 hm.2.1 hm.2.2 T
  exact Prob.costNumerator_stage_le
    (nativeE ring) N
    (fun M => TaggedTriple ring i j k a 1 M ∧
      TaggedShortBPhase ring j M ∧
      SealedCleanReady ring M i a)
    (TaggedDeleted i j k)
    (3 * n * a) (n * (3 * a - 1))
    hfirst hsecond

/-- Paper D.20 directly: 3*n for the one-edge target,
3*n*a for attacker preparation, n(3a-1) for clean live hit.
The exact native scheduler and current event are used in each stage. -/
theorem tagged_short_native_cost {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a : Nat)
    (N : TripleNativeState n)
    (ht : TaggedTriple ring i j k a 1 N) :
    ∀ T,
      costNumerator (nativeE ring)
        (TaggedDeleted i j k) N T ≤
      n ^ T * (6 * n * (a + 1)) := by
  have hfirst :=
    tagged_short_target_prep_cost
      hn ring i j k a N ht
  have hsecond :
      ∀ M : TripleNativeState n,
        (TaggedTriple ring i j k a 1 M ∧
          TaggedShortBPhase ring j M) →
        ∀ T,
          costNumerator (nativeE ring)
            (TaggedDeleted i j k) M T ≤
          n ^ T * (3 * n * a + n * (3 * a - 1)) := by
    intro M hm T
    exact tagged_short_after_target_cost
      hn ring i j k a M hm.1 hm.2 T
  have hcombined := Prob.costNumerator_stage_le
    (nativeE ring) N
    (fun M => TaggedTriple ring i j k a 1 M ∧
      TaggedShortBPhase ring j M)
    (TaggedDeleted i j k)
    (3 * n) (3 * n * a + n * (3 * a - 1))
    hfirst hsecond
  have ha : 1 ≤ a := ht.2.1.1
  have hcoef :
      3 * n + (3 * n * a + n * (3 * a - 1)) ≤
        6 * n * (a + 1) := by
    have hscalar :
        3 + (3 * a + (3 * a - 1)) ≤ 6 * (a + 1) := by omega
    calc
      3 * n + (3 * n * a + n * (3 * a - 1)) =
          n * (3 + (3 * a + (3 * a - 1))) := by
        simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm]
      _ ≤ n * (6 * (a + 1)) :=
        Nat.mul_le_mul_left n hscalar
      _ = 6 * n * (a + 1) := by ac_rfl
  intro T
  exact Nat.le_trans (hcombined T)
    (Nat.mul_le_mul_left (n ^ T) hcoef)

/-- Exact hshort signature of tagged_deletion_cost_of_long_short:
the only regime premise is b=1, with no stage hypothesis. -/
theorem tagged_short_hshort {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (ht : TaggedTriple ring i j k a b N) :
    b = 1 → ∀ T,
      costNumerator (nativeE ring)
        (TaggedDeleted i j k) N T ≤
      n ^ T * (6 * n * (a + b)) := by
  intro hb T
  subst b
  exact tagged_short_native_cost hn ring i j k a N ht T

/-- Consequently the remaining D.9 all-regime proof now has only
the long-attacker physical clock as an explicit premise. -/
theorem tagged_deletion_cost_of_long {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (ht : TaggedTriple ring i j k a b N)
    (hlong : 2 ≤ b → 2 * b + 1 ≤ a → ∀ T,
      costNumerator (nativeE ring)
        (TaggedDeleted i j k) N T ≤
        n ^ T * (112 * n * (a + b))) :
    ∀ T,
      costNumerator (nativeE ring)
        (TaggedDeleted i j k) N T ≤
      n ^ T * taggedTripleCeiling n a b := by
  exact tagged_deletion_cost_of_long_short
    hn ring i j k a b N ht hlong
    (tagged_short_hshort hn ring i j k a b N ht)




/-! ## History-carrying, certified no-retry short attack monitor -/

/-- A native B-ready/dummy and A-ready cut, retaining its exact
literal native configuration as the seed rather than resetting. -/
structure TaggedShortAttemptSeed {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a : Nat) where
  N : TripleNativeState n
  triple : TaggedTriple ring i j k a 1 N
  attackerReady : SealedCleanReady ring N i a
  boundary : TaggedShortBPhase ring j N

/-- The entire attacker phase is carried through each real edge,
with B's actual one-edge phase invariant. -/
structure TaggedShortAttemptState {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a : Nat) where
  N : TripleNativeState n
  triple : TaggedTriple ring i j k a 1 N
  attackerPhase : SealedPhase n
  attackerHolds : SealedPhaseHolds ring N i a attackerPhase
  boundary : TaggedShortBPhase ring j N

def tagged_short_attempt_start {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a : Nat)
    (seed : TaggedShortAttemptSeed ring i j k a) :
    TaggedShortAttemptState ring i j k a :=
  { N := seed.N
    triple := seed.triple
    attackerPhase := .ready
    attackerHolds := seed.attackerReady
    boundary := seed.boundary }

/-- The certificate never has a retry leaf; a success leaf means
actual deletion on the same edge, and a surviving leaf preserves
the literal nativeE result with its real sector proofs. -/
noncomputable def tagged_short_attempt_step_certified {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a : Nat)
    (z : TaggedShortAttemptState ring i j k a)
    (e : Fin n) :
    { out : AttemptNode (TaggedShortAttemptState ring i j k a)
        (TaggedShortAttemptSeed ring i j k a) //
      match out with
      | .success => TaggedDeleted i j k (nativeE ring z.N e)
      | .active z' => z'.N = nativeE ring z.N e
      | .retry _ => False } := by
  let M := nativeE ring z.N e
  by_cases hd : TaggedDeleted i j k M
  · exact ⟨.success, hd⟩
  · have ht : TaggedTriple ring i j k a 1 M :=
      tagged_triple_step_of_survival
        hn ring i j k a 1 z.N e z.triple hd
    have hB := tagged_short_b_phase_step
      ring i j k a z.N z.triple z.boundary e
    have hB' : TaggedShortBPhase ring j M := by
      rcases hB with hdeleted | hphase
      · exact False.elim (hd hdeleted)
      · exact hphase
    have hstage :=
      tagged_short_attacker_child_stage
        ring i j k a z.N e z.triple
        z.attackerPhase z.attackerHolds hd
    obtain ⟨phase', hp', _⟩ :=
      Classical.indefiniteDescription _ hstage
    exact ⟨.active
      { N := M
        triple := ht
        attackerPhase := phase'
        attackerHolds := hp'
        boundary := hB' }, rfl⟩

noncomputable def tagged_short_attempt_step {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a : Nat)
    (z : TaggedShortAttemptState ring i j k a)
    (e : Fin n) :
    AttemptNode (TaggedShortAttemptState ring i j k a)
      (TaggedShortAttemptSeed ring i j k a) :=
  (tagged_short_attempt_step_certified hn ring i j k a z e).val

/-- The actual history monitor's success and live successors
are certified by its dependent step. -/
theorem tagged_short_attempt_step_sound {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a : Nat)
    (z : TaggedShortAttemptState ring i j k a)
    (e : Fin n) :
    match tagged_short_attempt_step hn ring i j k a z e with
    | .success => TaggedDeleted i j k (nativeE ring z.N e)
    | .active z' => z'.N = nativeE ring z.N e
    | .retry _ => False :=
  (tagged_short_attempt_step_certified hn ring i j k a z e).property

noncomputable def tagged_short_retry_kernel {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a : Nat) :
    RetryKernel (TaggedShortAttemptState ring i j k a)
      (TaggedShortAttemptSeed ring i j k a) n where
  start := tagged_short_attempt_start ring i j k a
  step := tagged_short_attempt_step hn ring i j k a
  valid := fun _ => True
  retry_valid := by
    intro z e seed hstep
    have hs := tagged_short_attempt_step_sound
      hn ring i j k a z e
    rw [hstep] at hs
    exact False.elim hs

def TaggedShortAttemptGood {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a : Nat)
    (z : TaggedShortAttemptState ring i j k a) : Prop :=
  TaggedShortAttackGood ring i j k a z.N

theorem tagged_short_attempt_good_closed {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a : Nat)
    (z z' : TaggedShortAttemptState ring i j k a)
    (e : Fin n)
    (_hg : TaggedShortAttemptGood ring i j k a z)
    (_hs : tagged_short_attempt_step hn ring i j k a z e =
      .active z') :
    TaggedShortAttemptGood ring i j k a z' :=
  ⟨z'.triple, ⟨z'.attackerPhase, z'.attackerHolds⟩,
    z'.boundary⟩

noncomputable def tagged_short_attempt_potential {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a : Nat)
    (z : TaggedShortAttemptState ring i j k a) : Nat :=
  taggedQBellman ring i j k a z.N

theorem tagged_short_attempt_child_potential {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a : Nat)
    (z : TaggedShortAttemptState ring i j k a)
    (e : Fin n) :
    taggedAttemptNodePotential
        (tagged_short_attempt_potential ring i j k a)
        (tagged_short_attempt_step hn ring i j k a z e) =
      taggedQBellman ring i j k a (nativeE ring z.N e) := by
  have hs := tagged_short_attempt_step_sound
    hn ring i j k a z e
  cases hstep : tagged_short_attempt_step
      hn ring i j k a z e with
  | success =>
      have hdel : TaggedDeleted i j k (nativeE ring z.N e) := by
        simpa only [hstep] using hs
      have hzero := tagged_q_bellman_deleted_zero
        ring (nativeE ring z.N e) i j k a hdel
      simp only [hstep, taggedAttemptNodePotential]
      exact hzero.symm
  | active z' =>
      have hphys : z'.N = nativeE ring z.N e := by
        simpa only [hstep] using hs
      change
        tagged_short_attempt_potential ring i j k a z' =
          taggedQBellman ring i j k a (nativeE ring z.N e)
      unfold tagged_short_attempt_potential
      rw [hphys]
  | retry seed =>
      have hbad : False := by
        simpa only [hstep] using hs
      exact False.elim hbad

theorem tagged_short_attempt_super {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a : Nat) :
    TaggedAttemptCostSuper
      (tagged_short_retry_kernel hn ring i j k a)
      (TaggedShortAttemptGood ring i j k a)
      (tagged_short_attempt_potential ring i j k a) := by
  intro z _
  have hphysical := tagged_short_attack_bellman
    hn ring i j k a z.N
    ⟨z.triple, ⟨z.attackerPhase, z.attackerHolds⟩,
      z.boundary⟩
  have hsum :
      (List.ofFn (fun e : Fin n =>
        taggedAttemptNodePotential
          (tagged_short_attempt_potential ring i j k a)
          (tagged_short_attempt_step hn ring i j k a z e))).sum =
      (List.ofFn (fun e : Fin n =>
        taggedQBellman ring i j k a
          (nativeE ring z.N e))).sum :=
    ofFn_sum_eq _ _ (fun e =>
      tagged_short_attempt_child_potential
        hn ring i j k a z e)
  change
    n + (List.ofFn (fun e : Fin n =>
      taggedAttemptNodePotential
        (tagged_short_attempt_potential ring i j k a)
        (tagged_short_attempt_step hn ring i j k a z e))).sum ≤
      n * tagged_short_attempt_potential ring i j k a z
  rw [hsum]
  exact hphysical

/-- The requested finite-horizon cost of the certified history kernel,
without renewal: every live branch is a native state, every terminal
is true deletion, and there is never a retry. -/
theorem tagged_short_attempt_finite_cost {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a : Nat)
    (seed : TaggedShortAttemptSeed ring i j k a)
    (T : Nat) :
    attemptCostNumerator
      (tagged_short_retry_kernel hn ring i j k a)
      (.active
        ((tagged_short_retry_kernel hn ring i j k a).start seed))
      T ≤ n ^ T * (n * (3 * a - 1)) := by
  let K := tagged_short_retry_kernel hn ring i j k a
  let P := tagged_short_attempt_potential ring i j k a
  have hclosed : ∀ z e z',
      TaggedShortAttemptGood ring i j k a z →
      K.step z e = .active z' →
        TaggedShortAttemptGood ring i j k a z' := by
    intro z e z' hg hs
    exact tagged_short_attempt_good_closed
      hn ring i j k a z z' e hg hs
  have hsuper := tagged_short_attempt_super hn ring i j k a
  have hstart : TaggedShortAttemptGood ring i j k a (K.start seed) :=
    ⟨seed.triple,
      ⟨(.ready : SealedPhase n), seed.attackerReady⟩,
      seed.boundary⟩
  have hcost := tagged_attempt_cost_numerator_le_of_super
    K (TaggedShortAttemptGood ring i j k a) P
    hclosed hsuper (K.start seed) hstart T
  have hnot : ¬ TaggedDeleted i j k seed.N :=
    tagged_d15_triple_not_deleted ring i j k a 1
      seed.N seed.triple
  have hvalue :
      P (K.start seed) = n * (3 * a - 1) := by
    exact tagged_q_bellman_eq_phase
      ring seed.N i j k a .ready hnot seed.attackerReady
  calc
    attemptCostNumerator K (.active (K.start seed)) T ≤
        n ^ T * P (K.start seed) := hcost
    _ = n ^ T * (n * (3 * a - 1)) := by rw [hvalue]





/-- This short history monitor never emits a retry leaf. Therefore
its exact finite-horizon first-retry mass vanishes at every state. -/
theorem tagged_short_attempt_retry_zero {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a : Nat) :
    ∀ (z : TaggedShortAttemptState ring i j k a) T,
      retryCount (tagged_short_retry_kernel hn ring i j k a)
        (.active z) T = 0 := by
  let K := tagged_short_retry_kernel hn ring i j k a
  intro z T
  induction T generalizing z with
  | zero => rfl
  | succ T ih =>
      change
        (List.ofFn (fun e : Fin n =>
          retryCount K (K.step z e) T)).sum = 0
      have hchild : ∀ e : Fin n,
          retryCount K (K.step z e) T = 0 := by
        intro e
        have hs := tagged_short_attempt_step_sound
          hn ring i j k a z e
        cases hnode : K.step z e with
        | success =>
            simp [retryCount]
        | active z' =>
            simpa only [retryCount] using ih z'
        | retry seed =>
            have hreal :
                tagged_short_attempt_step hn ring i j k a z e =
                  .retry seed := hnode
            rw [hreal] at hs
            exact False.elim hs
      rw [ofFn_sum_eq _ (fun _ : Fin n => 0) hchild,
        ofFn_sum_const]
      rfl

/-- Exact same-letter physical simulation of the short monitor.
Its native projection never changes a field and every success
means genuine tagged deletion. No retry restart is possible. -/
theorem tagged_short_attempt_native_simulation {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a : Nat) :
    Prob.RetrySimulation
      (tagged_short_retry_kernel hn ring i j k a)
      (nativeE ring) (TaggedDeleted i j k)
      (fun M z => z.N = M) := by
  intro M z hrel _ e
  have hs := tagged_short_attempt_step_sound
    hn ring i j k a z e
  cases hnode :
      (tagged_short_retry_kernel hn ring i j k a).step z e with
  | success =>
      have hreal :
          tagged_short_attempt_step hn ring i j k a z e =
            .success := hnode
      rw [hreal] at hs
      rw [hrel] at hs
      exact hs
  | active z' =>
      have hreal :
          tagged_short_attempt_step hn ring i j k a z e =
            .active z' := hnode
      rw [hreal] at hs
      rw [hrel] at hs
      exact hs
  | retry seed =>
      have hreal :
          tagged_short_attempt_step hn ring i j k a z e =
            .retry seed := hnode
      rw [hreal] at hs
      exact False.elim hs

/-! ## Long-attacker D.18–D.19: exact open physical interfaces -/

/-- The long observer's proof-only stage labels; every physical
interaction must still run nativeE on the same configuration. -/
inductive TaggedLongAttemptMode where
  | preparation
  | targetRace
  | incident
  | vulnerable
  | recovery
  deriving DecidableEq

structure TaggedLongAttemptSeed {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat) where
  N : TripleNativeState n
  triple : TaggedTriple ring i j k a b N

structure TaggedLongAttemptState {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat) where
  N : TripleNativeState n
  mode : TaggedLongAttemptMode
  triple : TaggedTriple ring i j k a b N
  attackerPhase : Option (SealedPhase n)
  targetPhase : Option (SealedPhase n)
  retainedOffset : Option (Fin n)

/-- Exact A live bullet with 2*b remaining hops to its next
leader j. This is the *physical* D.18 preparation endpoint;
it cannot be replaced by a numerical countdown. -/
def TaggedLongRetained {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n) : Prop :=
  TaggedTriple ring i j k a b N ∧
    Sealed ring N j b ∧
    ∃ p : Fin n,
      SealedPhaseHolds ring N i a (.live p) ∧
        p.val + 2 * b = a

/-- A live attacker has no more than 2*b remaining hops.
The target remains sealed, and on survival the live bullet
must be retained rather than silently replaced by a dummy. -/
def TaggedLongNear {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n) : Prop :=
  TaggedTriple ring i j k a b N ∧
    Sealed ring N j b ∧
    ∃ p : Fin n,
      SealedPhaseHolds ring N i a (.live p) ∧
        a ≤ p.val + 2 * b


/-- Real first B-Ready preparation from an arbitrary peaceful
triple, stopping immediately at any tagged deletion. -/
theorem tagged_long_target_ready_prep_cost {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (ht : TaggedTriple ring i j k a b N) :
    ∀ T,
      costNumerator (nativeE ring)
        (fun M => (TaggedTriple ring i j k a b M ∧
          SealedCleanReady ring M j b) ∨
          TaggedDeleted i j k M) N T ≤
      n ^ T * (3 * n * b) := by
  let Good : TripleNativeState n → Prop :=
    fun M => (TaggedTriple ring i j k a b M ∧
      SealedCleanReady ring M j b) ∨
      TaggedDeleted i j k M
  have hclosed :
      ∀ M, TaggedTriple ring i j k a b M → ∀ e,
        ¬ Good (nativeE ring M e) →
          TaggedTriple ring i j k a b (nativeE ring M e) := by
    intro M hm e hnot
    have hsurvive : ¬ TaggedDeleted i j k (nativeE ring M e) := by
      intro hd
      exact hnot (Or.inr hd)
    exact tagged_triple_step_of_survival
      hn ring i j k a b M e hm hsurvive
  have htarget :
      ∀ M, TaggedTriple ring i j k a b M →
        SealedPrepTarget ring j k b M → Good M := by
    intro M hm hprep
    change (M j).l = false ∨ (M k).l = false ∨
      SealedCleanReady ring M j b at hprep
    rcases hprep with hj | hk | hr
    · exact Or.inr (Or.inr (Or.inl hj))
    · exact Or.inr (Or.inr (Or.inr hk))
    · exact Or.inl ⟨hm, hr⟩
  have hcomp := tagged_cost_invariant_target_le
    (nativeE ring)
    (TaggedTriple ring i j k a b)
    Good (SealedPrepTarget ring j k b)
    hclosed htarget N ht
  have hc : ConsecutiveNative ring N j k b := ht.2.2
  have hbpos : 0 < b := by
    have hb : 1 ≤ b := hc.1
    omega
  have hblt : b < n := hc.2.1
  have hclock :=
    (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (nativeE ring) (SealedPrepTarget ring j k b)
      (by omega : 0 < n) N (3 * n * b)).1
      (tagged_sealed_prep_expected_three
        hn ring j k b hbpos hblt N ht.1 hc)
  intro T
  exact Nat.le_trans (hcomp T) (hclock T)

/-- After B-Ready, A can be prepared at cost 3*n*a while B
remains Sealed, without any assumption that B stays Ready. -/
theorem tagged_long_attacker_ready_prep_cost {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (ht : TaggedTriple ring i j k a b N)
    (hB : Sealed ring N j b) :
    ∀ T,
      costNumerator (nativeE ring)
        (fun M => (TaggedTriple ring i j k a b M ∧
          Sealed ring M j b ∧
          SealedCleanReady ring M i a) ∨
          TaggedDeleted i j k M) N T ≤
      n ^ T * (3 * n * a) := by
  let Inv : TripleNativeState n → Prop :=
    fun M => TaggedTriple ring i j k a b M ∧
      Sealed ring M j b
  let Good : TripleNativeState n → Prop :=
    fun M => (TaggedTriple ring i j k a b M ∧
      Sealed ring M j b ∧
      SealedCleanReady ring M i a) ∨
      TaggedDeleted i j k M
  have hclosed : ∀ M, Inv M → ∀ e,
      ¬ Good (nativeE ring M e) →
        Inv (nativeE ring M e) := by
    intro M hm e hnot
    have hsurvive : ¬ TaggedDeleted i j k (nativeE ring M e) := by
      intro hd
      exact hnot (Or.inr hd)
    have ht' := tagged_triple_step_of_survival
      hn ring i j k a b M e hm.1 hsurvive
    have hBstep := sealed_all_edge_closed
      ring M j k b e hm.1.2.2 hm.2
    rcases hBstep with hj | hk | hsealed
    · exact False.elim (hsurvive (Or.inr (Or.inl hj)))
    · exact False.elim (hsurvive (Or.inr (Or.inr hk)))
    · exact ⟨ht', hsealed⟩
  have htarget : ∀ M, Inv M →
      SealedPrepTarget ring i j a M → Good M := by
    intro M hm hprep
    change (M i).l = false ∨ (M j).l = false ∨
      SealedCleanReady ring M i a at hprep
    rcases hprep with hi | hj | hready
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr (Or.inl hj))
    · exact Or.inl ⟨hm.1, hm.2, hready⟩
  have hcomp := tagged_cost_invariant_target_le
    (nativeE ring) Inv Good
    (SealedPrepTarget ring i j a)
    hclosed htarget N ⟨ht, hB⟩
  have hc : ConsecutiveNative ring N i j a := ht.2.1
  have hapos : 0 < a := by
    have ha : 1 ≤ a := hc.1
    omega
  have halt : a < n := hc.2.1
  have hclock :=
    (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (nativeE ring) (SealedPrepTarget ring i j a)
      (by omega : 0 < n) N (3 * n * a)).1
      (tagged_sealed_prep_expected_three
        hn ring i j a hapos halt N ht.1 hc)
  intro T
  exact Nat.le_trans (hcomp T) (hclock T)

/-- The exact reversed D.18 first-stage preparation cost:
B-Ready first, A-Ready second; B remains sealed. -/
theorem tagged_long_two_sector_prep_cost {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (ht : TaggedTriple ring i j k a b N) :
    ∀ T,
      costNumerator (nativeE ring)
        (fun M => (TaggedTriple ring i j k a b M ∧
          Sealed ring M j b ∧
          SealedCleanReady ring M i a) ∨
          TaggedDeleted i j k M) N T ≤
      n ^ T * (3 * n * (a + b)) := by
  let Prepared : TripleNativeState n → Prop :=
    fun M => TaggedTriple ring i j k a b M ∧
      SealedCleanReady ring M j b
  let Finish : TripleNativeState n → Prop :=
    fun M => (TaggedTriple ring i j k a b M ∧
      Sealed ring M j b ∧
      SealedCleanReady ring M i a) ∨
      TaggedDeleted i j k M
  have hfirstRaw :=
    tagged_long_target_ready_prep_cost
      hn ring i j k a b N ht
  have hfirst : ∀ T,
      costNumerator (nativeE ring)
        (fun M => Prepared M ∨ Finish M) N T ≤
        n ^ T * (3 * n * b) := by
    intro T
    have hsubset : ∀ M,
        (Prepared M ∨ TaggedDeleted i j k M) →
          (Prepared M ∨ Finish M) := by
      intro M hm
      rcases hm with hp | hd
      · exact Or.inl hp
      · exact Or.inr (Or.inr hd)
    exact Nat.le_trans
      (Prob.costNumerator_target_mono
        (nativeE ring)
        (fun M => Prepared M ∨ TaggedDeleted i j k M)
        (fun M => Prepared M ∨ Finish M)
        hsubset N T)
      (hfirstRaw T)
  have hsecond : ∀ M, Prepared M → ∀ T,
      costNumerator (nativeE ring) Finish M T ≤
        n ^ T * (3 * n * a) := by
    intro M hm T
    exact tagged_long_attacker_ready_prep_cost
      hn ring i j k a b M hm.1
      (sealed_of_clean_ready ring M j b hm.2) T
  have hcombined := Prob.costNumerator_stage_le
    (nativeE ring) N
    Prepared Finish
    (3 * n * b) (3 * n * a)
    hfirst hsecond
  intro T
  calc
    costNumerator (nativeE ring) Finish N T ≤
        n ^ T * (3 * n * b + 3 * n * a) := hcombined T
    _ = n ^ T * (3 * n * (a + b)) := by
      have hcoef :
          3 * n * b + 3 * n * a =
            3 * n * (a + b) := by
        rw [Nat.mul_add]
        omega
      rw [hcoef]

/-- First missing physical subclock of D.18: after both sectors
have been prepared in the B-first order, obtain an actual outgoing
A-Live firing, then move its unique bullet to exactly 2*b hops
from j. The incoming-dummy recovery loops must be paid here.
This is a named OPEN Prop, not a theorem or an axiom. -/
def TaggedLongLaunchAdvanceClock {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat) : Prop :=
  2 ≤ b → 2 * b + 1 ≤ a →
  ∀ N : TripleNativeState n,
    TaggedTriple ring i j k a b N →
    Sealed ring N j b →
    SealedCleanReady ring N i a →
    ∀ T,
      costNumerator (nativeE ring)
        (fun M => TaggedDeleted i j k M ∨
          TaggedLongRetained ring i j k a b M) N T ≤
        n ^ T * (n * (2 * a + (a - 1 - 2 * b)))

/-- Clock 1 (D.18), currently OPEN: from any peaceful tagged
triple, reach an actual retained A-Live front with exactly 2*b
hops remaining, or delete a tag, within n*(6*a+b).
The target B must be sealed at this endpoint. -/
def TaggedLongPreparationClock {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat) : Prop :=
  2 ≤ b → 2 * b + 1 ≤ a →
  ∀ N : TripleNativeState n,
    TaggedTriple ring i j k a b N →
    ∀ T,
      costNumerator (nativeE ring)
        (fun M => TaggedDeleted i j k M ∨
          TaggedLongRetained ring i j k a b M) N T ≤
        n ^ T * (n * (6 * a + b))

/-- The genuine first-expiring-front race. The attacker loses
if its live front is no longer retained before B is Ready.
A tagged deletion always stops beneficially and takes priority. -/
noncomputable def tagged_long_race_step {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n) (e : Fin n) :
    StopNode (TripleNativeState n) := by
  classical
  let M := nativeE ring N e
  exact
    if TaggedDeleted i j k M then .success
    else if ¬ TaggedLongNear ring i j k a b M then .failure
    else if SealedCleanReady ring M j b then .success
    else .active M

noncomputable def tagged_long_race_start {n : Nat}
    (ring : DirectedRing n) (j : Fin n) (b : Nat)
    (N : TripleNativeState n) :
    StopNode (TripleNativeState n) := by
  classical
  exact if SealedCleanReady ring N j b then .success
    else .active N

/-- Clock 2 (D.18–D.19), OPEN: physical two-front race.
The ≤1/2 finite-horizon failure-cylinder bound is the
adapted version of the fair 2*b-vs-2*b progress race. -/
def TaggedLongRaceClock {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat) : Prop :=
  ∀ N : TripleNativeState n,
    TaggedLongRetained ring i j k a b N →
    ∀ T,
      truncatedActiveCostNumerator
        (tagged_long_race_step ring i j k a b)
        (tagged_long_race_start ring j b N) T ≤
          n ^ T * (n * (2 * b - 1)) ∧
      2 * failureCount (tagged_long_race_step ring i j k a b)
        (tagged_long_race_start ring j b N) T ≤ n ^ T

/-- First outgoing/incoming service at j. The actual service is
applied before the stage outcome is classified. A genuine tagged
deletion wins over the outgoing-failure classification. -/
noncomputable def tagged_long_incident_step {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n)
    (N : TripleNativeState n) (e : Fin n) :
    StopNode (TripleNativeState n) := by
  classical
  let M := nativeE ring N e
  exact
    if TaggedDeleted i j k M then .success
    else if e = ring.leftNeighbor j then .success
    else if e = j then .failure
    else .active M

/-- Clock 3 (D.19), OPEN as a physical stage: expected first
incident service ≤n (a safe integer allowance instead of n/2),
outgoing-first mass ≤1/2. The winning incoming edge must further
certify actual Dummy(0) or deletion and retain the A live front. -/
def TaggedLongIncidentClock {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat) : Prop :=
  ∀ N : TripleNativeState n,
    TaggedLongNear ring i j k a b N →
    SealedCleanReady ring N j b →
    ∀ T,
      truncatedActiveCostNumerator
        (tagged_long_incident_step ring i j k)
        (.active N) T ≤ n ^ T * n ∧
      2 * failureCount (tagged_long_incident_step ring i j k)
        (.active N) T ≤ n ^ T

/-- Clock 4 (D.19), OPEN: the retained attacker now has at most
2*b hops and target B is actual Dummy(0). The controlled clock
must be ≤2*n*b and the ordinary raw vulnerable trial's completed
failure cylinders ≤3/4. These are separate facts, not assumed
independence of the two progress fronts. -/
def TaggedLongVulnerableClock {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat) : Prop :=
  ∀ N : TripleNativeState n,
    TaggedLongNear ring i j k a b N →
    TaggedCleanDummy ring i j a b N →
    ∀ T,
      costNumerator
        (taggedQNext ring j b (by omega : 2 ≤ n)
          (Ne.symm (tagged_q_incident_edges_distinct
            (by omega : 2 ≤ n) ring j)))
        (TaggedDeleted i j k) N T ≤
          n ^ T * (n * (2 * b)) ∧
      4 * failureCount
        (taggedTrialStep ring i j k b) (.active N) T ≤
          3 * n ^ T

/-- Sum of D.18's separate real preparation clocks.
The actual live-firing and retained-front witnesses are still
required to turn this arithmetic into TaggedLongPreparationClock. -/
theorem tagged_long_preparation_arithmetic
    (n a b : Nat) (hab : 2 * b + 1 ≤ a) :
    3 * n * (a + b) + 2 * n * a +
      n * (a - 1 - 2 * b) ≤ n * (6 * a + b) := by
  have hscalar :
      3 * (a + b) + 2 * a + (a - 1 - 2 * b) ≤
        6 * a + b := by
    omega
  calc
    3 * n * (a + b) + 2 * n * a +
        n * (a - 1 - 2 * b) =
        n * (3 * (a + b) + 2 * a +
          (a - 1 - 2 * b)) := by
      simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm]
    _ ≤ n * (6 * a + b) := Nat.mul_le_mul_left n hscalar

/-- The complete D.18 preparation clock follows from precisely
one missing physical subclock: native live launch and advancement
from the B-sealed/A-Ready cut. Both sector preparations are already
proved without looking ahead at the race outcome. -/
theorem tagged_long_preparation_of_launch_clock {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hLaunch : TaggedLongLaunchAdvanceClock ring i j k a b) :
    TaggedLongPreparationClock ring i j k a b := by
  intro hb hab N ht T
  let Prepared : TripleNativeState n → Prop :=
    fun M => TaggedTriple ring i j k a b M ∧
      Sealed ring M j b ∧ SealedCleanReady ring M i a
  let Goal : TripleNativeState n → Prop :=
    fun M => TaggedDeleted i j k M ∨
      TaggedLongRetained ring i j k a b M
  have hfirst : ∀ U,
      costNumerator (nativeE ring)
        (fun M => Prepared M ∨ Goal M) N U ≤
      n ^ U * (3 * n * (a + b)) := by
    intro U
    have hsubset : ∀ M,
        (Prepared M ∨ TaggedDeleted i j k M) →
          (Prepared M ∨ Goal M) := by
      intro M hm
      rcases hm with hp | hd
      · exact Or.inl hp
      · exact Or.inr (Or.inl hd)
    exact Nat.le_trans
      (Prob.costNumerator_target_mono
        (nativeE ring)
        (fun M => Prepared M ∨ TaggedDeleted i j k M)
        (fun M => Prepared M ∨ Goal M)
        hsubset N U)
      (tagged_long_two_sector_prep_cost
        hn ring i j k a b N ht U)
  have hsecond : ∀ M, Prepared M → ∀ U,
      costNumerator (nativeE ring) Goal M U ≤
      n ^ U * (n * (2 * a + (a - 1 - 2 * b))) := by
    intro M hm U
    exact hLaunch hb hab M hm.1 hm.2.1 hm.2.2 U
  have hcombined := Prob.costNumerator_stage_le
    (nativeE ring) N
    Prepared Goal
    (3 * n * (a + b))
    (n * (2 * a + (a - 1 - 2 * b)))
    hfirst hsecond
  have hcoeff :
      3 * n * (a + b) +
          n * (2 * a + (a - 1 - 2 * b)) ≤
        n * (6 * a + b) := by
    calc
      3 * n * (a + b) +
            n * (2 * a + (a - 1 - 2 * b)) =
          3 * n * (a + b) + 2 * n * a +
            n * (a - 1 - 2 * b) := by
        simp only [Nat.mul_add]
        ac_rfl
      _ ≤ n * (6 * a + b) :=
        tagged_long_preparation_arithmetic n a b hab
  exact Nat.le_trans (hcombined T)
    (Nat.mul_le_mul_left (n ^ T) hcoeff)

/-- With a whole n-unit incident allowance (instead of paper n/2),
the four long stage budgets and postfailure B recovery still fit
under 7*n*(a+b). This is an unconditional arithmetic certificate. -/
theorem tagged_long_attempt_budget
    (n a b : Nat) (ha : 1 ≤ a) (hb : 2 ≤ b) :
    n * (6 * a + b) + n * (2 * b - 1) + n +
      n * (2 * b) + n * (2 * b - 2) ≤
        7 * n * (a + b) := by
  have hscalar :
      (6 * a + b) + (2 * b - 1) + 1 +
        (2 * b) + (2 * b - 2) ≤
        7 * (a + b) := by
    omega
  calc
    n * (6 * a + b) + n * (2 * b - 1) + n +
        n * (2 * b) + n * (2 * b - 2) =
      n * ((6 * a + b) + (2 * b - 1) + 1 +
        (2 * b) + (2 * b - 2)) := by
      simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm]
    _ ≤ n * (7 * (a + b)) := Nat.mul_le_mul_left n hscalar
    _ = 7 * n * (a + b) := by ac_rfl

/-- An explicit, non-axiomatic interface for the missing *actual*
long-attempt kernel. The success and retry clauses must be proved
against nativeE; a history observer cannot reset N at a restart.
The four OPEN clocks above are the intended physical producers. -/
def TaggedLongNativeAttemptMachine {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat) : Prop :=
  ∃ K : RetryKernel
      (TaggedLongAttemptState ring i j k a b)
      (TaggedLongAttemptSeed ring i j k a b) n,
    (∀ s : TaggedLongAttemptSeed ring i j k a b, K.valid s) ∧
    (∀ s : TaggedLongAttemptSeed ring i j k a b,
      (K.start s).N = s.N) ∧
    Prob.RetrySimulation K (nativeE ring) (TaggedDeleted i j k)
      (fun M z => z.N = M) ∧
    (∀ s : TaggedLongAttemptSeed ring i j k a b,
      K.valid s → ∀ T,
        attemptCostNumerator K (.active (K.start s)) T ≤
          n ^ T * (7 * n * (a + b))) ∧
    (∀ s : TaggedLongAttemptSeed ring i j k a b,
      K.valid s → ∀ T,
        16 * retryCount K (.active (K.start s)) T ≤
          15 * n ^ T)

/-- Once the explicit native long-attempt machine is constructed
(and NOT merely assumed hidden in the paper), the exact renewal
API gives D.19 at its required factor 112. -/
theorem tagged_long_cost_of_machine {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hMachine : TaggedLongNativeAttemptMachine ring i j k a b)
    (N : TripleNativeState n)
    (ht : TaggedTriple ring i j k a b N) :
    ∀ T,
      costNumerator (nativeE ring) (TaggedDeleted i j k) N T ≤
        n ^ T * (112 * n * (a + b)) := by
  obtain ⟨K, hvalid, hstart, hsim, hcost, hretry⟩ := hMachine
  let B := 7 * n * (a + b)
  have hc :
      ∀ seed : TaggedLongAttemptSeed ring i j k a b,
        K.valid seed → ∀ T,
          costNumerator (Prob.attemptStepper K)
            (fun z => Prob.attemptGood z ∨ Prob.attemptFail z)
            (.active (K.start seed)) T ≤ n ^ T * B := by
    intro seed hs T
    simpa only [Prob.attempt_costNumerator_eq] using
      (hcost seed hs T)
  have hr :
      ∀ seed : TaggedLongAttemptSeed ring i j k a b,
        K.valid seed → ∀ T,
          16 * retryCount K (.active (K.start seed)) T ≤
            15 * n ^ T := hretry
  let seed : TaggedLongAttemptSeed ring i j k a b :=
    { N := N, triple := ht }
  have hrel : (K.start seed).N = N :=
    hstart seed
  have hceil : Prob.renewalCeiling B 15 16 = 16 * B := by
    simp [Prob.renewalCeiling, Prob.ceilNat,
      Nat.mod_one, Nat.mul_comm]
  have hresult := Prob.costNumerator_renewal_le
    (nativeE ring) (TaggedDeleted i j k)
    K (fun M z => z.N = M) hsim
    B 15 16 (by decide) hc hr
    N seed (hvalid seed) hrel
  intro T
  calc
    costNumerator (nativeE ring) (TaggedDeleted i j k) N T ≤
        n ^ T * Prob.renewalCeiling B 15 16 :=
      hresult T
    _ = n ^ T * (112 * n * (a + b)) := by
      rw [hceil]
      dsimp [B]
      have hcoeff : 16 * 7 = 112 := by decide
      calc
        n ^ T * (16 * (7 * n * (a + b))) =
            n ^ T * ((16 * 7) * n * (a + b)) := by ac_rfl
        _ = n ^ T * (112 * n * (a + b)) := by rw [hcoeff]




/-! ## D.18 literal first live firing and minimal-gap retained endpoint -/

/-- From a real A-Ready cut in the long regime, the physical
outgoing edge i either deletes one of the actual tagged leaders
or produces a sealed live bullet at offset one. This is the
native first-letter producer, not a synthetic restart. -/
theorem tagged_long_ready_outgoing_live {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (ha : 2 ≤ a)
    (N : TripleNativeState n)
    (ht : TaggedTriple ring i j k a b N)
    (hB : Sealed ring N j b)
    (hA : SealedCleanReady ring N i a) :
    TaggedDeleted i j k (nativeE ring N i) ∨
      (TaggedTriple ring i j k a b (nativeE ring N i) ∧
       Sealed ring (nativeE ring N i) j b ∧
       ∃ p : Fin n, p.val = 1 ∧
         SealedPhaseHolds ring (nativeE ring N i) i a (.live p)) := by
  let M := nativeE ring N i
  by_cases hdel : TaggedDeleted i j k M
  · exact Or.inl hdel
  · have ht' : TaggedTriple ring i j k a b M :=
      tagged_triple_step_of_survival
        hn ring i j k a b N i ht hdel
    have hsealed : TaggedSealed ring i j a b M :=
      tagged_sealed_step_of_survival
        ring i j k a b N i ht
        ⟨sealed_of_clean_ready ring N i a hA, hB⟩ hdel
    have hi : (M i).l = true := by
      cases hx : (M i).l with
      | false => exact False.elim (hdel (Or.inl hx))
      | true => rfl
    have hj : (M j).l = true := by
      cases hx : (M j).l with
      | false => exact False.elim (hdel (Or.inr (Or.inl hx)))
      | true => rfl
    obtain ⟨phase, hp, hstage⟩ :=
      sealed_close_step_stage ring N i j a i
        (.ready : SealedPhase n) ht.2.1 hA hi hj
    have hrzero :
        (SealedCloseProof.position ring i i).val = 0 := by
      have hh := sealed_close_nominated_position
        ring N i j a (.ready : SealedPhase n) ht.2.1 hA
      simpa [SealedPhaseEdge, SealedCloseProof.fromPhase,
        SealedCloseProof.nominated] using hh
    have hapos : 0 < a := by omega
    have hone : a ≠ 1 := by omega
    have htable :
        sealedCloseTable ring i a i (.ready : SealedPhase n) =
          .bullet true 1 := by
      simp [sealedCloseTable, hrzero, hapos, hone,
        SealedCloseProof.fromPhase, SealedCloseProof.insideStage]
    have hStage :
        SealedCloseProof.fromPhase phase = .bullet true 1 :=
      hstage.trans htable
    cases phase with
    | ready =>
        cases hStage
    | dummy p =>
        cases hStage
    | live p =>
        have hpval : p.val = 1 := by
          have hnom := congrArg SealedCloseProof.nominated hStage
          simpa only [SealedCloseProof.fromPhase,
            SealedCloseProof.nominated] using hnom
        exact Or.inr ⟨ht', hsealed.2, p, hpval, hp⟩
    | returning q =>
        cases hStage

/-- At the shortest long gap a=2b+1, the first genuine
A-Ready outgoing firing already produces the precise D.18
retained-front endpoint (unless it deletes a tag first). -/
theorem tagged_long_minimal_gap_retained {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hb : 2 ≤ b) (hab : a = 2 * b + 1)
    (N : TripleNativeState n)
    (ht : TaggedTriple ring i j k a b N)
    (hB : Sealed ring N j b)
    (hA : SealedCleanReady ring N i a) :
    TaggedDeleted i j k (nativeE ring N i) ∨
      TaggedLongRetained ring i j k a b (nativeE ring N i) := by
  have ha : 2 ≤ a := by omega
  rcases tagged_long_ready_outgoing_live
      hn ring i j k a b ha N ht hB hA with
    hdel | ⟨ht', hsealed, p, hpval, hphase⟩
  · exact Or.inl hdel
  · exact Or.inr ⟨ht', hsealed, p, hphase, by omega⟩

end L3


/-! ## Physical D.18 live-front progression, raw native E

The lemmas below concern an
actual sealed A-live bullet at an offset strictly before its retained
front; no ghost move, edge redirection, or assumed future encounter.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
attribute [local instance low] Classical.propDecidable

set_option autoImplicit false
set_option Elab.async false

/-- The raw SealedClose table says that a nonterminal live bullet
either advances one site on its uniquely nominated physical edge
or stays at its physical offset on every other edge. -/
theorem tagged_long_live_step_table
    (n a p r : Nat) (hp : p + 1 < a) :
    (if r < a then
      SealedCloseProof.insideStage a (.bullet true p) r
     else if r + 1 = n then
      SealedCloseProof.incomingStage (.bullet true p)
     else .bullet true p) =
        .bullet true (if r = p then p + 1 else p) := by
  by_cases hre : r = p
  · subst r
    have hlt : p < a := by omega
    have hlast : p + 1 ≠ a := by omega
    simp [hlt, hlast, SealedCloseProof.insideStage]
  · by_cases hr : r < a
    · simp [hr, hre, SealedCloseProof.insideStage]
    · simp [hr, hre, SealedCloseProof.incomingStage]

/-- On every surviving *actual* native step, an A-live bullet
whose remaining distance is at least 2b retains its identity,
and its position either stays fixed or advances by exactly one.
The latter happens exactly at its nominated physical edge.
Both tagged sectors and the original triple survive as stated. -/
theorem tagged_long_live_physical_step {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hb : 2 ≤ b)
    (N : TripleNativeState n) (e : Fin n)
    (ht : TaggedTriple ring i j k a b N)
    (hB : Sealed ring N j b)
    (p : Fin n)
    (hA : SealedPhaseHolds ring N i a (.live p))
    (hfar : p.val + 2 * b ≤ a)
    (hnot : ¬ TaggedDeleted i j k (nativeE ring N e)) :
    ∃ q : Fin n,
      SealedPhaseHolds ring (nativeE ring N e) i a (.live q) ∧
      (q.val =
        if e = SealedPhaseEdge ring i (.live p) then
          p.val + 1 else p.val) ∧
      TaggedTriple ring i j k a b (nativeE ring N e) ∧
      Sealed ring (nativeE ring N e) j b := by
  let M := nativeE ring N e
  let r := SealedCloseProof.position ring i e
  have hprogress : p.val + 1 < a := by omega
  have ht' : TaggedTriple ring i j k a b M :=
    tagged_triple_step_of_survival
      hn ring i j k a b N e ht hnot
  have hsealed :=
    tagged_sealed_step_of_survival
      ring i j k a b N e ht
      ⟨⟨.live p, hA⟩, hB⟩ hnot
  have hi : (M i).l = true := by
    cases hx : (M i).l with
    | false => exact False.elim (hnot (Or.inl hx))
    | true => rfl
  have hj : (M j).l = true := by
    cases hx : (M j).l with
    | false => exact False.elim (hnot (Or.inr (Or.inl hx)))
    | true => rfl
  obtain ⟨nextPhase, hnext, hstage⟩ :=
    sealed_close_step_stage
      ring N i j a e (.live p) ht.2.1 hA hi hj
  have htable :
      sealedCloseTable ring i a e (.live p) =
        .bullet true (if r.val = p.val then
          p.val + 1 else p.val) := by
    change
      (if r.val < a then
        SealedCloseProof.insideStage a (.bullet true p.val) r.val
       else if r.val + 1 = n then
        SealedCloseProof.incomingStage (.bullet true p.val)
       else .bullet true p.val) =
          .bullet true (if r.val = p.val then
            p.val + 1 else p.val)
    exact tagged_long_live_step_table n a p.val r.val hprogress
  have hnomPosition :
      (SealedCloseProof.position ring i
        (SealedPhaseEdge ring i (.live p))).val = p.val := by
    have hh := sealed_close_nominated_position
      ring N i j a (.live p) ht.2.1 hA
    simpa only [SealedCloseProof.fromPhase,
      SealedCloseProof.nominated] using hh
  have hport :
      (r.val = p.val) ↔
        e = SealedPhaseEdge ring i (.live p) := by
    constructor
    · intro he
      calc
        e = sealedSite ring i r.val :=
          sealed_close_edge_of_position ring i e r.val rfl
        _ = sealedSite ring i p.val := by rw [he]
        _ = SealedPhaseEdge ring i (.live p) := rfl
    · intro he
      change (SealedCloseProof.position ring i e).val = p.val
      rw [he]
      exact hnomPosition
  have hstage' :
      SealedCloseProof.fromPhase nextPhase =
        .bullet true (if r.val = p.val then
          p.val + 1 else p.val) := hstage.trans htable
  cases nextPhase with
  | ready =>
      cases hstage'
  | dummy q =>
      cases hstage'
  | live q =>
      have hqval :
          q.val = if r.val = p.val then p.val + 1 else p.val := by
        have hh := congrArg SealedCloseProof.nominated hstage'
        simpa only [SealedCloseProof.fromPhase,
          SealedCloseProof.nominated] using hh
      refine ⟨q, hnext, ?_, ht', hsealed.2⟩
      by_cases he : e = SealedPhaseEdge ring i (.live p)
      · have hr : r.val = p.val := hport.mpr he
        simpa only [if_pos he, if_pos hr] using hqval
      · have hr : r.val ≠ p.val := by
          intro heq
          exact he (hport.mp heq)
        simpa only [if_neg he, if_neg hr] using hqval
  | returning q =>
      cases hstage'

/-- Physical final advance to the retained front. The nominated
edge either deletes a tagged leader or makes the A-live bullet
exactly 2b hops from j; this works even for i=k. -/
theorem tagged_long_live_last_advance {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hb : 2 ≤ b)
    (N : TripleNativeState n)
    (ht : TaggedTriple ring i j k a b N)
    (hB : Sealed ring N j b)
    (p : Fin n)
    (hA : SealedPhaseHolds ring N i a (.live p))
    (hlast : p.val + 1 + 2 * b = a) :
    TaggedDeleted i j k
        (nativeE ring N (SealedPhaseEdge ring i (.live p))) ∨
      TaggedLongRetained ring i j k a b
        (nativeE ring N (SealedPhaseEdge ring i (.live p))) := by
  let e := SealedPhaseEdge ring i (.live p)
  let M := nativeE ring N e
  by_cases hdel : TaggedDeleted i j k M
  · exact Or.inl hdel
  · have hfar : p.val + 2 * b ≤ a := by omega
    obtain ⟨q, hq, hposition, htriple, hB'⟩ :=
      tagged_long_live_physical_step
        hn ring i j k a b hb N e ht hB p hA hfar hdel
    have hqpos : q.val = p.val + 1 := by
      simpa only [e, if_pos rfl, ↓reduceIte] using hposition
    exact Or.inr ⟨htriple, hB', q, hq, by omega⟩


/-! ### The finite-horizon live-front travel clock -/

/-- The guarded active domain stops strictly *before* the retained
2b-hop front. On first reaching equality, the clock terminates.
The strict inequality is needed: a bullet past that front would
not be an admissible continuation of this first-hit stage. -/
def TaggedLongAdvanceDomain {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n) : Prop :=
  TaggedTriple ring i j k a b N ∧
    Sealed ring N j b ∧
    ∃ p : Fin n,
      SealedPhaseHolds ring N i a (.live p) ∧
        p.val + 2 * b < a

/-- State-local Bellman credit of the real live bullet. It is
zero at a physical tagged deletion and at the retained front. -/
noncomputable def taggedLongAdvanceCredit {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n) : Nat :=
  if TaggedDeleted i j k N then 0
  else
    match taggedQAttackerPhase ring i a N with
    | .live p => a - (p.val + 2 * b)
    | _ => 0

theorem tagged_long_advance_credit_value {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n) (p : Fin n)
    (ht : TaggedTriple ring i j k a b N)
    (hp : SealedPhaseHolds ring N i a (.live p)) :
    taggedLongAdvanceCredit ring i j k a b N =
      a - (p.val + 2 * b) := by
  classical
  have hnot := tagged_d15_triple_not_deleted
    ring i j k a b N ht
  have hphase := tagged_q_attacker_phase_eq
    ring N i a (.live p) hp
  unfold taggedLongAdvanceCredit
  rw [if_neg hnot, hphase]

/-- One raw edge changes the live travel credit by at most one,
and the unique physical progress edge lowers it by one, unless
it has already hit deletion (where the credit is zero). -/
theorem tagged_long_advance_credit_step {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat) (hb : 2 ≤ b)
    (N : TripleNativeState n) (e : Fin n)
    (hs : TaggedLongAdvanceDomain ring i j k a b N)
    (p : Fin n)
    (hp : SealedPhaseHolds ring N i a (.live p))
    (hfar : p.val + 2 * b < a) :
    taggedLongAdvanceCredit ring i j k a b (nativeE ring N e) ≤
      taggedLongAdvanceCredit ring i j k a b N ∧
    (e = SealedPhaseEdge ring i (.live p) →
      taggedLongAdvanceCredit ring i j k a b (nativeE ring N e) + 1 ≤
        taggedLongAdvanceCredit ring i j k a b N) := by
  let M := nativeE ring N e
  have hbefore :
      taggedLongAdvanceCredit ring i j k a b N =
        a - (p.val + 2 * b) :=
    tagged_long_advance_credit_value
      ring i j k a b N p hs.1 hp
  have hpositive : 1 ≤ a - (p.val + 2 * b) := by omega
  by_cases hdel : TaggedDeleted i j k M
  · have hzero : taggedLongAdvanceCredit ring i j k a b M = 0 := by
      simp only [taggedLongAdvanceCredit, if_pos hdel]
    constructor
    · rw [hzero]
      exact Nat.zero_le _
    · intro _
      rw [hzero, Nat.zero_add, hbefore]
      exact hpositive
  · have hfarWeak : p.val + 2 * b ≤ a := by omega
    obtain ⟨q, hq, hpos, ht', hB'⟩ :=
      tagged_long_live_physical_step
        hn ring i j k a b hb N e hs.1 hs.2.1
        p hp hfarWeak hdel
    have hafter :
        taggedLongAdvanceCredit ring i j k a b M =
          a - (q.val + 2 * b) :=
      tagged_long_advance_credit_value
        ring i j k a b M q ht' hq
    by_cases he : e = SealedPhaseEdge ring i (.live p)
    · have hadvance : q.val = p.val + 1 := by
        simpa only [if_pos he] using hpos
      constructor
      · rw [hafter, hbefore, hadvance]
        omega
      · intro _
        rw [hafter, hbefore, hadvance]
        omega
    · have hsame : q.val = p.val := by
        simpa only [if_neg he] using hpos
      constructor
      · rw [hafter, hbefore, hsame]
        exact Nat.le_refl _
      · intro hx
        exact False.elim (he hx)

/-- Every surviving edge before first retained-front arrival
preserves the strict live-front domain. -/
theorem tagged_long_advance_domain_step {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat) (hb : 2 ≤ b)
    (N : TripleNativeState n) (e : Fin n)
    (hs : TaggedLongAdvanceDomain ring i j k a b N)
    (hnot :
      ¬ (TaggedDeleted i j k (nativeE ring N e) ∨
        TaggedLongRetained ring i j k a b (nativeE ring N e))) :
    TaggedLongAdvanceDomain ring i j k a b (nativeE ring N e) := by
  obtain ⟨ht, hB, p, hp, hfar⟩ := hs
  have hnodeleted : ¬ TaggedDeleted i j k (nativeE ring N e) := by
    intro hd
    exact hnot (Or.inl hd)
  have hweak : p.val + 2 * b ≤ a := by omega
  obtain ⟨q, hq, hpos, ht', hB'⟩ :=
    tagged_long_live_physical_step
      hn ring i j k a b hb N e ht hB p hp hweak hnodeleted
  have hlimit : q.val + 2 * b ≤ a := by
    by_cases he : e = SealedPhaseEdge ring i (.live p)
    · have hqpos : q.val = p.val + 1 := by
        simpa only [if_pos he] using hpos
      omega
    · have hqpos : q.val = p.val := by
        simpa only [if_neg he] using hpos
      omega
  have hneq : q.val + 2 * b ≠ a := by
    intro he
    exact hnot (Or.inr ⟨ht', hB', q, hq, he⟩)
  exact ⟨ht', hB', q, hq, by omega⟩

/-- Strict live progress at the chosen source edge and weak
nonincrease at all raw edges give the actual finite-horizon
Bellman bound n times the number of remaining bullet hops.
No assumption of independent service hits is needed. -/
theorem tagged_long_live_advance_cost {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat) (hb : 2 ≤ b)
    (N : TripleNativeState n)
    (ht : TaggedTriple ring i j k a b N)
    (hB : Sealed ring N j b)
    (p : Fin n)
    (hp : SealedPhaseHolds ring N i a (.live p))
    (hfar : p.val + 2 * b < a) :
    ∀ T,
      costNumerator (nativeE ring)
        (fun M => TaggedDeleted i j k M ∨
          TaggedLongRetained ring i j k a b M) N T ≤
      n ^ T * (n * (a - (p.val + 2 * b))) := by
  let Target : TripleNativeState n → Prop :=
    fun M => TaggedDeleted i j k M ∨
      TaggedLongRetained ring i j k a b M
  let Inv := TaggedLongAdvanceDomain ring i j k a b
  let C := taggedLongAdvanceCredit ring i j k a b
  let V : TripleNativeState n → Nat := fun M => n * C M
  have hclosed : ∀ M, Inv M → ∀ e,
      ¬ Target (nativeE ring M e) →
        Inv (nativeE ring M e) := by
    intro M hm e hnot
    exact tagged_long_advance_domain_step
      hn ring i j k a b hb M e hm hnot
  have hdrift : ∀ M, Inv M → ¬ Target M →
      n + (List.ofFn (fun e : Fin n =>
        V (nativeE ring M e))).sum ≤ n * V M := by
    intro M hm _
    obtain ⟨htriple, hsealed, q, hq, hfarq⟩ := hm
    have hbounds := fun e : Fin n =>
      tagged_long_advance_credit_step
        hn ring i j k a b hb M e
        ⟨htriple, hsealed, q, hq, hfarq⟩ q hq hfarq
    have hweak : ∀ e : Fin n,
        V (nativeE ring M e) ≤ V M := by
      intro e
      exact Nat.mul_le_mul_left n (hbounds e).1
    have hstrict :
        V (nativeE ring M (SealedPhaseEdge ring i (.live q))) +
          n ≤ V M := by
      have hh := (hbounds (SealedPhaseEdge ring i (.live q))).2 rfl
      calc
        V (nativeE ring M (SealedPhaseEdge ring i (.live q))) + n =
            n * (C (nativeE ring M
              (SealedPhaseEdge ring i (.live q))) + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
        _ ≤ n * C M := Nat.mul_le_mul_left n hh
    exact tagged_q_drift_from_nominated_edge
      (V M) (fun e : Fin n => V (nativeE ring M e))
      (SealedPhaseEdge ring i (.live q)) hweak hstrict
  have hcost := tagged_q_restricted_cost_of_potential
    (nativeE ring) Target Inv V
    hclosed hdrift N ⟨ht, hB, p, hp, hfar⟩
  have hvalue :
      V N = n * (a - (p.val + 2 * b)) := by
    exact congrArg (Nat.mul n)
      (tagged_long_advance_credit_value
        ring i j k a b N p ht hp)
  intro T
  calc
    costNumerator (nativeE ring) Target N T ≤
        n ^ T * V N := hcost T
    _ = n ^ T * (n * (a - (p.val + 2 * b))) := by
      rw [hvalue]


/-! ### D.18 first clean outgoing live launch with dummy recovery -/

/-- The first raw A-live launch, or an earlier physical tagged
deletion. It is independent of the attacker phase observer. -/
def TaggedLongAnyLiveStop {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a : Nat)
    (M : TripleNativeState n) : Prop :=
  TaggedDeleted i j k M ∨
    ∃ p : Fin n, SealedPhaseHolds ring M i a (.live p)

/-- At a Ready source the live-launch reserve is 2a services.
During a non-Ready dummy/return excursion the remaining sealed
phase rank is added once; every physical nominated service pays it. -/
noncomputable def taggedLongLaunchPotential {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a : Nat)
    (M : TripleNativeState n) : Nat :=
  if TaggedLongAnyLiveStop ring i j k a M then 0
  else n * (2 * a +
    SealedPhaseProgress a (taggedQAttackerPhase ring i a M))

private theorem tagged_long_launch_phase_value {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a : Nat)
    (M : TripleNativeState n)
    (phase : SealedPhase n)
    (hp : SealedPhaseHolds ring M i a phase)
    (hnot : ¬ TaggedLongAnyLiveStop ring i j k a M) :
    taggedLongLaunchPotential ring i j k a M =
      n * (2 * a +
        SealedCloseProof.rank a
          (SealedCloseProof.fromPhase phase)) := by
  unfold taggedLongLaunchPotential
  rw [if_neg hnot]
  rw [tagged_q_attacker_phase_eq ring M i a phase hp]
  cases phase <;> rfl

/-- The stopped child value is bounded by the literal native
successor stage. A deletion or the first A-live arrival has
zero continuation potential. -/
private theorem tagged_long_launch_child_rank {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n)
    (a b : Nat) (M : TripleNativeState n) (e : Fin n)
    (ht : TaggedTriple ring i j k a b M)
    (phase : SealedPhase n)
    (hp : SealedPhaseHolds ring M i a phase) :
    taggedLongLaunchPotential ring i j k a (nativeE ring M e) ≤
      n * (2 * a +
        SealedCloseProof.rank a
          (sealedCloseTable ring i a e phase)) := by
  classical
  by_cases hstop :
      TaggedLongAnyLiveStop ring i j k a (nativeE ring M e)
  · simp only [taggedLongLaunchPotential, if_pos hstop]
    exact Nat.zero_le _
  · have hnotdel :
        ¬ TaggedDeleted i j k (nativeE ring M e) := by
      intro hd
      exact hstop (Or.inl hd)
    have hi : (nativeE ring M e i).l = true := by
      cases hx : (nativeE ring M e i).l with
      | false => exact False.elim (hnotdel (Or.inl hx))
      | true => rfl
    have hj : (nativeE ring M e j).l = true := by
      cases hx : (nativeE ring M e j).l with
      | false => exact False.elim (hnotdel (Or.inr (Or.inl hx)))
      | true => rfl
    obtain ⟨after, hafter, hstage⟩ :=
      sealed_close_step_stage ring M i j a e phase
        ht.2.1 hp hi hj
    have hvalue :=
      tagged_long_launch_phase_value
        ring i j k a (nativeE ring M e) after hafter hstop
    calc
      taggedLongLaunchPotential ring i j k a (nativeE ring M e) ≤
          n * (2 * a +
            SealedCloseProof.rank a
              (SealedCloseProof.fromPhase after)) :=
        Nat.le_of_eq hvalue
      _ = n * (2 * a +
            SealedCloseProof.rank a
              (sealedCloseTable ring i a e phase)) := by
        rw [hstage]

end L3


/-! ## Complete D.18 launch Bellman and first-live handoff -/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false
attribute [local instance low] Classical.propDecidable

/-- The actual physical D.18 clean-launch clock: from a sealed
A-Ready, B-sealed cut, the mean waiting cost to the *first*
A-live firing or earlier tagged deletion is at most 2na.
The source's incoming Dummy(0) and all subsequent recovery
services are paid by this same finite-horizon Bellman potential. -/
theorem tagged_long_any_live_launch_cost {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (ha : 2 ≤ a) (N : TripleNativeState n)
    (ht : TaggedTriple ring i j k a b N)
    (hB : Sealed ring N j b)
    (hA : SealedCleanReady ring N i a) :
    ∀ T,
      costNumerator (nativeE ring)
        (TaggedLongAnyLiveStop ring i j k a) N T ≤
        n ^ T * (n * (2 * a)) := by
  classical
  let target := TaggedLongAnyLiveStop ring i j k a
  let potential := taggedLongLaunchPotential ring i j k a
  let Inv : TripleNativeState n → Prop :=
    fun M => TaggedTriple ring i j k a b M ∧
      TaggedSealed ring i j a b M
  have hclosed :
      ∀ M : TripleNativeState n, Inv M → ∀ e,
        ¬ target (nativeE ring M e) →
          Inv (nativeE ring M e) := by
    intro M hg e hnot
    have hsurvive : ¬ TaggedDeleted i j k (nativeE ring M e) := by
      intro hd
      exact hnot (Or.inl hd)
    have htr :=
      tagged_triple_step_of_survival
        hn ring i j k a b M e hg.1 hsurvive
    have hs :=
      tagged_sealed_step_of_survival
        ring i j k a b M e hg.1 hg.2 hsurvive
    exact ⟨htr, hs⟩
  have hdrift :
      ∀ M : TripleNativeState n, Inv M → ¬ target M →
        n + (List.ofFn (fun e : Fin n =>
          potential (nativeE ring M e))).sum ≤
            n * potential M := by
    intro M hg hnot
    obtain ⟨phase, hp⟩ := hg.2.1
    have hOld :
        potential M = n * (2 * a +
          SealedCloseProof.rank a
            (SealedCloseProof.fromPhase phase)) :=
      tagged_long_launch_phase_value
        ring i j k a M phase hp hnot
    by_cases hready : phase = .ready
    · subst phase
      have hports : i ≠ ring.leftNeighbor i :=
        tagged_q_incident_edges_distinct
          (by omega : 2 ≤ n) ring i
      have hcap :
          ∀ e : Fin n,
            potential (nativeE ring M e) ≤
              n * (2 * a +
                SealedCloseProof.rank a
                  (sealedCloseTable ring i a e
                    (.ready : SealedPhase n))) := by
        intro e
        exact tagged_long_launch_child_rank
          ring i j k a b M e hg.1 .ready hp
      have hterminal :
          target (nativeE ring M i) := by
        rcases tagged_long_ready_outgoing_live
            hn ring i j k a b ha M hg.1 hg.2.2 hp with
          hd | ⟨_, _, p, _, hlive⟩
        · exact Or.inl hd
        · exact Or.inr ⟨p, hlive⟩
      have hout :
          potential (nativeE ring M i) = 0 := by
        change (if target (nativeE ring M i) then 0
          else n * (2 * a +
            SealedPhaseProgress a
              (taggedQAttackerPhase ring i a
                (nativeE ring M i)))) = 0
        rw [if_pos hterminal]
      have hIncomingTable :
          sealedCloseTable ring i a
            (ring.leftNeighbor i) (.ready : SealedPhase n) =
              .bullet false 0 := by
        let pos := SealedCloseProof.position ring i
          (ring.leftNeighbor i)
        have hwrap : pos.val + 1 = n :=
          (sealed_close_incoming_iff ring i
            (ring.leftNeighbor i)).2 rfl
        have hlt : ¬ pos.val < a := by
          have hatn : a < n := hg.1.2.1.2.1
          omega
        change (if pos.val < a then
            SealedCloseProof.insideStage a .ready pos.val
           else if pos.val + 1 = n then
            SealedCloseProof.incomingStage .ready
           else .ready) = .bullet false 0
        simp only [if_neg hlt, if_pos hwrap,
          SealedCloseProof.incomingStage]
      have hin :
          potential (nativeE ring M (ring.leftNeighbor i)) ≤
            n * (4 * a - 1) := by
        have hh := hcap (ring.leftNeighbor i)
        rw [hIncomingTable] at hh
        have hcoef : 2 * a +
            SealedCloseProof.rank a (.bullet false 0) =
              4 * a - 1 := by
          simp only [SealedCloseProof.rank]
          omega
        simpa only [hcoef] using hh
      have hrest :
          ∀ e : Fin n, e ≠ i →
            e ≠ ring.leftNeighbor i →
              potential (nativeE ring M e) ≤
                n * (2 * a) := by
        intro e he hincoming
        have htable :=
          tagged_d15_ready_quiet_table ring i e a he hincoming
        have hh := hcap e
        rw [htable] at hh
        simpa only [SealedCloseProof.rank, Nat.add_zero] using hh
      have hreadyValue : potential M = n * (2 * a) := by
        simpa only [SealedCloseProof.fromPhase,
          SealedCloseProof.rank, Nat.add_zero] using hOld
      have hcoef : 1 + (4 * a - 1) = 2 * (2 * a) := by omega
      have hpair :
          n + potential (nativeE ring M i) +
            potential (nativeE ring M (ring.leftNeighbor i)) ≤
              2 * potential M := by
        calc
          n + potential (nativeE ring M i) +
              potential (nativeE ring M (ring.leftNeighbor i)) ≤
                n + 0 + n * (4 * a - 1) := by omega
          _ = n * (1 + (4 * a - 1)) := by
            rw [Nat.mul_add, Nat.mul_one]
            omega
          _ = n * (2 * (2 * a)) := by rw [hcoef]
          _ = 2 * (n * (2 * a)) := by ac_rfl
          _ = 2 * potential M := by rw [hreadyValue]
      have hrestNative :
          ∀ e : Fin n, e ≠ i →
            e ≠ ring.leftNeighbor i →
              potential (nativeE ring M e) ≤ potential M := by
        intro e he hincoming
        calc
          potential (nativeE ring M e) ≤
              n * (2 * a) := hrest e he hincoming
          _ = potential M := hreadyValue.symm
      exact tagged_q_ready_sum_of_two_edge_bounds
        (potential M)
        (fun e : Fin n => potential (nativeE ring M e))
        i (ring.leftNeighbor i) hports hpair hrestNative
    · have hcap :
          ∀ e : Fin n,
            potential (nativeE ring M e) ≤
              n * (2 * a +
                SealedCloseProof.rank a
                  (sealedCloseTable ring i a e phase)) := by
        intro e
        exact tagged_long_launch_child_rank
          ring i j k a b M e hg.1 phase hp
      have htable (e : Fin n) :=
        tagged_target_nonready_table_exact
          ring M i j a ha phase e hg.1.2.1 hp hready
      have hweak :
          ∀ e : Fin n,
            potential (nativeE ring M e) ≤ potential M := by
        intro e
        have hh := htable e
        have hrank :
            SealedCloseProof.rank a
                (sealedCloseTable ring i a e phase) ≤
              SealedCloseProof.rank a
                (SealedCloseProof.fromPhase phase) := by
          omega
        calc
          potential (nativeE ring M e) ≤
              n * (2 * a +
                SealedCloseProof.rank a
                  (sealedCloseTable ring i a e phase)) := hcap e
          _ ≤ n * (2 * a +
                SealedCloseProof.rank a
                  (SealedCloseProof.fromPhase phase)) :=
            Nat.mul_le_mul_left n
              (Nat.add_le_add_left hrank (2 * a))
          _ = potential M := hOld.symm
      let port := SealedPhaseEdge ring i phase
      have hnom := htable port
      have hrank :
          SealedCloseProof.rank a
            (sealedCloseTable ring i a port phase) + 1 =
          SealedCloseProof.rank a
            (SealedCloseProof.fromPhase phase) := by
        simpa only [port, ↓reduceIte] using hnom
      have hcoef :
          (2 * a + SealedCloseProof.rank a
            (sealedCloseTable ring i a port phase)) + 1 =
          2 * a + SealedCloseProof.rank a
            (SealedCloseProof.fromPhase phase) := by
        omega
      have hstrict :
          potential (nativeE ring M port) + n ≤
            potential M := by
        calc
          potential (nativeE ring M port) + n ≤
              n * (2 * a +
                SealedCloseProof.rank a
                  (sealedCloseTable ring i a port phase)) + n :=
            Nat.add_le_add_right (hcap port) n
          _ = n * ((2 * a +
                SealedCloseProof.rank a
                  (sealedCloseTable ring i a port phase)) + 1) :=
            (Nat.mul_succ _ _).symm
          _ = n * (2 * a +
                SealedCloseProof.rank a
                  (SealedCloseProof.fromPhase phase)) := by
            rw [hcoef]
          _ = potential M := hOld.symm
      exact tagged_q_drift_from_nominated_edge
        (potential M)
        (fun e : Fin n => potential (nativeE ring M e))
        port hweak hstrict
  have hinitial : ¬ target N := by
    intro hd
    rcases hd with hdel | ⟨p, hlive⟩
    · exact (tagged_d15_triple_not_deleted
        ring i j k a b N ht) hdel
    · have hh := tagged_sealed_phase_unique
        ring N i a (.ready : SealedPhase n)
        (.live p) hA hlive
      cases hh
  have hstartValue : potential N = n * (2 * a) := by
    have hh := tagged_long_launch_phase_value
      ring i j k a N (.ready : SealedPhase n)
      hA hinitial
    simpa only [SealedCloseProof.fromPhase,
      SealedCloseProof.rank, Nat.add_zero] using hh
  have hcost := tagged_q_restricted_cost_of_potential
    (nativeE ring) target Inv potential
    hclosed hdrift N
    ⟨ht, ⟨sealed_of_clean_ready ring N i a hA, hB⟩⟩
  intro T
  simpa only [hstartValue] using (hcost T)


/-! ### Exact launch-cut interface and the D.18 stage composition -/

/-- A truthful first-live-one cut: the native triple and sealed B
survive, and the live attacker occupies exactly source offset one. -/
def TaggedLongLiveOne {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (M : TripleNativeState n) : Prop :=
  TaggedTriple ring i j k a b M ∧
    Sealed ring M j b ∧
    ∃ p : Fin n,
      p.val = 1 ∧
      SealedPhaseHolds ring M i a (.live p)

/-- The remaining bridge in the D.18 two-clock splice:
from an A-Ready/B-sealed cut the first live event is the
physical one-site bullet (or a tagged deletion). This clock
cannot be assumed from an arbitrary live phase at offset p>1. -/
def TaggedLongFirstLiveOneClock {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat) : Prop :=
  2 ≤ b → 2 * b + 1 ≤ a →
  ∀ N : TripleNativeState n,
    TaggedTriple ring i j k a b N →
    Sealed ring N j b →
    SealedCleanReady ring N i a →
    ∀ T,
      costNumerator (nativeE ring)
        (fun M => TaggedDeleted i j k M ∨
          TaggedLongLiveOne ring i j k a b M) N T ≤
        n ^ T * (n * (2 * a))

/-- At an actual one-site live cut, advancing to the
retained 2b-hop front costs at most n(a−1−2b).
When a=2b+1 this cut is already the retained front. -/
theorem tagged_long_live_one_to_retained_cost {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hb : 2 ≤ b) (hab : 2 * b + 1 ≤ a)
    (M : TripleNativeState n)
    (hLive : TaggedLongLiveOne ring i j k a b M) :
    ∀ T,
      costNumerator (nativeE ring)
        (fun W => TaggedDeleted i j k W ∨
          TaggedLongRetained ring i j k a b W) M T ≤
        n ^ T * (n * (a - 1 - 2 * b)) := by
  obtain ⟨ht, hB, p, hpval, hphase⟩ := hLive
  by_cases hminimal : a = 2 * b + 1
  · have hretained : TaggedLongRetained ring i j k a b M :=
      ⟨ht, hB, p, hphase, by omega⟩
    intro T
    cases T with
    | zero =>
        simp only [costNumerator_zero]
        exact Nat.zero_le _
    | succ T =>
        rw [costNumerator_terminal
          (nativeE ring)
          (fun W => TaggedDeleted i j k W ∨
            TaggedLongRetained ring i j k a b W)
          M (Or.inr hretained) (T + 1)]
        exact Nat.zero_le _
  · have hfar : p.val + 2 * b < a := by omega
    intro T
    have hc := tagged_long_live_advance_cost
      hn ring i j k a b hb M ht hB p hphase hfar T
    have hscalar : a - (p.val + 2 * b) =
        a - 1 - 2 * b := by
      omega
    simpa only [hscalar] using hc

/-- The exact D.18 launch-and-advance clock follows from the
single physical first-Live(1) entrance clock. The live
progress and both budgets have been proved separately. -/
theorem tagged_long_launch_advance_of_first_live_one {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (hFirst : TaggedLongFirstLiveOneClock
      hn ring i j k a b) :
    TaggedLongLaunchAdvanceClock ring i j k a b := by
  intro hb hab N ht hB hA
  let LiveOne := TaggedLongLiveOne ring i j k a b
  let Goal : TripleNativeState n → Prop :=
    fun M => TaggedDeleted i j k M ∨
      TaggedLongRetained ring i j k a b M
  have hfirstRaw := hFirst hb hab N ht hB hA
  have hfirst : ∀ T,
      costNumerator (nativeE ring)
        (fun M => LiveOne M ∨ Goal M) N T ≤
      n ^ T * (n * (2 * a)) := by
    intro T
    have hsubset : ∀ M,
        (TaggedDeleted i j k M ∨ LiveOne M) →
          (LiveOne M ∨ Goal M) := by
      intro M h
      rcases h with hd | hl
      · exact Or.inr (Or.inl hd)
      · exact Or.inl hl
    exact Nat.le_trans
      (Prob.costNumerator_target_mono
        (nativeE ring)
        (fun M => TaggedDeleted i j k M ∨ LiveOne M)
        (fun M => LiveOne M ∨ Goal M)
        hsubset N T)
      (hfirstRaw T)
  have hsecond : ∀ M, LiveOne M → ∀ T,
      costNumerator (nativeE ring) Goal M T ≤
        n ^ T * (n * (a - 1 - 2 * b)) := by
    intro M hLive T
    exact tagged_long_live_one_to_retained_cost
      hn ring i j k a b hb hab M hLive T
  have hcombined := Prob.costNumerator_stage_le
    (nativeE ring) N LiveOne Goal
    (n * (2 * a)) (n * (a - 1 - 2 * b))
    hfirst hsecond
  intro T
  calc
    costNumerator (nativeE ring) Goal N T ≤
        n ^ T * (n * (2 * a) + n * (a - 1 - 2 * b)) :=
      hcombined T
    _ = n ^ T * (n * (2 * a + (a - 1 - 2 * b))) := by
      rw [← Nat.mul_add]


/-! ### First-live offset one: native stage handoff -/

/-- Pure exact table certificate. A sealed sector in a nonlive
stage can create a new live stage only from Ready with its
source-relative outgoing edge, and the newborn offset is one. -/
private theorem tagged_long_first_live_table
    (n a r q : Nat) (ha : 2 ≤ a)
    (s : SealedCloseProof.Stage)
    (hnolive : ∀ p, s ≠ .bullet true p)
    (h :
      (if r < a then
        SealedCloseProof.insideStage a s r
       else if r + 1 = n then
        SealedCloseProof.incomingStage s
       else s) = .bullet true q) :
    s = .ready ∧ r = 0 ∧ q = 1 := by
  cases s with
  | ready =>
      by_cases hr : r < a
      · by_cases hz : r = 0
        · have hnotone : a ≠ 1 := by omega
          simp only [if_pos hr, SealedCloseProof.insideStage,
            if_pos hz, if_neg hnotone] at h
          have hq : q = 1 := by
            have hh := congrArg SealedCloseProof.nominated h
            simpa only [SealedCloseProof.nominated] using hh.symm
          exact ⟨rfl, hz, hq⟩
        · simp only [if_pos hr, SealedCloseProof.insideStage,
            if_neg hz] at h
          cases h
      · by_cases hin : r + 1 = n
        · simp only [if_neg hr, if_pos hin,
            SealedCloseProof.incomingStage] at h
          cases h
        · simp only [if_neg hr, if_neg hin] at h
          cases h
  | bullet live p =>
      cases live with
      | true =>
          exact False.elim (hnolive p rfl)
      | false =>
          simp only [SealedCloseProof.insideStage,
            SealedCloseProof.incomingStage] at h
          repeat (split at h)
          all_goals (first
            | cases h
            | (generalize instDecidableEqNat (r + 1) n = d at h
               cases d <;> cases h))
  | returning p =>
      simp only [SealedCloseProof.insideStage,
        SealedCloseProof.incomingStage] at h
      repeat (split at h)
      all_goals (first
        | cases h
        | (generalize instDecidableEqNat (r + 1) n = d at h
           cases d <;> cases h))
/-- Exact physical lift of the first-live row. Starting from a
sealed nonlive A sector, any surviving nativeE edge which first
creates a live attacker creates Live(1), not an arbitrary live
bullet already farther along its route. -/
theorem tagged_long_new_live_is_one {n : Nat}
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (ha : 2 ≤ a)
    (N : TripleNativeState n) (e : Fin n)
    (ht : TaggedTriple ring i j k a b N)
    (hA : Sealed ring N i a)
    (hnolive :
      ¬ ∃ p : Fin n,
        SealedPhaseHolds ring N i a (.live p))
    (hnotdel : ¬ TaggedDeleted i j k (nativeE ring N e))
    (q : Fin n)
    (hnew : SealedPhaseHolds ring
      (nativeE ring N e) i a (.live q)) :
    q.val = 1 := by
  obtain ⟨phase, hp⟩ := hA
  have hi : (nativeE ring N e i).l = true := by
    cases hx : (nativeE ring N e i).l with
    | false => exact False.elim (hnotdel (Or.inl hx))
    | true => rfl
  have hj : (nativeE ring N e j).l = true := by
    cases hx : (nativeE ring N e j).l with
    | false => exact False.elim (hnotdel (Or.inr (Or.inl hx)))
    | true => rfl
  obtain ⟨after, hafter, hstage⟩ :=
    sealed_close_step_stage
      ring N i j a e phase ht.2.1 hp hi hj
  have hsame := tagged_sealed_phase_unique
    ring (nativeE ring N e) i a after (.live q)
    hafter hnew
  have hstage' :
      sealedCloseTable ring i a e phase = .bullet true q.val := by
    have hh : SealedCloseProof.fromPhase after =
        .bullet true q.val := by
      rw [hsame]
      rfl
    exact hstage.symm.trans hh
  let r := SealedCloseProof.position ring i e
  let s := SealedCloseProof.fromPhase phase
  have hnotLiveStage : ∀ t, s ≠ .bullet true t := by
    intro t
    change SealedCloseProof.fromPhase phase ≠ .bullet true t
    cases phase with
    | ready =>
        intro hh
        cases hh
    | dummy p =>
        intro hh
        cases hh
    | live p =>
        intro _
        exact hnolive ⟨p, hp⟩
    | returning p =>
        intro hh
        cases hh
  have hmodel :
      (if r.val < a then
        SealedCloseProof.insideStage a s r.val
       else if r.val + 1 = n then
        SealedCloseProof.incomingStage s
       else s) = .bullet true q.val := by
    change
      (if r.val < a then
        SealedCloseProof.insideStage a s r.val
       else if r.val + 1 = n then
        SealedCloseProof.incomingStage s
       else s) = .bullet true q.val at hstage'
    exact hstage'
  have hrow := tagged_long_first_live_table
    n a r.val q.val ha s hnotLiveStage hmodel
  exact hrow.2.2

/-- Before the first A-live bullet, a peaceful physical triple
with both sectors sealed remains in the same nonlive domain
on every native edge not already delivering the one-site launch
or deleting one of the tags. -/
def TaggedLongBeforeFirstLive {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (M : TripleNativeState n) : Prop :=
  TaggedTriple ring i j k a b M ∧
    TaggedSealed ring i j a b M ∧
    ¬ ∃ p : Fin n, SealedPhaseHolds ring M i a (.live p)

/-- Native first-live(1) entrance pays the same 2na cost as the
first-any-live clock. This step relies on the exact table row,
not on a future-history assertion or a synthetic phase reset. -/
theorem tagged_long_first_live_one_clock {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat) :
    TaggedLongFirstLiveOneClock hn ring i j k a b := by
  intro hb hab N ht hB hA
  have ha : 2 ≤ a := by omega
  let Q : TripleNativeState n → Prop :=
    fun M => TaggedDeleted i j k M ∨
      TaggedLongLiveOne ring i j k a b M
  let R := TaggedLongAnyLiveStop ring i j k a
  let Inv := TaggedLongBeforeFirstLive ring i j k a b
  have hclosed :
      ∀ M, Inv M → ∀ e,
        ¬ Q (nativeE ring M e) →
          Inv (nativeE ring M e) := by
    intro M hgood e hnot
    have hnotdel : ¬ TaggedDeleted i j k (nativeE ring M e) := by
      intro hd
      exact hnot (Or.inl hd)
    have htr := tagged_triple_step_of_survival
      hn ring i j k a b M e hgood.1 hnotdel
    have hsealed := tagged_sealed_step_of_survival
      ring i j k a b M e hgood.1 hgood.2.1 hnotdel
    have hnolive :
        ¬ ∃ p : Fin n,
          SealedPhaseHolds ring (nativeE ring M e) i a (.live p) := by
      intro hh
      obtain ⟨p, hp⟩ := hh
      have hpos := tagged_long_new_live_is_one
        ring i j k a b ha M e hgood.1
        hgood.2.1.1 hgood.2.2 hnotdel p hp
      have htarget : TaggedLongLiveOne
          ring i j k a b (nativeE ring M e) :=
        ⟨htr, hsealed.2, p, hpos, hp⟩
      exact hnot (Or.inr htarget)
    exact ⟨htr, hsealed, hnolive⟩
  have htarget : ∀ M, Inv M → R M → Q M := by
    intro M hgood hh
    rcases hh with hd | ⟨p, hp⟩
    · exact Or.inl hd
    · exact False.elim (hgood.2.2 ⟨p, hp⟩)
  have hnotStart :
      ¬ ∃ p : Fin n, SealedPhaseHolds ring N i a (.live p) := by
    intro hh
    obtain ⟨p, hp⟩ := hh
    have heq := tagged_sealed_phase_unique
      ring N i a (.ready : SealedPhase n) (.live p) hA hp
    cases heq
  have hcomp := tagged_cost_invariant_target_le
    (nativeE ring) Inv Q R hclosed htarget N
    ⟨ht, ⟨sealed_of_clean_ready ring N i a hA, hB⟩,
      hnotStart⟩
  have hlaunch := tagged_long_any_live_launch_cost
    hn ring i j k a b ha N ht hB hA
  intro T
  exact Nat.le_trans (hcomp T) (hlaunch T)

/-- D.18 is now reduced to the already proved two native clocks:
one first clean Live(1) launch and one forward nominated advance. -/
theorem tagged_long_launch_advance_clock {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat) :
    TaggedLongLaunchAdvanceClock ring i j k a b := by
  exact tagged_long_launch_advance_of_first_live_one
    hn ring i j k a b
    (tagged_long_first_live_one_clock hn ring i j k a b)

/-- D.18 full initial preparation, from a physical peaceful
triple without a hypothetical retained future cut. -/
theorem tagged_long_preparation_clock {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat) :
    TaggedLongPreparationClock ring i j k a b := by
  exact tagged_long_preparation_of_launch_clock
    hn ring i j k a b
    (tagged_long_launch_advance_clock hn ring i j k a b)


/-! ### D.19 race: the already-Ready target case -/

/-- A retained front with a target B that is already Ready has
won the first-target race at the current adapted stopping cut.
It does not consume an additional native edge. -/
theorem tagged_long_race_initial_ready {n : Nat}
    (ring : DirectedRing n) (j : Fin n) (b : Nat)
    (N : TripleNativeState n)
    (hready : SealedCleanReady ring N j b) :
    tagged_long_race_start ring j b N = .success := by
  classical
  simp [tagged_long_race_start, hready]

private theorem tagged_long_failure_success_zero
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) :
    ∀ T, failureCount step (.success) T = 0 := by
  intro T
  induction T with
  | zero => rfl
  | succ T ih =>
      change
        (List.ofFn (fun _ : Fin n =>
          failureCount step (.success) T)).sum = 0
      rw [ofFn_sum_eq _ (fun _ : Fin n => 0)
        (fun _ => ih), ofFn_sum_const]
      simp

/-- Both stopped D.19 race quantities vanish in the initial-Ready
case. This is a fully physical, same-native-stream statement and
is independent of the missing two-front fairness estimate. -/
theorem tagged_long_race_initial_ready_cost_and_mass {n : Nat}
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (hready : SealedCleanReady ring N j b) :
    ∀ T,
      truncatedActiveCostNumerator
        (tagged_long_race_step ring i j k a b)
        (tagged_long_race_start ring j b N) T = 0 ∧
      failureCount
        (tagged_long_race_step ring i j k a b)
        (tagged_long_race_start ring j b N) T = 0 := by
  intro T
  have hstart := tagged_long_race_initial_ready
    ring j b N hready
  rw [hstart]
  constructor
  · cases T <;> simp [truncatedActiveCostNumerator]
  · exact tagged_long_failure_success_zero
      (tagged_long_race_step ring i j k a b) T

end L3


/-! ## Finite-horizon fair two-front arithmetic

This section distinguishes a fair-coin counting identity from the
still-required same-edge native simulation. In the abstract race, u is
the B readiness quota and v the A live-bullet quota. First B completion
is success; first A completion is failure. n-2 unrelated letters
contribute the same count on both sides.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false
attribute [local instance low] Classical.propDecidable

/-- Failure-cylinder numerator for the fair two-front countdown,
including arbitrarily long stretches of irrelevant scheduler letters.
Boundary u=0 is success; v=0 with u>0 is failure. -/
def taggedLongFairFailure (n u v : Nat) : Nat → Nat
  | 0 =>
      if u = 0 then 0 else if v = 0 then 1 else 0
  | T + 1 =>
      if u = 0 then 0
      else if v = 0 then n ^ (T + 1)
      else
        (n - 2) * taggedLongFairFailure n u v T +
          taggedLongFairFailure n (u - 1) v T +
          taggedLongFairFailure n u (v - 1) T

/-- The finite-horizon failure numerator is monotone under
interchanging a shorter B quota and a longer A quota.
This is the binomial/reflection inequality, proved here using
only Pascal recursion and Nat arithmetic. -/
theorem tagged_long_fair_failure_swap
    (n : Nat) :
    ∀ T u v, u ≤ v →
      taggedLongFairFailure n u v T ≤
        taggedLongFairFailure n v u T := by
  intro T
  induction T with
  | zero =>
      intro u v huv
      by_cases hu : u = 0
      · subst u
        change 0 ≤ taggedLongFairFailure n v 0 0
        exact Nat.zero_le _
      · have hv : v ≠ 0 := by omega
        simp [taggedLongFairFailure, hu, hv]
  | succ T ih =>
      intro u v huv
      by_cases heq : u = v
      · subst v
        exact Nat.le_refl _
      by_cases hu : u = 0
      · subst u
        change 0 ≤ taggedLongFairFailure n v 0 (T + 1)
        exact Nat.zero_le _
      · have hv : v ≠ 0 := by omega
        have hcenter := Nat.mul_le_mul_left (n - 2)
          (ih u v huv)
        have hB := ih (u - 1) v (by omega)
        have hA := ih u (v - 1) (by omega)
        have hleft :
            taggedLongFairFailure n u v (T + 1) =
              (n - 2) * taggedLongFairFailure n u v T +
                taggedLongFairFailure n (u - 1) v T +
                taggedLongFairFailure n u (v - 1) T := by
          simp only [taggedLongFairFailure, if_neg hu, if_neg hv]
        have hright :
            taggedLongFairFailure n v u (T + 1) =
              (n - 2) * taggedLongFairFailure n v u T +
                taggedLongFairFailure n (v - 1) u T +
                taggedLongFairFailure n v (u - 1) T := by
          simp only [taggedLongFairFailure, if_neg hv, if_neg hu]
        rw [hleft, hright]
        omega

/-- Complementary oriented failure counts cannot exceed the
number of length-T scheduler words. On terminal sides their
combined count is exactly n^T; on active sides some mass remains. -/
theorem tagged_long_fair_failure_pair
    (n : Nat) (hn : 2 ≤ n) :
    ∀ T u v,
      taggedLongFairFailure n u v T +
        taggedLongFairFailure n v u T ≤ n ^ T := by
  intro T
  induction T with
  | zero =>
      intro u v
      by_cases hu : u = 0
      · subst u
        by_cases hv : v = 0
        · subst v
          simp [taggedLongFairFailure]
        · simp [taggedLongFairFailure, hv]
      · by_cases hv : v = 0
        · subst v
          simp [taggedLongFairFailure, hu]
        · simp [taggedLongFairFailure, hu, hv]
  | succ T ih =>
      intro u v
      by_cases hu : u = 0
      · subst u
        by_cases hv : v = 0
        · subst v
          simp [taggedLongFairFailure]
        · simp [taggedLongFairFailure, hv]
      · by_cases hv : v = 0
        · subst v
          simp [taggedLongFairFailure, hu]
        · have hcenter := Nat.mul_le_mul_left (n - 2)
            (ih u v)
          have hB := ih (u - 1) v
          have hA := ih u (v - 1)
          have hleft :
              taggedLongFairFailure n u v (T + 1) =
                (n - 2) * taggedLongFairFailure n u v T +
                  taggedLongFairFailure n (u - 1) v T +
                  taggedLongFairFailure n u (v - 1) T := by
            simp only [taggedLongFairFailure, if_neg hu, if_neg hv]
          have hright :
              taggedLongFairFailure n v u (T + 1) =
                (n - 2) * taggedLongFairFailure n v u T +
                  taggedLongFairFailure n (v - 1) u T +
                  taggedLongFairFailure n v (u - 1) T := by
            simp only [taggedLongFairFailure, if_neg hv, if_neg hu]
          calc
            taggedLongFairFailure n u v (T + 1) +
                taggedLongFairFailure n v u (T + 1) =
              (n - 2) * (taggedLongFairFailure n u v T +
                taggedLongFairFailure n v u T) +
                (taggedLongFairFailure n (u - 1) v T +
                  taggedLongFairFailure n v (u - 1) T) +
                (taggedLongFairFailure n u (v - 1) T +
                  taggedLongFairFailure n (v - 1) u T) := by
              rw [hleft, hright, Nat.mul_add]
              ac_rfl
            _ ≤ (n - 2) * n ^ T + n ^ T + n ^ T := by
              omega
            _ = n ^ (T + 1) := by
              have hnsub : n - 2 + 2 = n := by omega
              calc
                (n - 2) * n ^ T + n ^ T + n ^ T =
                    (n - 2 + 2) * n ^ T := by
                  rw [Nat.add_mul]
                  omega
                _ = n * n ^ T := by rw [hnsub]
                _ = n ^ (T + 1) := by
                  rw [Nat.pow_succ]
                  ac_rfl

/-- Exact division-free fair-race half-mass estimate for quotas
u≤v, at EVERY finite scheduler horizon, not only at infinity.
It is independent of any physical edge-separation assumption. -/
theorem tagged_long_fair_failure_half
    (n : Nat) (hn : 2 ≤ n)
    (u v T : Nat) (huv : u ≤ v) :
    2 * taggedLongFairFailure n u v T ≤ n ^ T := by
  have hswap := tagged_long_fair_failure_swap n T u v huv
  have hpair := tagged_long_fair_failure_pair n hn T u v
  omega


/-! ### D.19 physical B quota on a single nativeE edge -/

/-- A nonready sealed B sector's remaining quota is positive.
No assumption about A or the other tagged sector is used. -/
theorem tagged_long_race_b_rank_pos {n : Nat}
    (ring : DirectedRing n)
    (N : TripleNativeState n) (j : Fin n) (b : Nat)
    (phase : SealedPhase n)
    (hp : SealedPhaseHolds ring N j b phase)
    (hnr : phase ≠ .ready) :
    1 ≤ SealedPhaseProgress b phase := by
  cases phase with
  | ready =>
      exact False.elim (hnr rfl)
  | dummy p =>
      have hlt : p.val < b := hp.1.1
      simp only [SealedPhaseProgress]
      omega
  | live p =>
      have hlt : p.val < b := hp.1.1
      simp only [SealedPhaseProgress]
      omega
  | returning q =>
      have hpositive : 0 < q.val := hp.2.2.1
      simp only [SealedPhaseProgress]
      omega

/-- The first D.19 physical coupling ingredient: on EVERY
surviving raw nativeE service, B's actual sealed phase quota
never increases and decreases by at least one precisely when
the scheduler selects the *current* B nominated edge. -/
theorem tagged_long_race_b_progress {n : Nat}
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n) (e : Fin n)
    (ht : TaggedTriple ring i j k a b N)
    (phase : SealedPhase n)
    (hp : SealedPhaseHolds ring N j b phase)
    (hnr : phase ≠ .ready)
    (hnot : ¬ TaggedDeleted i j k (nativeE ring N e)) :
    ∃ nextPhase : SealedPhase n,
      SealedPhaseHolds ring (nativeE ring N e) j b nextPhase ∧
      SealedPhaseProgress b nextPhase ≤
        SealedPhaseProgress b phase ∧
      (e = SealedPhaseEdge ring j phase →
        SealedPhaseProgress b nextPhase + 1 ≤
          SealedPhaseProgress b phase) := by
  have hj : (nativeE ring N e j).l = true := by
    cases hx : (nativeE ring N e j).l with
    | false => exact False.elim (hnot (Or.inr (Or.inl hx)))
    | true => rfl
  have hk : (nativeE ring N e k).l = true := by
    cases hx : (nativeE ring N e k).l with
    | false => exact False.elim (hnot (Or.inr (Or.inr hx)))
    | true => rfl
  obtain ⟨nextPhase, hphase, hprogress⟩ :=
    sealed_close_step_with_progress
      ring N j k b e phase ht.2.2 hp hj hk
  exact ⟨nextPhase, hphase,
    (hprogress hnr).1, (hprogress hnr).2⟩

/-- The actual stopped race's B quota is read from the present
native configuration, not a separately simulated ghost count. -/
noncomputable def taggedLongRaceBRank {n : Nat}
    (ring : DirectedRing n) (j : Fin n) (b : Nat)
    (N : TripleNativeState n) : Nat :=
  SealedPhaseProgress b (taggedQAttackerPhase ring j b N)

/-- A stopped successor carries no future B-rank charge. -/
def taggedLongRaceNodeCredit {S : Type}
    (V : S → Nat) : StopNode S → Nat
  | .active x => V x
  | .success => 0
  | .failure => 0

/-- The exact B quota of a physical phase witness, as observed
by the current-state phase extractor. -/
theorem tagged_long_race_b_rank_value {n : Nat}
    (ring : DirectedRing n) (j : Fin n) (b : Nat)
    (N : TripleNativeState n)
    (phase : SealedPhase n)
    (hp : SealedPhaseHolds ring N j b phase) :
    taggedLongRaceBRank ring j b N =
      SealedPhaseProgress b phase := by
  unfold taggedLongRaceBRank
  rw [tagged_q_attacker_phase_eq ring N j b phase hp]

/-- The safe native active domain for the first-expiring-front
race, before B is ready and before the A-live near-phase fails. -/
def TaggedLongRaceActive {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n)
    (a b : Nat) (N : TripleNativeState n) : Prop :=
  TaggedLongNear ring i j k a b N ∧
    ¬ SealedCleanReady ring N j b


end L3

/-! ## Alias-free B-front physical-cost continuation

No proof-local let abbreviations are introduced in this continuation.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false
attribute [local instance low] Classical.propDecidable

/-- The actual active race successor is the literal nativeE child
and remains near-front with the B sector not Ready. -/
theorem tagged_long_race_active_step {n : Nat}
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N M : TripleNativeState n) (e : Fin n)
    (hactive : tagged_long_race_step ring i j k a b N e =
      .active M) :
    M = nativeE ring N e ∧
      TaggedLongRaceActive ring i j k a b M := by
  classical
  by_cases hdel : TaggedDeleted i j k (nativeE ring N e)
  · simp [tagged_long_race_step, hdel] at hactive
  · by_cases hnear :
        TaggedLongNear ring i j k a b (nativeE ring N e)
    · by_cases hready :
          SealedCleanReady ring (nativeE ring N e) j b
      · simp [tagged_long_race_step, hdel, hnear, hready] at hactive
      · have hsame : M = nativeE ring N e := by
          have hh := hactive.symm
          simpa [tagged_long_race_step, hdel, hnear, hready] using hh
        subst M
        exact ⟨rfl, hnear, hready⟩
    · simp [tagged_long_race_step, hdel, hnear] at hactive

/-! ### D.19 B quota and physical nominated-edge Bellman cost -/

/-- B-front credit from the actual present native phase. -/
noncomputable def taggedLongRaceBPotential {n : Nat}
    (ring : DirectedRing n) (j : Fin n) (b : Nat)
    (N : TripleNativeState n) : Nat :=
  n * taggedLongRaceBRank ring j b N

/-- Actual B-front Bellman inequality on every active physical cut. -/
theorem tagged_long_race_b_bellman {n : Nat}
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (hs : TaggedLongRaceActive ring i j k a b N) :
    n + (List.ofFn (fun e : Fin n =>
      taggedLongRaceNodeCredit (taggedLongRaceBPotential ring j b)
        (tagged_long_race_step ring i j k a b N e))).sum ≤
      n * taggedLongRaceBPotential ring j b N := by
  classical
  obtain ⟨phase, hp⟩ := hs.1.2.1
  have hnr : phase ≠ .ready := by
    intro he
    subst phase
    exact hs.2 hp
  have hpositive :=
    tagged_long_race_b_rank_pos ring N j b phase hp hnr
  have hOld :
      taggedLongRaceBPotential ring j b N =
        n * SealedPhaseProgress b phase :=
    congrArg (Nat.mul n)
      (tagged_long_race_b_rank_value ring j b N phase hp)
  have hNat :
      n ≤ taggedLongRaceBPotential ring j b N := by
    rw [hOld]
    calc
      n = n * 1 := (Nat.mul_one n).symm
      _ ≤ n * SealedPhaseProgress b phase :=
        Nat.mul_le_mul_left n hpositive
  have hterminal (e : Fin n)
      (hz : taggedLongRaceNodeCredit
        (taggedLongRaceBPotential ring j b)
        (tagged_long_race_step ring i j k a b N e) = 0) :
      taggedLongRaceNodeCredit
          (taggedLongRaceBPotential ring j b)
          (tagged_long_race_step ring i j k a b N e) ≤
        taggedLongRaceBPotential ring j b N ∧
      (e = SealedPhaseEdge ring j phase →
        taggedLongRaceNodeCredit
            (taggedLongRaceBPotential ring j b)
            (tagged_long_race_step ring i j k a b N e) + n ≤
          taggedLongRaceBPotential ring j b N) := by
    rw [hz]
    exact ⟨Nat.zero_le _, fun _ => by
      simpa only [Nat.zero_add] using hNat⟩
  have hchild (e : Fin n) :
      taggedLongRaceNodeCredit
          (taggedLongRaceBPotential ring j b)
          (tagged_long_race_step ring i j k a b N e) ≤
        taggedLongRaceBPotential ring j b N ∧
      (e = SealedPhaseEdge ring j phase →
        taggedLongRaceNodeCredit
            (taggedLongRaceBPotential ring j b)
            (tagged_long_race_step ring i j k a b N e) + n ≤
          taggedLongRaceBPotential ring j b N) := by
    by_cases hd : TaggedDeleted i j k (nativeE ring N e)
    · apply hterminal e
      have hnode :
          tagged_long_race_step ring i j k a b N e =
            .success := by
        simp [tagged_long_race_step, hd]
      rw [hnode]
      rfl
    · by_cases hnear :
        TaggedLongNear ring i j k a b (nativeE ring N e)
      · by_cases hready :
          SealedCleanReady ring (nativeE ring N e) j b
        · apply hterminal e
          have hnode :
              tagged_long_race_step ring i j k a b N e =
                .success := by
            simp [tagged_long_race_step, hd, hnear, hready]
          rw [hnode]
          rfl
        · have hnode :
              tagged_long_race_step ring i j k a b N e =
                .active (nativeE ring N e) := by
            simp [tagged_long_race_step, hd, hnear, hready]
          obtain ⟨nextPhase, hnext, hweak, hstrict⟩ :=
            tagged_long_race_b_progress ring i j k a b
              N e hs.1.1 phase hp hnr hd
          have hnew :
              taggedLongRaceBPotential ring j b (nativeE ring N e) =
                n * SealedPhaseProgress b nextPhase :=
            congrArg (Nat.mul n)
              (tagged_long_race_b_rank_value
                ring j b (nativeE ring N e) nextPhase hnext)
          have hchildValue :
              taggedLongRaceNodeCredit
                (taggedLongRaceBPotential ring j b)
                (tagged_long_race_step ring i j k a b N e) =
              taggedLongRaceBPotential ring j b
                (nativeE ring N e) := by
            rw [hnode]
            rfl
          constructor
          · rw [hchildValue, hnew, hOld]
            exact Nat.mul_le_mul_left n hweak
          · intro he
            have hq := hstrict he
            rw [hchildValue, hnew, hOld]
            calc
              n * SealedPhaseProgress b nextPhase + n =
                  n * (SealedPhaseProgress b nextPhase + 1) := by
                rw [Nat.mul_add, Nat.mul_one]
              _ ≤ n * SealedPhaseProgress b phase :=
                Nat.mul_le_mul_left n hq
      · apply hterminal e
        have hnode :
            tagged_long_race_step ring i j k a b N e =
              .failure := by
          simp [tagged_long_race_step, hd, hnear]
        rw [hnode]
        rfl
  have hweak : ∀ e : Fin n,
      taggedLongRaceNodeCredit
        (taggedLongRaceBPotential ring j b)
        (tagged_long_race_step ring i j k a b N e) ≤
        taggedLongRaceBPotential ring j b N :=
    fun e => (hchild e).1
  have hstrict :
      taggedLongRaceNodeCredit
          (taggedLongRaceBPotential ring j b)
          (tagged_long_race_step ring i j k a b N
            (SealedPhaseEdge ring j phase)) + n ≤
        taggedLongRaceBPotential ring j b N :=
    (hchild (SealedPhaseEdge ring j phase)).2 rfl
  exact tagged_q_drift_from_nominated_edge
    (taggedLongRaceBPotential ring j b N)
    (fun e : Fin n => taggedLongRaceNodeCredit
      (taggedLongRaceBPotential ring j b)
      (tagged_long_race_step ring i j k a b N e))
    (SealedPhaseEdge ring j phase) hweak hstrict

/-- B-rank bounds physical stopped cost independently of the A race. -/
theorem tagged_long_race_nonready_cost {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (hs : TaggedLongRaceActive ring i j k a b N) :
    ∀ T,
      truncatedActiveCostNumerator
        (tagged_long_race_step ring i j k a b)
        (.active N) T ≤ n ^ T * (n * (2 * b - 1)) := by
  classical
  have hmain : ∀ (T : Nat) (M : TripleNativeState n),
      TaggedLongRaceActive ring i j k a b M →
      truncatedActiveCostNumerator
        (tagged_long_race_step ring i j k a b)
        (.active M) T ≤
        n ^ T * taggedLongRaceBPotential ring j b M := by
    intro T
    induction T with
    | zero =>
        intro M _
        simp only [truncatedActiveCostNumerator]
        exact Nat.zero_le _
    | succ T ih =>
        intro M hm
        have hdrift :=
          tagged_long_race_b_bellman ring i j k a b M hm
        have hchild (e : Fin n) :
            truncatedActiveCostNumerator
              (tagged_long_race_step ring i j k a b)
              (tagged_long_race_step ring i j k a b M e) T ≤
            n ^ T * taggedLongRaceNodeCredit
              (taggedLongRaceBPotential ring j b)
              (tagged_long_race_step ring i j k a b M e) := by
          cases hnode : tagged_long_race_step ring i j k a b M e with
          | success =>
              cases T <;>
                simp [truncatedActiveCostNumerator,
                  taggedLongRaceNodeCredit]
          | failure =>
              cases T <;>
                simp [truncatedActiveCostNumerator,
                  taggedLongRaceNodeCredit]
          | active W =>
              have hphys :=
                tagged_long_race_active_step ring i j k a b
                  M W e hnode
              change
                truncatedActiveCostNumerator
                  (tagged_long_race_step ring i j k a b)
                  (.active W) T ≤
                n ^ T * taggedLongRaceBPotential ring j b W
              exact ih W hphys.2
        have hsum :
            (List.ofFn (fun e : Fin n =>
              truncatedActiveCostNumerator
                (tagged_long_race_step ring i j k a b)
                (tagged_long_race_step ring i j k a b M e) T)).sum ≤
              n ^ T * (List.ofFn (fun e : Fin n =>
                taggedLongRaceNodeCredit
                  (taggedLongRaceBPotential ring j b)
                  (tagged_long_race_step ring i j k a b M e))).sum := by
          calc
            _ ≤ (List.ofFn (fun e : Fin n =>
                  n ^ T * taggedLongRaceNodeCredit
                    (taggedLongRaceBPotential ring j b)
                    (tagged_long_race_step ring i j k a b M e))).sum :=
              ofFn_sum_le _ _ hchild
            _ = n ^ T * (List.ofFn (fun e : Fin n =>
                  taggedLongRaceNodeCredit
                    (taggedLongRaceBPotential ring j b)
                    (tagged_long_race_step ring i j k a b M e))).sum :=
              ofFn_sum_mul_left (n ^ T) _
        change n ^ (T + 1) +
          (List.ofFn (fun e : Fin n =>
            truncatedActiveCostNumerator
              (tagged_long_race_step ring i j k a b)
              (tagged_long_race_step ring i j k a b M e) T)).sum ≤
            n ^ (T + 1) * taggedLongRaceBPotential ring j b M
        calc
          n ^ (T + 1) +
              (List.ofFn (fun e : Fin n =>
                truncatedActiveCostNumerator
                  (tagged_long_race_step ring i j k a b)
                  (tagged_long_race_step ring i j k a b M e) T)).sum ≤
              n ^ (T + 1) +
                n ^ T * (List.ofFn (fun e : Fin n =>
                  taggedLongRaceNodeCredit
                    (taggedLongRaceBPotential ring j b)
                    (tagged_long_race_step ring i j k a b M e))).sum :=
            Nat.add_le_add_left hsum _
          _ = n ^ T * (n +
                (List.ofFn (fun e : Fin n =>
                  taggedLongRaceNodeCredit
                    (taggedLongRaceBPotential ring j b)
                    (tagged_long_race_step ring i j k a b M e))).sum) := by
            rw [Nat.mul_add, Nat.pow_succ]
          _ ≤ n ^ T * (n * taggedLongRaceBPotential ring j b M) :=
            Nat.mul_le_mul_left _ hdrift
          _ = n ^ (T + 1) *
                taggedLongRaceBPotential ring j b M := by
            rw [Nat.pow_succ, Nat.mul_assoc]
  obtain ⟨phase, hp⟩ := hs.1.2.1
  have hcap :=
    sealed_phase_progress_bound ring N j b phase hp
  have hvalue :
      taggedLongRaceBPotential ring j b N =
        n * SealedPhaseProgress b phase :=
    congrArg (Nat.mul n)
      (tagged_long_race_b_rank_value ring j b N phase hp)
  have hstartcap :
      taggedLongRaceBPotential ring j b N ≤
        n * (2 * b - 1) := by
    rw [hvalue]
    exact Nat.mul_le_mul_left n hcap
  intro T
  exact Nat.le_trans (hmain T N hs)
    (Nat.mul_le_mul_left (n ^ T) hstartcap)

/-- Initially Ready is an immediate stopped success; otherwise the
actual nominated B-front cost is at most n(2b-1). -/
theorem tagged_long_race_cost {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (hret : TaggedLongRetained ring i j k a b N) :
    ∀ T,
      truncatedActiveCostNumerator
        (tagged_long_race_step ring i j k a b)
        (tagged_long_race_start ring j b N) T ≤
          n ^ T * (n * (2 * b - 1)) := by
  have hnear : TaggedLongNear ring i j k a b N := by
    obtain ⟨ht, hB, p, hp, hdist⟩ := hret
    exact ⟨ht, hB, p, hp, by omega⟩
  by_cases hready : SealedCleanReady ring N j b
  · have hzero :=
      tagged_long_race_initial_ready_cost_and_mass
        ring i j k a b N hready
    intro T
    rw [(hzero T).1]
    exact Nat.zero_le _
  · have hstart :
        tagged_long_race_start ring j b N = .active N := by
      classical
      simp [tagged_long_race_start, hready]
    intro T
    rw [hstart]
    exact tagged_long_race_nonready_cost
      hn ring i j k a b N ⟨hnear, hready⟩ T

end L3


/-! ## Physical three-sector edge geometry and off-edge rows

These lemmas do not
claim the full stopped-race half-mass transfer.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false
attribute [local instance low] Classical.propDecidable

/-- Composition of physical clockwise shifts, without assuming
that either of the three tagged endpoints is distinct from the third. -/
theorem tagged_long_site_chain {n : Nat}
    (ring : DirectedRing n) (i : Fin n) (a r : Nat) :
    sealedSite ring (sealedSite ring i a) r =
      sealedSite ring i (a + r) := by
  apply Fin.ext
  change (((i.val + a) % n + r) % n) =
    (i.val + (a + r)) % n
  calc
    ((i.val + a) % n + r) % n =
        (i.val + a + r) % n :=
      Nat.mod_add_mod _ _ _
    _ = (i.val + (a + r)) % n := by
      congr 1
      omega

/-- Remove one complete physical traversal. -/
theorem tagged_long_site_wrap {n : Nat}
    (ring : DirectedRing n) (i : Fin n) (r : Nat)
    (hr : n ≤ r) :
    sealedSite ring i r = sealedSite ring i (r - n) := by
  apply Fin.ext
  change (i.val + r) % n = (i.val + (r - n)) % n
  have he : i.val + r = (i.val + (r - n)) + n := by
    omega
  rw [he, Nat.add_mod_right]

/-- Public source-relative offset inverse for the Fin n edge
classifier; the corresponding library lemma is private. -/
theorem tagged_long_site_position {n : Nat}
    (ring : DirectedRing n) (i : Fin n) (r : Nat)
    (hr : r < n) :
    (SealedCloseProof.position ring i
      (sealedSite ring i r)).val = r := by
  have he :
      SealedCloseProof.position ring i
        (sealedSite ring i r) = (⟨r, hr⟩ : Fin n) := by
    apply Fin.ext
    change (((i.val + r) % n + n - i.val) % n) = r
    by_cases hs : i.val + r < n
    · rw [Nat.mod_eq_of_lt hs]
      have hx : i.val + r + n - i.val = n + r := by
        omega
      rw [hx, Nat.add_mod_left, Nat.mod_eq_of_lt hr]
    · have hge : n ≤ i.val + r := by omega
      have hlt : i.val + r - n < n := by
        have hi := i.isLt
        omega
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
      have hx : i.val + r - n + n - i.val = r := by
        omega
      rw [hx, Nat.mod_eq_of_lt hr]
  exact congrArg Fin.val he

/-- The two actual consecutive native sectors cannot overlap.
If i=k this proof still applies: the two gaps can fill the ring,
but their half-open source intervals remain disjoint. -/
theorem tagged_long_triple_gap_le {n : Nat}
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (ht : TaggedTriple ring i j k a b N) :
    a + b ≤ n := by
  obtain ⟨haPos, haLt, hj, _, _, hquiet⟩ := ht.2.1
  obtain ⟨hbPos, hbLt, hk, _, hkLeader, _⟩ := ht.2.2
  by_cases hsum : a + b ≤ n
  · exact hsum
  · have hr : a + b - n < n := by omega
    have hsite : k = sealedSite ring i (a + b - n) := by
      calc
        k = sealedSite ring j b := hk
        _ = sealedSite ring (sealedSite ring i a) b := by
          rw [hj]
        _ = sealedSite ring i (a + b) :=
          tagged_long_site_chain ring i a b
        _ = sealedSite ring i (a + b - n) :=
          tagged_long_site_wrap ring i (a + b) (by omega)
    have hz := hquiet
      (⟨a + b - n, hr⟩ : Fin n)
      (by omega : 0 < a + b - n)
      (by omega : a + b - n < a)
    change (N (sealedSite ring i (a + b - n))).l = false at hz
    rw [← hsite] at hz
    rw [hkLeader] at hz
    cases hz

/-- An edge cannot lie simultaneously in the two physical source
sectors [i,j) and [j,k), including in the i=k two-leader case. -/
theorem tagged_long_region_exclusion {n : Nat}
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (ht : TaggedTriple ring i j k a b N)
    (e : Fin n) (r s : Nat)
    (hr : r < a) (hs : s < b)
    (heA : e = sealedSite ring i r)
    (heB : e = sealedSite ring j s) : False := by
  have hgap := tagged_long_triple_gap_le ring i j k a b N ht
  have hj : j = sealedSite ring i a := ht.2.1.2.2.1
  have hsame :
      sealedSite ring i r = sealedSite ring i (a + s) := by
    calc
      sealedSite ring i r = e := heA.symm
      _ = sealedSite ring j s := heB
      _ = sealedSite ring (sealedSite ring i a) s := by
        rw [hj]
      _ = sealedSite ring i (a + s) :=
        tagged_long_site_chain ring i a s
  have heq := congrArg
    (fun x : Fin n => (SealedCloseProof.position ring i x).val)
    hsame
  rw [tagged_long_site_position ring i r (by omega : r < n),
    tagged_long_site_position ring i (a + s)
      (by omega : a + s < n)] at heq
  omega

/-- Explicit Fin n trichotomy for a physical scheduler edge:
source in A=[i,j), source in B=[j,k), or source in the
complementary third sector. It never assumes i != k. -/
theorem tagged_long_fin_trichotomy {n : Nat}
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (ht : TaggedTriple ring i j k a b N)
    (e : Fin n) :
    ((SealedCloseProof.position ring i e).val < a ∧
      b ≤ (SealedCloseProof.position ring j e).val) ∨
    ((SealedCloseProof.position ring j e).val < b ∧
      a ≤ (SealedCloseProof.position ring i e).val) ∨
    (a ≤ (SealedCloseProof.position ring i e).val ∧
      b ≤ (SealedCloseProof.position ring j e).val) := by
  have hdisjoint :
      ¬ ((SealedCloseProof.position ring i e).val < a ∧
        (SealedCloseProof.position ring j e).val < b) := by
    intro h
    exact tagged_long_region_exclusion
      ring i j k a b N ht e
      (SealedCloseProof.position ring i e).val
      (SealedCloseProof.position ring j e).val
      h.1 h.2
      (sealed_close_edge_of_position ring i e _ rfl)
      (sealed_close_edge_of_position ring j e _ rfl)
  by_cases hA : (SealedCloseProof.position ring i e).val < a
  · have hB : b ≤ (SealedCloseProof.position ring j e).val := by
      have hnB :
          ¬ (SealedCloseProof.position ring j e).val < b := by
        intro hb
        exact hdisjoint ⟨hA, hb⟩
      omega
    exact Or.inl ⟨hA, hB⟩
  · by_cases hB : (SealedCloseProof.position ring j e).val < b
    · have hnA : a ≤ (SealedCloseProof.position ring i e).val := by
        omega
      exact Or.inr (Or.inl ⟨hB, hnA⟩)
    · have hnA : a ≤ (SealedCloseProof.position ring i e).val := by
        omega
      have hnB : b ≤ (SealedCloseProof.position ring j e).val := by
        omega
      exact Or.inr (Or.inr ⟨hnA, hnB⟩)

/-- The actual A-live and B-stage nominated physical scheduler
edges are different even when the first and third leaders coincide. -/
theorem tagged_long_nominated_edges_distinct {n : Nat}
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (ht : TaggedTriple ring i j k a b N)
    (p : Fin n)
    (hp : SealedPhaseHolds ring N i a (.live p))
    (phase : SealedPhase n)
    (hb : SealedPhaseHolds ring N j b phase) :
    SealedPhaseEdge ring i (.live p) ≠
      SealedPhaseEdge ring j phase := by
  have hA :
      (SealedCloseProof.position ring i
        (SealedPhaseEdge ring i (.live p))).val < a := by
    rw [sealed_close_nominated_position
      ring N i j a (.live p) ht.2.1 hp]
    simpa only [SealedCloseProof.fromPhase,
      SealedCloseProof.nominated] using hp.1.1
  have hB :
      (SealedCloseProof.position ring j
        (SealedPhaseEdge ring j phase)).val < b := by
    rw [sealed_close_nominated_position
      ring N j k b phase ht.2.2 hb]
    exact sealed_close_nominated_lt
      ring N j k b phase ht.2.2 hb
  intro he
  have hBSame :
      (SealedCloseProof.position ring j
        (SealedPhaseEdge ring i (.live p))).val < b := by
    rw [he]
    exact hB
  have htrich := tagged_long_fin_trichotomy
    ring i j k a b N ht (SealedPhaseEdge ring i (.live p))
  rcases htrich with hleft | hright | houtside
  · omega
  · omega
  · omega

/-- Every non-A-nominated surviving nativeE service preserves the
same *physical* A-live bullet, even at its final pre-j position.
This is the off-edge row missing from the old far-front-only lemma. -/
theorem tagged_long_live_off_nomination {n : Nat}
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n) (e : Fin n)
    (ht : TaggedTriple ring i j k a b N)
    (p : Fin n)
    (hp : SealedPhaseHolds ring N i a (.live p))
    (hne : e ≠ SealedPhaseEdge ring i (.live p))
    (hnot : ¬ TaggedDeleted i j k (nativeE ring N e)) :
    SealedPhaseHolds ring (nativeE ring N e) i a (.live p) := by
  have hi : (nativeE ring N e i).l = true := by
    cases hx : (nativeE ring N e i).l with
    | false => exact False.elim (hnot (Or.inl hx))
    | true => rfl
  have hj : (nativeE ring N e j).l = true := by
    cases hx : (nativeE ring N e j).l with
    | false => exact False.elim (hnot (Or.inr (Or.inl hx)))
    | true => rfl
  obtain ⟨nextPhase, hnext, hstage⟩ :=
    sealed_close_step_stage
      ring N i j a e (.live p) ht.2.1 hp hi hj
  have hnotIndex :
      (SealedCloseProof.position ring i e).val ≠ p.val := by
    intro heq
    have hphysical :=
      sealed_close_edge_of_position ring i e p.val heq
    have hnom :
        sealedSite ring i p.val =
          SealedPhaseEdge ring i (.live p) := rfl
    exact hne (hphysical.trans hnom)
  have htable :
      sealedCloseTable ring i a e (.live p) =
        .bullet true p.val := by
    change
      (if (SealedCloseProof.position ring i e).val < a then
        SealedCloseProof.insideStage a (.bullet true p.val)
          (SealedCloseProof.position ring i e).val
       else if (SealedCloseProof.position ring i e).val + 1 = n then
         SealedCloseProof.incomingStage (.bullet true p.val)
       else .bullet true p.val) = .bullet true p.val
    by_cases hinside : (SealedCloseProof.position ring i e).val < a
    · simp [hinside, SealedCloseProof.insideStage, hnotIndex]
    · simp [hinside, SealedCloseProof.incomingStage]
  have hactual :
      SealedCloseProof.fromPhase nextPhase =
        .bullet true p.val := hstage.trans htable
  cases nextPhase with
  | ready => cases hactual
  | dummy q => cases hactual
  | live q =>
      have hval : q.val = p.val := by
        have hh := congrArg SealedCloseProof.nominated hactual
        simpa only [SealedCloseProof.fromPhase,
          SealedCloseProof.nominated] using hh
      have heq : q = p := Fin.ext hval
      rw [heq] at hnext
      exact hnext
  | returning q => cases hactual

/-- Every off-B-nominated surviving nativeE service preserves the
*actual* extracted B-stage rank, rather than merely bounding it above.
Ready is excluded because an incoming edge can create Dummy(0). -/
theorem tagged_long_b_off_nomination {n : Nat}
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n) (e : Fin n)
    (ht : TaggedTriple ring i j k a b N)
    (phase : SealedPhase n)
    (hp : SealedPhaseHolds ring N j b phase)
    (hnr : phase ≠ .ready)
    (hne : e ≠ SealedPhaseEdge ring j phase)
    (hnot : ¬ TaggedDeleted i j k (nativeE ring N e)) :
    taggedLongRaceBRank ring j b (nativeE ring N e) =
      taggedLongRaceBRank ring j b N := by
  have hj : (nativeE ring N e j).l = true := by
    cases hx : (nativeE ring N e j).l with
    | false => exact False.elim (hnot (Or.inr (Or.inl hx)))
    | true => rfl
  have hk : (nativeE ring N e k).l = true := by
    cases hx : (nativeE ring N e k).l with
    | false => exact False.elim (hnot (Or.inr (Or.inr hx)))
    | true => rfl
  obtain ⟨nextPhase, hnext, hstage⟩ :=
    sealed_close_step_stage
      ring N j k b e phase ht.2.2 hp hj hk
  have hnotIndex :
      (SealedCloseProof.position ring j e).val ≠
        SealedCloseProof.nominated
          (SealedCloseProof.fromPhase phase) := by
    intro hindex
    have hphysical :=
      sealed_close_edge_of_position ring j e
        (SealedCloseProof.nominated
          (SealedCloseProof.fromPhase phase)) hindex
    have hnom :
        sealedSite ring j
          (SealedCloseProof.nominated
            (SealedCloseProof.fromPhase phase)) =
          SealedPhaseEdge ring j phase := by
      cases phase with
      | ready => exact False.elim (hnr rfl)
      | _ => rfl
    exact hne (hphysical.trans hnom)
  have htable :
      sealedCloseTable ring j b e phase =
        SealedCloseProof.fromPhase phase := by
    cases phase with
    | ready => exact False.elim (hnr rfl)
    | dummy p =>
        have hnePos :
            (SealedCloseProof.position ring j e).val ≠ p.val := by
          simpa only [SealedCloseProof.fromPhase,
            SealedCloseProof.nominated] using hnotIndex
        change
          (if (SealedCloseProof.position ring j e).val < b then
            SealedCloseProof.insideStage b (.bullet false p.val)
              (SealedCloseProof.position ring j e).val
           else if (SealedCloseProof.position ring j e).val + 1 = n then
             SealedCloseProof.incomingStage (.bullet false p.val)
           else .bullet false p.val) = .bullet false p.val
        by_cases hinside : (SealedCloseProof.position ring j e).val < b
        · simp [hinside, SealedCloseProof.insideStage, hnePos]
        · simp [hinside, SealedCloseProof.incomingStage]
    | live p =>
        have hnePos :
            (SealedCloseProof.position ring j e).val ≠ p.val := by
          simpa only [SealedCloseProof.fromPhase,
            SealedCloseProof.nominated] using hnotIndex
        change
          (if (SealedCloseProof.position ring j e).val < b then
            SealedCloseProof.insideStage b (.bullet true p.val)
              (SealedCloseProof.position ring j e).val
           else if (SealedCloseProof.position ring j e).val + 1 = n then
             SealedCloseProof.incomingStage (.bullet true p.val)
           else .bullet true p.val) = .bullet true p.val
        by_cases hinside : (SealedCloseProof.position ring j e).val < b
        · simp [hinside, SealedCloseProof.insideStage, hnePos]
        · simp [hinside, SealedCloseProof.incomingStage]
    | returning q =>
        have hqpos : 0 < q.val := hp.2.2.1
        have hnePos :
            (SealedCloseProof.position ring j e).val + 1 ≠ q.val := by
          intro heq
          apply hnotIndex
          change (SealedCloseProof.position ring j e).val =
            q.val - 1
          omega
        change
          (if (SealedCloseProof.position ring j e).val < b then
            SealedCloseProof.insideStage b (.returning q.val)
              (SealedCloseProof.position ring j e).val
           else if (SealedCloseProof.position ring j e).val + 1 = n then
             SealedCloseProof.incomingStage (.returning q.val)
           else .returning q.val) = .returning q.val
        by_cases hinside : (SealedCloseProof.position ring j e).val < b
        · simp [hinside, SealedCloseProof.insideStage, hnePos]
        · simp [hinside, SealedCloseProof.incomingStage]
  have hrank :
      SealedPhaseProgress b nextPhase =
        SealedPhaseProgress b phase := by
    calc
      SealedPhaseProgress b nextPhase =
          SealedCloseProof.rank b
            (SealedCloseProof.fromPhase nextPhase) := by
        cases nextPhase <;> rfl
      _ = SealedCloseProof.rank b
            (SealedCloseProof.fromPhase phase) :=
        congrArg (SealedCloseProof.rank b) (hstage.trans htable)
      _ = SealedPhaseProgress b phase := by
        cases phase <;> rfl
  calc
    taggedLongRaceBRank ring j b (nativeE ring N e) =
        SealedPhaseProgress b nextPhase :=
      tagged_long_race_b_rank_value
        ring j b (nativeE ring N e) nextPhase hnext
    _ = SealedPhaseProgress b phase := hrank
    _ = taggedLongRaceBRank ring j b N :=
      (tagged_long_race_b_rank_value ring j b N phase hp).symm

end L3



/-! ## Physical A-front rows and three-way race classifier

All the new successor statements below concern
the one actual nativeE scheduler edge, including the two-leader i = k case.
No independent ghost update is asserted here.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false
attribute [local instance low] Classical.propDecidable

/-- The A quota used by the fair two-front race is the actual
remaining clockwise distance of the unique A-live bullet. It is
zero outside a live stage; the active race always has a live stage. -/
noncomputable def taggedLongRaceAQuota {n : Nat}
    (ring : DirectedRing n) (i : Fin n) (a : Nat)
    (N : TripleNativeState n) : Nat :=
  match taggedQAttackerPhase ring i a N with
  | .live p => a - p.val
  | _ => 0

theorem tagged_long_race_a_quota_value {n : Nat}
    (ring : DirectedRing n) (i : Fin n) (a : Nat)
    (N : TripleNativeState n) (p : Fin n)
    (hp : SealedPhaseHolds ring N i a (.live p)) :
    taggedLongRaceAQuota ring i a N = a - p.val := by
  unfold taggedLongRaceAQuota
  rw [tagged_q_attacker_phase_eq ring N i a (.live p) hp]

/-- The near constraint applies to any physically valid witness
of the live A bullet, not only the existential witness originally
chosen in TaggedLongNear. -/
theorem tagged_long_race_a_near_witness {n : Nat}
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (hnear : TaggedLongNear ring i j k a b N)
    (p : Fin n)
    (hp : SealedPhaseHolds ring N i a (.live p)) :
    a ≤ p.val + 2 * b := by
  obtain ⟨old, hold, hbound⟩ := hnear.2.2
  have heq : old = p := by
    have hphase :
        (SealedPhase.live old : SealedPhase n) = .live p :=
      tagged_sealed_phase_unique ring N i a
        (.live old) (.live p) hold hp
    cases hphase
    rfl
  rw [heq] at hbound
  exact hbound

/-- The literal insideStage on A's nominated physical edge, while
at least one interior hop remains, produces the next A-live
phase at p+1, retaining the original near race domain. This
statement only excludes actual deletion of a tagged endpoint. -/
theorem tagged_long_race_a_nominated_interior_native {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (hs : TaggedLongRaceActive ring i j k a b N)
    (p : Fin n)
    (hp : SealedPhaseHolds ring N i a (.live p))
    (hinterior : p.val + 1 < a)
    (hnot : ¬ TaggedDeleted i j k
      (nativeE ring N (SealedPhaseEdge ring i (.live p)))) :
    ∃ q : Fin n,
      TaggedLongNear ring i j k a b
        (nativeE ring N (SealedPhaseEdge ring i (.live p))) ∧
      SealedPhaseHolds ring
        (nativeE ring N (SealedPhaseEdge ring i (.live p)))
        i a (.live q) ∧
      q.val = p.val + 1 := by
  have hi :
      (nativeE ring N (SealedPhaseEdge ring i (.live p)) i).l =
        true := by
    cases hx :
        (nativeE ring N (SealedPhaseEdge ring i (.live p)) i).l with
    | false => exact False.elim (hnot (Or.inl hx))
    | true => rfl
  have hj :
      (nativeE ring N (SealedPhaseEdge ring i (.live p)) j).l =
        true := by
    cases hx :
        (nativeE ring N (SealedPhaseEdge ring i (.live p)) j).l with
    | false => exact False.elim (hnot (Or.inr (Or.inl hx)))
    | true => rfl
  obtain ⟨nextPhase, hnext, hstage⟩ :=
    sealed_close_step_stage ring N i j a
      (SealedPhaseEdge ring i (.live p)) (.live p)
      hs.1.1.2.1 hp hi hj
  have hpos :
      (SealedCloseProof.position ring i
        (SealedPhaseEdge ring i (.live p))).val = p.val := by
    simpa only [SealedCloseProof.fromPhase,
      SealedCloseProof.nominated] using
      (sealed_close_nominated_position
        ring N i j a (.live p) hs.1.1.2.1 hp)
  have htable :
      sealedCloseTable ring i a
        (SealedPhaseEdge ring i (.live p)) (.live p) =
          .bullet true (p.val + 1) := by
    change
      (if (SealedCloseProof.position ring i
          (SealedPhaseEdge ring i (.live p))).val < a then
        SealedCloseProof.insideStage a (.bullet true p.val)
          (SealedCloseProof.position ring i
            (SealedPhaseEdge ring i (.live p))).val
       else if (SealedCloseProof.position ring i
          (SealedPhaseEdge ring i (.live p))).val + 1 = n then
        SealedCloseProof.incomingStage (.bullet true p.val)
       else .bullet true p.val) =
          .bullet true (p.val + 1)
    rw [hpos]
    simpa only [ite_true] using
      (tagged_long_live_step_table n a p.val p.val hinterior)
  have hstageLive :
      SealedCloseProof.fromPhase nextPhase =
        .bullet true (p.val + 1) := hstage.trans htable
  cases nextPhase with
  | ready =>
      cases hstageLive
  | dummy q =>
      cases hstageLive
  | live q =>
      have hqval : q.val = p.val + 1 := by
        have hh :=
          congrArg SealedCloseProof.nominated hstageLive
        simpa only [SealedCloseProof.fromPhase,
          SealedCloseProof.nominated] using hh
      have hnearOld :=
        tagged_long_race_a_near_witness
          ring i j k a b N hs.1 p hp
      have htripleNext :=
        tagged_triple_step_of_survival hn ring i j k a b
          N (SealedPhaseEdge ring i (.live p)) hs.1.1 hnot
      have hsealedNext :=
        tagged_sealed_step_of_survival
          ring i j k a b N
          (SealedPhaseEdge ring i (.live p)) hs.1.1
          ⟨⟨.live p, hp⟩, hs.1.2.1⟩ hnot
      refine ⟨q, ⟨htripleNext, hsealedNext.2,
        q, hnext, ?_⟩, hnext, hqval⟩
      omega
  | returning q =>
      cases hstageLive

/-- First physical A nominated row: in the interior, either the
actual tagged deletion stops successfully, or the stopped
successor is active with A's remaining live quota exactly
one smaller and the current nonready B rank unchanged. If B
becomes Ready, that is a success rather than an active child. -/
theorem tagged_long_race_a_nominated_interior {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (hs : TaggedLongRaceActive ring i j k a b N)
    (p : Fin n)
    (hp : SealedPhaseHolds ring N i a (.live p))
    (hinterior : p.val + 1 < a) :
    tagged_long_race_step ring i j k a b N
      (SealedPhaseEdge ring i (.live p)) = .success ∨
    ∃ q : Fin n,
      tagged_long_race_step ring i j k a b N
        (SealedPhaseEdge ring i (.live p)) =
          .active (nativeE ring N (SealedPhaseEdge ring i (.live p))) ∧
      SealedPhaseHolds ring
        (nativeE ring N (SealedPhaseEdge ring i (.live p)))
        i a (.live q) ∧
      q.val = p.val + 1 ∧
      a - q.val + 1 = a - p.val ∧
      taggedLongRaceBRank ring j b
        (nativeE ring N (SealedPhaseEdge ring i (.live p))) =
          taggedLongRaceBRank ring j b N := by
  classical
  by_cases hdel :
      TaggedDeleted i j k
        (nativeE ring N (SealedPhaseEdge ring i (.live p)))
  · left
    simp [tagged_long_race_step, hdel]
  · obtain ⟨q, hnearNext, hphaseNext, hqval⟩ :=
      tagged_long_race_a_nominated_interior_native
        hn ring i j k a b N hs p hp hinterior hdel
    by_cases hready :
        SealedCleanReady ring
          (nativeE ring N (SealedPhaseEdge ring i (.live p)))
          j b
    · left
      simp [tagged_long_race_step, hdel, hnearNext, hready]
    · right
      obtain ⟨phase, hBphase⟩ := hs.1.2.1
      have hnr : phase ≠ .ready := by
        intro he
        cases he
        exact hs.2 hBphase
      have hneB :
          SealedPhaseEdge ring i (.live p) ≠
            SealedPhaseEdge ring j phase :=
        tagged_long_nominated_edges_distinct
          ring i j k a b N hs.1.1 p hp phase hBphase
      have hrank :=
        tagged_long_b_off_nomination
          ring i j k a b N
          (SealedPhaseEdge ring i (.live p))
          hs.1.1 phase hBphase hnr hneB hdel
      have hdecrease : a - q.val + 1 = a - p.val := by
        omega
      refine ⟨q, ?_, hphaseNext, hqval, hdecrease, hrank⟩
      simp [tagged_long_race_step, hdel, hnearNext, hready]

/-- The final A-live nominated row has no live-stage successor
after the actual nativeE service. The physical insideStage entry
is either Ready (offset zero) or Returning(p) (positive offset).
This assertion is made after excluding a tagged deletion, and it
does not assume that the target B was already Ready. -/
theorem tagged_long_race_a_nominated_boundary_native {n : Nat}
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (hs : TaggedLongRaceActive ring i j k a b N)
    (p : Fin n)
    (hp : SealedPhaseHolds ring N i a (.live p))
    (hboundary : p.val + 1 = a)
    (hnot : ¬ TaggedDeleted i j k
      (nativeE ring N (SealedPhaseEdge ring i (.live p)))) :
    ¬ TaggedLongNear ring i j k a b
      (nativeE ring N (SealedPhaseEdge ring i (.live p))) := by
  have hi :
      (nativeE ring N (SealedPhaseEdge ring i (.live p)) i).l =
        true := by
    cases hx :
        (nativeE ring N (SealedPhaseEdge ring i (.live p)) i).l with
    | false => exact False.elim (hnot (Or.inl hx))
    | true => rfl
  have hj :
      (nativeE ring N (SealedPhaseEdge ring i (.live p)) j).l =
        true := by
    cases hx :
        (nativeE ring N (SealedPhaseEdge ring i (.live p)) j).l with
    | false => exact False.elim (hnot (Or.inr (Or.inl hx)))
    | true => rfl
  obtain ⟨nextPhase, hnext, hstage⟩ :=
    sealed_close_step_stage ring N i j a
      (SealedPhaseEdge ring i (.live p)) (.live p)
      hs.1.1.2.1 hp hi hj
  have hpos :
      (SealedCloseProof.position ring i
        (SealedPhaseEdge ring i (.live p))).val = p.val := by
    simpa only [SealedCloseProof.fromPhase,
      SealedCloseProof.nominated] using
      (sealed_close_nominated_position
        ring N i j a (.live p) hs.1.1.2.1 hp)
  have htable :
      sealedCloseTable ring i a
        (SealedPhaseEdge ring i (.live p)) (.live p) =
          if p.val = 0 then .ready else .returning p.val := by
    change
      (if (SealedCloseProof.position ring i
          (SealedPhaseEdge ring i (.live p))).val < a then
        SealedCloseProof.insideStage a (.bullet true p.val)
          (SealedCloseProof.position ring i
            (SealedPhaseEdge ring i (.live p))).val
       else if (SealedCloseProof.position ring i
          (SealedPhaseEdge ring i (.live p))).val + 1 = n then
        SealedCloseProof.incomingStage (.bullet true p.val)
       else .bullet true p.val) =
          if p.val = 0 then .ready else .returning p.val
    rw [hpos]
    have hlt : p.val < a := by omega
    simp only [ite_true, if_pos hlt, SealedCloseProof.insideStage,
      if_pos rfl, if_pos hboundary]
  have hstageTerminal :
      SealedCloseProof.fromPhase nextPhase =
        if p.val = 0 then .ready else .returning p.val :=
    hstage.trans htable
  intro hnear
  obtain ⟨q, hq, _⟩ := hnear.2.2
  have huniq :=
    tagged_sealed_phase_unique
      ring (nativeE ring N (SealedPhaseEdge ring i (.live p)))
      i a nextPhase (.live q) hnext hq
  have hcontra :
      (if p.val = 0 then SealedCloseProof.Stage.ready
        else SealedCloseProof.Stage.returning p.val) =
          SealedCloseProof.Stage.bullet true q.val := by
    calc
      (if p.val = 0 then SealedCloseProof.Stage.ready
          else SealedCloseProof.Stage.returning p.val) =
        SealedCloseProof.fromPhase nextPhase :=
          hstageTerminal.symm
      _ = SealedCloseProof.fromPhase (.live q : SealedPhase n) :=
        congrArg SealedCloseProof.fromPhase huniq
      _ = SealedCloseProof.Stage.bullet true q.val := rfl
  by_cases hz : p.val = 0
  · simp only [if_pos hz] at hcontra
    cases hcontra
  · simp only [if_neg hz] at hcontra
    cases hcontra

/-- The literal final A-live service is an A-terminal race letter:
either it deletes a tag (success), or, because A no longer has a
live bullet, the stopped race enters its failure branch. -/
theorem tagged_long_race_a_nominated_boundary {n : Nat}
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (hs : TaggedLongRaceActive ring i j k a b N)
    (p : Fin n)
    (hp : SealedPhaseHolds ring N i a (.live p))
    (hboundary : p.val + 1 = a) :
    tagged_long_race_step ring i j k a b N
      (SealedPhaseEdge ring i (.live p)) = .success ∨
    tagged_long_race_step ring i j k a b N
      (SealedPhaseEdge ring i (.live p)) = .failure := by
  classical
  by_cases hdel :
      TaggedDeleted i j k
        (nativeE ring N (SealedPhaseEdge ring i (.live p)))
  · left
    simp [tagged_long_race_step, hdel]
  · right
    have hnotNear :=
      tagged_long_race_a_nominated_boundary_native
        ring i j k a b N hs p hp hboundary hdel
    simp [tagged_long_race_step, hdel, hnotNear]

/-- Every other physical edge preserves the actual A-live bullet.
Together with survival of the sealed B sector, this forbids an
A-terminal failure on a non-A-nominated scheduler letter, even
if the very same edge happens to make B Ready. -/
theorem tagged_long_race_a_off_nomination_never_failure {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (hs : TaggedLongRaceActive ring i j k a b N)
    (e : Fin n) (p : Fin n)
    (hp : SealedPhaseHolds ring N i a (.live p))
    (hne : e ≠ SealedPhaseEdge ring i (.live p)) :
    tagged_long_race_step ring i j k a b N e ≠ .failure := by
  classical
  by_cases hdel : TaggedDeleted i j k (nativeE ring N e)
  · simp [tagged_long_race_step, hdel]
  · have hphaseNext :=
      tagged_long_live_off_nomination
        ring i j k a b N e hs.1.1 p hp hne hdel
    have htripleNext :=
      tagged_triple_step_of_survival
        hn ring i j k a b N e hs.1.1 hdel
    have hsealedNext :=
      tagged_sealed_step_of_survival
        ring i j k a b N e hs.1.1
        ⟨⟨.live p, hp⟩, hs.1.2.1⟩ hdel
    have hbound :=
      tagged_long_race_a_near_witness
        ring i j k a b N hs.1 p hp
    have hnearNext :
        TaggedLongNear ring i j k a b (nativeE ring N e) :=
      ⟨htripleNext, hsealedNext.2, p, hphaseNext, hbound⟩
    by_cases hready :
        SealedCleanReady ring (nativeE ring N e) j b
    · simp [tagged_long_race_step, hdel, hnearNext, hready]
    · simp [tagged_long_race_step, hdel, hnearNext, hready]

/-- Any active stopped successor is the actual nativeE result and
has not deleted any tagged leader. This is only a case analysis
of the already-defined stop dispatcher. -/
theorem tagged_long_race_active_not_deleted {n : Nat}
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N M : TripleNativeState n) (e : Fin n)
    (hactive :
      tagged_long_race_step ring i j k a b N e = .active M) :
    ¬ TaggedDeleted i j k (nativeE ring N e) := by
  intro hdel
  have hsuccess :
      tagged_long_race_step ring i j k a b N e = .success := by
    simp [tagged_long_race_step, hdel]
  rw [hsuccess] at hactive
  cases hactive

/-- D.19 physically coupled edge specification, at every active
native configuration (not at a presupposed future state).

B nomination: success, or an active child whose B rank falls while
A's live quota is unchanged.
A nomination: success, A-terminal failure, or an active child whose
live quota falls exactly one while B's rank is unchanged.
All other physical edges: success or an active child preserving both.

The two nominated edges are distinct by the already established trichotomy
even in the two-leader i = k case. -/
def TaggedLongRacePhysicalEdgeSpec {n : Nat}
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat) : Prop :=
  ∀ (N : TripleNativeState n),
    TaggedLongRaceActive ring i j k a b N →
    ∀ (p : Fin n) (phase : SealedPhase n),
      SealedPhaseHolds ring N i a (.live p) →
      SealedPhaseHolds ring N j b phase →
      ∀ e : Fin n,
        (e = SealedPhaseEdge ring j phase →
          tagged_long_race_step ring i j k a b N e = .success ∨
          ∃ M : TripleNativeState n,
            tagged_long_race_step ring i j k a b N e = .active M ∧
            taggedLongRaceBRank ring j b M + 1 ≤
              taggedLongRaceBRank ring j b N ∧
            taggedLongRaceAQuota ring i a M =
              taggedLongRaceAQuota ring i a N) ∧
        (e = SealedPhaseEdge ring i (.live p) →
          tagged_long_race_step ring i j k a b N e = .success ∨
          tagged_long_race_step ring i j k a b N e = .failure ∨
          ∃ M : TripleNativeState n,
            tagged_long_race_step ring i j k a b N e = .active M ∧
            taggedLongRaceAQuota ring i a M + 1 =
              taggedLongRaceAQuota ring i a N ∧
            taggedLongRaceBRank ring j b M =
              taggedLongRaceBRank ring j b N) ∧
        (e ≠ SealedPhaseEdge ring j phase ∧
          e ≠ SealedPhaseEdge ring i (.live p) →
          tagged_long_race_step ring i j k a b N e = .success ∨
          ∃ M : TripleNativeState n,
            tagged_long_race_step ring i j k a b N e = .active M ∧
            taggedLongRaceAQuota ring i a M =
              taggedLongRaceAQuota ring i a N ∧
            taggedLongRaceBRank ring j b M =
              taggedLongRaceBRank ring j b N)

/-- Physical three-way classifier assembled from the two actual
nominated source regions, the literal A final-row classification,
the off-nomination equalities, and B's progress law. -/
theorem tagged_long_race_physical_edge_spec {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat) :
    TaggedLongRacePhysicalEdgeSpec ring i j k a b := by
  intro N hs p phase hp hphase e
  have ht : TaggedTriple ring i j k a b N := hs.1.1
  have hnr : phase ≠ .ready := by
    intro he
    cases he
    exact hs.2 hphase
  have hdistinct :
      SealedPhaseEdge ring i (.live p) ≠
        SealedPhaseEdge ring j phase :=
    tagged_long_nominated_edges_distinct
      ring i j k a b N ht p hp phase hphase
  refine ⟨?_, ?_, ?_⟩
  · intro hBnom
    subst e
    have hnotA :
        SealedPhaseEdge ring j phase ≠
          SealedPhaseEdge ring i (.live p) :=
      Ne.symm hdistinct
    have hnotFailure :=
      tagged_long_race_a_off_nomination_never_failure
        hn ring i j k a b N hs
        (SealedPhaseEdge ring j phase) p hp hnotA
    cases hnode :
        tagged_long_race_step ring i j k a b N
          (SealedPhaseEdge ring j phase) with
    | success =>
        exact Or.inl rfl
    | failure =>
        exact False.elim (hnotFailure hnode)
    | active M =>
        obtain ⟨hM, _⟩ :=
          tagged_long_race_active_step
            ring i j k a b N M (SealedPhaseEdge ring j phase)
            hnode
        subst M
        have hnotDelete :=
          tagged_long_race_active_not_deleted
            ring i j k a b N
            (nativeE ring N (SealedPhaseEdge ring j phase))
            (SealedPhaseEdge ring j phase) hnode
        obtain ⟨nextPhase, hnext, _, hstrict⟩ :=
          tagged_long_race_b_progress
            ring i j k a b N
            (SealedPhaseEdge ring j phase)
            ht phase hphase hnr hnotDelete
        have hBdecrease :
            taggedLongRaceBRank ring j b
              (nativeE ring N (SealedPhaseEdge ring j phase)) + 1 ≤
                taggedLongRaceBRank ring j b N := by
          rw [tagged_long_race_b_rank_value
            ring j b
            (nativeE ring N (SealedPhaseEdge ring j phase))
            nextPhase hnext,
            tagged_long_race_b_rank_value
              ring j b N phase hphase]
          exact hstrict rfl
        have hAphase :=
          tagged_long_live_off_nomination
            ring i j k a b N
            (SealedPhaseEdge ring j phase)
            ht p hp hnotA hnotDelete
        have hAsame :
            taggedLongRaceAQuota ring i a
              (nativeE ring N (SealedPhaseEdge ring j phase)) =
                taggedLongRaceAQuota ring i a N := by
          calc
            taggedLongRaceAQuota ring i a
                (nativeE ring N (SealedPhaseEdge ring j phase)) =
                  a - p.val :=
              tagged_long_race_a_quota_value
                ring i a
                (nativeE ring N (SealedPhaseEdge ring j phase))
                p hAphase
            _ = taggedLongRaceAQuota ring i a N :=
              (tagged_long_race_a_quota_value
                ring i a N p hp).symm
        exact Or.inr ⟨
          nativeE ring N (SealedPhaseEdge ring j phase),
          rfl, hBdecrease, hAsame⟩
  · intro hAnom
    subst e
    by_cases hinterior : p.val + 1 < a
    · rcases tagged_long_race_a_nominated_interior
        hn ring i j k a b N hs p hp hinterior with
        hsuccess | ⟨q, hnode, hqphase, hqpos, hdecrease, hBsame⟩
      · exact Or.inl hsuccess
      · have hAdecrease :
            taggedLongRaceAQuota ring i a
              (nativeE ring N (SealedPhaseEdge ring i (.live p))) + 1 =
              taggedLongRaceAQuota ring i a N := by
          calc
            taggedLongRaceAQuota ring i a
                (nativeE ring N (SealedPhaseEdge ring i (.live p))) + 1 =
                (a - q.val) + 1 :=
              congrArg (fun z : Nat => z + 1)
                (tagged_long_race_a_quota_value
                  ring i a
                  (nativeE ring N (SealedPhaseEdge ring i (.live p)))
                  q hqphase)
            _ = a - p.val := hdecrease
            _ = taggedLongRaceAQuota ring i a N :=
              (tagged_long_race_a_quota_value ring i a N p hp).symm
        exact Or.inr (Or.inr ⟨
          nativeE ring N (SealedPhaseEdge ring i (.live p)),
          hnode, hAdecrease, hBsame⟩)
    · have hboundary : p.val + 1 = a := by
        have hlt : p.val < a := hp.1.1
        omega
      rcases tagged_long_race_a_nominated_boundary
        ring i j k a b N hs p hp hboundary with
        hsuccess | hfailure
      · exact Or.inl hsuccess
      · exact Or.inr (Or.inl hfailure)
  · intro hother
    have hnotFailure :=
      tagged_long_race_a_off_nomination_never_failure
        hn ring i j k a b N hs e p hp hother.2
    cases hnode : tagged_long_race_step ring i j k a b N e with
    | success =>
        exact Or.inl rfl
    | failure =>
        exact False.elim (hnotFailure hnode)
    | active M =>
        obtain ⟨hM, _⟩ :=
          tagged_long_race_active_step
            ring i j k a b N M e hnode
        subst M
        have hnotDelete :=
          tagged_long_race_active_not_deleted
            ring i j k a b N (nativeE ring N e) e hnode
        have hAphase :=
          tagged_long_live_off_nomination
            ring i j k a b N e ht p hp hother.2 hnotDelete
        have hAsame :
            taggedLongRaceAQuota ring i a (nativeE ring N e) =
              taggedLongRaceAQuota ring i a N := by
          calc
            taggedLongRaceAQuota ring i a (nativeE ring N e) =
                a - p.val :=
              tagged_long_race_a_quota_value
                ring i a (nativeE ring N e) p hAphase
            _ = taggedLongRaceAQuota ring i a N :=
              (tagged_long_race_a_quota_value
                ring i a N p hp).symm
        have hBsame :=
          tagged_long_b_off_nomination
            ring i j k a b N e ht phase hphase
            hnr hother.1 hnotDelete
        exact Or.inr ⟨nativeE ring N e,
          rfl, hAsame, hBsame⟩

end L3



/-! ## Monotonicity of the abstract fair two-front race

This section concerns only
taggedLongFairFailure, not the physical stopped-race domination.
The B readiness quota u is monotone increasing for the failure
numerator. The A remaining-hop quota v is antitone for n >= 2.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- If the target B requires more nominated hits, failure cannot
become less likely. The proof is finite-horizon and uses exactly
the existing three-term fair-race recursion. -/
theorem tagged_long_fair_failure_b_monotone
    (n : Nat) :
    ∀ (T uSmall uLarge v : Nat), uSmall ≤ uLarge →
      taggedLongFairFailure n uSmall v T ≤
        taggedLongFairFailure n uLarge v T := by
  intro T
  induction T with
  | zero =>
      intro uSmall uLarge v hle
      by_cases hsmall : uSmall = 0
      · subst uSmall
        change 0 ≤ taggedLongFairFailure n uLarge v 0
        exact Nat.zero_le _
      · have hlarge : uLarge ≠ 0 := by omega
        by_cases hv : v = 0
        · simp [taggedLongFairFailure, hsmall, hlarge, hv]
        · simp [taggedLongFairFailure, hsmall, hlarge, hv]
  | succ T ih =>
      intro uSmall uLarge v hle
      by_cases hsmall : uSmall = 0
      · subst uSmall
        change 0 ≤ taggedLongFairFailure n uLarge v (T + 1)
        exact Nat.zero_le _
      · have hlarge : uLarge ≠ 0 := by omega
        by_cases hv : v = 0
        · simp [taggedLongFairFailure, hsmall, hlarge, hv]
        · have hcenter :=
            Nat.mul_le_mul_left (n - 2)
              (ih uSmall uLarge v hle)
          have hB :=
            ih (uSmall - 1) (uLarge - 1) v (by omega)
          have hA :=
            ih uSmall uLarge (v - 1) hle
          have hleft :
              taggedLongFairFailure n uSmall v (T + 1) =
                (n - 2) * taggedLongFairFailure n uSmall v T +
                  taggedLongFairFailure n (uSmall - 1) v T +
                  taggedLongFairFailure n uSmall (v - 1) T := by
            simp only [taggedLongFairFailure,
              if_neg hsmall, if_neg hv]
          have hright :
              taggedLongFairFailure n uLarge v (T + 1) =
                (n - 2) * taggedLongFairFailure n uLarge v T +
                  taggedLongFairFailure n (uLarge - 1) v T +
                  taggedLongFairFailure n uLarge (v - 1) T := by
            simp only [taggedLongFairFailure,
              if_neg hlarge, if_neg hv]
          rw [hleft, hright]
          exact Nat.add_le_add
            (Nat.add_le_add hcenter hB) hA

/-- The correct A-quota direction is reversed: allowing the live
attacker more hops cannot increase its failure-cylinder mass.
For vSmall = 0 the already-proved fair-race pair bound supplies
the exact terminal n^T ceiling. -/
theorem tagged_long_fair_failure_a_antitone
    (n : Nat) (hn : 2 ≤ n) :
    ∀ (T u vSmall vLarge : Nat), vSmall ≤ vLarge →
      taggedLongFairFailure n u vLarge T ≤
        taggedLongFairFailure n u vSmall T := by
  intro T
  induction T with
  | zero =>
      intro u vSmall vLarge hle
      by_cases hu : u = 0
      · simp [taggedLongFairFailure, hu]
      · by_cases hsmall : vSmall = 0
        · subst vSmall
          by_cases hlarge : vLarge = 0
          · simp [taggedLongFairFailure, hu, hlarge]
          · simp [taggedLongFairFailure, hu, hlarge]
        · have hlarge : vLarge ≠ 0 := by omega
          simp [taggedLongFairFailure, hu, hsmall, hlarge]
  | succ T ih =>
      intro u vSmall vLarge hle
      by_cases hu : u = 0
      · simp [taggedLongFairFailure, hu]
      · by_cases hsmall : vSmall = 0
        · subst vSmall
          have hpair :=
            tagged_long_fair_failure_pair n hn
              (T + 1) u vLarge
          have hterminal :
              taggedLongFairFailure n u 0 (T + 1) =
                n ^ (T + 1) := by
            simp [taggedLongFairFailure, hu]
          rw [hterminal]
          omega
        · have hlarge : vLarge ≠ 0 := by omega
          have hcenter :=
            Nat.mul_le_mul_left (n - 2)
              (ih u vSmall vLarge hle)
          have hB :=
            ih (u - 1) vSmall vLarge hle
          have hA :=
            ih u (vSmall - 1) (vLarge - 1) (by omega)
          have hleft :
              taggedLongFairFailure n u vLarge (T + 1) =
                (n - 2) * taggedLongFairFailure n u vLarge T +
                  taggedLongFairFailure n (u - 1) vLarge T +
                  taggedLongFairFailure n u (vLarge - 1) T := by
            simp only [taggedLongFairFailure,
              if_neg hu, if_neg hlarge]
          have hright :
              taggedLongFairFailure n u vSmall (T + 1) =
                (n - 2) * taggedLongFairFailure n u vSmall T +
                  taggedLongFairFailure n (u - 1) vSmall T +
                  taggedLongFairFailure n u (vSmall - 1) T := by
            simp only [taggedLongFairFailure,
              if_neg hu, if_neg hsmall]
          rw [hleft, hright]
          exact Nat.add_le_add
            (Nat.add_le_add hcenter hB) hA

/-- Closed counterexample to the proposed (incorrect)
nondecreasing-in-v inequality:
n = 2, u = 1, v = 0, v' = 1, T = 0.
Here the two failure counts are respectively 1 and 0. -/
theorem tagged_long_fair_failure_a_wrong_direction :
    taggedLongFairFailure 2 1 0 0 = 1 ∧
      taggedLongFairFailure 2 1 1 0 = 0 ∧
      ¬ (taggedLongFairFailure 2 1 0 0 ≤
          taggedLongFairFailure 2 1 1 0) := by
  simp [taggedLongFairFailure]

end L3



/-! ## Exact two-letter scheduler split and physical failure domination

This continuation proves only the
finite-horizon failureCount domination for actual active cuts. It uses
the physical edge classifier and the pre-existing abstract monotonicity,
not a fabricated independent scheduler or an expected-time claim.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false
attribute [local instance low] Classical.propDecidable

/-- The requested explicit List.finRange n decomposition:
the two distinct nominated physical edges are counted once each,
and every other directed edge has the common third weight. -/
theorem tagged_long_finRange_two_edge_sum {n : Nat}
    (edgeB edgeA : Fin n) (valueB valueA ordinary : Nat)
    (hBA : edgeB ≠ edgeA) :
    ((List.finRange n).map (fun e : Fin n =>
      if e = edgeB then valueB
      else if e = edgeA then valueA else ordinary)).sum =
        valueB + valueA + (n - 2) * ordinary := by
  have hAB : edgeA ≠ edgeB := Ne.symm hBA
  have hsplit :=
    sum_two_exceptions
      (List.finRange n) edgeB edgeA
      (fun e : Fin n =>
        if e = edgeB then valueB
        else if e = edgeA then valueA else ordinary)
      ordinary
      (List.nodup_finRange n)
      (List.mem_finRange edgeB)
      (List.mem_finRange edgeA)
      hBA
      (by
        intro e _ hneB hneA
        simp only [if_neg hneB, if_neg hneA])
  simpa only [List.length_finRange, ite_true,
    if_neg hAB] using hsplit

/-- The stopped tree itself is defined with List.ofFn. This is the
same two-special-edge formula in that exact representation; its proof
uses the finite uniform sum and single-spike lemmas,
rather than assuming an unverified finRange/ofFn conversion. -/
theorem tagged_long_ofFn_two_edge_sum {n : Nat}
    (hn : 2 ≤ n)
    (edgeB edgeA : Fin n) (valueB valueA ordinary : Nat)
    (hBA : edgeB ≠ edgeA) :
    (List.ofFn (fun e : Fin n =>
      if e = edgeB then valueB
      else if e = edgeA then valueA else ordinary)).sum =
        valueB + valueA + (n - 2) * ordinary := by
  have hAB : edgeA ≠ edgeB := Ne.symm hBA
  have hconst :
      (List.ofFn (fun _ : Fin n => ordinary)).sum =
      (List.ofFn (fun e : Fin n =>
        (if e = edgeB then ordinary else 0) +
          (if e = edgeA then ordinary else 0) +
          (if e = edgeB then 0
           else if e = edgeA then 0 else ordinary))).sum :=
    ofFn_sum_eq _ _ (by
      intro e
      by_cases hb : e = edgeB
      · subst e
        simp [hBA]
      · by_cases ha : e = edgeA
        · subst e
          simp [hAB]
        · simp [hb, ha])
  have htotal :
      n * ordinary =
        ordinary + ordinary +
          (List.ofFn (fun e : Fin n =>
            if e = edgeB then 0
            else if e = edgeA then 0 else ordinary)).sum := by
    calc
      n * ordinary =
          (List.ofFn (fun _ : Fin n => ordinary)).sum :=
        (ofFn_sum_const n ordinary).symm
      _ = (List.ofFn (fun e : Fin n =>
            (if e = edgeB then ordinary else 0) +
              (if e = edgeA then ordinary else 0) +
              (if e = edgeB then 0
               else if e = edgeA then 0 else ordinary))).sum :=
        hconst
      _ = ordinary + ordinary +
            (List.ofFn (fun e : Fin n =>
              if e = edgeB then 0
              else if e = edgeA then 0 else ordinary)).sum := by
        rw [ofFn_sum_add, ofFn_sum_add,
          tagged_q_sum_spike n edgeB ordinary,
          tagged_q_sum_spike n edgeA ordinary]
  have hlinear :
      n * ordinary =
        ordinary + ordinary + (n - 2) * ordinary := by
    have hnSplit : n = 2 + (n - 2) := by omega
    calc
      n * ordinary = (2 + (n - 2)) * ordinary :=
        congrArg (fun z : Nat => z * ordinary) hnSplit
      _ = 2 * ordinary + (n - 2) * ordinary :=
        Nat.add_mul 2 (n - 2) ordinary
      _ = ordinary + ordinary + (n - 2) * ordinary := by
        omega
  have houtside :
      (List.ofFn (fun e : Fin n =>
        if e = edgeB then 0
        else if e = edgeA then 0 else ordinary)).sum =
          (n - 2) * ordinary := by
    omega
  have hpoint (e : Fin n) :
      (if e = edgeB then valueB
       else if e = edgeA then valueA else ordinary) =
        (if e = edgeB then valueB else 0) +
          (if e = edgeA then valueA else 0) +
          (if e = edgeB then 0
           else if e = edgeA then 0 else ordinary) := by
    by_cases hb : e = edgeB
    · subst e
      simp [hBA]
    · by_cases ha : e = edgeA
      · subst e
        simp [hAB]
      · simp [hb, ha]
  calc
    (List.ofFn (fun e : Fin n =>
        if e = edgeB then valueB
        else if e = edgeA then valueA else ordinary)).sum =
      (List.ofFn (fun e : Fin n =>
        (if e = edgeB then valueB else 0) +
          (if e = edgeA then valueA else 0) +
          (if e = edgeB then 0
           else if e = edgeA then 0 else ordinary))).sum :=
        ofFn_sum_eq _ _ hpoint
    _ = valueB + valueA +
          (List.ofFn (fun e : Fin n =>
            if e = edgeB then 0
            else if e = edgeA then 0 else ordinary)).sum := by
      rw [ofFn_sum_add, ofFn_sum_add,
        tagged_q_sum_spike n edgeB valueB,
        tagged_q_sum_spike n edgeA valueA]
    _ = valueB + valueA + (n - 2) * ordinary := by
      rw [houtside]

/-- The A-terminal abstract boundary, including depth zero:
when B has positive rank and A has exhausted its live quota,
every remaining length-T scheduler word is a failure. -/
private theorem tagged_long_fair_failure_terminal
    (n u T : Nat) (hu : 0 < u) :
    taggedLongFairFailure n u 0 T = n ^ T := by
  have hnonzero : u ≠ 0 := by omega
  cases T with
  | zero =>
      simp [taggedLongFairFailure, hnonzero]
  | succ T =>
      simp [taggedLongFairFailure, hnonzero]

/-- D.19 finite-horizon *physical* failure-count domination. Each
active successor is obtained from precisely one nativeE service.
B's unique nominated edge reduces its current B rank by at least
one; A's distinct nominated edge either stops, or reduces its
physical live quota by one; all other letters preserve both
quotas or stop successfully.

No half-mass probability transfer is asserted in this theorem. -/
theorem tagged_long_race_failure_dominated {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat) :
    ∀ (T : Nat) (N : TripleNativeState n),
      TaggedLongRaceActive ring i j k a b N →
      failureCount
        (tagged_long_race_step ring i j k a b) (.active N) T ≤
      taggedLongFairFailure n
        (taggedLongRaceBRank ring j b N)
        (taggedLongRaceAQuota ring i a N) T := by
  intro T
  induction T with
  | zero =>
      intro N _
      change (0 : Nat) ≤
        taggedLongFairFailure n
          (taggedLongRaceBRank ring j b N)
          (taggedLongRaceAQuota ring i a N) 0
      exact Nat.zero_le _
  | succ T ih =>
      intro N hs
      have hnTwo : 2 ≤ n := by omega
      obtain ⟨p, hpA, _⟩ := hs.1.2.2
      obtain ⟨phase, hpB⟩ := hs.1.2.1
      have hnr : phase ≠ .ready := by
        intro he
        cases he
        exact hs.2 hpB
      have hBpositive :
          0 < taggedLongRaceBRank ring j b N := by
        rw [tagged_long_race_b_rank_value
          ring j b N phase hpB]
        have hpos :=
          tagged_long_race_b_rank_pos
            ring N j b phase hpB hnr
        omega
      have hApositive :
          0 < taggedLongRaceAQuota ring i a N := by
        rw [tagged_long_race_a_quota_value
          ring i a N p hpA]
        have hlt : p.val < a := hpA.1.1
        omega
      have hBnonzero :
          taggedLongRaceBRank ring j b N ≠ 0 := by omega
      have hAnonzero :
          taggedLongRaceAQuota ring i a N ≠ 0 := by omega
      have hBA :
          SealedPhaseEdge ring j phase ≠
            SealedPhaseEdge ring i (.live p) :=
        (tagged_long_nominated_edges_distinct
          ring i j k a b N hs.1.1 p hpA phase hpB).symm
      have hphysical :=
        tagged_long_race_physical_edge_spec
          hn ring i j k a b N hs p phase hpA hpB
      have hchild (e : Fin n) :
          failureCount
            (tagged_long_race_step ring i j k a b)
            (tagged_long_race_step ring i j k a b N e) T ≤
          if e = SealedPhaseEdge ring j phase then
            taggedLongFairFailure n
              (taggedLongRaceBRank ring j b N - 1)
              (taggedLongRaceAQuota ring i a N) T
          else if e = SealedPhaseEdge ring i (.live p) then
            taggedLongFairFailure n
              (taggedLongRaceBRank ring j b N)
              (taggedLongRaceAQuota ring i a N - 1) T
          else
            taggedLongFairFailure n
              (taggedLongRaceBRank ring j b N)
              (taggedLongRaceAQuota ring i a N) T := by
        by_cases hb : e = SealedPhaseEdge ring j phase
        · simp only [if_pos hb]
          rcases (hphysical e).1 hb with
            hsuccess | ⟨M, hactive, hstrict, hAsame⟩
          · rw [hsuccess,
              tagged_failure_count_success_zero]
            exact Nat.zero_le _
          · have hnext :=
              (tagged_long_race_active_step
                ring i j k a b N M e hactive).2
            have hrec := ih M hnext
            rw [hAsame] at hrec
            have hBshort :
                taggedLongRaceBRank ring j b M ≤
                  taggedLongRaceBRank ring j b N - 1 := by
              omega
            have hmono :=
              tagged_long_fair_failure_b_monotone n T
                (taggedLongRaceBRank ring j b M)
                (taggedLongRaceBRank ring j b N - 1)
                (taggedLongRaceAQuota ring i a N) hBshort
            rw [hactive]
            exact Nat.le_trans hrec hmono
        · by_cases ha : e = SealedPhaseEdge ring i (.live p)
          · simp only [if_neg hb, if_pos ha]
            rcases (hphysical e).2.1 ha with
              hsuccess | hfailure | ⟨M, hactive, hAstep, hBsame⟩
            · rw [hsuccess,
                tagged_failure_count_success_zero]
              exact Nat.zero_le _
            · have hfailureNom :
                  tagged_long_race_step ring i j k a b N
                    (SealedPhaseEdge ring i (.live p)) =
                      .failure := by
                simpa only [ha] using hfailure
              have hlast : p.val + 1 = a := by
                by_cases hinterior : p.val + 1 < a
                · rcases tagged_long_race_a_nominated_interior
                    hn ring i j k a b N hs p hpA hinterior with
                    hsuccessNom | hactiveNom
                  · rw [hfailureNom] at hsuccessNom
                    cases hsuccessNom
                  · obtain ⟨q, hactiveNomNode, _⟩ := hactiveNom
                    rw [hfailureNom] at hactiveNomNode
                    cases hactiveNomNode
                · have hpLess : p.val < a := hpA.1.1
                  omega
              have hAunit :
                  taggedLongRaceAQuota ring i a N = 1 := by
                rw [tagged_long_race_a_quota_value
                  ring i a N p hpA]
                omega
              calc
                failureCount
                  (tagged_long_race_step ring i j k a b)
                  (tagged_long_race_step ring i j k a b N e) T =
                    n ^ T := by
                  rw [hfailure]
                  exact tagged_failure_count_failure_eq_pow
                    (tagged_long_race_step ring i j k a b) T
                _ = taggedLongFairFailure n
                      (taggedLongRaceBRank ring j b N)
                      (taggedLongRaceAQuota ring i a N - 1) T := by
                  rw [hAunit]
                  change n ^ T =
                    taggedLongFairFailure n
                      (taggedLongRaceBRank ring j b N) 0 T
                  exact (tagged_long_fair_failure_terminal n
                    (taggedLongRaceBRank ring j b N)
                    T hBpositive).symm
                _ ≤ taggedLongFairFailure n
                      (taggedLongRaceBRank ring j b N)
                      (taggedLongRaceAQuota ring i a N - 1) T :=
                  Nat.le_refl _
            · have hnext :=
                (tagged_long_race_active_step
                  ring i j k a b N M e hactive).2
              have hrec := ih M hnext
              have hAshort :
                  taggedLongRaceAQuota ring i a M =
                    taggedLongRaceAQuota ring i a N - 1 := by
                omega
              rw [hAshort, hBsame] at hrec
              rw [hactive]
              exact hrec
          · simp only [if_neg hb, if_neg ha]
            rcases (hphysical e).2.2 ⟨hb, ha⟩ with
              hsuccess | ⟨M, hactive, hAsame, hBsame⟩
            · rw [hsuccess,
                tagged_failure_count_success_zero]
              exact Nat.zero_le _
            · have hnext :=
                (tagged_long_race_active_step
                  ring i j k a b N M e hactive).2
              have hrec := ih M hnext
              rw [hAsame, hBsame] at hrec
              rw [hactive]
              exact hrec
      have hsum :
          (List.ofFn (fun e : Fin n =>
            if e = SealedPhaseEdge ring j phase then
              taggedLongFairFailure n
                (taggedLongRaceBRank ring j b N - 1)
                (taggedLongRaceAQuota ring i a N) T
            else if e = SealedPhaseEdge ring i (.live p) then
              taggedLongFairFailure n
                (taggedLongRaceBRank ring j b N)
                (taggedLongRaceAQuota ring i a N - 1) T
            else
              taggedLongFairFailure n
                (taggedLongRaceBRank ring j b N)
                (taggedLongRaceAQuota ring i a N) T)).sum =
          taggedLongFairFailure n
            (taggedLongRaceBRank ring j b N - 1)
            (taggedLongRaceAQuota ring i a N) T +
          taggedLongFairFailure n
            (taggedLongRaceBRank ring j b N)
            (taggedLongRaceAQuota ring i a N - 1) T +
          (n - 2) *
            taggedLongFairFailure n
              (taggedLongRaceBRank ring j b N)
              (taggedLongRaceAQuota ring i a N) T :=
        tagged_long_ofFn_two_edge_sum hnTwo
          (SealedPhaseEdge ring j phase)
          (SealedPhaseEdge ring i (.live p))
          (taggedLongFairFailure n
            (taggedLongRaceBRank ring j b N - 1)
            (taggedLongRaceAQuota ring i a N) T)
          (taggedLongFairFailure n
            (taggedLongRaceBRank ring j b N)
            (taggedLongRaceAQuota ring i a N - 1) T)
          (taggedLongFairFailure n
            (taggedLongRaceBRank ring j b N)
            (taggedLongRaceAQuota ring i a N) T)
          hBA
      have hsumLe :
          (List.ofFn (fun e : Fin n =>
            failureCount
              (tagged_long_race_step ring i j k a b)
              (tagged_long_race_step ring i j k a b N e) T)).sum ≤
          (List.ofFn (fun e : Fin n =>
            if e = SealedPhaseEdge ring j phase then
              taggedLongFairFailure n
                (taggedLongRaceBRank ring j b N - 1)
                (taggedLongRaceAQuota ring i a N) T
            else if e = SealedPhaseEdge ring i (.live p) then
              taggedLongFairFailure n
                (taggedLongRaceBRank ring j b N)
                (taggedLongRaceAQuota ring i a N - 1) T
            else
              taggedLongFairFailure n
                (taggedLongRaceBRank ring j b N)
                (taggedLongRaceAQuota ring i a N) T)).sum :=
        ofFn_sum_le _ _ hchild
      have habstract :
          taggedLongFairFailure n
            (taggedLongRaceBRank ring j b N)
            (taggedLongRaceAQuota ring i a N) (T + 1) =
          (n - 2) *
            taggedLongFairFailure n
              (taggedLongRaceBRank ring j b N)
              (taggedLongRaceAQuota ring i a N) T +
          taggedLongFairFailure n
            (taggedLongRaceBRank ring j b N - 1)
            (taggedLongRaceAQuota ring i a N) T +
          taggedLongFairFailure n
            (taggedLongRaceBRank ring j b N)
            (taggedLongRaceAQuota ring i a N - 1) T := by
        simp only [taggedLongFairFailure,
          if_neg hBnonzero, if_neg hAnonzero]
      change
        (List.ofFn (fun e : Fin n =>
          failureCount
            (tagged_long_race_step ring i j k a b)
            (tagged_long_race_step ring i j k a b N e) T)).sum ≤
        taggedLongFairFailure n
          (taggedLongRaceBRank ring j b N)
          (taggedLongRaceAQuota ring i a N) (T + 1)
      calc
        (List.ofFn (fun e : Fin n =>
          failureCount
            (tagged_long_race_step ring i j k a b)
            (tagged_long_race_step ring i j k a b N e) T)).sum ≤
          (List.ofFn (fun e : Fin n =>
            if e = SealedPhaseEdge ring j phase then
              taggedLongFairFailure n
                (taggedLongRaceBRank ring j b N - 1)
                (taggedLongRaceAQuota ring i a N) T
            else if e = SealedPhaseEdge ring i (.live p) then
              taggedLongFairFailure n
                (taggedLongRaceBRank ring j b N)
                (taggedLongRaceAQuota ring i a N - 1) T
            else
              taggedLongFairFailure n
                (taggedLongRaceBRank ring j b N)
                (taggedLongRaceAQuota ring i a N) T)).sum :=
          hsumLe
        _ = taggedLongFairFailure n
              (taggedLongRaceBRank ring j b N - 1)
              (taggedLongRaceAQuota ring i a N) T +
            taggedLongFairFailure n
              (taggedLongRaceBRank ring j b N)
              (taggedLongRaceAQuota ring i a N - 1) T +
            (n - 2) *
              taggedLongFairFailure n
                (taggedLongRaceBRank ring j b N)
                (taggedLongRaceAQuota ring i a N) T :=
          hsum
        _ = taggedLongFairFailure n
              (taggedLongRaceBRank ring j b N)
              (taggedLongRaceAQuota ring i a N) (T + 1) := by
          rw [habstract]
          omega

end L3

/-! ## Retained-start quota order and physical half-mass transfer -/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false
attribute [local instance low] Classical.propDecidable

/-- A retained cut already forces at least three agents:
b is positive, the retained A gap is at least 2*b, and a<n. -/
theorem tagged_long_retained_size {n : Nat}
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (hret : TaggedLongRetained ring i j k a b N) :
    3 ≤ n := by
  have hb : 1 ≤ b := hret.1.2.2.1
  have ha : a < n := hret.1.2.1.2.1
  obtain ⟨p, hp, hdist⟩ := hret.2.2
  omega

/-- At a retained cut A has exactly 2*b remaining hops, while
the actual sealed B phase has rank at most 2*b-1. -/
theorem tagged_long_retained_quotas {n : Nat}
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (hret : TaggedLongRetained ring i j k a b N) :
    taggedLongRaceAQuota ring i a N = 2 * b ∧
      taggedLongRaceBRank ring j b N ≤ 2 * b - 1 := by
  obtain ⟨p, hp, hdist⟩ := hret.2.2
  constructor
  · rw [tagged_long_race_a_quota_value ring i a N p hp]
    omega
  · obtain ⟨phase, hphase⟩ := hret.2.1
    rw [tagged_long_race_b_rank_value ring j b N phase hphase]
    exact sealed_phase_progress_bound ring N j b phase hphase

/-- The retained physical start has the quota order needed by
the finite-horizon fair-race half-mass theorem. -/
theorem tagged_long_race_retained_quota_order {n : Nat}
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (hret : TaggedLongRetained ring i j k a b N) :
    taggedLongRaceBRank ring j b N ≤
      taggedLongRaceAQuota ring i a N := by
  obtain ⟨hA, hB⟩ :=
    tagged_long_retained_quotas ring i j k a b N hret
  rw [hA]
  exact Nat.le_trans hB (Nat.sub_le _ _)

/-- The actual start is either a terminal success or the original
active physical cut with B quota no greater than A quota. -/
theorem tagged_long_race_start_cut {n : Nat}
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (hret : TaggedLongRetained ring i j k a b N) :
    tagged_long_race_start ring j b N = .success ∨
      ∃ M : TripleNativeState n,
        tagged_long_race_start ring j b N = .active M ∧
        TaggedLongRaceActive ring i j k a b M ∧
        taggedLongRaceBRank ring j b M ≤
          taggedLongRaceAQuota ring i a M := by
  classical
  by_cases hready : SealedCleanReady ring N j b
  · exact Or.inl (tagged_long_race_initial_ready ring j b N hready)
  · apply Or.inr
    refine ⟨N, ?_, ?_, ?_⟩
    · simp [tagged_long_race_start, hready]
    · refine ⟨?_, hready⟩
      obtain ⟨ht, hB, p, hp, hdist⟩ := hret
      exact ⟨ht, hB, p, hp, by omega⟩
    · exact tagged_long_race_retained_quota_order
        ring i j k a b N hret

/-- D.19 half-mass bound for the physical race from an exact retained cut,
with an initially Ready target handled as an immediate terminal success. -/
theorem tagged_long_race_failure_half {n : Nat}
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (hret : TaggedLongRetained ring i j k a b N) :
    ∀ T,
      2 * failureCount
        (tagged_long_race_step ring i j k a b)
        (tagged_long_race_start ring j b N) T ≤ n ^ T := by
  classical
  have hn : 3 ≤ n := tagged_long_retained_size
    ring i j k a b N hret
  have hquota := tagged_long_race_retained_quota_order
    ring i j k a b N hret
  have hnear : TaggedLongNear ring i j k a b N := by
    obtain ⟨ht, hB, p, hp, hdist⟩ := hret
    exact ⟨ht, hB, p, hp, by omega⟩
  by_cases hready : SealedCleanReady ring N j b
  · have hzero := tagged_long_race_initial_ready_cost_and_mass
      ring i j k a b N hready
    intro T
    rw [(hzero T).2, Nat.mul_zero]
    exact Nat.zero_le _
  · have hstart :
        tagged_long_race_start ring j b N = .active N := by
      simp [tagged_long_race_start, hready]
    intro T
    rw [hstart]
    exact Nat.le_trans
      (Nat.mul_le_mul_left 2
        (tagged_long_race_failure_dominated
          hn ring i j k a b T N ⟨hnear, hready⟩))
      (tagged_long_fair_failure_half n (by omega)
        (taggedLongRaceBRank ring j b N)
        (taggedLongRaceAQuota ring i a N) T hquota)

/-- Both finite-horizon estimates for the physical retained-front race:
the existing B-front cost and the transferred failure half-mass bound. -/
theorem tagged_long_race_clock {n : Nat}
    (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat) :
    TaggedLongRaceClock ring i j k a b := by
  unfold TaggedLongRaceClock
  intro N hret T
  have hn : 3 ≤ n := tagged_long_retained_size
    ring i j k a b N hret
  exact
    ⟨tagged_long_race_cost hn ring i j k a b N hret T,
      tagged_long_race_failure_half ring i j k a b N hret T⟩

end L3


/-! ## Physical first-incident-service clock

The stopping rule's incoming edge is an
unconditional success (after deletion priority), whereas the outgoing
edge is failure only in the absence of a tagged deletion. Thus the
finite-horizon half-mass argument needs no phase invariant.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false
attribute [local instance low] Classical.propDecidable

/-- The physical incoming scheduler ticket always stops successfully.
This is a statement about the actual nativeE step, not a ghost coin. -/
theorem tagged_long_incident_incoming_success {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n)
    (M : TripleNativeState n) :
    tagged_long_incident_step ring i j k M (ring.leftNeighbor j) =
      .success := by
  classical
  simp [tagged_long_incident_step]

/-- The outgoing ticket fails unless the native step has already
deleted a tag, in which case deletion has priority and succeeds. -/
theorem tagged_long_incident_outgoing_class {n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (M : TripleNativeState n) :
    tagged_long_incident_step ring i j k M j =
      if TaggedDeleted i j k (nativeE ring M j) then
        .success
      else .failure := by
  classical
  have hneq : j ≠ ring.leftNeighbor j :=
    tagged_q_incident_edges_distinct hn ring j
  simp [tagged_long_incident_step, hneq]

/-- A scheduler ticket at neither incident port cannot create a
failure leaf. It either deletes a tag or continues on nativeE. -/
theorem tagged_long_incident_other_class {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n)
    (M : TripleNativeState n) (e : Fin n)
    (hinc : e ≠ ring.leftNeighbor j) (hout : e ≠ j) :
    tagged_long_incident_step ring i j k M e =
      if TaggedDeleted i j k (nativeE ring M e) then
        .success
      else .active (nativeE ring M e) := by
  classical
  simp [tagged_long_incident_step, hinc, hout]

/-- Uniform truncated cost for the first incident service. The
incoming ticket alone gives a one-unit potential, charged n per
active cut; additional deletion successes only reduce its cost. -/
theorem tagged_long_incident_cost {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n)
    (N : TripleNativeState n) :
    ∀ T,
      truncatedActiveCostNumerator
        (tagged_long_incident_step ring i j k)
        (.active N) T ≤ n ^ T * n := by
  classical
  have hmain :
      ∀ T (M : TripleNativeState n),
        truncatedActiveCostNumerator
          (tagged_long_incident_step ring i j k)
          (.active M) T ≤ n ^ T * n := by
    intro T
    induction T with
    | zero =>
        intro M
        simp only [truncatedActiveCostNumerator]
        exact Nat.zero_le _
    | succ T ih =>
        intro M
        have hweak (e : Fin n) :
            taggedLongRaceNodeCredit
              (fun _ : TripleNativeState n => n)
              (tagged_long_incident_step ring i j k M e) ≤ n := by
          cases hnode : tagged_long_incident_step ring i j k M e with
          | success => simp [taggedLongRaceNodeCredit]
          | failure => simp [taggedLongRaceNodeCredit]
          | active W => simp [taggedLongRaceNodeCredit]
        have hstrict :
            taggedLongRaceNodeCredit
                (fun _ : TripleNativeState n => n)
                (tagged_long_incident_step ring i j k M
                  (ring.leftNeighbor j)) + n ≤ n := by
          rw [tagged_long_incident_incoming_success ring i j k M]
          simp [taggedLongRaceNodeCredit]
        have hdrift :
            n + (List.ofFn (fun e : Fin n =>
              taggedLongRaceNodeCredit
                (fun _ : TripleNativeState n => n)
                (tagged_long_incident_step ring i j k M e))).sum ≤
                n * n :=
          tagged_q_drift_from_nominated_edge n
            (fun e : Fin n =>
              taggedLongRaceNodeCredit
                (fun _ : TripleNativeState n => n)
                (tagged_long_incident_step ring i j k M e))
            (ring.leftNeighbor j) hweak hstrict
        have hchild (e : Fin n) :
            truncatedActiveCostNumerator
              (tagged_long_incident_step ring i j k)
              (tagged_long_incident_step ring i j k M e) T ≤
                n ^ T * taggedLongRaceNodeCredit
                  (fun _ : TripleNativeState n => n)
                  (tagged_long_incident_step ring i j k M e) := by
          cases hnode : tagged_long_incident_step ring i j k M e with
          | success =>
              cases T <;> simp [truncatedActiveCostNumerator,
                taggedLongRaceNodeCredit]
          | failure =>
              cases T <;> simp [truncatedActiveCostNumerator,
                taggedLongRaceNodeCredit]
          | active W =>
              change
                truncatedActiveCostNumerator
                  (tagged_long_incident_step ring i j k)
                  (.active W) T ≤ n ^ T * n
              exact ih W
        have hsum :
            (List.ofFn (fun e : Fin n =>
              truncatedActiveCostNumerator
                (tagged_long_incident_step ring i j k)
                (tagged_long_incident_step ring i j k M e) T)).sum ≤
              n ^ T * (List.ofFn (fun e : Fin n =>
                taggedLongRaceNodeCredit
                  (fun _ : TripleNativeState n => n)
                  (tagged_long_incident_step ring i j k M e))).sum := by
          calc
            _ ≤ (List.ofFn (fun e : Fin n =>
                  n ^ T * taggedLongRaceNodeCredit
                    (fun _ : TripleNativeState n => n)
                    (tagged_long_incident_step ring i j k M e))).sum :=
              ofFn_sum_le _ _ hchild
            _ = n ^ T * (List.ofFn (fun e : Fin n =>
                  taggedLongRaceNodeCredit
                    (fun _ : TripleNativeState n => n)
                    (tagged_long_incident_step ring i j k M e))).sum :=
              ofFn_sum_mul_left (n ^ T) _
        change
          n ^ (T + 1) +
            (List.ofFn (fun e : Fin n =>
              truncatedActiveCostNumerator
                (tagged_long_incident_step ring i j k)
                (tagged_long_incident_step ring i j k M e) T)).sum ≤
            n ^ (T + 1) * n
        calc
          _ ≤ n ^ (T + 1) +
              n ^ T * (List.ofFn (fun e : Fin n =>
                taggedLongRaceNodeCredit
                  (fun _ : TripleNativeState n => n)
                  (tagged_long_incident_step ring i j k M e))).sum :=
            Nat.add_le_add_left hsum _
          _ = n ^ T * (n +
              (List.ofFn (fun e : Fin n =>
                taggedLongRaceNodeCredit
                  (fun _ : TripleNativeState n => n)
                  (tagged_long_incident_step ring i j k M e))).sum) := by
            rw [Nat.pow_succ, Nat.mul_add]
          _ ≤ n ^ T * (n * n) :=
            Nat.mul_le_mul_left (n ^ T) hdrift
          _ = n ^ (T + 1) * n := by
            rw [Nat.pow_succ, Nat.mul_assoc]
  intro T
  exact hmain T N

/-- At every horizon the outgoing-first failure cylinders have
at most half of all scheduler words. The incoming edge gives zero
failure; the outgoing edge contributes at most n^T; each other
edge inherits the same half-bound inductively. -/
theorem tagged_long_incident_failure_half {n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (N : TripleNativeState n) :
    ∀ T,
      2 * failureCount
        (tagged_long_incident_step ring i j k)
        (.active N) T ≤ n ^ T := by
  classical
  have hports : ring.leftNeighbor j ≠ j :=
    Ne.symm (tagged_q_incident_edges_distinct hn ring j)
  have hmain :
      ∀ T (M : TripleNativeState n),
        2 * failureCount
          (tagged_long_incident_step ring i j k)
          (.active M) T ≤ n ^ T := by
    intro T
    induction T with
    | zero =>
        intro M
        simp [failureCount, treeWeight, failureWeight]
    | succ T ih =>
        intro M
        have hchild (e : Fin n) :
            2 * failureCount
                (tagged_long_incident_step ring i j k)
                (tagged_long_incident_step ring i j k M e) T ≤
              if e = ring.leftNeighbor j then 0
              else if e = j then 2 * n ^ T else n ^ T := by
          by_cases hinc : e = ring.leftNeighbor j
          · subst e
            rw [tagged_long_incident_incoming_success ring i j k M,
              tagged_failure_count_success_zero
                (tagged_long_incident_step ring i j k) T]
            simp
          · by_cases hout : e = j
            · subst e
              by_cases hdel :
                  TaggedDeleted i j k (nativeE ring M j)
              · rw [tagged_long_incident_outgoing_class
                    hn ring i j k M, if_pos hdel,
                    tagged_failure_count_success_zero
                      (tagged_long_incident_step ring i j k) T]
                simp [hinc]
              · rw [tagged_long_incident_outgoing_class
                    hn ring i j k M, if_neg hdel,
                    tagged_failure_count_failure_eq_pow
                      (tagged_long_incident_step ring i j k) T]
                simp [hinc]
            · by_cases hdel :
                  TaggedDeleted i j k (nativeE ring M e)
              · rw [tagged_long_incident_other_class
                    ring i j k M e hinc hout, if_pos hdel,
                    tagged_failure_count_success_zero
                      (tagged_long_incident_step ring i j k) T]
                simp [hinc, hout]
              · rw [tagged_long_incident_other_class
                    ring i j k M e hinc hout, if_neg hdel]
                simpa only [if_neg hinc, if_neg hout]
                  using ih (nativeE ring M e)
        have hsum :
            (List.ofFn (fun e : Fin n =>
              2 * failureCount
                (tagged_long_incident_step ring i j k)
                (tagged_long_incident_step ring i j k M e) T)).sum ≤
              (List.ofFn (fun e : Fin n =>
                if e = ring.leftNeighbor j then 0
                else if e = j then 2 * n ^ T else n ^ T)).sum :=
          ofFn_sum_le _ _ hchild
        change
          2 * (List.ofFn (fun e : Fin n =>
            failureCount (tagged_long_incident_step ring i j k)
              (tagged_long_incident_step ring i j k M e) T)).sum ≤
            n ^ (T + 1)
        calc
          2 * (List.ofFn (fun e : Fin n =>
              failureCount (tagged_long_incident_step ring i j k)
                (tagged_long_incident_step ring i j k M e) T)).sum =
            (List.ofFn (fun e : Fin n =>
              2 * failureCount (tagged_long_incident_step ring i j k)
                (tagged_long_incident_step ring i j k M e) T)).sum :=
              (ofFn_sum_mul_left 2 _).symm
          _ ≤ (List.ofFn (fun e : Fin n =>
                if e = ring.leftNeighbor j then 0
                else if e = j then 2 * n ^ T else n ^ T)).sum :=
            hsum
          _ = 0 + 2 * n ^ T + (n - 2) * n ^ T :=
            tagged_long_ofFn_two_edge_sum hn
              (ring.leftNeighbor j) j 0 (2 * n ^ T)
              (n ^ T) hports
          _ = n ^ (T + 1) := by
            have hcount : 2 + (n - 2) = n := by omega
            calc
              0 + 2 * n ^ T + (n - 2) * n ^ T =
                  (2 + (n - 2)) * n ^ T := by
                rw [Nat.add_mul]
                omega
              _ = n * n ^ T := by rw [hcount]
              _ = n ^ (T + 1) := by
                rw [Nat.pow_succ]
                ac_rfl
  intro T
  exact hmain T N

/-- Clock 3 of D.19, on the exact literal stopped physical stream.
No independence assertion is needed, and neither estimate relies
on the initial Ready cut after its premise has been discharged. -/
theorem tagged_long_incident_clock {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat) :
    TaggedLongIncidentClock ring i j k a b := by
  intro N hnear _ T
  have ha : 0 < a := hnear.1.2.1.1
  have han : a < n := hnear.1.2.1.2.1
  have hn : 2 ≤ n := by omega
  exact
    ⟨tagged_long_incident_cost ring i j k N T,
      tagged_long_incident_failure_half hn ring i j k N T⟩

end L3


/-! ## Certified incident handoff and vulnerable Q cost

The raw vulnerable-trial 3/4 finite-horizon
failure estimate is not established here.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false
attribute [local instance low] Classical.propDecidable

/-- The successful incoming incident service is physically certified:
either a tagged leader is actually deleted, or the resulting native
configuration both retains the A-live front and places an actual
clean Dummy(0) at B. If the incoming edge were A's nominated live
edge, the literal live-hit row at the Ready responder j would instead
delete j. There is no reset or ghost transition here. -/
theorem tagged_long_incident_success_certified {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (hnear : TaggedLongNear ring i j k a b N)
    (hready : SealedCleanReady ring N j b) :
    TaggedDeleted i j k
        (nativeE ring N (ring.leftNeighbor j)) ∨
      (TaggedLongNear ring i j k a b
          (nativeE ring N (ring.leftNeighbor j)) ∧
        TaggedCleanDummy ring i j a b
          (nativeE ring N (ring.leftNeighbor j))) := by
  classical
  have hports : ring.leftNeighbor j ≠ j :=
    Ne.symm (tagged_q_incident_edges_distinct
      (by omega : 2 ≤ n) ring j)
  have hnext : ring.rightNeighbor (ring.leftNeighbor j) = j :=
    tagged_right_of_left (by omega : 2 ≤ n) ring j
  by_cases hdeleted : TaggedDeleted i j k
      (nativeE ring N (ring.leftNeighbor j))
  · exact Or.inl hdeleted
  · obtain ⟨p, hA, hquota⟩ := hnear.2.2
    have hprepared : TaggedPrepared ring i j a b N :=
      ⟨⟨.live p, hA⟩, hready⟩
    have hincoming := tagged_prepared_incoming_dummy_actual
      ring i j k a b N (ring.leftNeighbor j)
      hports hnext hnear.1 hprepared
    rcases hincoming with hdead | hclean
    · exact False.elim (hdeleted hdead)
    · have hnotA :
          ring.leftNeighbor j ≠
            SealedPhaseEdge ring i (.live p) := by
        intro he
        have hsource :
            (N (ring.leftNeighbor j)).b = (2 : Fin 3) := by
          rw [he]
          change (sealedAt ring N i p).b = (2 : Fin 3)
          exact hA.1.2.1
        have hjl : (N j).l = true :=
          hnear.1.2.1.2.2.2.2.1
        have hjs : (N j).sg = true :=
          ((sealedCleanReady_iff ring N j b).1 hready).1
        have hrow :=
          tagged_short_live_hit_row
            (N (ring.leftNeighbor j)) (N j)
            (Or.inl hsource) hjl (Or.inl hjs)
        have hpair :
            nativeE ring N (ring.leftNeighbor j) j =
              (certLiteralEPair
                (N (ring.leftNeighbor j)) (N j)).2 := by
          simp [nativeE, hnext, Ne.symm hports]
        have hjdead :
            (nativeE ring N (ring.leftNeighbor j) j).l =
              false := by
          rw [hpair]
          exact hrow
        exact hdeleted (Or.inr (Or.inl hjdead))
      have hAnext :
          SealedPhaseHolds ring
            (nativeE ring N (ring.leftNeighbor j))
            i a (.live p) :=
        tagged_long_live_off_nomination ring i j k a b N
          (ring.leftNeighbor j) hnear.1 p hA hnotA hdeleted
      have htriple :
          TaggedTriple ring i j k a b
            (nativeE ring N (ring.leftNeighbor j)) :=
        tagged_triple_step_of_survival hn ring i j k a b N
          (ring.leftNeighbor j) hnear.1 hdeleted
      have hBsealed :
          Sealed ring (nativeE ring N (ring.leftNeighbor j))
            j b :=
        ⟨.dummy (sealedZero ring), hclean.2⟩
      exact Or.inr
        ⟨⟨htriple, hBsealed, p, hAnext, hquota⟩, hclean⟩

/-- D.19 controlled vulnerable clock: the actual Q-start credit is
n*(a-p), which is at most 2*n*b for the current retained A-live
front. The already established reachable Q-Bellman drift controls
every physical descendant until an actual tagged deletion. -/
theorem tagged_long_vulnerable_q_cost {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (hnear : TaggedLongNear ring i j k a b N)
    (hclean : TaggedCleanDummy ring i j a b N) :
    ∀ T,
      costNumerator
        (taggedQNext ring j b (by omega : 2 ≤ n)
          (Ne.symm (tagged_q_incident_edges_distinct
            (by omega : 2 ≤ n) ring j)))
        (TaggedDeleted i j k) N T ≤
          n ^ T * (n * (2 * b)) := by
  classical
  have hports : ring.leftNeighbor j ≠ j :=
    Ne.symm (tagged_q_incident_edges_distinct
      (by omega : 2 ≤ n) ring j)
  have hclosed :
      ∀ M, TaggedQActiveReach ring i j k a b
          (by omega : 2 ≤ n) hports N M →
        ∀ e, ¬ TaggedDeleted i j k
            (taggedQNext ring j b (by omega : 2 ≤ n)
              hports M e) →
          TaggedQActiveReach ring i j k a b
            (by omega : 2 ≤ n) hports N
            (taggedQNext ring j b (by omega : 2 ≤ n)
              hports M e) := by
    intro M hreach e hnot
    exact tagged_q_reach_surviving_step ring i j k a b
      (by omega : 2 ≤ n) hports N M e hreach hnot
  have hdrift :
      ∀ M, TaggedQActiveReach ring i j k a b
          (by omega : 2 ≤ n) hports N M →
        ¬ TaggedDeleted i j k M →
          n + (List.ofFn (fun e : Fin n =>
            taggedQBellman ring i j k a
              (taggedQNext ring j b (by omega : 2 ≤ n)
                hports M e))).sum ≤
            n * taggedQBellman ring i j k a M := by
    intro M hreach hnot
    exact tagged_q_reachable_drift hn ring i j k a b
      hports N M hnear.1 hclean hreach hnot
  have hgeneral :=
    tagged_q_restricted_cost_of_potential
      (taggedQNext ring j b (by omega : 2 ≤ n) hports)
      (TaggedDeleted i j k)
      (TaggedQActiveReach ring i j k a b
        (by omega : 2 ≤ n) hports N)
      (taggedQBellman ring i j k a)
      hclosed hdrift
  obtain ⟨p, hp, hquota⟩ := hnear.2.2
  have hnot : ¬ TaggedDeleted i j k N :=
    tagged_d15_triple_not_deleted ring i j k a b N hnear.1
  have hvalue :
      taggedQBellman ring i j k a N =
        n * (a - p.val) := by
    rw [tagged_q_bellman_eq_phase
      ring N i j k a (.live p) hnot hp]
    rfl
  have hcap :
      taggedQBellman ring i j k a N ≤ n * (2 * b) := by
    rw [hvalue]
    exact Nat.mul_le_mul_left n (by omega)
  intro T
  exact Nat.le_trans
    (hgeneral N TaggedQActiveReach.start T)
    (Nat.mul_le_mul_left (n ^ T) hcap)

/-- Exact remaining finite-horizon interface. The full Clock 4 follows
from the raw vulnerable-trial 3/4 failure estimate, not from the
weaker previously established 63/64 and 51/52 moderate-regime bounds. -/
theorem tagged_long_vulnerable_clock_of_failure {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hfailure : ∀ N : TripleNativeState n,
      TaggedLongNear ring i j k a b N →
      TaggedCleanDummy ring i j a b N →
      ∀ T,
        4 * failureCount
          (taggedTrialStep ring i j k b) (.active N) T ≤
          3 * n ^ T) :
    TaggedLongVulnerableClock hn ring i j k a b := by
  intro N hnear hclean T
  exact
    ⟨tagged_long_vulnerable_q_cost
      hn ring i j k a b N hnear hclean T,
      hfailure N hnear hclean T⟩

end L3


/-! ## The finite-horizon D.19 vulnerable estimate

The theorem below proves the
paper's long-attacker clock under the explicit paper premise 2 <= b.

The original TaggedLongVulnerableClock definition quantifies over b=1
as well. The target-cycle lemma tagged_q_target_physical_count presently
requires 2 <= b; no unconditional b=1 clock is claimed here.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false
attribute [local instance low] Classical.propDecidable

/-- A stopped tree whose success leaves occur at the first physical
target hit never costs more than the corresponding first-hit native
cost. This theorem is independent of protocol-specific transitions. -/
theorem tagged_long_stopped_cost_le_raw
    {S : Type} {n : Nat}
    (next : S → Fin n → S)
    (target : S → Prop)
    (step : S → Fin n → StopNode S)
    (hstep : ∀ x e,
      step x e =
        if target (next x e) then .success
        else .active (next x e)) :
    ∀ T x, ¬ target x →
      truncatedActiveCostNumerator step (.active x) T ≤
        costNumerator next target x T := by
  classical
  intro T
  induction T with
  | zero =>
      intro x _
      simp [truncatedActiveCostNumerator, costNumerator]
  | succ T ih =>
      intro x hnot
      rw [costNumerator_succ next target x hnot T]
      change
        n ^ (T + 1) +
          (List.ofFn (fun e : Fin n =>
            truncatedActiveCostNumerator step (step x e) T)).sum ≤
          n ^ (T + 1) +
            (List.ofFn (fun e : Fin n =>
              costNumerator next target (next x e) T)).sum
      apply Nat.add_le_add_left
      apply ofFn_sum_le
      intro e
      rw [hstep x e]
      by_cases ht : target (next x e)
      · rw [if_pos ht]
        cases T with
        | zero =>
            simp [truncatedActiveCostNumerator, costNumerator]
        | succ U =>
            simp [truncatedActiveCostNumerator, costNumerator, ht]
      · rw [if_neg ht]
        exact ih (next x e) ht

/-- The existing physical Q Bellman bound can be applied to the
stopped Q tree, not merely the un-stopped costNumerator. -/
theorem tagged_long_vulnerable_stopped_q_cost {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (hnear : TaggedLongNear ring i j k a b N)
    (hclean : TaggedCleanDummy ring i j a b N) :
    ∀ T,
      truncatedActiveCostNumerator
        (taggedQStopped ring i j k b (by omega : 2 ≤ n)
          (Ne.symm (tagged_q_incident_edges_distinct
            (by omega : 2 ≤ n) ring j)))
        (.active N) T ≤ n ^ T * (n * (2 * b)) := by
  classical
  have hnot : ¬ TaggedDeleted i j k N :=
    tagged_d15_triple_not_deleted ring i j k a b N hnear.1
  have hcompare :=
    tagged_long_stopped_cost_le_raw
      (taggedQNext ring j b (by omega : 2 ≤ n)
        (Ne.symm (tagged_q_incident_edges_distinct
          (by omega : 2 ≤ n) ring j)))
      (TaggedDeleted i j k)
      (taggedQStopped ring i j k b (by omega : 2 ≤ n)
        (Ne.symm (tagged_q_incident_edges_distinct
          (by omega : 2 ≤ n) ring j)))
      (fun M e =>
        tagged_q_stopped_eq ring i j k b
          (by omega : 2 ≤ n)
          (Ne.symm (tagged_q_incident_edges_distinct
            (by omega : 2 ≤ n) ring j)) M e)
  intro T
  exact Nat.le_trans (hcompare T N hnot)
    (tagged_long_vulnerable_q_cost hn ring i j k a b N
      hnear hclean T)

/-- D.19 target-cycle count: from a clean-dummy native seed with
A-live distance at most 2b, the controlled expected number of Ready
collapses is at most two, in the exact finite-horizon numerator. -/
theorem tagged_long_vulnerable_collapse_two {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hb : 2 ≤ b)
    (N : TripleNativeState n)
    (hnear : TaggedLongNear ring i j k a b N)
    (hclean : TaggedCleanDummy ring i j a b N) :
    ∀ T,
      collapseCountNumerator
        (taggedTrialStep ring i j k b)
        (taggedRedirection ring j b (by omega : 2 ≤ n)
          (Ne.symm (tagged_q_incident_edges_distinct
            (by omega : 2 ≤ n) ring j)))
        (.active N) T ≤ 2 * n ^ T := by
  classical
  have hports : ring.leftNeighbor j ≠ j :=
    Ne.symm (tagged_q_incident_edges_distinct
      (by omega : 2 ≤ n) ring j)
  have hcharge :
      taggedQTargetHit ring j b =
        serviceCharge
          (taggedD15TargetActive ring j b)
          (fun M => SealedPhaseEdge ring j
            (taggedQAttackerPhase ring j b M)) := by
    funext M e
    exact tagged_d15_charge_is_service ring j b M e
  intro T
  have hledger :=
    tagged_q_target_physical_count hn ring i j k a b
      hb hports N hnear.1 hclean T
  rw [hcharge] at hledger
  have hcomp :=
    compensator_cleared
      (taggedQStopped ring i j k b (by omega : 2 ≤ n) hports)
      (taggedD15TargetActive ring j b)
      (fun M => SealedPhaseEdge ring j
        (taggedQAttackerPhase ring j b M))
      (collapseCountNumerator
        (taggedTrialStep ring i j k b)
        (taggedRedirection ring j b (by omega : 2 ≤ n) hports))
      (2 * b - 1) (.active N) T hledger
  have hcost :=
    tagged_long_vulnerable_stopped_q_cost
      hn ring i j k a b N hnear hclean T
  have hcancel :
      (2 * b - 1) *
        collapseCountNumerator
          (taggedTrialStep ring i j k b)
          (taggedRedirection ring j b (by omega : 2 ≤ n) hports)
          (.active N) T ≤ (2 * b) * n ^ T := by
    have hscaled :
        n * ((2 * b - 1) *
          collapseCountNumerator
            (taggedTrialStep ring i j k b)
            (taggedRedirection ring j b (by omega : 2 ≤ n)
              hports)
            (.active N) T) ≤ n * ((2 * b) * n ^ T) := by
      calc
        _ ≤ truncatedActiveCostNumerator
          (taggedQStopped ring i j k b (by omega : 2 ≤ n)
            hports) (.active N) T := hcomp
        _ ≤ n ^ T * (n * (2 * b)) := hcost
        _ = n * ((2 * b) * n ^ T) := by ac_rfl
    exact Nat.le_of_mul_le_mul_left hscaled
      (by omega : 0 < n)
  have hfactor : 2 * b ≤ 2 * (2 * b - 1) := by omega
  have hcap :
      (2 * b - 1) *
        collapseCountNumerator
          (taggedTrialStep ring i j k b)
          (taggedRedirection ring j b (by omega : 2 ≤ n)
            hports)
          (.active N) T ≤
        (2 * b - 1) * (2 * n ^ T) := by
    calc
      _ ≤ (2 * b) * n ^ T := hcancel
      _ ≤ (2 * (2 * b - 1)) * n ^ T :=
        Nat.mul_le_mul_right (n ^ T) hfactor
      _ = (2 * b - 1) * (2 * n ^ T) := by ac_rfl
  exact Nat.le_of_mul_le_mul_left hcap
    (by omega : 0 < 2 * b - 1)

/-- The m=1 affine secant for every controlled word, including
active leaves. 3*2^T <= 4*2^(T-N)+N*2^T is the integer
certificate for the paper's Jensen step at E_Q[N] <= 2. -/
theorem tagged_long_secant_nonretry
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S)
    (r : ControlledSchedulerMass.Redirection S n)
    (z : StopNode S) (hz : z ≠ .failure)
    (hcontrolled : ∀ s e,
      ControlledSchedulerMass.controlledStep step r s e ≠ .failure)
    (T : Nat) :
    3 * (2 ^ T * n ^ T) ≤
      4 * weightedQNonRetryNumerator step r z T +
        2 ^ T * collapseCountNumerator step r z T := by
  have hpoint : ∀ idx : Fin (n ^ T),
      3 * 2 ^ T ≤
        4 * powSuccessOrActive
          (ControlledSchedulerMass.runWord
            (ControlledSchedulerMass.controlledStep step r) z
            (FixedSpanRenewalPayload.rawWord n T idx))
          (T - ControlledSchedulerMass.eventCount
            (ControlledSchedulerMass.controlledStep step r) r z
            (FixedSpanRenewalPayload.rawWord n T idx)) +
        2 ^ T * ControlledSchedulerMass.eventCount
          (ControlledSchedulerMass.controlledStep step r) r z
          (FixedSpanRenewalPayload.rawWord n T idx) := by
    intro idx
    have hNT :
        ControlledSchedulerMass.eventCount
          (ControlledSchedulerMass.controlledStep step r) r z
          (FixedSpanRenewalPayload.rawWord n T idx) ≤ T := by
      have hh := tagged_q_event_count_le_length
        (ControlledSchedulerMass.controlledStep step r) r z
        (FixedSpanRenewalPayload.rawWord n T idx)
      simpa [FixedSpanRenewalPayload.rawWord_length] using hh
    have hsec :
        3 * 2 ^ T ≤
          4 * 2 ^ (T - ControlledSchedulerMass.eventCount
            (ControlledSchedulerMass.controlledStep step r) r z
            (FixedSpanRenewalPayload.rawWord n T idx)) +
          ControlledSchedulerMass.eventCount
            (ControlledSchedulerMass.controlledStep step r) r z
            (FixedSpanRenewalPayload.rawWord n T idx) * 2 ^ T := by
      simpa using tagged_q_secant_scaled 1 T
        (ControlledSchedulerMass.eventCount
          (ControlledSchedulerMass.controlledStep step r) r z
          (FixedSpanRenewalPayload.rawWord n T idx)) hNT
    have hnf :
        ControlledSchedulerMass.runWord
          (ControlledSchedulerMass.controlledStep step r) z
          (FixedSpanRenewalPayload.rawWord n T idx) ≠ .failure :=
      tagged_d15_safe_word
        (ControlledSchedulerMass.controlledStep step r)
        hcontrolled z hz (FixedSpanRenewalPayload.rawWord n T idx)
    cases hr : ControlledSchedulerMass.runWord
        (ControlledSchedulerMass.controlledStep step r) z
        (FixedSpanRenewalPayload.rawWord n T idx) with
    | active y =>
        simpa [powSuccessOrActive, hr, Nat.mul_comm] using hsec
    | success =>
        simpa [powSuccessOrActive, hr, Nat.mul_comm] using hsec
    | failure =>
        exact False.elim (hnf hr)
  have hsum :=
    ofFn_sum_le
      (fun _ : Fin (n ^ T) => 3 * 2 ^ T)
      (fun idx : Fin (n ^ T) =>
        4 * powSuccessOrActive
          (ControlledSchedulerMass.runWord
            (ControlledSchedulerMass.controlledStep step r) z
            (FixedSpanRenewalPayload.rawWord n T idx))
          (T - ControlledSchedulerMass.eventCount
            (ControlledSchedulerMass.controlledStep step r) r z
            (FixedSpanRenewalPayload.rawWord n T idx)) +
        2 ^ T * ControlledSchedulerMass.eventCount
          (ControlledSchedulerMass.controlledStep step r) r z
          (FixedSpanRenewalPayload.rawWord n T idx))
      hpoint
  rw [ofFn_sum_const, ofFn_sum_add,
    ofFn_sum_mul_left, ofFn_sum_mul_left] at hsum
  rw [
    FixedSpanRenewalPayload.rawWord_sum n T
      (fun w =>
        powSuccessOrActive
          (ControlledSchedulerMass.runWord
            (ControlledSchedulerMass.controlledStep step r) z w)
          (T - ControlledSchedulerMass.eventCount
            (ControlledSchedulerMass.controlledStep step r) r z w)),
    FixedSpanRenewalPayload.rawWord_sum n T
      (fun w => ControlledSchedulerMass.eventCount
        (ControlledSchedulerMass.controlledStep step r) r z w)
  ] at hsum
  have hword :
      n ^ T * (3 * 2 ^ T) ≤
        4 * weightedQNonRetryNumerator step r z T +
          2 ^ T * collapseCountNumerator step r z T := by
    simpa [weightedQNonRetryNumerator,
      collapseCountNumerator] using hsum
  calc
    3 * (2 ^ T * n ^ T) =
        n ^ T * (3 * 2 ^ T) := by ac_rfl
    _ ≤ 4 * weightedQNonRetryNumerator step r z T +
          2 ^ T * collapseCountNumerator step r z T := hword

/-- Division-free 1/4 nonfailure bound: the Q-collapse moment
at most two combines with the m=1 secant and the exact adaptive
change of measure. -/
theorem tagged_long_nonretry_quarter
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S)
    (r : ControlledSchedulerMass.Redirection S n)
    (z : StopNode S) (hz : z ≠ .failure)
    (hcontrolled : ∀ s e,
      ControlledSchedulerMass.controlledStep step r s e ≠ .failure)
    (T : Nat)
    (hcollapse :
      collapseCountNumerator step r z T ≤ 2 * n ^ T) :
    n ^ T ≤ 4 * (activeCount step z T +
      successCount step z T) := by
  have hsec := tagged_long_secant_nonretry
    step r z hz hcontrolled T
  have hmoment :
      2 ^ T * collapseCountNumerator step r z T ≤
        2 * (2 ^ T * n ^ T) := by
    calc
      _ ≤ 2 ^ T * (2 * n ^ T) :=
        Nat.mul_le_mul_left (2 ^ T) hcollapse
      _ = 2 * (2 ^ T * n ^ T) := by ac_rfl
  have hweighted :
      2 ^ T * n ^ T ≤
        4 * weightedQNonRetryNumerator step r z T := by
    omega
  have hchange :=
    weighted_changeOfMeasure_nonretry step r z T
  have hscaled :
      2 ^ T * n ^ T ≤
        2 ^ T * (4 * (activeCount step z T +
          successCount step z T)) := by
    calc
      _ ≤ 4 * weightedQNonRetryNumerator step r z T :=
        hweighted
      _ ≤ 4 * (2 ^ T * (activeCount step z T +
          successCount step z T)) :=
        Nat.mul_le_mul_left 4 hchange
      _ = 2 ^ T * (4 * (activeCount step z T +
          successCount step z T)) := by ac_rfl
  exact Nat.le_of_mul_le_mul_left hscaled
    (Nat.pow_pos (by decide : 0 < 2))

/-- The long-regime raw vulnerable trial's failure cylinders
have mass at most 3/4 at EVERY finite horizon. This is the
paper's exact Q-change-of-measure estimate, not a fair two-edge
race of the raw scheduler. -/
theorem tagged_long_vulnerable_failure_quarter {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hb : 2 ≤ b)
    (N : TripleNativeState n)
    (hnear : TaggedLongNear ring i j k a b N)
    (hclean : TaggedCleanDummy ring i j a b N) :
    ∀ T,
      4 * failureCount
        (taggedTrialStep ring i j k b)
        (.active N) T ≤ 3 * n ^ T := by
  classical
  have hports : ring.leftNeighbor j ≠ j :=
    Ne.symm (tagged_q_incident_edges_distinct
      (by omega : 2 ≤ n) ring j)
  have hcontrolled : ∀ s e,
      ControlledSchedulerMass.controlledStep
        (taggedTrialStep ring i j k b)
        (taggedRedirection ring j b (by omega : 2 ≤ n) hports)
        s e ≠ .failure := by
    intro s e
    change taggedQStopped ring i j k b (by omega : 2 ≤ n)
      hports s e ≠ .failure
    rw [tagged_q_stopped_eq ring i j k b
      (by omega : 2 ≤ n) hports s e]
    split <;> simp
  intro T
  have hcollapse :=
    tagged_long_vulnerable_collapse_two
      hn ring i j k a b hb N hnear hclean T
  have hnonretry :=
    tagged_long_nonretry_quarter
      (taggedTrialStep ring i j k b)
      (taggedRedirection ring j b (by omega : 2 ≤ n) hports)
      (.active N) (by simp) hcontrolled T hcollapse
  have hpartition :=
    node_count_partition (taggedTrialStep ring i j k b)
      (.active N) T
  omega

/-- D.19 Clock 4 in the paper's stated long-attacker regime b>=2:
both the Q-controlled 2nb cost and the original-scheduler 3/4
failure-cylinder estimate. The definition itself has no b premise,
so this theorem keeps the required parameter hypothesis explicit. -/
theorem tagged_long_vulnerable_clock {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hb : 2 ≤ b) :
    TaggedLongVulnerableClock hn ring i j k a b := by
  exact tagged_long_vulnerable_clock_of_failure
    hn ring i j k a b
    (fun N hnear hclean T =>
      tagged_long_vulnerable_failure_quarter
        hn ring i j k a b hb N hnear hclean T)

end L3


/-! ## Native long-attempt monitor and remaining composition interface

The monitor below applies exactly one
nativeE edge per scheduler letter and keeps a genuine native survivor
as its retry seed. It does NOT yet establish the two quantitative
attempt bounds needed to instantiate TaggedLongNativeAttemptMachine.

At the first presently missing physical bridge, the incident mode
requires closure of Near and Ready under every nonincident surviving
service. The associated stopped-stage composition / retry-mass transfer
also remains to be proved; no hypothesis is secretly discharged.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false
attribute [local instance low] Classical.propDecidable

/-- The first attempt mode skips only stages whose certified entrance
already holds at the literal initial native state. In particular,
a retained and B-Ready seed goes directly to the incident stage. -/
noncomputable def tagged_long_attempt_start {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (seed : TaggedLongAttemptSeed ring i j k a b) :
    TaggedLongAttemptState ring i j k a b :=
  { N := seed.N
    mode :=
      if TaggedLongRetained ring i j k a b seed.N then
        if SealedCleanReady ring seed.N j b then
          .incident
        else .targetRace
      else .preparation
    triple := seed.triple
    attackerPhase := none
    targetPhase := none
    retainedOffset := none }

/-- Proof-only mode dispatcher. It does not modify the native state:
preparation ends at an exact retained cut; a retained race enters the
incident stage when B is actually Ready; an incoming incident letter
enters the vulnerable trial. -/
noncomputable def tagged_long_attempt_follow_mode {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (z : TaggedLongAttemptState ring i j k a b)
    (e : Fin n) (M : TripleNativeState n) : TaggedLongAttemptMode :=
  match z.mode with
  | .preparation =>
      if TaggedLongRetained ring i j k a b M then
        if SealedCleanReady ring M j b then
          .incident
        else .targetRace
      else .preparation
  | .targetRace =>
      if SealedCleanReady ring M j b then .incident else .targetRace
  | .incident =>
      if e = ring.leftNeighbor j then .vulnerable else .incident
  | .vulnerable => .vulnerable
  | .recovery => .recovery

/-- Stage failure is an immediate retry at the actual post-nativeE
configuration. The recovery mode is reserved but not entered by this
kernel: a new attempt's preparation is valid from every tagged triple,
so no fictitious Ready reset is performed. -/
noncomputable def tagged_long_attempt_retry_edge {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (z : TaggedLongAttemptState ring i j k a b)
    (e : Fin n) (M : TripleNativeState n) : Prop :=
  match z.mode with
  | .preparation => False
  | .targetRace => ¬ TaggedLongNear ring i j k a b M
  | .incident => e = j
  | .vulnerable => SealedCleanReady ring z.N j b ∧ e = j
  | .recovery => True

/-- Every possible one-letter output has a same-edge nativeE
certificate. A success means actual tagged deletion. An active child
retains exactly the new physical configuration. A retry seed carries
that exact configuration and its surviving tagged-triple witness. -/
noncomputable def tagged_long_attempt_step_certified {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (z : TaggedLongAttemptState ring i j k a b)
    (e : Fin n) :
    { out : AttemptNode
        (TaggedLongAttemptState ring i j k a b)
        (TaggedLongAttemptSeed ring i j k a b) //
      match out with
      | .success =>
          TaggedDeleted i j k (nativeE ring z.N e)
      | .active z' =>
          z'.N = nativeE ring z.N e
      | .retry seed =>
          seed.N = nativeE ring z.N e } := by
  classical
  by_cases hd : TaggedDeleted i j k (nativeE ring z.N e)
  · exact ⟨.success, hd⟩
  · have ht : TaggedTriple ring i j k a b
        (nativeE ring z.N e) :=
      tagged_triple_step_of_survival
        hn ring i j k a b z.N e z.triple hd
    by_cases hr : tagged_long_attempt_retry_edge
        ring i j k a b z e (nativeE ring z.N e)
    · exact ⟨.retry
        { N := nativeE ring z.N e
          triple := ht }, rfl⟩
    · exact ⟨.active
        { N := nativeE ring z.N e
          mode := tagged_long_attempt_follow_mode
            ring i j k a b z e (nativeE ring z.N e)
          triple := ht
          attackerPhase := none
          targetPhase := none
          retainedOffset := none }, rfl⟩

/-- Extract the one-letter observer transition from its physical
certificate. The observer has no state-editing primitive. -/
noncomputable def tagged_long_attempt_step {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (z : TaggedLongAttemptState ring i j k a b)
    (e : Fin n) :
    AttemptNode (TaggedLongAttemptState ring i j k a b)
      (TaggedLongAttemptSeed ring i j k a b) :=
  (tagged_long_attempt_step_certified
    hn ring i j k a b z e).val

theorem tagged_long_attempt_step_sound {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (z : TaggedLongAttemptState ring i j k a b)
    (e : Fin n) :
    match tagged_long_attempt_step hn ring i j k a b z e with
    | .success =>
        TaggedDeleted i j k (nativeE ring z.N e)
    | .active z' =>
        z'.N = nativeE ring z.N e
    | .retry seed =>
        seed.N = nativeE ring z.N e :=
  (tagged_long_attempt_step_certified hn ring i j k a b z e).property

/-- A retry starts from exactly the original native survivor. -/
theorem tagged_long_attempt_start_native {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (seed : TaggedLongAttemptSeed ring i j k a b) :
    (tagged_long_attempt_start ring i j k a b seed).N =
      seed.N := by
  rfl

/-- Full physical kernel. All tagged-triple seeds are valid, and a
retry is a surviving native configuration, never a canonical reset. -/
noncomputable def tagged_long_native_retry_kernel {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat) :
    RetryKernel (TaggedLongAttemptState ring i j k a b)
      (TaggedLongAttemptSeed ring i j k a b) n where
  start := tagged_long_attempt_start ring i j k a b
  step := tagged_long_attempt_step hn ring i j k a b
  valid := fun _ => True
  retry_valid := by
    intro _ _ _ _
    trivial

/-- Success, continuation, and retry are certified on the SAME
physical scheduler letter. This is the nontrivial simulation clause
of TaggedLongNativeAttemptMachine, independent of stage bounds. -/
theorem tagged_long_attempt_native_simulation {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat) :
    Prob.RetrySimulation
      (tagged_long_native_retry_kernel hn ring i j k a b)
      (nativeE ring) (TaggedDeleted i j k)
      (fun M z => z.N = M) := by
  intro M z hrel _ e
  have hs := tagged_long_attempt_step_sound
    hn ring i j k a b z e
  cases hnode :
      (tagged_long_native_retry_kernel hn ring i j k a b).step z e with
  | success =>
      have hreal :
          tagged_long_attempt_step hn ring i j k a b z e =
            .success := hnode
      rw [hreal] at hs
      rw [hrel] at hs
      exact hs
  | active z' =>
      have hreal :
          tagged_long_attempt_step hn ring i j k a b z e =
            .active z' := hnode
      rw [hreal] at hs
      rw [hrel] at hs
      exact hs
  | retry seed =>
      have hreal :
          tagged_long_attempt_step hn ring i j k a b z e =
            .retry seed := hnode
      rw [hreal] at hs
      rw [hrel] at hs
      change (tagged_long_attempt_start
        ring i j k a b seed).N = nativeE ring M e
      exact (tagged_long_attempt_start_native
        ring i j k a b seed).trans hs

/-- The already established D.19 arithmetic even pays for the additional
B recovery stage, which this immediate-retry observer does not need.
Thus its four stage allowances fit into the prescribed attempt cost. -/
theorem tagged_long_machine_budget_arithmetic
    (n a b : Nat) (ha : 1 ≤ a) (hb : 2 ≤ b) :
    n * (6 * a + b) + n * (2 * b - 1) + n +
      n * (2 * b) ≤ 7 * n * (a + b) := by
  have hh := tagged_long_attempt_budget n a b ha hb
  omega

/-- Exact first missing incident-stage physical closure interface.
For any surviving scheduler edge incident to neither port of j,
the actual A-live near front and the actual B-Ready cut must persist.
This is NOT assumed as a theorem by the preceding construction. -/
def TaggedLongIncidentOffPortClosure {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat) : Prop :=
  ∀ N : TripleNativeState n,
    TaggedLongNear ring i j k a b N →
    SealedCleanReady ring N j b →
    ∀ e : Fin n,
      e ≠ ring.leftNeighbor j →
      e ≠ j →
      ¬ TaggedDeleted i j k (nativeE ring N e) →
      TaggedLongNear ring i j k a b (nativeE ring N e) ∧
        SealedCleanReady ring (nativeE ring N e) j b

/-- A reduction after kernel construction and native simulation.
The only remaining hypotheses are the two EXACT finite-horizon
per-attempt bounds; they require physical stage closure and
same-word stopped-stage composition, not just scalar arithmetic. -/
theorem tagged_long_native_attempt_machine_of_bounds {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hb : 2 ≤ b)
    (hcost :
      ∀ s : TaggedLongAttemptSeed ring i j k a b,
        ∀ T,
          attemptCostNumerator
            (tagged_long_native_retry_kernel hn ring i j k a b)
            (.active
              ((tagged_long_native_retry_kernel
                hn ring i j k a b).start s)) T ≤
            n ^ T * (7 * n * (a + b)))
    (hretry :
      ∀ s : TaggedLongAttemptSeed ring i j k a b,
        ∀ T,
          16 * retryCount
            (tagged_long_native_retry_kernel hn ring i j k a b)
            (.active
              ((tagged_long_native_retry_kernel
                hn ring i j k a b).start s)) T ≤
            15 * n ^ T) :
    TaggedLongNativeAttemptMachine ring i j k a b := by
  refine ⟨tagged_long_native_retry_kernel hn ring i j k a b,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro seed
    trivial
  · intro seed
    exact tagged_long_attempt_start_native ring i j k a b seed
  · exact tagged_long_attempt_native_simulation
      hn ring i j k a b
  · intro seed _ T
    exact hcost seed T
  · intro seed _ T
    exact hretry seed T

end L3


/-! ## Physical incident closure and delayed-service handoff

The exact nativeE
off-port invariant is proved below. The following same-word
four-stage attempt cost and retry-cylinder composition is still OPEN.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false
attribute [local instance low] Classical.propDecidable

/-- B's actual Ready phase is preserved by every surviving native
service at neither incident port of j. An interior B service at a
positive offset cannot launch a new bullet while B is Ready; the
only other Ready-changing edge is the incoming port. -/
theorem tagged_long_ready_off_port_preserved {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n) (e : Fin n)
    (ht : TaggedTriple ring i j k a b N)
    (hready : SealedCleanReady ring N j b)
    (hin : e ≠ ring.leftNeighbor j) (hout : e ≠ j)
    (hnot : ¬ TaggedDeleted i j k (nativeE ring N e)) :
    SealedCleanReady ring (nativeE ring N e) j b := by
  have hj : (nativeE ring N e j).l = true := by
    cases hx : (nativeE ring N e j).l with
    | false => exact False.elim (hnot (Or.inr (Or.inl hx)))
    | true => rfl
  have hk : (nativeE ring N e k).l = true := by
    cases hx : (nativeE ring N e k).l with
    | false => exact False.elim (hnot (Or.inr (Or.inr hx)))
    | true => rfl
  obtain ⟨phase, hp, hstage⟩ :=
    sealed_close_step_stage ring N j k b e
      (.ready : SealedPhase n) ht.2.2 hready hj hk
  have hnotRoot :
      (SealedCloseProof.position ring j e).val ≠ 0 := by
    intro hzero
    have hsite :=
      sealed_close_edge_of_position ring j e 0 hzero
    exact hout (hsite.trans (sealedSite_zero ring j))
  have hnotWrap :
      (SealedCloseProof.position ring j e).val + 1 ≠ n := by
    intro hwrap
    exact hin ((sealed_close_incoming_iff ring j e).mp hwrap)
  have htable :
      sealedCloseTable ring j b e (.ready : SealedPhase n) =
        .ready := by
    change
      (if (SealedCloseProof.position ring j e).val < b then
        SealedCloseProof.insideStage b .ready
          (SealedCloseProof.position ring j e).val
       else if (SealedCloseProof.position ring j e).val + 1 = n then
        SealedCloseProof.incomingStage .ready else .ready) =
      .ready
    split
    · simp [SealedCloseProof.insideStage, hnotRoot]
    · first
        | rfl
        | (split
           · rename_i hw
             exact False.elim (hnotWrap hw)
           · rfl)
  have hphaseReady :
      SealedCloseProof.fromPhase phase = .ready :=
    hstage.trans htable
  cases phase with
  | ready => exact hp
  | dummy q => cases hphaseReady
  | live q => cases hphaseReady
  | returning q => cases hphaseReady

/-- A near live front advances one physical interior service on its
current nominated edge, even when B has already reached Ready.
Unlike the older race-specific lemma, no B-nonready premise is used. -/
theorem tagged_long_near_nominated_interior_native {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (hnear : TaggedLongNear ring i j k a b N)
    (p : Fin n)
    (hp : SealedPhaseHolds ring N i a (.live p))
    (hinterior : p.val + 1 < a)
    (hnot : ¬ TaggedDeleted i j k
      (nativeE ring N (SealedPhaseEdge ring i (.live p)))) :
    ∃ q : Fin n,
      TaggedLongNear ring i j k a b
        (nativeE ring N (SealedPhaseEdge ring i (.live p))) ∧
      SealedPhaseHolds ring
        (nativeE ring N (SealedPhaseEdge ring i (.live p)))
        i a (.live q) ∧
      q.val = p.val + 1 := by
  have hi :
      (nativeE ring N (SealedPhaseEdge ring i (.live p)) i).l =
        true := by
    cases hx :
        (nativeE ring N (SealedPhaseEdge ring i (.live p)) i).l with
    | false => exact False.elim (hnot (Or.inl hx))
    | true => rfl
  have hj :
      (nativeE ring N (SealedPhaseEdge ring i (.live p)) j).l =
        true := by
    cases hx :
        (nativeE ring N (SealedPhaseEdge ring i (.live p)) j).l with
    | false => exact False.elim (hnot (Or.inr (Or.inl hx)))
    | true => rfl
  obtain ⟨nextPhase, hnext, hstage⟩ :=
    sealed_close_step_stage ring N i j a
      (SealedPhaseEdge ring i (.live p)) (.live p)
      hnear.1.2.1 hp hi hj
  have hpos :
      (SealedCloseProof.position ring i
        (SealedPhaseEdge ring i (.live p))).val = p.val := by
    simpa only [SealedCloseProof.fromPhase,
      SealedCloseProof.nominated] using
      (sealed_close_nominated_position
        ring N i j a (.live p) hnear.1.2.1 hp)
  have htable :
      sealedCloseTable ring i a
        (SealedPhaseEdge ring i (.live p)) (.live p) =
          .bullet true (p.val + 1) := by
    change
      (if (SealedCloseProof.position ring i
          (SealedPhaseEdge ring i (.live p))).val < a then
        SealedCloseProof.insideStage a (.bullet true p.val)
          (SealedCloseProof.position ring i
            (SealedPhaseEdge ring i (.live p))).val
       else if (SealedCloseProof.position ring i
          (SealedPhaseEdge ring i (.live p))).val + 1 = n then
        SealedCloseProof.incomingStage (.bullet true p.val)
       else .bullet true p.val) =
          .bullet true (p.val + 1)
    rw [hpos]
    simpa only [ite_true] using
      (tagged_long_live_step_table n a p.val p.val hinterior)
  have hstageLive :
      SealedCloseProof.fromPhase nextPhase =
        .bullet true (p.val + 1) := hstage.trans htable
  cases nextPhase with
  | ready =>
      cases hstageLive
  | dummy q =>
      cases hstageLive
  | live q =>
      have hqval : q.val = p.val + 1 := by
        have hh := congrArg SealedCloseProof.nominated hstageLive
        simpa only [SealedCloseProof.fromPhase,
          SealedCloseProof.nominated] using hh
      have hnearOld :=
        tagged_long_race_a_near_witness
          ring i j k a b N hnear p hp
      have htripleNext :=
        tagged_triple_step_of_survival hn ring i j k a b
          N (SealedPhaseEdge ring i (.live p)) hnear.1 hnot
      have hsealedNext :=
        tagged_sealed_step_of_survival
          ring i j k a b N
          (SealedPhaseEdge ring i (.live p)) hnear.1
          ⟨⟨.live p, hp⟩, hnear.2.1⟩ hnot
      refine ⟨q, ⟨htripleNext, hsealedNext.2,
        q, hnext, ?_⟩, hnext, hqval⟩
      omega
  | returning q =>
      cases hstageLive

/-- The exact missing Clock-3 physical closure. At an off-port
service, B remains Ready and A's unique live bullet is retained,
including when A's nominated interior service advances by one.
The final A-live service would have been the incoming port of j,
which is excluded by the hypotheses. -/
theorem tagged_long_incident_off_port_closure {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat) :
    TaggedLongIncidentOffPortClosure ring i j k a b := by
  intro N hnear hready e hin hout hnot
  have hreadyNext :
      SealedCleanReady ring (nativeE ring N e) j b :=
    tagged_long_ready_off_port_preserved
      ring i j k a b N e hnear.1 hready hin hout hnot
  obtain ⟨p, hp, hquota⟩ := hnear.2.2
  by_cases hnom : e = SealedPhaseEdge ring i (.live p)
  · have hnotBoundary : p.val + 1 ≠ a := by
      intro hboundary
      have ha : 1 ≤ a := hnear.1.2.1.1
      have hj : j = sealedSite ring i a :=
        hnear.1.2.1.2.2.1
      have hindex : p.val = a + (n - 1) - n := by
        omega
      have hlast :
          SealedPhaseEdge ring i (.live p) =
            ring.leftNeighbor j := by
        calc
          SealedPhaseEdge ring i (.live p) =
              sealedSite ring i p.val := rfl
          _ = sealedSite ring i (a + (n - 1) - n) :=
            congrArg (sealedSite ring i) hindex
          _ = sealedSite ring i (a + (n - 1)) :=
            (tagged_long_site_wrap
              ring i (a + (n - 1)) (by omega)).symm
          _ = sealedSite ring (sealedSite ring i a) (n - 1) :=
            (tagged_long_site_chain ring i a (n - 1)).symm
          _ = sealedSite ring j (n - 1) := by rw [hj]
          _ = ring.leftNeighbor j :=
            sealed_close_last_site_left ring j
      exact hin (hnom.trans hlast)
    have hinterior : p.val + 1 < a := by
      have hlt : p.val < a := hp.1.1
      omega
    subst e
    obtain ⟨q, hnearNext, hphaseNext, hposition⟩ :=
      tagged_long_near_nominated_interior_native
        hn ring i j k a b N hnear p hp hinterior hnot
    exact ⟨hnearNext, hreadyNext⟩
  · have htripleNext :
        TaggedTriple ring i j k a b (nativeE ring N e) :=
      tagged_triple_step_of_survival
        hn ring i j k a b N e hnear.1 hnot
    have hAnext :
        SealedPhaseHolds ring (nativeE ring N e)
          i a (.live p) :=
      tagged_long_live_off_nomination
        ring i j k a b N e hnear.1 p hp hnom hnot
    have hsealedNext :
        Sealed ring (nativeE ring N e) j b :=
      sealed_of_clean_ready ring (nativeE ring N e) j b hreadyNext
    exact
      ⟨⟨htripleNext, hsealedNext, p, hAnext, hquota⟩,
        hreadyNext⟩

/-- Stage-three active successors at arbitrary physical cuts are
genuine native children preserving the full near/Ready invariant.
This is the missing invariant behind delayed first incident service. -/
theorem tagged_long_incident_active_preserves {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (N M : TripleNativeState n) (e : Fin n)
    (hnear : TaggedLongNear ring i j k a b N)
    (hready : SealedCleanReady ring N j b)
    (hactive :
      tagged_long_incident_step ring i j k N e = .active M) :
    M = nativeE ring N e ∧
      TaggedLongNear ring i j k a b M ∧
      SealedCleanReady ring M j b := by
  classical
  by_cases hin : e = ring.leftNeighbor j
  · subst e
    rw [tagged_long_incident_incoming_success ring i j k N] at hactive
    cases hactive
  · by_cases hout : e = j
    · subst e
      rw [tagged_long_incident_outgoing_class
        (by omega : 2 ≤ n) ring i j k N] at hactive
      split at hactive <;> cases hactive
    · have hnot : ¬ TaggedDeleted i j k (nativeE ring N e) := by
        intro hd
        have hs :
            tagged_long_incident_step ring i j k N e = .success := by
          simp [tagged_long_incident_step, hd]
        rw [hs] at hactive
        cases hactive
      have hclass := tagged_long_incident_other_class
        ring i j k N e hin hout
      rw [hclass, if_neg hnot] at hactive
      cases hactive
      have hclosed := tagged_long_incident_off_port_closure
        hn ring i j k a b N hnear hready e hin hout hnot
      exact ⟨rfl, hclosed.1, hclosed.2⟩

end L3


/-! ## Finite-word cut algebra and physical vulnerable cost

The generic cut reserve below is exactly
the additional hypothesis required to multiply conditional stopped
stage bounds; no independence hypothesis is used. Producing that
reserve for the actual five-mode kernel remains open.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false
attribute [local instance low] Classical.propDecidable

/-- Two-stage cost composition from an exact same-word stage cut.
This cut is an explicit hypothesis, not an independence claim.
A separate physical stage observer must prove it before application. -/
theorem tagged_long_cost_add_of_cut
    {S : Type} {n : Nat}
    (whole first : S → Fin n → StopNode S)
    (R : S → Prop) (Bfirst Bsecond : Nat)
    (hcut : ∀ x, R x → ∀ T,
      truncatedActiveCostNumerator whole (.active x) T ≤
        truncatedActiveCostNumerator first (.active x) T +
          n ^ T * Bsecond)
    (hfirst : ∀ x, R x → ∀ T,
      truncatedActiveCostNumerator first (.active x) T ≤
        n ^ T * Bfirst) :
    ∀ x, R x → ∀ T,
      truncatedActiveCostNumerator whole (.active x) T ≤
        n ^ T * (Bfirst + Bsecond) := by
  intro x hx T
  calc
    _ ≤ truncatedActiveCostNumerator first (.active x) T +
          n ^ T * Bsecond := hcut x hx T
    _ ≤ n ^ T * Bfirst + n ^ T * Bsecond :=
      Nat.add_le_add_right (hfirst x hx T) _
    _ = n ^ T * (Bfirst + Bsecond) := by
      rw [Nat.mul_add]

/-- The exact finite-word product numerator. The first-stage success
and failure counts are disjoint, by node_count_partition. Once a
same-word cut comparison is supplied, no independence is needed:
F_total <= F_first + (f_second/d_second)*S_first. -/
theorem tagged_long_failure_product_of_cut
    {S : Type} {n : Nat}
    (whole first : S → Fin n → StopNode S)
    (R : S → Prop)
    (denFirst numFirst denSecond numSecond : Nat)
    (hnum : numSecond ≤ denSecond)
    (hfirst : ∀ x, R x → ∀ T,
      denFirst * failureCount first (.active x) T ≤
        numFirst * n ^ T)
    (hcut : ∀ x, R x → ∀ T,
      denSecond * failureCount whole (.active x) T ≤
        denSecond * failureCount first (.active x) T +
          numSecond * successCount first (.active x) T) :
    ∀ x, R x → ∀ T,
      (denFirst * denSecond) *
        failureCount whole (.active x) T ≤
      (denFirst * numSecond +
        numFirst * (denSecond - numSecond)) * n ^ T := by
  intro x hx T
  have hc := hcut x hx T
  have hfirstBound := hfirst x hx T
  have hpart := node_count_partition first (.active x) T
  have hFS :
      failureCount first (.active x) T +
        successCount first (.active x) T ≤ n ^ T := by
    omega
  have hden :
      denSecond = (denSecond - numSecond) + numSecond := by
    omega
  calc
    (denFirst * denSecond) *
        failureCount whole (.active x) T =
      denFirst * (denSecond *
        failureCount whole (.active x) T) := by ac_rfl
    _ ≤ denFirst *
        (denSecond * failureCount first (.active x) T +
          numSecond * successCount first (.active x) T) :=
      Nat.mul_le_mul_left denFirst hc
    _ = denFirst * (denSecond - numSecond) *
        failureCount first (.active x) T +
          (denFirst * numSecond) *
            (failureCount first (.active x) T +
              successCount first (.active x) T) := by
      generalize failureCount first (.active x) T = F
      generalize successCount first (.active x) T = G
      generalize hd : denSecond - numSecond = d at hden
      rw [hden]
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    _ ≤ denFirst * (denSecond - numSecond) *
        failureCount first (.active x) T +
          (denFirst * numSecond) * n ^ T :=
      Nat.add_le_add_left
        (Nat.mul_le_mul_left (denFirst * numSecond) hFS) _
    _ = (denSecond - numSecond) *
        (denFirst * failureCount first (.active x) T) +
          (denFirst * numSecond) * n ^ T := by
      ac_rfl
    _ ≤ (denSecond - numSecond) * (numFirst * n ^ T) +
          (denFirst * numSecond) * n ^ T :=
      Nat.add_le_add_right
        (Nat.mul_le_mul_left (denSecond - numSecond)
          hfirstBound) _
    _ = (denFirst * numSecond +
          numFirst * (denSecond - numSecond)) * n ^ T := by
      rw [Nat.add_mul]
      ac_rfl

/-- Every physical active raw child must also be a controlled
active child, on the same scheduler letter and same native successor.
This property alone bounds the raw truncated active cost by the
controlled active cost. -/
theorem tagged_long_cost_mono_of_active
    {S : Type} {n : Nat}
    (raw controlled : S → Fin n → StopNode S)
    (hactive : ∀ s e t, raw s e = .active t →
      controlled s e = .active t) :
    ∀ z T,
      truncatedActiveCostNumerator raw z T ≤
        truncatedActiveCostNumerator controlled z T := by
  intro z T
  induction T generalizing z with
  | zero =>
      cases z <;> simp [truncatedActiveCostNumerator]
  | succ T ih =>
      cases z with
      | success =>
          simp [truncatedActiveCostNumerator]
      | failure =>
          simp [truncatedActiveCostNumerator]
      | active s =>
          change n ^ (T + 1) +
              (List.ofFn (fun e : Fin n =>
                truncatedActiveCostNumerator raw (raw s e) T)).sum ≤
            n ^ (T + 1) +
              (List.ofFn (fun e : Fin n =>
                truncatedActiveCostNumerator controlled
                  (controlled s e) T)).sum
          apply Nat.add_le_add_left
          apply ofFn_sum_le
          intro e
          cases h : raw s e with
          | active t =>
              have hc := hactive s e t h
              rw [hc]
              exact ih (.active t)
          | success =>
              cases T <;> simp [truncatedActiveCostNumerator]
          | failure =>
              cases T <;> simp [truncatedActiveCostNumerator]

/-- On every raw active vulnerable edge, Q uses that SAME physical
nativeE row. The only redirected letter is a raw failure and thus
cannot be a raw active child. -/
theorem tagged_long_raw_active_is_q_active {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (b : Nat)
    (hn : 2 ≤ n) (hports : ring.leftNeighbor j ≠ j)
    (N M : TripleNativeState n) (e : Fin n)
    (hactive : taggedTrialStep ring i j k b N e = .active M) :
    taggedQStopped ring i j k b hn hports N e = .active M := by
  classical
  have hnotdel :
      ¬ TaggedDeleted i j k (nativeE ring N e) := by
    intro hd
    have hs :
        taggedTrialStep ring i j k b N e = .success := by
      simp [taggedTrialStep, hd]
    rw [hs] at hactive
    cases hactive
  have hnotfail :
      ¬ (SealedCleanReady ring N j b ∧ e = j) := by
    intro hf
    obtain ⟨hr, he⟩ := hf
    rw [he] at hnotdel
    have hs :
        taggedTrialStep ring i j k b N e = .failure := by
      rw [he]
      simp [taggedTrialStep, hnotdel, hr]
    rw [hs] at hactive
    cases hactive
  have hnext :
      taggedQNext ring j b hn hports N e =
        nativeE ring N e := by
    by_cases he : e = j
    · have hnready : ¬ SealedCleanReady ring N j b := by
        intro hr
        exact hnotfail ⟨hr, he⟩
      subst e
      exact tagged_d15_raw_q_same_nonready
        ring j b hn hports N hnready
    · exact tagged_d15_raw_q_same_other_edge
        ring j b hn hports N e he
  have hphysical :
      nativeE ring N e = M := by
    have hh :
        (StopNode.active (nativeE ring N e)) = .active M := by
      simpa [taggedTrialStep, hnotdel, hnotfail] using hactive
    cases hh
    rfl
  rw [tagged_q_stopped_eq ring i j k b hn hports N e,
    hnext, if_neg hnotdel, hphysical]

/-- The raw vulnerable stage has a finite-horizon expected active
cost at most 2nb, not merely the controlled Q process. -/
theorem tagged_long_vulnerable_raw_cost {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (hnear : TaggedLongNear ring i j k a b N)
    (hclean : TaggedCleanDummy ring i j a b N) :
    ∀ T,
      truncatedActiveCostNumerator
        (taggedTrialStep ring i j k b) (.active N) T ≤
      n ^ T * (n * (2 * b)) := by
  have hports : ring.leftNeighbor j ≠ j :=
    Ne.symm (tagged_q_incident_edges_distinct
      (by omega : 2 ≤ n) ring j)
  intro T
  calc
    truncatedActiveCostNumerator
        (taggedTrialStep ring i j k b) (.active N) T ≤
      truncatedActiveCostNumerator
        (taggedQStopped ring i j k b (by omega : 2 ≤ n)
          hports) (.active N) T :=
      tagged_long_cost_mono_of_active
        (taggedTrialStep ring i j k b)
        (taggedQStopped ring i j k b (by omega : 2 ≤ n)
          hports)
        (fun M e V h =>
          tagged_long_raw_active_is_q_active
            ring i j k b (by omega : 2 ≤ n)
            hports M V e h) (.active N) T
    _ ≤ n ^ T * (n * (2 * b)) :=
      tagged_long_vulnerable_stopped_q_cost
        hn ring i j k a b N hnear hclean T

end L3


/-! ## Native same-word stage-mode handoff certificates

The proofs concern each actual nativeE letter of the
long RetryKernel, and preserve the historical-mode predicates.
They do not assert the still-unproved finite-word attempt reserves.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false
attribute [local instance low] Classical.propDecidable

/-- A retained A-live front is Near, whether or not B is Ready. -/
theorem tagged_long_retained_to_near {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (hret : TaggedLongRetained ring i j k a b N) :
    TaggedLongNear ring i j k a b N := by
  obtain ⟨ht, hB, p, hp, hdistance⟩ := hret
  exact ⟨ht, hB, p, hp, by omega⟩

/-- A true native deletion outranks any stage transition. -/
theorem tagged_long_attempt_step_on_delete {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (z : TaggedLongAttemptState ring i j k a b)
    (e : Fin n)
    (hdel : TaggedDeleted i j k (nativeE ring z.N e)) :
    tagged_long_attempt_step hn ring i j k a b z e =
      .success := by
  classical
  simp [tagged_long_attempt_step,
    tagged_long_attempt_step_certified, hdel]

/-- A nondeleting retry carries the exact nativeE successor. -/
theorem tagged_long_attempt_step_on_retry {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (z : TaggedLongAttemptState ring i j k a b)
    (e : Fin n)
    (hdel : ¬ TaggedDeleted i j k (nativeE ring z.N e))
    (hretry : tagged_long_attempt_retry_edge
      ring i j k a b z e (nativeE ring z.N e)) :
    ∃ seed : TaggedLongAttemptSeed ring i j k a b,
      tagged_long_attempt_step hn ring i j k a b z e =
        .retry seed ∧ seed.N = nativeE ring z.N e := by
  have htriple : TaggedTriple ring i j k a b
      (nativeE ring z.N e) :=
    tagged_triple_step_of_survival
      hn ring i j k a b z.N e z.triple hdel
  refine ⟨⟨nativeE ring z.N e, htriple⟩, ?_, rfl⟩
  classical
  simp [tagged_long_attempt_step,
    tagged_long_attempt_step_certified, hdel, hretry]

/-- An actual nondeleting, nonretry child has exactly the dispatcher
mode and the physical nativeE state. -/
theorem tagged_long_attempt_step_on_active {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (z : TaggedLongAttemptState ring i j k a b)
    (e : Fin n)
    (hdel : ¬ TaggedDeleted i j k (nativeE ring z.N e))
    (hretry : ¬ tagged_long_attempt_retry_edge
      ring i j k a b z e (nativeE ring z.N e)) :
    ∃ z' : TaggedLongAttemptState ring i j k a b,
      tagged_long_attempt_step hn ring i j k a b z e =
        .active z' ∧
      z'.N = nativeE ring z.N e ∧
      z'.mode = tagged_long_attempt_follow_mode
        ring i j k a b z e (nativeE ring z.N e) := by
  have htriple : TaggedTriple ring i j k a b
      (nativeE ring z.N e) :=
    tagged_triple_step_of_survival
      hn ring i j k a b z.N e z.triple hdel
  refine ⟨⟨nativeE ring z.N e,
    tagged_long_attempt_follow_mode
      ring i j k a b z e (nativeE ring z.N e),
    htriple, none, none, none⟩, ?_, rfl, rfl⟩
  classical
  simp [tagged_long_attempt_step,
    tagged_long_attempt_step_certified, hdel, hretry]

/-- Invert any actual active edge: it is neither deletion nor retry
and uses the exact same post-service native state. -/
theorem tagged_long_attempt_active_child_mode {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (z z' : TaggedLongAttemptState ring i j k a b)
    (e : Fin n)
    (hactive : tagged_long_attempt_step
      hn ring i j k a b z e = .active z') :
    z'.N = nativeE ring z.N e ∧
      z'.mode = tagged_long_attempt_follow_mode
        ring i j k a b z e (nativeE ring z.N e) ∧
      ¬ tagged_long_attempt_retry_edge
        ring i j k a b z e (nativeE ring z.N e) := by
  have hdel : ¬ TaggedDeleted i j k (nativeE ring z.N e) := by
    intro hd
    have hs := tagged_long_attempt_step_on_delete
      hn ring i j k a b z e hd
    rw [hs] at hactive
    cases hactive
  have hnotretry : ¬ tagged_long_attempt_retry_edge
      ring i j k a b z e (nativeE ring z.N e) := by
    intro hr
    obtain ⟨seed, hs, _⟩ :=
      tagged_long_attempt_step_on_retry
        hn ring i j k a b z e hdel hr
    rw [hs] at hactive
    cases hactive
  obtain ⟨M, hstep, hphysical, hmode⟩ :=
    tagged_long_attempt_step_on_active
      hn ring i j k a b z e hdel hnotretry
  rw [hstep] at hactive
  cases hactive
  exact ⟨hphysical, hmode, hnotretry⟩

/-- Stage-indexed active invariant; recovery is impossible in this
immediate-retry kernel. Stage 1 is Near and non-Ready, stage 2 is
Near and Ready. Stage 3 only needs a valid initial entrance cut. -/
def TaggedLongAttemptStageGood {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (z : TaggedLongAttemptState ring i j k a b) : Prop :=
  match z.mode with
  | .preparation => ¬ TaggedLongRetained ring i j k a b z.N
  | .targetRace =>
      TaggedLongNear ring i j k a b z.N ∧
        ¬ SealedCleanReady ring z.N j b
  | .incident =>
      TaggedLongNear ring i j k a b z.N ∧
        SealedCleanReady ring z.N j b
  | .vulnerable => True
  | .recovery => False

/-- Starting a new attempt consumes no scheduler letter, even when
Retained and/or B-Ready hold at the very first native seed. -/
theorem tagged_long_attempt_stage_good_start {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (seed : TaggedLongAttemptSeed ring i j k a b) :
    TaggedLongAttemptStageGood ring i j k a b
      (tagged_long_attempt_start ring i j k a b seed) := by
  classical
  by_cases hret : TaggedLongRetained
      ring i j k a b seed.N
  · have hnear := tagged_long_retained_to_near
      ring i j k a b seed.N hret
    by_cases hready : SealedCleanReady ring seed.N j b
    · simpa [TaggedLongAttemptStageGood,
        tagged_long_attempt_start, hret, hready] using
        (show TaggedLongNear ring i j k a b seed.N ∧
          SealedCleanReady ring seed.N j b from ⟨hnear, hready⟩)
    · simpa [TaggedLongAttemptStageGood,
        tagged_long_attempt_start, hret, hready] using
        (show TaggedLongNear ring i j k a b seed.N ∧
          ¬ SealedCleanReady ring seed.N j b from
          ⟨hnear, hready⟩)
  · simp [TaggedLongAttemptStageGood,
      tagged_long_attempt_start, hret]

/-- The mode invariant closes over each actual active native step.
It uses the off-port incident closure at the only place where
the A-live near witness might otherwise have been discarded. -/
theorem tagged_long_attempt_stage_good_active {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (z z' : TaggedLongAttemptState ring i j k a b)
    (e : Fin n)
    (hgood : TaggedLongAttemptStageGood ring i j k a b z)
    (hactive : tagged_long_attempt_step
      hn ring i j k a b z e = .active z') :
    TaggedLongAttemptStageGood ring i j k a b z' := by
  classical
  obtain ⟨hphysical, hmode, hnotretry⟩ :=
    tagged_long_attempt_active_child_mode
      hn ring i j k a b z z' e hactive
  cases hm : z.mode with
  | preparation =>
      by_cases hret : TaggedLongRetained ring i j k a b
          (nativeE ring z.N e)
      · have hnear := tagged_long_retained_to_near
          ring i j k a b (nativeE ring z.N e) hret
        by_cases hready :
            SealedCleanReady ring (nativeE ring z.N e) j b
        · simpa [TaggedLongAttemptStageGood, hmode,
            tagged_long_attempt_follow_mode, hm, hret,
            hready, hphysical] using
            (show TaggedLongNear ring i j k a b
                (nativeE ring z.N e) ∧
              SealedCleanReady ring (nativeE ring z.N e) j b
              from ⟨hnear, hready⟩)
        · simpa [TaggedLongAttemptStageGood, hmode,
            tagged_long_attempt_follow_mode, hm, hret,
            hready, hphysical] using
            (show TaggedLongNear ring i j k a b
                (nativeE ring z.N e) ∧
              ¬ SealedCleanReady ring (nativeE ring z.N e) j b
              from ⟨hnear, hready⟩)
      · simpa [TaggedLongAttemptStageGood, hmode,
          tagged_long_attempt_follow_mode, hm, hret,
          hphysical] using hret
  | targetRace =>
      have hnear : TaggedLongNear ring i j k a b
          (nativeE ring z.N e) := by
        by_cases hnear : TaggedLongNear ring i j k a b
            (nativeE ring z.N e)
        · exact hnear
        · have hretry : tagged_long_attempt_retry_edge
              ring i j k a b z e (nativeE ring z.N e) := by
            simp [tagged_long_attempt_retry_edge, hm, hnear]
          exact False.elim (hnotretry hretry)
      by_cases hready :
          SealedCleanReady ring (nativeE ring z.N e) j b
      · simpa [TaggedLongAttemptStageGood, hmode,
          tagged_long_attempt_follow_mode, hm, hready,
          hphysical] using
          (show TaggedLongNear ring i j k a b
              (nativeE ring z.N e) ∧
            SealedCleanReady ring (nativeE ring z.N e) j b
            from ⟨hnear, hready⟩)
      · simpa [TaggedLongAttemptStageGood, hmode,
          tagged_long_attempt_follow_mode, hm, hready,
          hphysical] using
          (show TaggedLongNear ring i j k a b
              (nativeE ring z.N e) ∧
            ¬ SealedCleanReady ring (nativeE ring z.N e) j b
            from ⟨hnear, hready⟩)
  | incident =>
      have hcut : TaggedLongNear ring i j k a b z.N ∧
          SealedCleanReady ring z.N j b := by
        simpa [TaggedLongAttemptStageGood, hm] using hgood
      by_cases hin : e = ring.leftNeighbor j
      · simpa [TaggedLongAttemptStageGood, hmode,
          tagged_long_attempt_follow_mode, hm, hin]
      · have hout : e ≠ j := by
          intro he
          have hr : tagged_long_attempt_retry_edge
              ring i j k a b z e (nativeE ring z.N e) := by
            simp [tagged_long_attempt_retry_edge, hm, he]
          exact hnotretry hr
        have hnotdel :
            ¬ TaggedDeleted i j k (nativeE ring z.N e) := by
          rw [← hphysical]
          exact tagged_d15_triple_not_deleted
            ring i j k a b z'.N z'.triple
        have hclosed := tagged_long_incident_off_port_closure
          hn ring i j k a b z.N hcut.1 hcut.2
            e hin hout hnotdel
        simpa [TaggedLongAttemptStageGood, hmode,
          tagged_long_attempt_follow_mode, hm, hin,
          hphysical] using hclosed
  | vulnerable =>
      simp [TaggedLongAttemptStageGood, hmode,
        tagged_long_attempt_follow_mode, hm]
  | recovery =>
      have hf : False := by
        simpa [TaggedLongAttemptStageGood, hm] using hgood
      exact False.elim hf

/-- Inductively reached active states keep the exact stage-domain
invariant, not merely the native tagged-triple flags. -/
inductive TaggedLongAttemptActiveReach {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (seed : TaggedLongAttemptSeed ring i j k a b) :
    TaggedLongAttemptState ring i j k a b → Prop where
  | start :
      TaggedLongAttemptActiveReach hn ring i j k a b seed
        (tagged_long_attempt_start ring i j k a b seed)
  | step {z z' : TaggedLongAttemptState ring i j k a b}
      (hreach : TaggedLongAttemptActiveReach
        hn ring i j k a b seed z)
      (e : Fin n)
      (hactive : tagged_long_attempt_step
        hn ring i j k a b z e = .active z') :
      TaggedLongAttemptActiveReach hn ring i j k a b seed z'

theorem tagged_long_attempt_reachable_stage_good {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (seed : TaggedLongAttemptSeed ring i j k a b)
    {z : TaggedLongAttemptState ring i j k a b}
    (hreach : TaggedLongAttemptActiveReach
      hn ring i j k a b seed z) :
    TaggedLongAttemptStageGood ring i j k a b z := by
  induction hreach with
  | start =>
      exact tagged_long_attempt_stage_good_start
        ring i j k a b seed
  | step hreach e hactive ih =>
      exact tagged_long_attempt_stage_good_active
        hn ring i j k a b _ _ e ih hactive

/-- An incoming incident active child is genuinely near-live,
contains B's clean Dummy(0), and enters vulnerable mode. -/
theorem tagged_long_attempt_incident_handoff {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (z z' : TaggedLongAttemptState ring i j k a b)
    (e : Fin n)
    (hgood : TaggedLongAttemptStageGood ring i j k a b z)
    (hm : z.mode = .incident)
    (hin : e = ring.leftNeighbor j)
    (hactive : tagged_long_attempt_step
      hn ring i j k a b z e = .active z') :
    TaggedLongNear ring i j k a b z'.N ∧
      TaggedCleanDummy ring i j a b z'.N ∧
      z'.mode = .vulnerable := by
  obtain ⟨hphysical, hmode, _⟩ :=
    tagged_long_attempt_active_child_mode
      hn ring i j k a b z z' e hactive
  have hcut :
      TaggedLongNear ring i j k a b z.N ∧
        SealedCleanReady ring z.N j b := by
    simpa [TaggedLongAttemptStageGood, hm] using hgood
  subst e
  have hnodelete :
      ¬ TaggedDeleted i j k
        (nativeE ring z.N (ring.leftNeighbor j)) := by
    rw [← hphysical]
    exact tagged_d15_triple_not_deleted
      ring i j k a b z'.N z'.triple
  have hcert :=
    tagged_long_incident_success_certified
      hn ring i j k a b z.N hcut.1 hcut.2
  rcases hcert with hdel | ⟨hnear, hclean⟩
  · exact False.elim (hnodelete hdel)
  · have hmodeV : z'.mode = .vulnerable := by
      rw [hmode]
      simp [tagged_long_attempt_follow_mode, hm]
    exact ⟨by simpa only [hphysical] using hnear,
      by simpa only [hphysical] using hclean, hmodeV⟩

/-- Actual first retained preparation cut: Ready B bypasses the
race; otherwise the next mode is the real target race. -/
theorem tagged_long_attempt_preparation_handoff {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (z z' : TaggedLongAttemptState ring i j k a b)
    (e : Fin n)
    (hm : z.mode = .preparation)
    (hactive : tagged_long_attempt_step
      hn ring i j k a b z e = .active z')
    (hret : TaggedLongRetained ring i j k a b z'.N) :
    z'.mode = .targetRace ∨ z'.mode = .incident := by
  obtain ⟨hphysical, hmode, _⟩ :=
    tagged_long_attempt_active_child_mode
      hn ring i j k a b z z' e hactive
  have hretNative : TaggedLongRetained ring i j k a b
      (nativeE ring z.N e) := by
    simpa only [hphysical] using hret
  by_cases hready :
      SealedCleanReady ring (nativeE ring z.N e) j b
  · right
    rw [hmode]
    simp [tagged_long_attempt_follow_mode, hm,
      hretNative, hready]
  · left
    rw [hmode]
    simp [tagged_long_attempt_follow_mode, hm,
      hretNative, hready]

/-- At an active target-race B-Ready winning cut, the next native
state satisfies the actual incident-stage entrance predicates. -/
theorem tagged_long_attempt_race_handoff {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (z z' : TaggedLongAttemptState ring i j k a b)
    (e : Fin n)
    (hgood : TaggedLongAttemptStageGood ring i j k a b z)
    (hm : z.mode = .targetRace)
    (hactive : tagged_long_attempt_step
      hn ring i j k a b z e = .active z')
    (hready : SealedCleanReady ring z'.N j b) :
    TaggedLongNear ring i j k a b z'.N ∧
      SealedCleanReady ring z'.N j b ∧
      z'.mode = .incident := by
  have hgood' :=
    tagged_long_attempt_stage_good_active
      hn ring i j k a b z z' e hgood hactive
  obtain ⟨hphysical, hmode, _⟩ :=
    tagged_long_attempt_active_child_mode
      hn ring i j k a b z z' e hactive
  have hreadyNative :
      SealedCleanReady ring (nativeE ring z.N e) j b := by
    simpa only [hphysical] using hready
  have hincident : z'.mode = .incident := by
    rw [hmode]
    simp [tagged_long_attempt_follow_mode, hm, hreadyNative]
  have hcut :
      TaggedLongNear ring i j k a b z'.N ∧
        SealedCleanReady ring z'.N j b := by
    simpa [TaggedLongAttemptStageGood, hincident] using hgood'
  exact ⟨hcut.1, hcut.2, hincident⟩

end L3


/-! ## Exact first-entrance cut accounting

The generic theorems work with one
actual first stage, preserving its entry configuration and scheduler
letters. They do not assume a restart, independence, or a uniform
failure bound at arbitrarily late active cuts. The application below
covers the vulnerable stage; later handoffs remain unfinished.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false
attribute [local instance low] Classical.propDecidable

/-- The precise native-state cut relation for a first stopped stage.
The first-stage outcome has exactly three interpretations:
active is the same physical child within the current stage;
failure is an actual retry leaf; success is either true deletion
or entry into a post-stage continuation. -/
def TaggedFirstCutMatches {A Seed S : Type} {n : Nat}
    (K : RetryKernel A Seed n)
    (stage : S → Fin n → StopNode S)
    (physical : A → S) (R Post : A → Prop) : Prop :=
  ∀ z, R z → ∀ e,
    match stage (physical z) e with
    | .active y =>
        ∃ z', K.step z e = .active z' ∧
          R z' ∧ physical z' = y
    | .failure =>
        ∃ seed, K.step z e = .retry seed
    | .success =>
        K.step z e = .success ∨
          ∃ z', K.step z e = .active z' ∧ Post z'

/-- A completed first stage on the success node has success mass
exactly n^T, including all unused scheduler letters. -/
theorem tagged_first_cut_success_pow
    {S : Type} {n : Nat}
    (stage : S → Fin n → StopNode S) :
    ∀ T, successCount stage (.success) T = n ^ T := by
  intro T
  induction T with
  | zero => rfl
  | succ T ih =>
      change (List.ofFn (fun _ : Fin n =>
        successCount stage (.success) T)).sum = n ^ (T + 1)
      rw [ofFn_sum_eq _ (fun _ : Fin n => n ^ T)
        (fun _ => ih), ofFn_sum_const, Nat.pow_succ]
      ac_rfl

theorem tagged_first_cut_failure_success_zero
    {S : Type} {n : Nat}
    (stage : S → Fin n → StopNode S) :
    ∀ T, successCount stage (.failure) T = 0 := by
  intro T
  induction T with
  | zero => rfl
  | succ T ih =>
      change (List.ofFn (fun _ : Fin n =>
        successCount stage (.failure) T)).sum = 0
      rw [ofFn_sum_eq _ (fun _ : Fin n => 0)
        (fun _ => ih), ofFn_sum_const]
      rfl

/-- Strong-Markov cost reserve on exactly the first stage-entrance
cut. The continuation cost is imposed only on first-stage success
leaves which are not actual terminal deletion. -/
theorem tagged_first_cut_cost_reserve
    {A Seed S : Type} {n : Nat}
    (K : RetryKernel A Seed n)
    (stage : S → Fin n → StopNode S)
    (physical : A → S) (R Post : A → Prop) (B : Nat)
    (hmatch : TaggedFirstCutMatches K stage physical R Post)
    (hpost : ∀ z, Post z → ∀ T,
      attemptCostNumerator K (.active z) T ≤ n ^ T * B) :
    ∀ z, R z → ∀ T,
      attemptCostNumerator K (.active z) T ≤
        truncatedActiveCostNumerator stage (.active (physical z)) T +
          n ^ T * B := by
  intro z hz T
  induction T generalizing z with
  | zero =>
      simp [attemptCostNumerator, truncatedActiveCostNumerator]
  | succ T ih =>
      have hchild : ∀ e : Fin n,
          attemptCostNumerator K (K.step z e) T ≤
            truncatedActiveCostNumerator stage
              (stage (physical z) e) T + n ^ T * B := by
        intro e
        have hm := hmatch z hz e
        cases he : stage (physical z) e with
        | active y =>
            obtain ⟨z', hstep, hr, hp⟩ := by
              simpa only [he] using hm
            rw [hstep]
            have hh := ih z' hr
            rw [hp] at hh
            exact hh
        | failure =>
            obtain ⟨seed, hs⟩ : ∃ seed, K.step z e = .retry seed := by
              simpa only [he] using hm
            rw [hs]
            cases T <;>
              simp [attemptCostNumerator,
                truncatedActiveCostNumerator, he]
        | success =>
            have hcase :
                K.step z e = .success ∨
                ∃ z', K.step z e = .active z' ∧ Post z' := by
              simpa only [he] using hm
            rcases hcase with hs | ⟨z', hs, hp⟩
            · rw [hs]
              cases T <;>
                simp [attemptCostNumerator,
                  truncatedActiveCostNumerator, he]
            · rw [hs]
              have hb := hpost z' hp T
              exact Nat.le_trans hb (Nat.le_add_left _ _)
      have hsum :=
        ofFn_sum_le
          (fun e : Fin n => attemptCostNumerator K (K.step z e) T)
          (fun e : Fin n =>
            truncatedActiveCostNumerator stage
              (stage (physical z) e) T + n ^ T * B)
          hchild
      rw [ofFn_sum_add, ofFn_sum_const] at hsum
      change n ^ (T + 1) +
          (List.ofFn (fun e : Fin n =>
            attemptCostNumerator K (K.step z e) T)).sum ≤
        (n ^ (T + 1) +
          (List.ofFn (fun e : Fin n =>
            truncatedActiveCostNumerator stage
              (stage (physical z) e) T)).sum) +
          n ^ (T + 1) * B
      have hpow : n * (n ^ T * B) = n ^ (T + 1) * B := by
        rw [Nat.pow_succ]
        ac_rfl
      rw [hpow] at hsum
      omega

/-- An exact first-cut retry-cylinder reserve. Stage failure is
charged as retry; stage success contributes only its certified
post-stage conditional failure numerator. Active words are NOT
charged as failures. -/
theorem tagged_first_cut_retry_reserve
    {A Seed S : Type} {n : Nat}
    (K : RetryKernel A Seed n)
    (stage : S → Fin n → StopNode S)
    (physical : A → S) (R Post : A → Prop)
    (den num : Nat)
    (hmatch : TaggedFirstCutMatches K stage physical R Post)
    (hpost : ∀ z, Post z → ∀ T,
      den * retryCount K (.active z) T ≤ num * n ^ T) :
    ∀ z, R z → ∀ T,
      den * retryCount K (.active z) T ≤
        den * failureCount stage (.active (physical z)) T +
          num * successCount stage (.active (physical z)) T := by
  intro z hz T
  induction T generalizing z with
  | zero =>
      simp [retryCount, failureCount, successCount, treeWeight,
        failureWeight, successWeight]
  | succ T ih =>
      have hchild : ∀ e : Fin n,
          den * retryCount K (K.step z e) T ≤
            den * failureCount stage (stage (physical z) e) T +
              num * successCount stage (stage (physical z) e) T := by
        intro e
        have hm := hmatch z hz e
        cases he : stage (physical z) e with
        | active y =>
            obtain ⟨z', hs, hr, hp⟩ := by
              simpa only [he] using hm
            rw [hs]
            have hh := ih z' hr
            rw [hp] at hh
            exact hh
        | failure =>
            obtain ⟨seed, hs⟩ : ∃ seed, K.step z e = .retry seed := by
              simpa only [he] using hm
            rw [hs]
            simpa [retryCount, he,
              tagged_failure_count_failure_eq_pow,
              tagged_first_cut_failure_success_zero]
        | success =>
            have hcase :
                K.step z e = .success ∨
                  ∃ z', K.step z e = .active z' ∧ Post z' := by
              simpa only [he] using hm
            rcases hcase with hs | ⟨z', hs, hp⟩
            · rw [hs]
              simp [retryCount, he,
                tagged_failure_count_success_zero,
                tagged_first_cut_success_pow]
            · rw [hs]
              have hh := hpost z' hp T
              simpa [he, tagged_failure_count_success_zero,
                tagged_first_cut_success_pow] using hh
      change den *
          (List.ofFn (fun e : Fin n =>
            retryCount K (K.step z e) T)).sum ≤
        den * (List.ofFn (fun e : Fin n =>
          failureCount stage (stage (physical z) e) T)).sum +
        num * (List.ofFn (fun e : Fin n =>
          successCount stage (stage (physical z) e) T)).sum
      calc
        _ = (List.ofFn (fun e : Fin n =>
              den * retryCount K (K.step z e) T)).sum :=
          (ofFn_sum_mul_left den _).symm
        _ ≤ (List.ofFn (fun e : Fin n =>
              den * failureCount stage
                (stage (physical z) e) T +
              num * successCount stage
                (stage (physical z) e) T)).sum :=
          ofFn_sum_le _ _ hchild
        _ = (List.ofFn (fun e : Fin n =>
              den * failureCount stage (stage (physical z) e) T)).sum +
            (List.ofFn (fun e : Fin n =>
              num * successCount stage (stage (physical z) e) T)).sum :=
          ofFn_sum_add _ _
        _ = den * (List.ofFn (fun e : Fin n =>
              failureCount stage (stage (physical z) e) T)).sum +
            num * (List.ofFn (fun e : Fin n =>
              successCount stage (stage (physical z) e) T)).sum := by
          rw [ofFn_sum_mul_left, ofFn_sum_mul_left]

/-- A uniform conditional post-stage estimate and first-stage
cost estimate imply the sum of the budgets, even when the clock
is started at a nonzero history-dependent stopping time. -/
theorem tagged_first_cut_cost_add
    {A Seed S : Type} {n : Nat}
    (K : RetryKernel A Seed n)
    (stage : S → Fin n → StopNode S)
    (physical : A → S) (R Post : A → Prop)
    (Bfirst Bpost : Nat)
    (hmatch : TaggedFirstCutMatches K stage physical R Post)
    (hfirst : ∀ z, R z → ∀ T,
      truncatedActiveCostNumerator stage (.active (physical z)) T ≤
        n ^ T * Bfirst)
    (hpost : ∀ z, Post z → ∀ T,
      attemptCostNumerator K (.active z) T ≤ n ^ T * Bpost) :
    ∀ z, R z → ∀ T,
      attemptCostNumerator K (.active z) T ≤
        n ^ T * (Bfirst + Bpost) := by
  intro z hz T
  calc
    _ ≤ truncatedActiveCostNumerator stage
        (.active (physical z)) T + n ^ T * Bpost :=
      tagged_first_cut_cost_reserve
        K stage physical R Post Bpost hmatch hpost z hz T
    _ ≤ n ^ T * Bfirst + n ^ T * Bpost :=
      Nat.add_le_add_right (hfirst z hz T) _
    _ = n ^ T * (Bfirst + Bpost) := by
      rw [Nat.mul_add]

/-- The exact finite-word failure-product bound for a sequential
first cut, with the current stage's failure hypothesis imposed ONLY
at its original entrance state, not at its later active descendants. -/
theorem tagged_first_cut_failure_product
    {A Seed S : Type} {n : Nat}
    (K : RetryKernel A Seed n)
    (stage : S → Fin n → StopNode S)
    (physical : A → S) (R Post : A → Prop)
    (denFirst numFirst denPost numPost : Nat)
    (hnum : numPost ≤ denPost)
    (hmatch : TaggedFirstCutMatches K stage physical R Post)
    (hfirst : ∀ z, R z → ∀ T,
      denFirst * failureCount stage (.active (physical z)) T ≤
        numFirst * n ^ T)
    (hpost : ∀ z, Post z → ∀ T,
      denPost * retryCount K (.active z) T ≤ numPost * n ^ T) :
    ∀ z, R z → ∀ T,
      (denFirst * denPost) * retryCount K (.active z) T ≤
        (denFirst * numPost +
          numFirst * (denPost - numPost)) * n ^ T := by
  intro z hz T
  have hc := tagged_first_cut_retry_reserve
    K stage physical R Post denPost numPost
    hmatch hpost z hz T
  have hf := hfirst z hz T
  have hpart := node_count_partition stage (.active (physical z)) T
  have hsum :
      failureCount stage (.active (physical z)) T +
        successCount stage (.active (physical z)) T ≤ n ^ T := by
    omega
  have hden : denPost = (denPost - numPost) + numPost := by
    omega
  calc
    (denFirst * denPost) * retryCount K (.active z) T =
        denFirst * (denPost * retryCount K (.active z) T) := by
      ac_rfl
    _ ≤ denFirst * (denPost *
          failureCount stage (.active (physical z)) T +
          numPost * successCount stage (.active (physical z)) T) :=
      Nat.mul_le_mul_left denFirst hc
    _ = denFirst * (denPost - numPost) *
          failureCount stage (.active (physical z)) T +
        (denFirst * numPost) *
          (failureCount stage (.active (physical z)) T +
            successCount stage (.active (physical z)) T) := by
      generalize failureCount stage (.active (physical z)) T = F
      generalize successCount stage (.active (physical z)) T = G
      generalize hdd : denPost - numPost = d at hden ⊢
      rw [hden]
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]
    _ ≤ denFirst * (denPost - numPost) *
          failureCount stage (.active (physical z)) T +
        (denFirst * numPost) * n ^ T :=
      Nat.add_le_add_left
        (Nat.mul_le_mul_left (denFirst * numPost) hsum) _
    _ = (denPost - numPost) *
          (denFirst * failureCount stage
            (.active (physical z)) T) +
        (denFirst * numPost) * n ^ T := by ac_rfl
    _ ≤ (denPost - numPost) * (numFirst * n ^ T) +
          (denFirst * numPost) * n ^ T :=
      Nat.add_le_add_right
        (Nat.mul_le_mul_left (denPost - numPost) hf) _
    _ = (denFirst * numPost +
          numFirst * (denPost - numPost)) * n ^ T := by
      rw [Nat.add_mul]
      ac_rfl

/-- Physical matching of the final vulnerable stage. On the raw
Ready-outgoing edge the same physical service is a kernel retry,
not a controlled Q continuation; all raw active edges preserve the
literal native child and the vulnerable history mode. -/
theorem tagged_long_vulnerable_first_cut_matches {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat) :
    TaggedFirstCutMatches
      (tagged_long_native_retry_kernel hn ring i j k a b)
      (taggedTrialStep ring i j k b)
      (fun z => z.N)
      (fun z => z.mode = .vulnerable)
      (fun _ => False) := by
  intro z hz e
  by_cases hd : TaggedDeleted i j k (nativeE ring z.N e)
  · have hs : taggedTrialStep ring i j k b z.N e = .success := by
      simp [taggedTrialStep, hd]
    rw [hs]
    exact Or.inl (tagged_long_attempt_step_on_delete
      hn ring i j k a b z e hd)
  · by_cases hf : SealedCleanReady ring z.N j b ∧ e = j
    · have hs : taggedTrialStep ring i j k b z.N e = .failure := by
        have hd' := hd
        rw [hf.2] at hd'
        rw [hf.2]
        simp [taggedTrialStep, hd', hf.1]
      rw [hs]
      have hr : tagged_long_attempt_retry_edge
          ring i j k a b z e (nativeE ring z.N e) := by
        simpa [tagged_long_attempt_retry_edge, hz] using hf
      obtain ⟨seed, hretry, _⟩ :=
        tagged_long_attempt_step_on_retry
          hn ring i j k a b z e hd hr
      exact ⟨seed, hretry⟩
    · have hs : taggedTrialStep ring i j k b z.N e =
          .active (nativeE ring z.N e) := by
        simp [taggedTrialStep, hd, hf]
      rw [hs]
      have hr : ¬ tagged_long_attempt_retry_edge
          ring i j k a b z e (nativeE ring z.N e) := by
        simpa [tagged_long_attempt_retry_edge, hz] using hf
      obtain ⟨z', hstep, hnative, hmode⟩ :=
        tagged_long_attempt_step_on_active
          hn ring i j k a b z e hd hr
      have hmodeV : z'.mode = .vulnerable := by
        rw [hmode]
        simp [tagged_long_attempt_follow_mode, hz]
      exact ⟨z', hstep, hmodeV, hnative⟩

/-- The actual kernel agrees with the raw last-stage cost and
first-retry cylinder counts at every vulnerable-mode entrance.
Only the direction needed for D.19 is asserted. -/
theorem tagged_long_vulnerable_kernel_dominated {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (z : TaggedLongAttemptState ring i j k a b)
    (hmode : z.mode = .vulnerable) :
    ∀ T,
      attemptCostNumerator
        (tagged_long_native_retry_kernel hn ring i j k a b)
        (.active z) T ≤
          truncatedActiveCostNumerator
            (taggedTrialStep ring i j k b) (.active z.N) T ∧
      retryCount
        (tagged_long_native_retry_kernel hn ring i j k a b)
        (.active z) T ≤
          failureCount
            (taggedTrialStep ring i j k b) (.active z.N) T := by
  intro T
  have hm := tagged_long_vulnerable_first_cut_matches
    hn ring i j k a b
  have hc := tagged_first_cut_cost_reserve
    (tagged_long_native_retry_kernel hn ring i j k a b)
    (taggedTrialStep ring i j k b)
    (fun q => q.N)
    (fun q => q.mode = .vulnerable)
    (fun _ => False) 0 hm
    (by intro q hfalse; cases hfalse)
    z hmode T
  have hr := tagged_first_cut_retry_reserve
    (tagged_long_native_retry_kernel hn ring i j k a b)
    (taggedTrialStep ring i j k b)
    (fun q => q.N)
    (fun q => q.mode = .vulnerable)
    (fun _ => False) 1 0 hm
    (by intro q hfalse; cases hfalse)
    z hmode T
  constructor
  · simpa using hc
  · simpa using hr

/-- Clock four at its actual FIRST native entrance, not a synthetic
Q seed: cost at most 2nb and retry mass at most 3/4. -/
theorem tagged_long_vulnerable_kernel_first_entrance {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hb : 2 ≤ b)
    (z : TaggedLongAttemptState ring i j k a b)
    (hmode : z.mode = .vulnerable)
    (hnear : TaggedLongNear ring i j k a b z.N)
    (hclean : TaggedCleanDummy ring i j a b z.N) :
    ∀ T,
      attemptCostNumerator
        (tagged_long_native_retry_kernel hn ring i j k a b)
        (.active z) T ≤ n ^ T * (n * (2 * b)) ∧
      4 * retryCount
        (tagged_long_native_retry_kernel hn ring i j k a b)
        (.active z) T ≤ 3 * n ^ T := by
  intro T
  have hdom := tagged_long_vulnerable_kernel_dominated
    hn ring i j k a b z hmode T
  have hrawcost := tagged_long_vulnerable_raw_cost
    hn ring i j k a b z.N hnear hclean T
  have hrawfail := tagged_long_vulnerable_failure_quarter
    hn ring i j k a b hb z.N hnear hclean T
  exact ⟨Nat.le_trans hdom.1 hrawcost,
    Nat.le_trans (Nat.mul_le_mul_left 4 hdom.2) hrawfail⟩

end L3


/-! ## Same-native first incident and race cuts

The race's half-mass
bound is used only at its retained first entrance, never claimed
at arbitrary later active descendants.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false
attribute [local instance low] Classical.propDecidable

def TaggedLongIncidentEntrance {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (z : TaggedLongAttemptState ring i j k a b) : Prop :=
  z.mode = .incident ∧
    TaggedLongNear ring i j k a b z.N ∧
    SealedCleanReady ring z.N j b

def TaggedLongVulnerableEntrance {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (z : TaggedLongAttemptState ring i j k a b) : Prop :=
  z.mode = .vulnerable ∧
    TaggedLongNear ring i j k a b z.N ∧
    TaggedCleanDummy ring i j a b z.N

/-- Every incident stage successor is classified on exactly the
same nativeE edge. The successful incoming edge is allowed only
because the certified handoff supplies the real clean Dummy(0). -/
theorem tagged_long_incident_first_cut_matches {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat) :
    TaggedFirstCutMatches
      (tagged_long_native_retry_kernel hn ring i j k a b)
      (tagged_long_incident_step ring i j k)
      (fun z => z.N)
      (TaggedLongIncidentEntrance ring i j k a b)
      (TaggedLongVulnerableEntrance ring i j k a b) := by
  intro z hz e
  obtain ⟨hm, hnear, hready⟩ := hz
  have hgood : TaggedLongAttemptStageGood ring i j k a b z := by
    simpa [TaggedLongAttemptStageGood, hm] using
      (show TaggedLongNear ring i j k a b z.N ∧
        SealedCleanReady ring z.N j b from ⟨hnear, hready⟩)
  have hports : ring.leftNeighbor j ≠ j :=
    Ne.symm (tagged_q_incident_edges_distinct
      (by omega : 2 ≤ n) ring j)
  by_cases hd : TaggedDeleted i j k (nativeE ring z.N e)
  · have hs : tagged_long_incident_step ring i j k z.N e =
        .success := by
      simp [tagged_long_incident_step, hd]
    rw [hs]
    exact Or.inl
      (tagged_long_attempt_step_on_delete
        hn ring i j k a b z e hd)
  · by_cases hin : e = ring.leftNeighbor j
    · have hs : tagged_long_incident_step ring i j k z.N e =
          .success := by
        simp [tagged_long_incident_step, hd, hin]
      rw [hs]
      have hout : e ≠ j := by
        intro he
        exact hports (hin.symm.trans he)
      have hnotretry : ¬ tagged_long_attempt_retry_edge
          ring i j k a b z e (nativeE ring z.N e) := by
        simp [tagged_long_attempt_retry_edge, hm, hout]
      obtain ⟨z', hstep, _, _⟩ :=
        tagged_long_attempt_step_on_active
          hn ring i j k a b z e hd hnotretry
      have hhandoff := tagged_long_attempt_incident_handoff
        hn ring i j k a b z z' e hgood hm hin hstep
      exact Or.inr ⟨z', hstep,
        ⟨hhandoff.2.2, hhandoff.1, hhandoff.2.1⟩⟩
    · by_cases hout : e = j
      · have hs : tagged_long_incident_step ring i j k z.N e =
            .failure := by
          have hd' := hd
          rw [hout] at hd'
          simp [tagged_long_incident_step, hd', hin, hout, Ne.symm hports]
        rw [hs]
        have hretry : tagged_long_attempt_retry_edge
            ring i j k a b z e (nativeE ring z.N e) := by
          simp [tagged_long_attempt_retry_edge, hm, hout]
        obtain ⟨seed, hstep, _⟩ :=
          tagged_long_attempt_step_on_retry
            hn ring i j k a b z e hd hretry
        exact ⟨seed, hstep⟩
      · have hs : tagged_long_incident_step ring i j k z.N e =
            .active (nativeE ring z.N e) := by
          simp [tagged_long_incident_step, hd, hin, hout]
        rw [hs]
        have hnotretry : ¬ tagged_long_attempt_retry_edge
            ring i j k a b z e (nativeE ring z.N e) := by
          simp [tagged_long_attempt_retry_edge, hm, hout]
        obtain ⟨z', hstep, hphysical, hmode⟩ :=
          tagged_long_attempt_step_on_active
            hn ring i j k a b z e hd hnotretry
        have hclosed := tagged_long_incident_off_port_closure
          hn ring i j k a b z.N hnear hready e hin hout hd
        have hmodeIncident : z'.mode = .incident := by
          rw [hmode]
          simp [tagged_long_attempt_follow_mode, hm, hin]
        have hnearChild : TaggedLongNear ring i j k a b z'.N := by
          rw [hphysical]
          exact hclosed.1
        have hreadyChild : SealedCleanReady ring z'.N j b := by
          rw [hphysical]
          exact hclosed.2
        exact ⟨z', hstep,
          ⟨hmodeIncident, hnearChild, hreadyChild⟩, hphysical⟩

/-- Clock 3 plus the previously established Clock 4 on the
first literal incident entrance: cost n+2nb, retry mass 7/8.
No near/Ready premise is required at later stage-3 active cuts
beyond the closure proved by the match theorem. -/
theorem tagged_long_incident_kernel_first_entrance {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hb : 2 ≤ b)
    (z : TaggedLongAttemptState ring i j k a b)
    (hz : TaggedLongIncidentEntrance ring i j k a b z) :
    ∀ T,
      attemptCostNumerator
        (tagged_long_native_retry_kernel hn ring i j k a b)
        (.active z) T ≤ n ^ T * (n + n * (2 * b)) ∧
      8 * retryCount
        (tagged_long_native_retry_kernel hn ring i j k a b)
        (.active z) T ≤ 7 * n ^ T := by
  intro T
  have hm := tagged_long_incident_first_cut_matches
    hn ring i j k a b
  constructor
  · exact tagged_first_cut_cost_add
      (tagged_long_native_retry_kernel hn ring i j k a b)
      (tagged_long_incident_step ring i j k)
      (fun q => q.N)
      (TaggedLongIncidentEntrance ring i j k a b)
      (TaggedLongVulnerableEntrance ring i j k a b)
      n (n * (2 * b)) hm
      (by
        intro q hq U
        exact (tagged_long_incident_clock
          ring i j k a b q.N hq.2.1 hq.2.2 U).1)
      (by
        intro q hq U
        exact (tagged_long_vulnerable_kernel_first_entrance
          hn ring i j k a b hb q hq.1 hq.2.1 hq.2.2 U).1)
      z hz T
  · have hbound := tagged_first_cut_failure_product
      (tagged_long_native_retry_kernel hn ring i j k a b)
      (tagged_long_incident_step ring i j k)
      (fun q => q.N)
      (TaggedLongIncidentEntrance ring i j k a b)
      (TaggedLongVulnerableEntrance ring i j k a b)
      2 1 4 3 (by omega) hm
      (by
        intro q hq U
        rw [Nat.one_mul]
        exact (tagged_long_incident_clock
          ring i j k a b q.N hq.2.1 hq.2.2 U).2)
      (by
        intro q hq U
        exact (tagged_long_vulnerable_kernel_first_entrance
          hn ring i j k a b hb q hq.1 hq.2.1 hq.2.2 U).2)
      z hz T
    simpa using hbound

/-- An entrance-specific version of the exact failure product.
Unlike a uniform-R theorem, only the ORIGINAL first entrance has
the stage failure certificate; R need only close under its active
descendants. This distinction is essential for the two-front race. -/
theorem tagged_first_cut_failure_product_at
    {A Seed S : Type} {n : Nat}
    (K : RetryKernel A Seed n)
    (stage : S → Fin n → StopNode S)
    (physical : A → S) (R Post : A → Prop)
    (denFirst numFirst denPost numPost : Nat)
    (hnum : numPost ≤ denPost)
    (hmatch : TaggedFirstCutMatches K stage physical R Post)
    (hpost : ∀ z, Post z → ∀ T,
      denPost * retryCount K (.active z) T ≤ numPost * n ^ T)
    (z : A) (hz : R z)
    (hfirst : ∀ T,
      denFirst * failureCount stage (.active (physical z)) T ≤
        numFirst * n ^ T) :
    ∀ T,
      (denFirst * denPost) * retryCount K (.active z) T ≤
        (denFirst * numPost +
          numFirst * (denPost - numPost)) * n ^ T := by
  intro T
  have hc := tagged_first_cut_retry_reserve
    K stage physical R Post denPost numPost
    hmatch hpost z hz T
  have hf := hfirst T
  have hpart := node_count_partition stage (.active (physical z)) T
  have hsum :
      failureCount stage (.active (physical z)) T +
        successCount stage (.active (physical z)) T ≤ n ^ T := by
    omega
  have hden : denPost = (denPost - numPost) + numPost := by
    omega
  calc
    (denFirst * denPost) * retryCount K (.active z) T =
        denFirst * (denPost * retryCount K (.active z) T) := by
      ac_rfl
    _ ≤ denFirst * (denPost *
          failureCount stage (.active (physical z)) T +
          numPost * successCount stage (.active (physical z)) T) :=
      Nat.mul_le_mul_left denFirst hc
    _ = denFirst * (denPost - numPost) *
          failureCount stage (.active (physical z)) T +
        (denFirst * numPost) *
          (failureCount stage (.active (physical z)) T +
            successCount stage (.active (physical z)) T) := by
      generalize failureCount stage (.active (physical z)) T = F
      generalize successCount stage (.active (physical z)) T = G
      generalize hdd : denPost - numPost = d at hden ⊢
      rw [hden]
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]
    _ ≤ denFirst * (denPost - numPost) *
          failureCount stage (.active (physical z)) T +
        (denFirst * numPost) * n ^ T :=
      Nat.add_le_add_left
        (Nat.mul_le_mul_left (denFirst * numPost) hsum) _
    _ = (denPost - numPost) *
          (denFirst * failureCount stage
            (.active (physical z)) T) +
        (denFirst * numPost) * n ^ T := by ac_rfl
    _ ≤ (denPost - numPost) * (numFirst * n ^ T) +
          (denFirst * numPost) * n ^ T :=
      Nat.add_le_add_right
        (Nat.mul_le_mul_left (denPost - numPost) hf) _
    _ = (denFirst * numPost +
          numFirst * (denPost - numPost)) * n ^ T := by
      rw [Nat.add_mul]
      ac_rfl

def TaggedLongRaceEntrance {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (z : TaggedLongAttemptState ring i j k a b) : Prop :=
  z.mode = .targetRace ∧
    TaggedLongRaceActive ring i j k a b z.N

def TaggedLongRaceRetainedEntrance {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (z : TaggedLongAttemptState ring i j k a b) : Prop :=
  TaggedLongRaceEntrance ring i j k a b z ∧
    TaggedLongRetained ring i j k a b z.N

/-- The race match is maintained over the broad near/nonReady active
domain. The stronger retained condition is NOT imposed here, since
an A-live advance can destroy exact retention without ending race. -/
theorem tagged_long_race_first_cut_matches {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat) :
    TaggedFirstCutMatches
      (tagged_long_native_retry_kernel hn ring i j k a b)
      (tagged_long_race_step ring i j k a b)
      (fun z => z.N)
      (TaggedLongRaceEntrance ring i j k a b)
      (TaggedLongIncidentEntrance ring i j k a b) := by
  intro z hz e
  obtain ⟨hm, hrace⟩ := hz
  have hgood : TaggedLongAttemptStageGood ring i j k a b z := by
    simpa [TaggedLongAttemptStageGood, hm, TaggedLongRaceActive]
      using hrace
  by_cases hd : TaggedDeleted i j k (nativeE ring z.N e)
  · have hs : tagged_long_race_step ring i j k a b z.N e =
        .success := by
      simp [tagged_long_race_step, hd]
    rw [hs]
    exact Or.inl
      (tagged_long_attempt_step_on_delete
        hn ring i j k a b z e hd)
  · by_cases hnear :
        TaggedLongNear ring i j k a b (nativeE ring z.N e)
    · by_cases hready :
          SealedCleanReady ring (nativeE ring z.N e) j b
      · have hs : tagged_long_race_step ring i j k a b z.N e =
            .success := by
          simp [tagged_long_race_step, hd, hnear, hready]
        rw [hs]
        have hnotretry : ¬ tagged_long_attempt_retry_edge
            ring i j k a b z e (nativeE ring z.N e) := by
          simp [tagged_long_attempt_retry_edge, hm, hnear]
        obtain ⟨z', hstep, hphysical, _⟩ :=
          tagged_long_attempt_step_on_active
            hn ring i j k a b z e hd hnotretry
        have hreadyChild : SealedCleanReady ring z'.N j b := by
          rw [hphysical]
          exact hready
        have hhandoff := tagged_long_attempt_race_handoff
          hn ring i j k a b z z' e hgood hm hstep hreadyChild
        exact Or.inr ⟨z', hstep,
          ⟨hhandoff.2.2, hhandoff.1, hhandoff.2.1⟩⟩
      · have hs : tagged_long_race_step ring i j k a b z.N e =
            .active (nativeE ring z.N e) := by
          simp [tagged_long_race_step, hd, hnear, hready]
        rw [hs]
        have hnotretry : ¬ tagged_long_attempt_retry_edge
            ring i j k a b z e (nativeE ring z.N e) := by
          simp [tagged_long_attempt_retry_edge, hm, hnear]
        obtain ⟨z', hstep, hphysical, hmode⟩ :=
          tagged_long_attempt_step_on_active
            hn ring i j k a b z e hd hnotretry
        have hmodeRace : z'.mode = .targetRace := by
          rw [hmode]
          simp [tagged_long_attempt_follow_mode, hm, hready]
        have hnearChild : TaggedLongNear ring i j k a b z'.N := by
          rw [hphysical]
          exact hnear
        have hnotReadyChild : ¬ SealedCleanReady ring z'.N j b := by
          rw [hphysical]
          exact hready
        exact ⟨z', hstep,
          ⟨hmodeRace, ⟨hnearChild, hnotReadyChild⟩⟩, hphysical⟩
    · have hs : tagged_long_race_step ring i j k a b z.N e =
          .failure := by
        simp [tagged_long_race_step, hd, hnear]
      rw [hs]
      have hretry : tagged_long_attempt_retry_edge
          ring i j k a b z e (nativeE ring z.N e) := by
        simpa [tagged_long_attempt_retry_edge, hm] using hnear
      obtain ⟨seed, hstep, _⟩ :=
        tagged_long_attempt_step_on_retry
          hn ring i j k a b z e hd hretry
      exact ⟨seed, hstep⟩

/-- Clock 2 is used at the retained FIRST entrance, not arbitrary
later race states. Composing its half-mass bound with 7/8 downstream
incident retry yields the claimed 15/16 kernel retry numerator. -/
theorem tagged_long_race_kernel_first_entrance {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hb : 2 ≤ b)
    (z : TaggedLongAttemptState ring i j k a b)
    (hz : TaggedLongRaceRetainedEntrance ring i j k a b z) :
    ∀ T,
      attemptCostNumerator
        (tagged_long_native_retry_kernel hn ring i j k a b)
        (.active z) T ≤
          n ^ T * (n * (2 * b - 1) + (n + n * (2 * b))) ∧
      16 * retryCount
        (tagged_long_native_retry_kernel hn ring i j k a b)
        (.active z) T ≤ 15 * n ^ T := by
  intro T
  have hmatch := tagged_long_race_first_cut_matches
    hn ring i j k a b
  have hstart :
      tagged_long_race_start ring j b z.N = .active z.N := by
    classical
    simp [tagged_long_race_start, hz.1.2.2]
  have hclock :=
    tagged_long_race_clock ring i j k a b z.N hz.2 T
  rw [hstart] at hclock
  constructor
  · have hreserve := tagged_first_cut_cost_reserve
      (tagged_long_native_retry_kernel hn ring i j k a b)
      (tagged_long_race_step ring i j k a b)
      (fun q => q.N)
      (TaggedLongRaceEntrance ring i j k a b)
      (TaggedLongIncidentEntrance ring i j k a b)
      (n + n * (2 * b)) hmatch
      (by
        intro q hq U
        exact (tagged_long_incident_kernel_first_entrance
          hn ring i j k a b hb q hq U).1)
      z hz.1 T
    calc
      _ ≤ truncatedActiveCostNumerator
          (tagged_long_race_step ring i j k a b)
          (.active z.N) T + n ^ T * (n + n * (2 * b)) :=
        hreserve
      _ ≤ n ^ T * (n * (2 * b - 1)) +
          n ^ T * (n + n * (2 * b)) :=
        Nat.add_le_add_right hclock.1 _
      _ = n ^ T *
          (n * (2 * b - 1) + (n + n * (2 * b))) := by
        simp only [Nat.mul_add]
  · have hbound := tagged_first_cut_failure_product_at
      (tagged_long_native_retry_kernel hn ring i j k a b)
      (tagged_long_race_step ring i j k a b)
      (fun q => q.N)
      (TaggedLongRaceEntrance ring i j k a b)
      (TaggedLongIncidentEntrance ring i j k a b)
      2 1 8 7 (by omega) hmatch
      (by
        intro q hq U
        exact (tagged_long_incident_kernel_first_entrance
          hn ring i j k a b hb q hq U).2)
      z hz.1 (by
        intro U
        have hhalf :=
          (tagged_long_race_clock
            ring i j k a b z.N hz.2 U).2
        rw [hstart] at hhalf
        rw [Nat.one_mul]
        exact hhalf)
      T
    simpa using hbound

end L3


/-! ## Preparation first hit and complete four-stage composition

The first-hit StopNode observer charges the literal
nativeE interaction until tagged deletion or the exactly retained
front. It never rewinds a configuration. Clock 1 has no failure
outcome, so its first-cut failure factor is 1.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false
attribute [local instance low] Classical.propDecidable

/-- The physical first-hit stopping observer has no failure leaf. -/
noncomputable def taggedFirstHitStep {S : Type} {n : Nat}
    (next : S → Fin n → S) (P : S → Prop)
    (x : S) (e : Fin n) : StopNode S := by
  classical
  exact if P (next x e) then .success else .active (next x e)

/-- On a genuinely nonterminal entrance, the finite-word stopped
active cost is exactly the existing native first-hit cost. -/
theorem tagged_first_hit_cost_exact {S : Type} {n : Nat}
    (next : S → Fin n → S) (P : S → Prop)
    (x : S) (hx : ¬ P x) :
    ∀ T,
      truncatedActiveCostNumerator
        (taggedFirstHitStep next P) (.active x) T =
      costNumerator next P x T := by
  have hmain :
      ∀ T (y : S), ¬ P y →
        truncatedActiveCostNumerator
          (taggedFirstHitStep next P) (.active y) T =
        costNumerator next P y T := by
    intro T
    induction T with
    | zero =>
        intro y _
        rfl
    | succ T ih =>
        intro y hy
        have hchild (e : Fin n) :
            truncatedActiveCostNumerator
              (taggedFirstHitStep next P)
              (taggedFirstHitStep next P y e) T =
            costNumerator next P (next y e) T := by
          by_cases hp : P (next y e)
          · have hstep :
                taggedFirstHitStep next P y e = .success := by
              simp [taggedFirstHitStep, hp]
            rw [hstep]
            cases T with
            | zero => rfl
            | succ U =>
                change 0 = costNumerator next P (next y e) (U + 1)
                exact (costNumerator_terminal
                  next P (next y e) hp (U + 1)).symm
          · have hstep :
                taggedFirstHitStep next P y e =
                  .active (next y e) := by
              simp [taggedFirstHitStep, hp]
            rw [hstep]
            exact ih (next y e) hp
        rw [costNumerator_succ next P y hy T]
        change
          n ^ (T + 1) +
            (List.ofFn (fun e : Fin n =>
              truncatedActiveCostNumerator
                (taggedFirstHitStep next P)
                (taggedFirstHitStep next P y e) T)).sum =
          n ^ (T + 1) +
            (List.ofFn (fun e : Fin n =>
              costNumerator next P (next y e) T)).sum
        rw [ofFn_sum_eq _ _ hchild]
  intro T
  exact hmain T x hx

/-- Every finite-depth failure cylinder is empty for a first-hit
observer: it can return only active or success. -/
theorem tagged_first_hit_failure_zero {S : Type} {n : Nat}
    (next : S → Fin n → S) (P : S → Prop) :
    ∀ (x : S) T,
      failureCount (taggedFirstHitStep next P) (.active x) T = 0 := by
  have hmain :
      ∀ T (y : S),
        failureCount (taggedFirstHitStep next P) (.active y) T =
          0 := by
    intro T
    induction T with
    | zero =>
        intro y
        simp [failureCount, treeWeight, failureWeight]
    | succ T ih =>
        intro y
        change (List.ofFn (fun e : Fin n =>
          failureCount
            (taggedFirstHitStep next P)
            (taggedFirstHitStep next P y e) T)).sum = 0
        rw [ofFn_sum_eq _ (fun _ : Fin n => 0) (fun e => by
          by_cases hp : P (next y e)
          · have hstep :
                taggedFirstHitStep next P y e = .success := by
              simp [taggedFirstHitStep, hp]
            rw [hstep]
            exact tagged_failure_count_success_zero
              (taggedFirstHitStep next P) T
          · have hstep :
                taggedFirstHitStep next P y e =
                  .active (next y e) := by
              simp [taggedFirstHitStep, hp]
            rw [hstep]
            exact ih (next y e)), ofFn_sum_const]
        rfl
  intro x T
  exact hmain T x

def TaggedLongPreparationGoal {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n) : Prop :=
  TaggedDeleted i j k N ∨ TaggedLongRetained ring i j k a b N

def TaggedLongPreparationEntrance {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (z : TaggedLongAttemptState ring i j k a b) : Prop :=
  z.mode = .preparation ∧
    ¬ TaggedLongRetained ring i j k a b z.N

/-- Stage 1's success leaf is either real deletion or a retained
native front; if B is already Ready the actual next mode skips the
race, consuming zero scheduler letters for that skipped stage. -/
theorem tagged_long_preparation_first_cut_matches {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat) :
    TaggedFirstCutMatches
      (tagged_long_native_retry_kernel hn ring i j k a b)
      (taggedFirstHitStep (nativeE ring)
        (TaggedLongPreparationGoal ring i j k a b))
      (fun z => z.N)
      (TaggedLongPreparationEntrance ring i j k a b)
      (fun z =>
        TaggedLongRaceRetainedEntrance ring i j k a b z ∨
          TaggedLongIncidentEntrance ring i j k a b z) := by
  intro z hz e
  obtain ⟨hm, hnotret⟩ := hz
  have hgood : TaggedLongAttemptStageGood ring i j k a b z := by
    simpa [TaggedLongAttemptStageGood, hm] using hnotret
  by_cases hd : TaggedDeleted i j k (nativeE ring z.N e)
  · have hs :
        taggedFirstHitStep (nativeE ring)
          (TaggedLongPreparationGoal ring i j k a b) z.N e =
            .success := by
      simp [taggedFirstHitStep, TaggedLongPreparationGoal, hd]
    rw [hs]
    exact Or.inl (tagged_long_attempt_step_on_delete
      hn ring i j k a b z e hd)
  · by_cases hret :
        TaggedLongRetained ring i j k a b (nativeE ring z.N e)
    · have hs :
          taggedFirstHitStep (nativeE ring)
            (TaggedLongPreparationGoal ring i j k a b) z.N e =
              .success := by
        simp [taggedFirstHitStep, TaggedLongPreparationGoal, hret]
      rw [hs]
      have hnotretry : ¬ tagged_long_attempt_retry_edge
          ring i j k a b z e (nativeE ring z.N e) := by
        simp [tagged_long_attempt_retry_edge, hm]
      obtain ⟨z', hstep, hphysical, _⟩ :=
        tagged_long_attempt_step_on_active
          hn ring i j k a b z e hd hnotretry
      have hretChild : TaggedLongRetained ring i j k a b z'.N := by
        rw [hphysical]
        exact hret
      have hgoodChild := tagged_long_attempt_stage_good_active
        hn ring i j k a b z z' e hgood hstep
      have hhandoff := tagged_long_attempt_preparation_handoff
        hn ring i j k a b z z' e hm hstep hretChild
      rcases hhandoff with hmodeRace | hmodeIncident
      · have hcut : TaggedLongNear ring i j k a b z'.N ∧
            ¬ SealedCleanReady ring z'.N j b := by
          simpa [TaggedLongAttemptStageGood, hmodeRace] using hgoodChild
        exact Or.inr ⟨z', hstep,
          Or.inl ⟨⟨hmodeRace, hcut⟩, hretChild⟩⟩
      · have hcut : TaggedLongNear ring i j k a b z'.N ∧
            SealedCleanReady ring z'.N j b := by
          simpa [TaggedLongAttemptStageGood, hmodeIncident] using hgoodChild
        exact Or.inr ⟨z', hstep,
          Or.inr ⟨hmodeIncident, hcut.1, hcut.2⟩⟩
    · have hs :
          taggedFirstHitStep (nativeE ring)
            (TaggedLongPreparationGoal ring i j k a b) z.N e =
              .active (nativeE ring z.N e) := by
        simp [taggedFirstHitStep, TaggedLongPreparationGoal, hd, hret]
      rw [hs]
      have hnotretry : ¬ tagged_long_attempt_retry_edge
          ring i j k a b z e (nativeE ring z.N e) := by
        simp [tagged_long_attempt_retry_edge, hm]
      obtain ⟨z', hstep, hphysical, hmode⟩ :=
        tagged_long_attempt_step_on_active
          hn ring i j k a b z e hd hnotretry
      have hmodePrep : z'.mode = .preparation := by
        rw [hmode]
        simp [tagged_long_attempt_follow_mode, hm, hret]
      have hretChild :
          ¬ TaggedLongRetained ring i j k a b z'.N := by
        rw [hphysical]
        exact hret
      exact ⟨z', hstep, ⟨hmodePrep, hretChild⟩, hphysical⟩

/-- Clock 1's terminal predicate agrees with the observer at
every actual preparation entrance, not only the original seed. -/
theorem tagged_long_preparation_first_cost {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hb : 2 ≤ b) (hab : 2 * b + 1 ≤ a)
    (z : TaggedLongAttemptState ring i j k a b)
    (hz : TaggedLongPreparationEntrance ring i j k a b z) :
    ∀ T,
      truncatedActiveCostNumerator
        (taggedFirstHitStep (nativeE ring)
          (TaggedLongPreparationGoal ring i j k a b))
        (.active z.N) T ≤ n ^ T * (n * (6 * a + b)) := by
  have hnotGoal :
      ¬ TaggedLongPreparationGoal ring i j k a b z.N := by
    intro hg
    rcases hg with hd | hr
    · exact (tagged_d15_triple_not_deleted
        ring i j k a b z.N z.triple) hd
    · exact hz.2 hr
  intro T
  rw [tagged_first_hit_cost_exact
    (nativeE ring) (TaggedLongPreparationGoal ring i j k a b)
    z.N hnotGoal T]
  exact tagged_long_preparation_clock
    hn ring i j k a b hb hab z.N z.triple T

/-- The preparation clock has no failure leaf. An already-Ready B
enters incident directly, while nonReady retained cuts enter race. -/
theorem tagged_long_preparation_kernel_first_entrance {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hb : 2 ≤ b) (hab : 2 * b + 1 ≤ a)
    (z : TaggedLongAttemptState ring i j k a b)
    (hz : TaggedLongPreparationEntrance ring i j k a b z) :
    ∀ T,
      attemptCostNumerator
        (tagged_long_native_retry_kernel hn ring i j k a b)
        (.active z) T ≤
          n ^ T * (n * (6 * a + b) +
            (n * (2 * b - 1) + (n + n * (2 * b)))) ∧
      16 * retryCount
        (tagged_long_native_retry_kernel hn ring i j k a b)
        (.active z) T ≤ 15 * n ^ T := by
  intro T
  have hmatch := tagged_long_preparation_first_cut_matches
    hn ring i j k a b
  constructor
  · exact tagged_first_cut_cost_add
      (tagged_long_native_retry_kernel hn ring i j k a b)
      (taggedFirstHitStep (nativeE ring)
        (TaggedLongPreparationGoal ring i j k a b))
      (fun q => q.N)
      (TaggedLongPreparationEntrance ring i j k a b)
      (fun q =>
        TaggedLongRaceRetainedEntrance ring i j k a b q ∨
          TaggedLongIncidentEntrance ring i j k a b q)
      (n * (6 * a + b))
      (n * (2 * b - 1) + (n + n * (2 * b))) hmatch
      (by
        intro q hq U
        exact tagged_long_preparation_first_cost
          hn ring i j k a b hb hab q hq U)
      (by
        intro q hq U
        rcases hq with hr | hi
        · exact (tagged_long_race_kernel_first_entrance
            hn ring i j k a b hb q hr U).1
        · have hh := (tagged_long_incident_kernel_first_entrance
            hn ring i j k a b hb q hi U).1
          exact Nat.le_trans hh
            (Nat.mul_le_mul_left (n ^ U)
              (Nat.le_add_left
                (n + n * (2 * b)) (n * (2 * b - 1)))))
      z hz T
  · have hbound := tagged_first_cut_failure_product
      (tagged_long_native_retry_kernel hn ring i j k a b)
      (taggedFirstHitStep (nativeE ring)
        (TaggedLongPreparationGoal ring i j k a b))
      (fun q => q.N)
      (TaggedLongPreparationEntrance ring i j k a b)
      (fun q =>
        TaggedLongRaceRetainedEntrance ring i j k a b q ∨
          TaggedLongIncidentEntrance ring i j k a b q)
      1 0 16 15 (by omega) hmatch
      (by
        intro q _ U
        have hh := tagged_first_hit_failure_zero
          (nativeE ring)
          (TaggedLongPreparationGoal ring i j k a b) q.N U
        simp [hh])
      (by
        intro q hq U
        rcases hq with hr | hi
        · exact (tagged_long_race_kernel_first_entrance
            hn ring i j k a b hb q hr U).2
        · have hh := (tagged_long_incident_kernel_first_entrance
            hn ring i j k a b hb q hi U).2
          calc
            16 * retryCount
                (tagged_long_native_retry_kernel hn ring i j k a b)
                (.active q) U =
              2 * (8 * retryCount
                (tagged_long_native_retry_kernel hn ring i j k a b)
                (.active q) U) := by omega
            _ ≤ 2 * (7 * n ^ U) :=
              Nat.mul_le_mul_left 2 hh
            _ ≤ 15 * n ^ U := by omega)
      z hz T
    simpa using hbound

/-- A retry seed is inspected without consuming a scheduler letter.
Exactly one of the three genuine first-stage entrances holds. -/
theorem tagged_long_attempt_start_cases {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (seed : TaggedLongAttemptSeed ring i j k a b) :
    TaggedLongPreparationEntrance ring i j k a b
      (tagged_long_attempt_start ring i j k a b seed) ∨
    TaggedLongRaceRetainedEntrance ring i j k a b
      (tagged_long_attempt_start ring i j k a b seed) ∨
    TaggedLongIncidentEntrance ring i j k a b
      (tagged_long_attempt_start ring i j k a b seed) := by
  classical
  have hnative := tagged_long_attempt_start_native
    ring i j k a b seed
  by_cases hret : TaggedLongRetained ring i j k a b seed.N
  · have hnear := tagged_long_retained_to_near
      ring i j k a b seed.N hret
    by_cases hready : SealedCleanReady ring seed.N j b
    · right
      right
      have hm :
          (tagged_long_attempt_start ring i j k a b seed).mode =
            .incident := by
        simp [tagged_long_attempt_start, hret, hready]
      have hnear' : TaggedLongNear ring i j k a b
          (tagged_long_attempt_start ring i j k a b seed).N := by
        rw [hnative]
        exact hnear
      have hready' : SealedCleanReady ring
          (tagged_long_attempt_start ring i j k a b seed).N j b := by
        rw [hnative]
        exact hready
      exact ⟨hm, hnear', hready'⟩
    · right
      left
      have hm :
          (tagged_long_attempt_start ring i j k a b seed).mode =
            .targetRace := by
        simp [tagged_long_attempt_start, hret, hready]
      have hnear' : TaggedLongNear ring i j k a b
          (tagged_long_attempt_start ring i j k a b seed).N := by
        rw [hnative]
        exact hnear
      have hready' : ¬ SealedCleanReady ring
          (tagged_long_attempt_start ring i j k a b seed).N j b := by
        rw [hnative]
        exact hready
      have hret' : TaggedLongRetained ring i j k a b
          (tagged_long_attempt_start ring i j k a b seed).N := by
        rw [hnative]
        exact hret
      exact ⟨⟨hm, ⟨hnear', hready'⟩⟩, hret'⟩
  · left
    have hm :
        (tagged_long_attempt_start ring i j k a b seed).mode =
          .preparation := by
      simp [tagged_long_attempt_start, hret]
    have hnot' : ¬ TaggedLongRetained ring i j k a b
        (tagged_long_attempt_start ring i j k a b seed).N := by
      rw [hnative]
      exact hret
    exact ⟨hm, hnot'⟩

/-- The four genuine stage budgets give both kernel-wide D.19
premises, on every tagged-triple seed. The only extra condition is
the long-regime a >= 2b+1 required by Clock 1 itself. -/
theorem tagged_long_native_long_regime_attempt_machine {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hb : 2 ≤ b) (hab : 2 * b + 1 ≤ a) :
    TaggedLongNativeAttemptMachine ring i j k a b := by
  have hall :
      ∀ seed : TaggedLongAttemptSeed ring i j k a b,
        ∀ T,
          attemptCostNumerator
            (tagged_long_native_retry_kernel hn ring i j k a b)
            (.active
              ((tagged_long_native_retry_kernel
                hn ring i j k a b).start seed)) T ≤
            n ^ T * (7 * n * (a + b)) ∧
          16 * retryCount
            (tagged_long_native_retry_kernel hn ring i j k a b)
            (.active
              ((tagged_long_native_retry_kernel
                hn ring i j k a b).start seed)) T ≤
            15 * n ^ T := by
    intro seed T
    have hcases := tagged_long_attempt_start_cases
      ring i j k a b seed
    have ha : 1 ≤ a := seed.triple.2.1.1
    have hbudget := tagged_long_machine_budget_arithmetic
      n a b ha hb
    have hcap :
        n * (6 * a + b) +
          (n * (2 * b - 1) + (n + n * (2 * b))) ≤
          7 * n * (a + b) := by
      omega
    rcases hcases with hp | hr | hi
    · have hh := tagged_long_preparation_kernel_first_entrance
        hn ring i j k a b hb hab
        (tagged_long_attempt_start ring i j k a b seed)
        hp T
      exact ⟨Nat.le_trans hh.1
        (Nat.mul_le_mul_left (n ^ T) hcap), hh.2⟩
    · have hh := tagged_long_race_kernel_first_entrance
        hn ring i j k a b hb
        (tagged_long_attempt_start ring i j k a b seed)
        hr T
      have hcapRace :
          n * (2 * b - 1) + (n + n * (2 * b)) ≤
            7 * n * (a + b) := by
        exact Nat.le_trans
          (Nat.le_add_left
            (n * (2 * b - 1) + (n + n * (2 * b)))
            (n * (6 * a + b))) hcap
      exact ⟨Nat.le_trans hh.1
        (Nat.mul_le_mul_left (n ^ T) hcapRace), hh.2⟩
    · have hh := tagged_long_incident_kernel_first_entrance
        hn ring i j k a b hb
        (tagged_long_attempt_start ring i j k a b seed)
        hi T
      have hcapIncident :
          n + n * (2 * b) ≤ 7 * n * (a + b) := by
        exact Nat.le_trans
          (Nat.le_add_left
            (n + n * (2 * b)) (n * (2 * b - 1)))
          (Nat.le_trans
            (Nat.le_add_left
              (n * (2 * b - 1) + (n + n * (2 * b)))
              (n * (6 * a + b))) hcap)
      have hretry :
          16 * retryCount
            (tagged_long_native_retry_kernel hn ring i j k a b)
            (.active (tagged_long_attempt_start
              ring i j k a b seed)) T ≤ 15 * n ^ T := by
        calc
          16 * retryCount
              (tagged_long_native_retry_kernel hn ring i j k a b)
              (.active (tagged_long_attempt_start
                ring i j k a b seed)) T =
            2 * (8 * retryCount
              (tagged_long_native_retry_kernel hn ring i j k a b)
              (.active (tagged_long_attempt_start
                ring i j k a b seed)) T) := by omega
          _ ≤ 2 * (7 * n ^ T) :=
            Nat.mul_le_mul_left 2 hh.2
          _ ≤ 15 * n ^ T := by omega
      exact ⟨Nat.le_trans hh.1
        (Nat.mul_le_mul_left (n ^ T) hcapIncident), hretry⟩
  exact tagged_long_native_attempt_machine_of_bounds
    hn ring i j k a b hb
    (by intro seed T; exact (hall seed T).1)
    (by intro seed T; exact (hall seed T).2)

end L3


/-! ## D.19 long-machine closure, D.9 all-regime ceiling

The numerical D.19 factor 112
is certified here for b = 1 and for b >= 2, a >= 2*b+1. For the
remaining moderate regime a <= 2*b the existing D.15 certificate
only establishes taggedTripleCeiling, not factor 112. The full
requested 112 statement is therefore not declared as a theorem.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false
attribute [local instance low] Classical.propDecidable

/-- The four-clock native attempt machine yields exactly the
D.19 factor 16 * 7 = 112 from every real long-regime tagged triple.
This stops at an actual deleted tag on nativeE. -/
theorem tagged_triple_native_cost_long {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (hb : 2 ≤ b) (hab : 2 * b + 1 ≤ a)
    (N : TripleNativeState n)
    (htriple : TaggedTriple ring i j k a b N) :
    ∀ T,
      costNumerator (nativeE ring) (TaggedDeleted i j k) N T ≤
        n ^ T * (112 * n * (a + b)) := by
  exact tagged_long_cost_of_machine
    ring i j k a b
    (tagged_long_native_long_regime_attempt_machine
      hn ring i j k a b hb hab)
    N htriple

/-- The D.20 sixfold one-edge bound fits inside the requested
112 allowance; no long-regime assumption is needed at b = 1. -/
theorem tagged_short_budget_within_long (n a b : Nat) :
    6 * n * (a + b) ≤ 112 * n * (a + b) := by
  have hcoeff : 6 ≤ 112 := by omega
  calc
    6 * n * (a + b) = 6 * (n * (a + b)) := by ac_rfl
    _ ≤ 112 * (n * (a + b)) :=
      Nat.mul_le_mul_right (n * (a + b)) hcoeff
    _ = 112 * n * (a + b) := by ac_rfl

theorem tagged_triple_native_cost_short {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (htriple : TaggedTriple ring i j k a b N)
    (hb : b = 1) :
    ∀ T,
      costNumerator (nativeE ring) (TaggedDeleted i j k) N T ≤
        n ^ T * (112 * n * (a + b)) := by
  intro T
  exact Nat.le_trans
    (tagged_short_hshort
      hn ring i j k a b N htriple hb T)
    (Nat.mul_le_mul_left (n ^ T)
      (tagged_short_budget_within_long n a b))

/-- Precisely the currently proved domain of the coefficient 112.
The omitted case is 2 <= b and 1 <= a <= 2*b. -/
theorem tagged_triple_native_cost_covered {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (htriple : TaggedTriple ring i j k a b N)
    (hcovered : b = 1 ∨ (2 ≤ b ∧ 2 * b + 1 ≤ a)) :
    ∀ T,
      costNumerator (nativeE ring) (TaggedDeleted i j k) N T ≤
        n ^ T * (112 * n * (a + b)) := by
  rcases hcovered with hb | ⟨hb, hab⟩
  · exact tagged_triple_native_cost_short
      hn ring i j k a b N htriple hb
  · exact tagged_triple_native_cost_long
      hn ring i j k a b hb hab N htriple

/-- The unconditional native first-deletion certificate is the
original all-regime D.9 integer ceiling, not the unproved uniform
112 bound. Its middle branch uses the earlier D.15 theorem;
the present append discharges the last open long hlong producer. -/
theorem tagged_triple_native_cost_ceiling {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (htriple : TaggedTriple ring i j k a b N) :
    ∀ T,
      costNumerator (nativeE ring) (TaggedDeleted i j k) N T ≤
        n ^ T * taggedTripleCeiling n a b := by
  apply tagged_deletion_cost_of_long
    hn ring i j k a b N htriple
  intro hb hab T
  exact tagged_triple_native_cost_long
    hn ring i j k a b hb hab N htriple T

/-- The expected-time form of the now unconditional D.9 native
ceiling, using the existing exact finite-horizon equivalence. -/
theorem tagged_triple_native_expected_ceiling {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (htriple : TaggedTriple ring i j k a b N) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (nativeE ring) (TaggedDeleted i j k) N
      ((taggedTripleCeiling n a b : Nat) : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (nativeE ring) (TaggedDeleted i j k)
    (by omega : 0 < n) N (taggedTripleCeiling n a b)).2
  exact tagged_triple_native_cost_ceiling
    hn ring i j k a b N htriple

/-- The requested factor-112 expected-time conclusion holds on the
same explicitly covered short-or-long domain. -/
theorem tagged_triple_native_expected_covered {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n) (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (htriple : TaggedTriple ring i j k a b N)
    (hcovered : b = 1 ∨ (2 ≤ b ∧ 2 * b + 1 ≤ a)) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (nativeE ring) (TaggedDeleted i j k) N
      ((112 * n * (a + b) : Nat) : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (nativeE ring) (TaggedDeleted i j k)
    (by omega : 0 < n) N (112 * n * (a + b))).2
  exact tagged_triple_native_cost_covered
    hn ring i j k a b N htriple hcovered

/-- The checked D.15 alias seed with leaders at 0,2,4 is a genuine
counterexample to any assertion that TaggedTriple itself implies
the long-regime inequality. Both gaps are exactly two. -/
theorem tagged_triple_moderate_witness :
    TaggedTriple taggedD15AliasRing
      (0 : Fin 5) (2 : Fin 5) (4 : Fin 5)
      2 2 taggedD15AliasSeed ∧
    2 ≤ (2 : Nat) ∧
    ¬ (2 * (2 : Nat) + 1 ≤ (2 : Nat)) := by
  exact ⟨tagged_d15_alias_initial_triple, by omega, by omega⟩

end L3
