import Leader.Wu.Splice.HoldRepairChainLength
import Leader.Wu.Splice.HoldRepairProgressMass
import Leader.Wu.Birth.LeaderlessBirthMassRenewal

set_option autoImplicit false
set_option Elab.async false

/-! # V10j with leaders: physical services come at rate `Θ(1/n²)` letters, uniformly over safe starts

Weighted renewal (`weighted_tail`): if from every `Good` state the length-`L` words that stay `Good`, weighted by
`W` of their endpoint, have total at most `P/Q` times `W` of the start, then over `k` blocks the weighted count is at
most `(P/Q)^k`.  Instance: the V10j composed service with a flag recording whether a physical service has occurred,
`Good` = flag down and `SpliceSafeV7g`, and `W = 2^PsiJ`.  From the 1/64 progress mass
(`B9SpliceV10jProgressMass.progress_massJ`) and the amortized potential (`B9SpliceV10jAmortizedChain.psiJ_drop`: a
non-physical change lowers `PsiJ`), one block of `6 n` letters has weighted escape factor `127/128`
(`block_escape`).  Since `PsiJ ≤ 7 n`, the words of length `k * 6 n` without a physical service number at most
`(127/128)^k * 2^(7n) * n^(k*6n)` (`noPhysical_tail`), and at `k = 128 * (7 n + log2 n + 1)` at most a `1/n`
fraction of the words avoid physical services (`noPhysical_one_over_n`).  With or without leaders, on every ring
with `n ≥ 3`, from every `SpliceSafeV7g` configuration. -/

namespace B9SpliceV10jPhysicalRate

open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV6
  B9SpliceTableV10g B9SpliceTableV10j B9SpliceV10hControllerRowsSafe B9SpliceV10eTransparency
  B9SpliceV10ePairWeight B9SpliceLocalStepMass B9SpliceV10jGlobalProgress B9SpliceV10jProgressMass
  B9SpliceV10jAmortizedPotential B9SpliceV10jAmortizedChain BirthLeaderlessBirthMassRenewal
  FixedSpanRenewalPayload

/-! ## Word sums -/

section WordSums

variable {n : Nat}

theorem wordSum_congr_len {T : Nat} (f g : List (Fin n) → Nat) (h : ∀ u : List (Fin n), u.length = T → f u = g u) :
    wordSum n T f = wordSum n T g := by
  rw [← rawWord_sum n T f, ← rawWord_sum n T g]
  apply FiniteUniformStoppingTree.ofFn_sum_eq
  intro i
  exact h _ (rawWord_length n T i)

theorem wordSum_mono_len {T : Nat} (f g : List (Fin n) → Nat) (h : ∀ u : List (Fin n), u.length = T → f u ≤ g u) :
    wordSum n T f ≤ wordSum n T g := by
  rw [← rawWord_sum n T f, ← rawWord_sum n T g]
  apply FiniteUniformStoppingTree.ofFn_sum_le
  intro i
  exact h _ (rawWord_length n T i)

theorem wordSum_mul_l (T c : Nat) (f : List (Fin n) → Nat) :
    wordSum n T (fun u => c * f u) = c * wordSum n T f := by
  rw [← rawWord_sum n T (fun u => c * f u), ← rawWord_sum n T f]
  exact FiniteUniformStoppingTree.ofFn_sum_mul_left c _

theorem wordSum_add' (T : Nat) (f g : List (Fin n) → Nat) :
    wordSum n T (fun u => f u + g u) = wordSum n T f + wordSum n T g := by
  rw [← rawWord_sum n T (fun u => f u + g u), ← rawWord_sum n T f, ← rawWord_sum n T g,
    FiniteUniformStoppingTree.ofFn_sum_add]

theorem wordSum_const' (T c : Nat) : wordSum n T (fun _ => c) = c * n ^ T := by
  rw [← rawWord_sum n T (fun _ => c)]
  simp only [FiniteUniformStoppingTree.ofFn_sum_const]
  exact Nat.mul_comm _ _

theorem wordSum_horizon (T U : Nat) (f : List (Fin n) → Nat) :
    wordSum n (T + U) f = wordSum n T (fun u => wordSum n U (fun v => f (u ++ v))) := by
  induction T generalizing f with
  | zero => simp [wordSum, allSchedules]
  | succ T ih =>
      rw [Nat.succ_add]
      change wordSum n (T + U + 1) f = wordSum n (T + 1) (fun u => wordSum n U (fun v => f (u ++ v)))
      rw [wordSum_succ, wordSum_succ]
      apply FiniteUniformStoppingTree.ofFn_sum_eq
      intro e
      simpa only [List.cons_append] using ih (f := fun w => f (e :: w))

end WordSums

/-! ## Weighted renewal -/

section Weighted

variable {S : Type} {n : Nat}

noncomputable def weightedAlive (step : S → Fin n → S) (Good : S → Prop) (W : S → Nat) (x : S) (T : Nat) : Nat :=
  wordSum n T (fun u => aliveBit step Good x u * W (u.foldl step x))

def WeightedEscape (step : S → Fin n → S) (Good : S → Prop) (W : S → Nat) (L P Q : Nat) : Prop :=
  ∀ x, Good x → Q * weightedAlive step Good W x L ≤ P * (W x * n ^ L)

theorem weighted_tail (step : S → Fin n → S) (Good : S → Prop) (W : S → Nat) (L P Q : Nat)
    (hmass : WeightedEscape step Good W L P Q) :
    ∀ (k : Nat) (x : S), Good x → Q ^ k * weightedAlive step Good W x (k * L) ≤ P ^ k * (W x * n ^ (k * L)) := by
  intro k
  induction k with
  | zero =>
      intro x _
      simp only [Nat.pow_zero, Nat.one_mul, Nat.zero_mul]
      unfold weightedAlive
      calc wordSum n 0 (fun u => aliveBit step Good x u * W (u.foldl step x))
          ≤ wordSum n 0 (fun _ => W x) := wordSum_mono_len _ _ (fun u hu => by
              rw [List.length_eq_zero_iff.mp hu]
              have := aliveBit_le_one step Good x []
              simp only [List.foldl_nil]
              calc aliveBit step Good x [] * W x ≤ 1 * W x := Nat.mul_le_mul_right _ this
                _ = W x := Nat.one_mul _)
        _ = W x * n ^ 0 := wordSum_const' 0 (W x)
  | succ k ih =>
      intro x hx
      have hsplit : weightedAlive step Good W x ((k + 1) * L) =
          wordSum n L (fun u => aliveBit step Good x u * weightedAlive step Good W (u.foldl step x) (k * L)) := by
        unfold weightedAlive
        rw [show (k + 1) * L = L + k * L by rw [Nat.succ_mul]; omega, wordSum_horizon]
        apply wordSum_congr_len
        intro u _
        rw [← wordSum_mul_l]
        apply wordSum_congr_len
        intro v _
        rw [aliveBit_append step Good x u v, List.foldl_append, Nat.mul_assoc]
      have hpoint : ∀ u : List (Fin n), u.length = L →
          Q ^ k * (aliveBit step Good x u * weightedAlive step Good W (u.foldl step x) (k * L)) ≤
            (P ^ k * n ^ (k * L)) * (aliveBit step Good x u * W (u.foldl step x)) := by
        intro u _
        by_cases hpos : 0 < aliveBit step Good x u
        · have hgood := good_of_aliveBit_pos step Good x u hpos
          have h1 : aliveBit step Good x u = 1 := by
            have := aliveBit_le_one step Good x u
            omega
          rw [h1, Nat.one_mul, Nat.one_mul]
          have := ih _ hgood
          calc Q ^ k * weightedAlive step Good W (u.foldl step x) (k * L)
              ≤ P ^ k * (W (u.foldl step x) * n ^ (k * L)) := this
            _ = P ^ k * n ^ (k * L) * W (u.foldl step x) := by ac_rfl
        · have h0 : aliveBit step Good x u = 0 := by omega
          simp [h0]
      have hsum : Q ^ k * weightedAlive step Good W x ((k + 1) * L) ≤
          (P ^ k * n ^ (k * L)) * weightedAlive step Good W x L := by
        rw [hsplit, ← wordSum_mul_l]
        unfold weightedAlive
        rw [← wordSum_mul_l]
        exact wordSum_mono_len _ _ hpoint
      have hm := hmass x hx
      calc Q ^ (k + 1) * weightedAlive step Good W x ((k + 1) * L)
          = Q * (Q ^ k * weightedAlive step Good W x ((k + 1) * L)) := by rw [Nat.pow_succ]; ac_rfl
        _ ≤ Q * ((P ^ k * n ^ (k * L)) * weightedAlive step Good W x L) := Nat.mul_le_mul_left Q hsum
        _ = (P ^ k * n ^ (k * L)) * (Q * weightedAlive step Good W x L) := by ac_rfl
        _ ≤ (P ^ k * n ^ (k * L)) * (P * (W x * n ^ L)) := Nat.mul_le_mul_left _ hm
        _ = P ^ (k + 1) * (W x * n ^ ((k + 1) * L)) := by
            rw [Nat.pow_succ, show (k + 1) * L = k * L + L by rw [Nat.succ_mul], Nat.pow_add]
            ac_rfl

end Weighted

/-! ## The flagged V10j service -/

section Instance

variable {n psi width kappa tau : Nat}

/-- One V10j service, and a flag that goes up at the first physical service. -/
noncomputable def stepF (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n)
    (x : R1ConfigV6 n psi kappa tau × Bool) (e : Fin n) : R1ConfigV6 n psi kappa tau × Bool := by
  classical
  exact (stepV10j hpsi hwidth hle ring x.1 e,
    x.2 || decide (PhysicalServiceAt hpsi hwidth hle ring x.1 (stepV10j hpsi hwidth hle ring x.1 e) e))

def GoodF (hpsi : 0 < psi) (ring : DirectedRing n) (x : R1ConfigV6 n psi kappa tau × Bool) : Prop :=
  x.2 = false ∧ SpliceSafeV7g hpsi ring x.1

noncomputable def WF (hpsi : 0 < psi) (ring : DirectedRing n) (x : R1ConfigV6 n psi kappa tau × Bool) : Nat :=
  2 ^ PsiJ hpsi ring x.1

theorem stepF_fst (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n) :
    ∀ (u : List (Fin n)) (x : R1ConfigV6 n psi kappa tau × Bool),
      (u.foldl (stepF hpsi hwidth hle ring) x).1 = serveWordG (stepV10j hpsi hwidth hle ring) u x.1
  | [], _ => rfl
  | e :: u, x => stepF_fst hpsi hwidth hle ring u (stepF hpsi hwidth hle ring x e)

theorem not_physical_of_good_step (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n)
    (x : R1ConfigV6 n psi kappa tau × Bool) (e : Fin n) (h : GoodF hpsi ring (stepF hpsi hwidth hle ring x e)) :
    ¬ PhysicalServiceAt hpsi hwidth hle ring x.1 (stepV10j hpsi hwidth hle ring x.1 e) e := by
  classical
  intro hp
  have h2 := h.1
  unfold stepF at h2
  simp only [decide_eq_true hp, Bool.or_true] at h2
  exact absurd h2 (by decide)

/-- Along an alive word no service is physical. -/
theorem physCount_zero_of_alive (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n) :
    ∀ (u : List (Fin n)) (x : R1ConfigV6 n psi kappa tau × Bool),
      AliveAlong (stepF hpsi hwidth hle ring) (GoodF hpsi ring) x u →
        physCountG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) u x.1 = 0
  | [], _, _ => rfl
  | e :: u, x, h => by
      classical
      have hg := aliveAlong_good (step := stepF hpsi hwidth hle ring) (Good := GoodF hpsi ring) h.2
      have hnp := not_physical_of_good_step hpsi hwidth hle ring x e hg
      have ih := physCount_zero_of_alive hpsi hwidth hle ring u _ h.2
      show (if PhysicalServiceAt hpsi hwidth hle ring x.1 (stepV10j hpsi hwidth hle ring x.1 e) e then 1 else 0) +
        physCountG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) u (stepV10j hpsi hwidth hle ring x.1 e) = 0
      rw [if_neg hnp, Nat.zero_add]
      exact ih

/-- Along an alive word `PsiJ` never increases, and it strictly drops unless the configuration is unchanged. -/
theorem psi_along_alive (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n)
    (hn : 3 ≤ n) :
    ∀ (u : List (Fin n)) (x : R1ConfigV6 n psi kappa tau × Bool),
      AliveAlong (stepF hpsi hwidth hle ring) (GoodF hpsi ring) x u →
        serveWordG (stepV10j hpsi hwidth hle ring) u x.1 = x.1 ∨
          PsiJ hpsi ring (serveWordG (stepV10j hpsi hwidth hle ring) u x.1) < PsiJ hpsi ring x.1
  | [], _, _ => Or.inl rfl
  | e :: u, x, h => by
      classical
      have hx := aliveAlong_good (step := stepF hpsi hwidth hle ring) (Good := GoodF hpsi ring) h
      have hg := aliveAlong_good (step := stepF hpsi hwidth hle ring) (Good := GoodF hpsi ring) h.2
      have hnp := not_physical_of_good_step hpsi hwidth hle ring x e hg
      have ih := psi_along_alive hpsi hwidth hle ring hn u _ h.2
      show serveWordG (stepV10j hpsi hwidth hle ring) u (stepV10j hpsi hwidth hle ring x.1 e) = x.1 ∨
        PsiJ hpsi ring (serveWordG (stepV10j hpsi hwidth hle ring) u (stepV10j hpsi hwidth hle ring x.1 e)) <
          PsiJ hpsi ring x.1
      by_cases hch : stepV10j hpsi hwidth hle ring x.1 e = x.1
      · have ih' := ih
        simp only [stepF, hch] at ih'
        rw [hch]
        exact ih'
      · right
        have hd := psiJ_drop hpsi hwidth hle ring hn x.1 hx.2 e hnp hch
        rcases ih with h1 | h1
        · simp only [stepF] at h1
          rw [h1]; exact hd
        · simp only [stepF] at h1
          omega

theorem psi_le_along_alive (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n)
    (hn : 3 ≤ n) (u : List (Fin n)) (x : R1ConfigV6 n psi kappa tau × Bool)
    (h : AliveAlong (stepF hpsi hwidth hle ring) (GoodF hpsi ring) x u) :
    PsiJ hpsi ring (serveWordG (stepV10j hpsi hwidth hle ring) u x.1) ≤ PsiJ hpsi ring x.1 := by
  rcases psi_along_alive hpsi hwidth hle ring hn u x h with h1 | h1
  · rw [h1]; exact Nat.le_refl _
  · exact Nat.le_of_lt h1

/-- One block: weighted escape factor `127/128`. -/
theorem block_escape (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n)
    (hn : 3 ≤ n) :
    WeightedEscape (stepF (kappa := kappa) (tau := tau) hpsi hwidth hle ring) (GoodF hpsi ring) (WF hpsi ring)
      (6 * n) 127 128 := by
  classical
  intro x hx
  obtain ⟨e, hmass⟩ := progress_massJ hpsi hwidth hle ring hn x.1 hx.2
  have hpoint : ∀ u : List (Fin n), u.length = 6 * n →
      2 * (aliveBit (stepF hpsi hwidth hle ring) (GoodF hpsi ring) x u *
          WF hpsi ring (u.foldl (stepF hpsi hwidth hle ring) x)) +
        progressBitG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) x.1 e u * 2 ^ PsiJ hpsi ring x.1 ≤
      2 * 2 ^ PsiJ hpsi ring x.1 := by
    intro u _
    have hpb : progressBitG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) x.1 e u ≤ 1 := by
      unfold progressBitG; split <;> omega
    by_cases hal : AliveAlong (stepF hpsi hwidth hle ring) (GoodF hpsi ring) x u
    · have hab : aliveBit (stepF hpsi hwidth hle ring) (GoodF hpsi ring) x u = 1 := by
        unfold aliveBit; rw [if_pos hal]
      rw [hab, Nat.one_mul]
      unfold WF
      rw [stepF_fst]
      have hle1 := psi_le_along_alive hpsi hwidth hle ring hn u x hal
      by_cases hprog : progressBitG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) x.1 e u = 1
      · rw [hprog, Nat.one_mul]
        -- the progress is a pair-weight drop at a prefix, so the configuration changed along that prefix
        have hdrop : PsiJ hpsi ring (serveWordG (stepV10j hpsi hwidth hle ring) u x.1) < PsiJ hpsi ring x.1 := by
          unfold progressBitG at hprog
          split at hprog
          · rename_i hc
            rcases hc with hc | ⟨w', ⟨t, ht⟩, hw⟩
            · have := physCount_zero_of_alive hpsi hwidth hle ring u x hal
              omega
            · subst ht
              have hal' := (aliveAlong_append (stepF hpsi hwidth hle ring) (GoodF hpsi ring) x w' t).1 hal
              have hne : serveWordG (stepV10j hpsi hwidth hle ring) w' x.1 ≠ x.1 := by
                intro heq; rw [heq] at hw; exact Nat.lt_irrefl _ hw
              have h1 : PsiJ hpsi ring (serveWordG (stepV10j hpsi hwidth hle ring) w' x.1) < PsiJ hpsi ring x.1 := by
                rcases psi_along_alive hpsi hwidth hle ring hn w' x hal'.1 with h | h
                · exact absurd h hne
                · exact h
              have h2 := psi_le_along_alive hpsi hwidth hle ring hn t _ hal'.2
              rw [stepF_fst] at h2
              rw [serveWordG_append]
              omega
          · omega
        have hp2 : 2 * 2 ^ PsiJ hpsi ring (serveWordG (stepV10j hpsi hwidth hle ring) u x.1) ≤
            2 ^ PsiJ hpsi ring x.1 := by
          have := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.succ_le_of_lt hdrop)
          rw [Nat.pow_succ] at this
          omega
        omega
      · have hp0 : progressBitG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) x.1 e u = 0 := by omega
        rw [hp0, Nat.zero_mul, Nat.add_zero]
        exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide) hle1)
    · have hab : aliveBit (stepF hpsi hwidth hle ring) (GoodF hpsi ring) x u = 0 := by
        unfold aliveBit; rw [if_neg hal]
      rw [hab, Nat.zero_mul, Nat.mul_zero, Nat.zero_add]
      calc progressBitG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) x.1 e u * 2 ^ PsiJ hpsi ring x.1
          ≤ 1 * 2 ^ PsiJ hpsi ring x.1 := Nat.mul_le_mul_right _ hpb
        _ ≤ 2 * 2 ^ PsiJ hpsi ring x.1 := Nat.mul_le_mul_right _ (by decide)
  have hsum := wordSum_mono_len _ _ hpoint
  rw [wordSum_add', wordSum_mul_l, wordSum_const'] at hsum
  have hsum2 : wordSum n (6 * n) (fun u =>
      progressBitG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) x.1 e u * 2 ^ PsiJ hpsi ring x.1) =
      2 ^ PsiJ hpsi ring x.1 * wordSum n (6 * n) (progressBitG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) x.1 e) := by
    rw [← wordSum_mul_l]
    apply wordSum_congr_len
    intro u _
    exact Nat.mul_comm _ _
  rw [hsum2] at hsum
  unfold weightedAlive
  unfold WF
  have hm2 := Nat.mul_le_mul_left (2 ^ PsiJ hpsi ring x.1) hmass
  -- 128 A ≤ 64 (2 * 2^p * N - 2^p * prog) and 64 * 2^p * prog ≥ 2^p * N
  have key : 128 * wordSum n (6 * n) (fun u => aliveBit (stepF hpsi hwidth hle ring) (GoodF hpsi ring) x u *
      2 ^ PsiJ hpsi ring (u.foldl (stepF hpsi hwidth hle ring) x).1) ≤
      127 * (2 ^ PsiJ hpsi ring x.1 * n ^ (6 * n)) := by
    have e1 : wordSum n (6 * n) (fun u => aliveBit (stepF hpsi hwidth hle ring) (GoodF hpsi ring) x u *
        WF hpsi ring (u.foldl (stepF hpsi hwidth hle ring) x)) =
        wordSum n (6 * n) (fun u => aliveBit (stepF hpsi hwidth hle ring) (GoodF hpsi ring) x u *
        2 ^ PsiJ hpsi ring (u.foldl (stepF hpsi hwidth hle ring) x).1) := rfl
    rw [e1] at hsum
    have e2 : 2 ^ PsiJ hpsi ring x.1 * (64 * wordSum n (6 * n)
        (progressBitG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) x.1 e)) =
        64 * (2 ^ PsiJ hpsi ring x.1 * wordSum n (6 * n)
        (progressBitG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) x.1 e)) := by ac_rfl
    rw [e2] at hm2
    have e3 : 2 * 2 ^ PsiJ hpsi ring x.1 * n ^ (6 * n) = 2 * (2 ^ PsiJ hpsi ring x.1 * n ^ (6 * n)) := by ac_rfl
    rw [e3] at hsum
    omega
  exact key

/-- Words with no physical service are alive. -/
theorem alive_of_noPhys (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n) :
    ∀ (u : List (Fin n)) (C : R1ConfigV6 n psi kappa tau), SpliceSafeV7g hpsi ring C →
      physCountG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) u C = 0 →
        AliveAlong (stepF hpsi hwidth hle ring) (GoodF hpsi ring) (C, false) u
  | [], _, hS, _ => ⟨rfl, hS⟩
  | e :: u, C, hS, h => by
      classical
      have h' : (if PhysicalServiceAt hpsi hwidth hle ring C (stepV10j hpsi hwidth hle ring C e) e then 1 else 0) +
          physCountG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) u (stepV10j hpsi hwidth hle ring C e) = 0 := h
      have hnp : ¬ PhysicalServiceAt hpsi hwidth hle ring C (stepV10j hpsi hwidth hle ring C e) e := by
        intro hp; rw [if_pos hp] at h'; omega
      rw [if_neg hnp, Nat.zero_add] at h'
      refine ⟨⟨rfl, hS⟩, ?_⟩
      have hst : stepF hpsi hwidth hle ring (C, false) e = (stepV10j hpsi hwidth hle ring C e, false) := by
        unfold stepF
        simp only [Bool.false_or, decide_eq_false hnp]
      rw [hst]
      exact alive_of_noPhys hpsi hwidth hle ring u _ (stepV10j_preserves_spliceSafeV7g hpsi hwidth hle ring C e hS) h'

noncomputable def noPhysBit (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (u : List (Fin n)) : Nat := by
  classical
  exact if physCountG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) u C = 0 then 1 else 0

/-- Geometric tail of the words without a physical service. -/
theorem noPhysical_tail (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n)
    (hn : 3 ≤ n) (C : R1ConfigV6 n psi kappa tau) (hS : SpliceSafeV7g hpsi ring C) (k : Nat) :
    128 ^ k * wordSum n (k * (6 * n)) (noPhysBit hpsi hwidth hle ring C) ≤
      127 ^ k * (2 ^ (7 * n) * n ^ (k * (6 * n))) := by
  classical
  have ht := weighted_tail (stepF hpsi hwidth hle ring) (GoodF hpsi ring) (WF hpsi ring) (6 * n) 127 128
    (block_escape hpsi hwidth hle ring hn) k (C, false) ⟨rfl, hS⟩
  have hmono : wordSum n (k * (6 * n)) (noPhysBit hpsi hwidth hle ring C) ≤
      weightedAlive (stepF hpsi hwidth hle ring) (GoodF hpsi ring) (WF hpsi ring) (C, false) (k * (6 * n)) := by
    unfold weightedAlive
    apply wordSum_mono_len
    intro u _
    unfold noPhysBit
    split
    · rename_i h0
      have hal := alive_of_noPhys hpsi hwidth hle ring u C hS h0
      have hab : aliveBit (stepF hpsi hwidth hle ring) (GoodF hpsi ring) (C, false) u = 1 := by
        unfold aliveBit; rw [if_pos hal]
      rw [hab, Nat.one_mul]
      exact Nat.one_le_two_pow
    · exact Nat.zero_le _
  have hW : WF hpsi ring (C, false) ≤ 2 ^ (7 * n) :=
    Nat.pow_le_pow_right (by decide) (PsiJ_le hpsi ring C)
  calc 128 ^ k * wordSum n (k * (6 * n)) (noPhysBit hpsi hwidth hle ring C)
      ≤ 128 ^ k * weightedAlive (stepF hpsi hwidth hle ring) (GoodF hpsi ring) (WF hpsi ring) (C, false)
          (k * (6 * n)) := Nat.mul_le_mul_left _ hmono
    _ ≤ 127 ^ k * (WF hpsi ring (C, false) * n ^ (k * (6 * n))) := ht
    _ ≤ 127 ^ k * (2 ^ (7 * n) * n ^ (k * (6 * n))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hW)

/-- `1/n` corollary: within `128 (7 n + log2 n + 1)` blocks of `6 n` letters, at most a `1/n` fraction of the
words avoid physical services. -/
theorem noPhysical_one_over_n (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n)
    (hn : 3 ≤ n) (C : R1ConfigV6 n psi kappa tau) (hS : SpliceSafeV7g hpsi ring C) :
    n * wordSum n (128 * (7 * n + (Nat.log2 n + 1)) * (6 * n)) (noPhysBit hpsi hwidth hle ring C) ≤
      n ^ (128 * (7 * n + (Nat.log2 n + 1)) * (6 * n)) := by
  let s := 7 * n + (Nat.log2 n + 1)
  let T := 128 * s * (6 * n)
  have ht := noPhysical_tail hpsi hwidth hle ring hn C hS (128 * s)
  have hbase : 2 * 127 ^ 128 ≤ 128 ^ 128 := by decide
  have hratio : 2 ^ s * 127 ^ (128 * s) ≤ 128 ^ (128 * s) := by
    have h1 : (2 * 127 ^ 128) ^ s ≤ (128 ^ 128) ^ s := Nat.pow_le_pow_left hbase s
    rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at h1
    exact h1
  have hnpow : n ≤ 2 ^ (Nat.log2 n + 1) := (LeaderCountDyadicTail.log_parameters n (by omega)).2.2.2
  have hsplit : 2 ^ s = 2 ^ (7 * n) * 2 ^ (Nat.log2 n + 1) := by
    show 2 ^ (7 * n + (Nat.log2 n + 1)) = _
    rw [Nat.pow_add]
  have hpos : 0 < 127 ^ (128 * s) * 2 ^ (7 * n) := Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
  apply Nat.le_of_mul_le_mul_left _ hpos
  calc 127 ^ (128 * s) * 2 ^ (7 * n) * (n * wordSum n T (noPhysBit hpsi hwidth hle ring C))
      ≤ 127 ^ (128 * s) * 2 ^ (7 * n) * (2 ^ (Nat.log2 n + 1) * wordSum n T (noPhysBit hpsi hwidth hle ring C)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hnpow)
    _ = (2 ^ s * 127 ^ (128 * s)) * wordSum n T (noPhysBit hpsi hwidth hle ring C) := by
        rw [hsplit]; ac_rfl
    _ ≤ 128 ^ (128 * s) * wordSum n T (noPhysBit hpsi hwidth hle ring C) := Nat.mul_le_mul_right _ hratio
    _ ≤ 127 ^ (128 * s) * (2 ^ (7 * n) * n ^ T) := ht
    _ = 127 ^ (128 * s) * 2 ^ (7 * n) * n ^ T := by ac_rfl

end Instance

end B9SpliceV10jPhysicalRate
