import Leader.Wu.Splice.HoldRepairAmortizedPotential

set_option autoImplicit false
set_option Elab.async false

/-! # V10j with leaders: at most `7 n` non-stutter services between physical services

`PsiJ C = Σ_i (cellWJ (C i) + (4 - bonusJ (C i) (C (i+1))))` is at most `7 n` (`PsiJ_le`).  On a ring with at least
three sites, a V10j service from a `SpliceSafeV7g` configuration that is not a physical service and changes the
configuration lowers `PsiJ` (`psiJ_drop`), by the row theorem `B9SpliceV10jAmortizedPotential.row_amortized`:
the two served cells and the served edge lose local potential, and the edge entering the served pair and the
edge leaving it keep or raise their bonus.  Hence along any word of non-physical, configuration-changing services
from a `SpliceSafeV7g` configuration the number of services is at most `PsiJ C ≤ 7 n` (`chain_length_le`,
`chain_length_le_seven_mul`), with or without leaders.  Every V10j service is a stutter, a physical service or
such a service. -/

namespace B9SpliceV10jAmortizedChain

open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceTableV10g B9SpliceTableV10j B9SpliceV10hControllerRowsSafe B9SpliceV10eTransparency
  B9SpliceV10jRowProgress B9SpliceV10jAmortizedPotential B9SpliceV10jGlobalProgress

variable {n psi width kappa tau : Nat}

/-! ## The potential -/

noncomputable def edgeTermJ (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (i : Fin n) :
    Nat :=
  cellWJ (C i) + (4 - bonusJ hpsi (C i) (C (ring.rightNeighbor i)))

noncomputable def PsiJ (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) : Nat :=
  (List.ofFn (edgeTermJ hpsi ring C)).sum

theorem ofFn_sum_le_mul : ∀ (m c : Nat) (f : Fin m → Nat), (∀ i, f i ≤ c) → (List.ofFn f).sum ≤ m * c
  | 0, _, _, _ => by simp
  | m + 1, c, f, h => by
    rw [List.ofFn_succ, List.sum_cons, Nat.succ_mul]
    have h1 := h 0
    have h2 := ofFn_sum_le_mul m c (fun i => f i.succ) (fun i => h i.succ)
    omega

theorem PsiJ_le (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) :
    PsiJ hpsi ring C ≤ 7 * n := by
  unfold PsiJ
  have h := ofFn_sum_le_mul n 7 (edgeTermJ hpsi ring C) (fun i => by
    unfold edgeTermJ
    have := cellWJ_le (C i)
    omega)
  omega

/-- Two indices: pointwise below elsewhere and strictly below on the pair gives a strictly smaller sum. -/
theorem ofFn_sum_two_lt (f g : Fin n → Nat) (e j : Fin n) (hej : e ≠ j)
    (hle : ∀ i, i ≠ e → i ≠ j → g i ≤ f i) (hlt : g e + g j < f e + f j) :
    (List.ofFn g).sum < (List.ofFn f).sum := by
  let M : Fin n → Nat := fun i => if i = e then f e else if i = j then f j else g i
  let N : Fin n → Nat := fun i => if i = e then f e else g i
  have h1 := B9SpliceTableV10d.ofFn_sum_split M f e (fun i hi => by
    by_cases hij : i = j
    · subst hij; simp [M, hi]
    · simp only [M, hi, hij, if_false]; exact hle i hi hij)
  have h2 := B9SpliceTableV10d.ofFn_sum_split g N e (fun i hi => by simp [N, hi])
  have h3 := B9SpliceTableV10d.ofFn_sum_split N M j (fun i hi => by
    by_cases hie : i = e
    · subst hie; simp [N, M]
    · simp [N, M, hie, hi])
  have hMe : M e = f e := by simp [M]
  have hNe : N e = f e := by simp [N]
  have hMj : M j = f j := by simp [M, Ne.symm hej]
  have hNj : N j = g j := by simp [N, Ne.symm hej]
  rw [hMe] at h1
  rw [hNe] at h2
  rw [hMj, hNj] at h3
  omega

/-! ## Ring facts -/

theorem rn_inj (ring : DirectedRing n) {a b : Fin n} (hab : ring.rightNeighbor a = ring.rightNeighbor b) : a = b := by
  apply Fin.ext
  have hv := congrArg Fin.val hab
  simp only [DirectedRing.rightNeighbor] at hv
  have ha := a.isLt
  have hb := b.isLt
  by_cases h1 : a.val + 1 < n
  · rw [Nat.mod_eq_of_lt h1] at hv
    by_cases h2 : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt h2] at hv; omega
    · have h3 : b.val + 1 = n := by omega
      rw [h3, Nat.mod_self] at hv; omega
  · have h3 : a.val + 1 = n := by omega
    rw [h3, Nat.mod_self] at hv
    by_cases h2 : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt h2] at hv; omega
    · omega

theorem rn_rn_ne (ring : DirectedRing n) (hn : 3 ≤ n) (e : Fin n) : ring.rightNeighbor (ring.rightNeighbor e) ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  have he := e.isLt
  by_cases h1 : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt h1] at hv
    by_cases h2 : e.val + 1 + 1 < n
    · rw [Nat.mod_eq_of_lt h2] at hv; omega
    · have h3 : e.val + 1 + 1 = n := by omega
      rw [h3, Nat.mod_self] at hv; omega
  · have h3 : e.val + 1 = n := by omega
    rw [h3, Nat.mod_self] at hv
    rw [Nat.mod_eq_of_lt (by omega : 0 + 1 < n)] at hv
    omega

/-! ## One service -/

theorem stepV10j_eq_writeAt (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) (hself : ring.rightNeighbor e ≠ e) :
    stepV10j hpsi hwidth hle ring C e =
      writeAt ring C e (rowV10j hpsi hwidth hle (C e) (C (ring.rightNeighbor e))) := by
  unfold stepV10j; rw [if_neg hself]

theorem psiJ_drop (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (hn : 3 ≤ n) (C : R1ConfigV6 n psi kappa tau) (hS : SpliceSafeV7g hpsi ring C)
    (e : Fin n)
    (hnp : ¬ PhysicalServiceAt hpsi hwidth hle ring C (stepV10j hpsi hwidth hle ring C e) e)
    (hch : stepV10j hpsi hwidth hle ring C e ≠ C) :
    PsiJ hpsi ring (stepV10j hpsi hwidth hle ring C e) < PsiJ hpsi ring C := by
  classical
  have hself := rightNeighbor_ne_of_two_le ring (by omega) e
  have hstep := stepV10j_eq_writeAt hpsi hwidth hle ring C e hself
  have hout := row_amortized hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) (hS.2.1 e) (hS.2.1 _)
  generalize rowV10j hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) = w at hstep hout
  rcases hout with hp | hsame | ⟨hlt, hf1, hf2⟩
  · exfalso
    apply hnp
    rw [hstep]
    have hw := physical_of_row hpsi hwidth hle ring C e hself (C e, C (ring.rightNeighbor e)) w hp
    rwa [B9SpliceV10hWholeStepSafe.writeAt_self] at hw
  · exfalso
    apply hch
    rw [hstep, hsame]
    exact B9SpliceV10hWholeStepSafe.writeAt_self ring C e
  · rw [hstep]
    unfold PsiJ
    apply ofFn_sum_two_lt _ _ e (ring.rightNeighbor e) (Ne.symm hself)
    · intro i hie hij
      unfold edgeTermJ
      rw [writeAt_other ring C e w i hie hij]
      by_cases hi1 : ring.rightNeighbor i = e
      · rw [hi1, writeAt_e]
        have hb : bonusJ hpsi (C i) (C e) ≤ bonusJ hpsi (C i) w.1 := by
          rcases hf1 with h | h
          · rw [h]; exact Nat.le_refl _
          · rw [bonusJ_right_zero hpsi _ _ h]; exact Nat.zero_le _
        omega
      · have hi2 : ring.rightNeighbor i ≠ ring.rightNeighbor e := fun h => hie (rn_inj ring h)
        rw [writeAt_other ring C e w _ hi1 hi2]
        exact Nat.le_refl _
    · unfold edgeTermJ
      have hjj : ring.rightNeighbor (ring.rightNeighbor e) ≠ e := rn_rn_ne ring hn e
      have hjj2 : ring.rightNeighbor (ring.rightNeighbor e) ≠ ring.rightNeighbor e :=
        rightNeighbor_ne_of_two_le ring (by omega) _
      rw [writeAt_other ring C e w _ hjj hjj2, writeAt_e, writeAt_j ring C e w hself]
      have hb : bonusJ hpsi (C (ring.rightNeighbor e)) (C (ring.rightNeighbor (ring.rightNeighbor e))) ≤
          bonusJ hpsi w.2 (C (ring.rightNeighbor (ring.rightNeighbor e))) := by
        rcases hf2 with h | h
        · rw [h]; exact Nat.le_refl _
        · rw [bonusJ_left_zero hpsi _ _ h]; exact Nat.zero_le _
      unfold LocalJ at hlt
      have := bonusJ_le hpsi (C (ring.rightNeighbor e)) (C (ring.rightNeighbor (ring.rightNeighbor e)))
      omega

/-! ## Chains -/

/-- Every service of the word is non-physical and changes the configuration. -/
def NonPhysChangingAlong (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n) :
    R1ConfigV6 n psi kappa tau → List (Fin n) → Prop
  | _, [] => True
  | C, e :: es =>
      ¬ PhysicalServiceAt hpsi hwidth hle ring C (stepV10j hpsi hwidth hle ring C e) e ∧
      stepV10j hpsi hwidth hle ring C e ≠ C ∧
      NonPhysChangingAlong hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring C e) es

theorem chain_length_le (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (hn : 3 ≤ n) (w : List (Fin n)) :
    ∀ C : R1ConfigV6 n psi kappa tau, SpliceSafeV7g hpsi ring C →
      NonPhysChangingAlong hpsi hwidth hle ring C w → w.length ≤ PsiJ hpsi ring C := by
  induction w with
  | nil => intro C _ _; exact Nat.zero_le _
  | cons e es ih =>
      intro C hS h
      have hd := psiJ_drop hpsi hwidth hle ring hn C hS e h.1 h.2.1
      have hrest := ih _ (stepV10j_preserves_spliceSafeV7g hpsi hwidth hle ring C e hS) h.2.2
      simp only [List.length_cons]
      omega

theorem chain_length_le_seven_mul (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (hn : 3 ≤ n) (w : List (Fin n)) (C : R1ConfigV6 n psi kappa tau)
    (hS : SpliceSafeV7g hpsi ring C) (h : NonPhysChangingAlong hpsi hwidth hle ring C w) :
    w.length ≤ 7 * n :=
  Nat.le_trans (chain_length_le hpsi hwidth hle ring hn w C hS h) (PsiJ_le hpsi ring C)

end B9SpliceV10jAmortizedChain
