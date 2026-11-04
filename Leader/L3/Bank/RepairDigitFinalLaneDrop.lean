import Leader.L3.Bank.RepairDigitFinalLaneStep

/-!
# T18: delivery edge, progress existence and size of the lane rank

* `bankRepairDigitLaneDel`: the delivery edge `(L - 1, L)` never raises the lane rank, and
  drops it when a start exists and either a `D` is delivered or a `U` at `L - 1` turns into `D`.
* `bankRepairDigitLaneProgress`: off the receipt, either a final-block edge is active, the
  leader reset drops a positive weight, or a start exists and the delimiter waits empty.
* `bankRepairDigitPipeProgress`: the previous block's pipeline always has a progress edge
  (it is perpetual): a deliverable token at `L - 1`, or an edge lowering `Φ`.
-/

namespace L3.RenewalReferenceClock

set_option autoImplicit false

theorem bankRepairDigitLaneRankCongr (R m : Nat) (out out' : Nat → BankRepairDigitOutSh)
    (inp inp' : Nat → BankRepairDigitInSh) (lv lv' : Nat → Bool)
    (hoo : ∀ i, i < R → out' i = out i)
    (ho : ∀ k, k < m → inp' k = inp k ∧ lv' k = lv k) :
    bankRepairDigitLaneRank R m out' inp' lv' = bankRepairDigitLaneRank R m out inp lv := by
  have hs : ∀ k, k < m → bankRepairDigitStartOf inp' lv' k = bankRepairDigitStartOf inp lv k := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0]; rfl
    rw [bankRepairDigitStartOfPos _ _ _ h0, bankRepairDigitStartOfPos _ _ _ h0]
    obtain ⟨c1, c2⟩ := ho k hk
    obtain ⟨c3, c4⟩ := ho (k - 1) (by omega)
    rw [c1, c2, c3, c4]
  have hl : bankRepairDigitLastStart m inp' lv' = bankRepairDigitLastStart m inp lv :=
    bankRepairDigitLastOfCongr _ _ m hs
  have hlm : bankRepairDigitLastStart m inp lv ≤ m := bankRepairDigitLastOfLe _ m
  have hn : bankRepairDigitNeedOf m inp' lv' = bankRepairDigitNeedOf m inp lv := by
    unfold bankRepairDigitNeedOf
    rw [hl]
    apply bankRepairDigitSumCntCongr
    intro k _ hk2
    unfold bankRepairDigitNeedG
    obtain ⟨c1, c2⟩ := ho k (by omega)
    rw [hs k (by omega), c1, c2]
  have hp : bankRepairDigitPhiOf R out' = bankRepairDigitPhiOf R out :=
    bankRepairDigitMinCntCongr _ _ _ _ (fun i hi => by simp only [hoo i hi])
  have hlam : ∀ s, bankRepairDigitLamOf m s inp' lv' = bankRepairDigitLamOf m s inp lv := by
    intro s
    apply bankRepairDigitSumCntCongr
    intro k _ hk2
    obtain ⟨c1, c2⟩ := ho k (by omega)
    simp only [c1, c2]
  unfold bankRepairDigitLaneRank
  rw [hl, hn, hp, hlam]

theorem bankRepairDigitClsEPLive (i : BankRepairDigitInSh) : bankRepairDigitClsEP i true = false := by
  cases i <;> rfl

theorem bankRepairDigitClsOPLive (i : BankRepairDigitInSh) : bankRepairDigitClsOP i true = false := by
  cases i <;> rfl

theorem bankRepairDigitLamLiveE (m j : Nat) (s : Bool) (i : BankRepairDigitInSh) :
    bankRepairDigitLam m j s .E true ≤ bankRepairDigitLam m j s i true := by
  unfold bankRepairDigitLam
  exact Nat.add_le_add_left (Nat.zero_le _) _

theorem bankRepairDigitLamPLe (m : Nat) (s T : Bool) :
    bankRepairDigitLam m 0 s (.P T) false ≤ bankRepairDigitLam m 0 s .E false + (m + 2) := by
  cases s <;> simp [bankRepairDigitLam, bankRepairDigitLamIn]

theorem bankRepairDigitLamPOff (m : Nat) (T : Bool) :
    bankRepairDigitLam m 0 false (.P T) false = 0 := by
  simp [bankRepairDigitLam, bankRepairDigitLamIn]

theorem bankRepairDigitPhiWPos (R i : Nat) (hi : i + 1 < R) (o : BankRepairDigitOutSh) :
    1 ≤ bankRepairDigitPhiW R i o := by
  cases o <;> simp [bankRepairDigitPhiW] <;> omega

/-! ### The delivery edge -/

theorem bankRepairDigitLaneDel (R m : Nat) (hR : 1 ≤ R) (hm : 1 ≤ m)
    (out out' : Nat → BankRepairDigitOutSh) (inp inp' : Nat → BankRepairDigitInSh)
    (lv lv' : Nat → Bool)
    (hoo : ∀ i, i < R → i ≠ R - 1 → out' i = out i)
    (ho : ∀ k, k < m → k ≠ 0 → inp' k = inp k ∧ lv' k = lv k)
    (hr : (out' (R - 1), inp' 0, lv' 0) =
      bankRepairDigitDelStep (out (R - 1)) (inp 0) (lv 0)) :
    bankRepairDigitLaneRank R m out' inp' lv' +
      (if 0 < bankRepairDigitLastStart m inp lv ∧
          ((bankRepairDigitIsDSh (out (R - 1)) = true ∧ inp 0 = .E ∧ lv 0 = false) ∨
            out (R - 1) = .U) then 1 else 0) ≤
    bankRepairDigitLaneRank R m out inp lv := by
  have e1 : out' (R - 1) = (bankRepairDigitDelStep (out (R - 1)) (inp 0) (lv 0)).1 := by
    rw [← hr]
  have e2 : inp' 0 = (bankRepairDigitDelStep (out (R - 1)) (inp 0) (lv 0)).2.1 := by
    rw [← hr]
  have e3 : lv' 0 = (bankRepairDigitDelStep (out (R - 1)) (inp 0) (lv 0)).2.2 := by
    rw [← hr]
  have hsame : bankRepairDigitClsEP (inp' 0) (lv' 0) = bankRepairDigitClsEP (inp 0) (lv 0) →
      ∀ k, k < m → bankRepairDigitStartOf inp' lv' k = bankRepairDigitStartOf inp lv k := by
    intro hEP k hk
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0]; rfl
    rw [bankRepairDigitStartOfPos _ _ _ h0, bankRepairDigitStartOfPos _ _ _ h0]
    obtain ⟨c1, c2⟩ := ho k hk (by omega)
    rw [c1, c2]
    by_cases hk1 : k = 1
    · rw [hk1, show 1 - 1 = 0 from rfl, hEP]
    · obtain ⟨c3, c4⟩ := ho (k - 1) (by omega) (by omega)
      rw [c3, c4]
  have hlm : bankRepairDigitLastStart m inp lv ≤ m := bankRepairDigitLastOfLe _ m
  by_cases hdel : bankRepairDigitIsDSh (out (R - 1)) = true ∧ inp 0 = .E ∧ lv 0 = false
  · obtain ⟨hD, hi, hk⟩ := hdel
    obtain ⟨T, hT⟩ : ∃ T, out (R - 1) = .D T := by
      cases h : out (R - 1) with
      | D T => exact ⟨T, rfl⟩
      | _ => rw [h] at hD; exact absurd hD (by decide)
    rw [hT, hi, hk] at e2 e3
    have hi' : inp' 0 = .P T := by rw [e2]; rfl
    have hk' : lv' 0 = false := by rw [e3]; rfl
    have hst := hsame (by rw [hi', hk', hi, hk]; rfl)
    have hls : bankRepairDigitLastStart m inp' lv' = bankRepairDigitLastStart m inp lv :=
      bankRepairDigitLastOfCongr _ _ m hst
    have hphi : bankRepairDigitPhiOf R out' ≤ 2 * R := bankRepairDigitMinCntCap _ _ _
    have hgo : ∀ k, k < m → k ≠ 0 → bankRepairDigitNeedG inp' lv' k = bankRepairDigitNeedG inp lv k := by
      intro k hk1 hk2
      unfold bankRepairDigitNeedG
      obtain ⟨c1, c2⟩ := ho k hk1 hk2
      rw [hst k hk1, c1, c2]
    have hg0 : bankRepairDigitNeedG inp' lv' 0 + 1 ≤ bankRepairDigitNeedG inp lv 0 := by
      unfold bankRepairDigitNeedG
      rw [hi', hk', hi, hk]
      simp [bankRepairDigitStartOf, bankRepairDigitClsOP]
    by_cases hp : 0 < bankRepairDigitLastStart m inp lv
    · have hneed : bankRepairDigitNeedOf m inp' lv' + 1 ≤ bankRepairDigitNeedOf m inp lv := by
        unfold bankRepairDigitNeedOf
        rw [hls]
        exact bankRepairDigitSumCntPoint _ _ 0 0 1 _
          (fun i _ h2 h3 => Nat.le_of_eq (hgo i (by omega) h3)) (Nat.le_refl 0) (by omega) hg0
      have hlam : bankRepairDigitLamOf m true inp' lv' ≤
          bankRepairDigitLamOf m true inp lv + (m + 2) := by
        apply bankRepairDigitSumCntPointUp _ _ 0 0 (m + 2) m
        · intro i _ h2 h3
          obtain ⟨c1, c2⟩ := ho i (by omega) h3
          simp only [c1, c2, Nat.le_refl]
        · show bankRepairDigitLam m 0 true (inp' 0) (lv' 0) ≤
            bankRepairDigitLam m 0 true (inp 0) (lv 0) + (m + 2)
          rw [hi', hk', hi, hk]
          exact bankRepairDigitLamPLe m true T
      have hr1 : bankRepairDigitLaneRank R m out' inp' lv' =
          (2 * R + m + 3) * bankRepairDigitNeedOf m inp' lv' + bankRepairDigitPhiOf R out' +
            bankRepairDigitLamOf m true inp' lv' := by
        unfold bankRepairDigitLaneRank
        rw [hls, if_pos hp, decide_eq_true hp]
      have hr0 : bankRepairDigitLaneRank R m out inp lv =
          (2 * R + m + 3) * bankRepairDigitNeedOf m inp lv + bankRepairDigitPhiOf R out +
            bankRepairDigitLamOf m true inp lv := by
        unfold bankRepairDigitLaneRank
        rw [if_pos hp, decide_eq_true hp]
      rw [hr1, hr0, if_pos ⟨hp, Or.inl ⟨hD, hi, hk⟩⟩]
      have h1 := Nat.mul_le_mul_left (2 * R + m + 3) hneed
      rw [Nat.mul_add, Nat.mul_one] at h1
      omega
    · have hz : bankRepairDigitLastStart m inp lv = 0 := by omega
      have hn0 : bankRepairDigitNeedOf m inp' lv' = 0 := by
        unfold bankRepairDigitNeedOf
        rw [hls, hz]
        rfl
      have hlam : bankRepairDigitLamOf m false inp' lv' ≤ bankRepairDigitLamOf m false inp lv := by
        apply bankRepairDigitSumCntMono
        intro i _ h2
        by_cases h3 : i = 0
        · rw [h3]
          show bankRepairDigitLam m 0 false (inp' 0) (lv' 0) ≤
            bankRepairDigitLam m 0 false (inp 0) (lv 0)
          rw [hi', hk', bankRepairDigitLamPOff]
          exact Nat.zero_le _
        · obtain ⟨c1, c2⟩ := ho i (by omega) h3
          simp only [c1, c2, Nat.le_refl]
      have hr1 : bankRepairDigitLaneRank R m out' inp' lv' =
          (2 * R + m + 3) * 0 + 0 + bankRepairDigitLamOf m false inp' lv' := by
        unfold bankRepairDigitLaneRank
        rw [hls, if_neg hp, decide_eq_false hp, hn0]
      have hr0 : bankRepairDigitLaneRank R m out inp lv =
          (2 * R + m + 3) * bankRepairDigitNeedOf m inp lv + 0 +
            bankRepairDigitLamOf m false inp lv := by
        unfold bankRepairDigitLaneRank
        rw [if_neg hp, decide_eq_false hp]
      rw [hr1, hr0, if_neg (fun h => hp h.1)]
      omega
  · have hc := bankRepairDigitDelStepCls (out (R - 1)) (inp 0) (lv 0)
    rw [← e1, ← e2, ← e3] at hc
    rcases hc with ⟨hD, hi, hk, _, _⟩ | ⟨hin, hk', hout⟩
    · exact absurd ⟨hD, hi, hk⟩ hdel
    have hEP : bankRepairDigitClsEP (inp' 0) (lv' 0) = bankRepairDigitClsEP (inp 0) (lv 0) := by
      rcases hin with h | ⟨h1, h2⟩
      · rw [h, hk']
      · rw [h2, hk', h1, bankRepairDigitClsEPLive, bankRepairDigitClsEPLive]
    have hOP : bankRepairDigitClsOP (inp' 0) (lv' 0) = bankRepairDigitClsOP (inp 0) (lv 0) := by
      rcases hin with h | ⟨h1, h2⟩
      · rw [h, hk']
      · rw [h2, hk', h1, bankRepairDigitClsOPLive, bankRepairDigitClsOPLive]
    have hst := hsame hEP
    have hls : bankRepairDigitLastStart m inp' lv' = bankRepairDigitLastStart m inp lv :=
      bankRepairDigitLastOfCongr _ _ m hst
    have hneed : bankRepairDigitNeedOf m inp' lv' = bankRepairDigitNeedOf m inp lv := by
      unfold bankRepairDigitNeedOf
      rw [hls]
      apply bankRepairDigitSumCntCongr
      intro k _ hk2
      unfold bankRepairDigitNeedG
      by_cases h0 : k = 0
      · rw [h0, hst 0 hm, hOP]
      · obtain ⟨c1, c2⟩ := ho k (by omega) h0
        rw [hst k (by omega), c1, c2]
    have hlamle : ∀ s, bankRepairDigitLamOf m s inp' lv' ≤ bankRepairDigitLamOf m s inp lv := by
      intro s
      apply bankRepairDigitSumCntMono
      intro k _ hk2
      by_cases h0 : k = 0
      · rw [h0]
        show bankRepairDigitLam m 0 s (inp' 0) (lv' 0) ≤ bankRepairDigitLam m 0 s (inp 0) (lv 0)
        rcases hin with h | ⟨h1, h2⟩
        · rw [h, hk']; exact Nat.le_refl _
        · rw [h2, hk', h1]; exact bankRepairDigitLamLiveE m 0 s _
      · obtain ⟨c1, c2⟩ := ho k (by omega) h0
        simp only [c1, c2, Nat.le_refl]
    have hw : bankRepairDigitPhiW R (R - 1) (out' (R - 1)) ≤
        bankRepairDigitPhiW R (R - 1) (out (R - 1)) := by
      rcases hout with h | ⟨h1, h2⟩
      · rw [h]; exact Nat.le_refl _
      · rw [h2, h1]
        show 2 * (R - 1 - (R - 1)) ≤ 2 * (R - 1 - (R - 1)) + 1
        omega
    have hphi : bankRepairDigitPhiOf R out' ≤ bankRepairDigitPhiOf R out := by
      apply bankRepairDigitMinCntMono
      intro i hi
      by_cases h : i = R - 1
      · rw [h]; exact hw
      · simp only [hoo i hi h, Nat.le_refl]
    have hl2 := hlamle (decide (0 < bankRepairDigitLastStart m inp lv))
    unfold bankRepairDigitLaneRank
    rw [hls, hneed]
    by_cases hU : 0 < bankRepairDigitLastStart m inp lv ∧ out (R - 1) = .U
    · have hc : 0 < bankRepairDigitLastStart m inp lv ∧
          ((bankRepairDigitIsDSh (out (R - 1)) = true ∧ inp 0 = .E ∧ lv 0 = false) ∨
            out (R - 1) = .U) := ⟨hU.1, Or.inr hU.2⟩
      rw [if_pos hc]
      simp only [if_pos hU.1]
      have hD' : out' (R - 1) = .D false := by rw [e1, hU.2]; rfl
      have a1 := bankRepairDigitMinCntLe (fun i => bankRepairDigitPhiW R i (out' i)) (2 * R) R
        (R - 1) (by omega)
      have a2 : 1 ≤ bankRepairDigitPhiOf R out := by
        apply bankRepairDigitMinCntGe _ _ _ (by omega)
        intro i hi
        by_cases h : i = R - 1
        · show 1 ≤ bankRepairDigitPhiW R i (out i)
          rw [h, hU.2]
          show 1 ≤ 2 * (R - 1 - (R - 1)) + 1
          omega
        · exact bankRepairDigitPhiWPos R i (by omega) _
      have a3 : bankRepairDigitPhiW R (R - 1) (out' (R - 1)) = 0 := by
        rw [hD']
        show 2 * (R - 1 - (R - 1)) = 0
        omega
      unfold bankRepairDigitPhiOf at a2 ⊢
      omega
    · have hc : ¬ (0 < bankRepairDigitLastStart m inp lv ∧
          ((bankRepairDigitIsDSh (out (R - 1)) = true ∧ inp 0 = .E ∧ lv 0 = false) ∨
            out (R - 1) = .U)) := fun h => by
        rcases h.2 with h2 | h2
        · exact hdel h2
        · exact hU ⟨h.1, h2⟩
      rw [if_neg hc]
      have : (if 0 < bankRepairDigitLastStart m inp lv then bankRepairDigitPhiOf R out' else 0) ≤
          (if 0 < bankRepairDigitLastStart m inp lv then bankRepairDigitPhiOf R out else 0) := by
        split <;> omega
      omega

/-! ### Progress inside the final block -/

theorem bankRepairDigitFinIdle (s bx : Bool) (x : BankRepairDigitInSh) (kx : Bool)
    (y : BankRepairDigitInSh) (ky : Bool)
    (h : bankRepairDigitFinActive s bx x kx y ky = false) :
    kx = false ∧ x ≠ .X ∧ (∀ T, x = .S T → bx = false ∧ T = false) ∧
      (s = true → bankRepairDigitIsPSh x = true →
        ky = true ∨ y = .X ∨ bankRepairDigitIsPSh y = true) := by
  revert h
  cases s <;> cases bx <;> rcases x with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> cases kx <;>
    rcases y with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> cases ky <;> decide

theorem bankRepairDigitLamIdle (m j : Nat) (hj : j < m) (s : Bool) (x : BankRepairDigitInSh)
    (k : Bool) (h : bankRepairDigitLam m j s x k = 0) :
    k = false ∧ x ≠ .X ∧ (∀ T, x = .S T → j ≠ 0 ∧ T = false) ∧
      (s = true → bankRepairDigitIsPSh x = false) := by
  have hmj : 1 ≤ m - j := by omega
  unfold bankRepairDigitLam at h
  cases k
  · simp only [Bool.false_eq_true, if_false, Nat.zero_add] at h
    refine ⟨rfl, ?_, ?_, ?_⟩
    · rintro rfl
      simp [bankRepairDigitLamIn] at h
      omega
    · rintro T rfl
      simp only [bankRepairDigitLamIn] at h
      by_cases hj0 : j = 0
      · rw [if_pos hj0] at h; omega
      · rw [if_neg hj0] at h
        refine ⟨hj0, ?_⟩
        cases T
        · rfl
        · simp at h; all_goals omega
    · rintro rfl
      cases x <;> simp [bankRepairDigitLamIn, bankRepairDigitIsPSh] at h ⊢
      all_goals omega
  · simp only [if_true] at h
    omega

/-- Off the receipt, the final block has local progress or waits for a delivery. -/
theorem bankRepairDigitLaneProgress (m : Nat) (hm : 1 ≤ m) (inp : Nat → BankRepairDigitInSh)
    (lv : Nat → Bool) (hbad : ∃ j, j < m ∧ ¬ bankRepairDigitFinOKSh m j (inp j) (lv j)) :
    (∃ j, j + 1 < m ∧ bankRepairDigitFinActive (decide (0 < bankRepairDigitLastStart m inp lv))
        (decide (j = 0)) (inp j) (lv j) (inp (j + 1)) (lv (j + 1)) = true) ∨
      0 < bankRepairDigitLam m (m - 1) (decide (0 < bankRepairDigitLastStart m inp lv))
        (inp (m - 1)) (lv (m - 1)) ∨
      (0 < bankRepairDigitLastStart m inp lv ∧ inp 0 = .E ∧ lv 0 = false) := by
  generalize hs : decide (0 < bankRepairDigitLastStart m inp lv) = s
  by_cases h1 : ∃ j, j + 1 < m ∧
      bankRepairDigitFinActive s (decide (j = 0)) (inp j) (lv j) (inp (j + 1)) (lv (j + 1)) = true
  · exact Or.inl h1
  by_cases h2 : 0 < bankRepairDigitLam m (m - 1) s (inp (m - 1)) (lv (m - 1))
  · exact Or.inr (Or.inl h2)
  right; right
  have hA : ∀ j, j + 1 < m →
      bankRepairDigitFinActive s (decide (j = 0)) (inp j) (lv j) (inp (j + 1)) (lv (j + 1)) =
        false := by
    intro j hj
    cases h : bankRepairDigitFinActive s (decide (j = 0)) (inp j) (lv j) (inp (j + 1))
      (lv (j + 1))
    · rfl
    · exact absurd ⟨j, hj, h⟩ h1
  have hB := bankRepairDigitLamIdle m (m - 1) (by omega) s (inp (m - 1)) (lv (m - 1)) (by omega)
  have hlv : ∀ j, j < m → lv j = false := by
    intro j hj
    by_cases hj1 : j + 1 < m
    · exact (bankRepairDigitFinIdle _ _ _ _ _ _ (hA j hj1)).1
    · rw [show j = m - 1 by omega]; exact hB.1
  have hX : ∀ j, j < m → inp j ≠ .X := by
    intro j hj
    by_cases hj1 : j + 1 < m
    · exact (bankRepairDigitFinIdle _ _ _ _ _ _ (hA j hj1)).2.1
    · rw [show j = m - 1 by omega]; exact hB.2.1
  have hS : ∀ j, j < m → ∀ T, inp j = .S T → j ≠ 0 ∧ T = false := by
    intro j hj T hT
    by_cases hj1 : j + 1 < m
    · obtain ⟨a, b⟩ := (bankRepairDigitFinIdle _ _ _ _ _ _ (hA j hj1)).2.2.1 T hT
      exact ⟨fun h => by rw [h] at a; exact absurd a (by decide), b⟩
    · have hjm : j = m - 1 := by omega
      rw [hjm] at hT ⊢
      exact hB.2.2.1 T hT
  cases s
  · -- no start: every site is `E` or `P` with the carry off
    exfalso
    have hz : bankRepairDigitLastStart m inp lv = 0 := by
      have := of_decide_eq_false hs
      omega
    have hep : ∀ j, j < m → bankRepairDigitClsEP (inp j) (lv j) = true := by
      intro j
      induction j with
      | zero =>
          intro hj
          rw [hlv 0 hj]
          cases h : inp 0 with
          | E => rfl
          | P T => rfl
          | X => exact absurd h (hX 0 hj)
          | S T => exact absurd rfl (hS 0 hj T h).1
      | succ j ih =>
          intro hj
          rw [hlv (j + 1) hj]
          cases h : inp (j + 1) with
          | E => rfl
          | P T => rfl
          | X => exact absurd h (hX (j + 1) hj)
          | S T =>
              exfalso
              have hT := (hS (j + 1) hj T h).2
              have hst : bankRepairDigitStartOf inp lv (j + 1) = true := by
                show (bankRepairDigitClsOS (inp (j + 1)) (lv (j + 1)) &&
                  bankRepairDigitClsEP (inp j) (lv j)) = true
                rw [ih (by omega), h, hT, hlv (j + 1) hj]
                rfl
              have := bankRepairDigitLastOfGe _ m (j + 1) hj hst
              unfold bankRepairDigitLastStart at hz
              omega
    obtain ⟨j, hj, hn⟩ := hbad
    exact hn (Or.inr (hep j hj))
  · have hp : 0 < bankRepairDigitLastStart m inp lv := of_decide_eq_true hs
    have hnoP : ∀ d j, j + d = m - 1 → bankRepairDigitIsPSh (inp j) = false := by
      intro d
      induction d with
      | zero =>
          intro j hj
          rw [show j = m - 1 by omega]
          exact hB.2.2.2 rfl
      | succ d ih =>
          intro j hj
          cases hP : bankRepairDigitIsPSh (inp j)
          · rfl
          · exfalso
            rcases (bankRepairDigitFinIdle _ _ _ _ _ _ (hA j (by omega))).2.2.2 rfl hP with
              h | h | h
            · rw [hlv (j + 1) (by omega)] at h; exact Bool.noConfusion h
            · exact hX (j + 1) (by omega) h
            · rw [ih (j + 1) (by omega)] at h; exact Bool.noConfusion h
    refine ⟨hp, ?_, hlv 0 hm⟩
    cases h : inp 0 with
    | E => rfl
    | X => exact absurd h (hX 0 hm)
    | S T => exact absurd rfl (hS 0 hm T h).1
    | P T =>
        have := hnoP (m - 1) 0 (by omega)
        rw [h] at this
        simp [bankRepairDigitIsPSh] at this

/-! ### The perpetual pipeline -/

theorem bankRepairDigitPipeCapLocal (R : Nat) (hR : 2 ≤ R) (o1 o2 : BankRepairDigitOutSh) :
    min (bankRepairDigitPhiW R 0 (bankRepairDigitPipeStep true o1 o2).1)
        (bankRepairDigitPhiW R 1 (bankRepairDigitPipeStep true o1 o2).2) < 2 * R := by
  rcases o1 with _ | _ | ⟨_ | _⟩ <;> rcases o2 with _ | _ | ⟨_ | _⟩ <;>
    simp [bankRepairDigitPipeStep, bankRepairDigitPhiW] <;> omega

theorem bankRepairDigitPipeMinLocal (R i : Nat) (hi : i + 1 < R) (bx : Bool)
    (o1 o2 : BankRepairDigitOutSh) (h1 : o1 ≠ .E)
    (h2 : bankRepairDigitPhiW R i o1 ≤ bankRepairDigitPhiW R (i + 1) o2) :
    min (bankRepairDigitPhiW R i (bankRepairDigitPipeStep bx o1 o2).1)
        (bankRepairDigitPhiW R (i + 1) (bankRepairDigitPipeStep bx o1 o2).2) <
      bankRepairDigitPhiW R i o1 := by
  rcases o1 with _ | _ | ⟨_ | _⟩ <;> rcases o2 with _ | _ | ⟨_ | _⟩ <;> cases bx <;>
    simp [bankRepairDigitPipeStep, bankRepairDigitPhiW] at h1 h2 ⊢ <;> omega

/-- The previous block always offers progress: a token at `L - 1` to deliver, or a pipeline
edge lowering `Φ`. -/
theorem bankRepairDigitPipeProgress (R : Nat) (hR : 2 ≤ R) (out : Nat → BankRepairDigitOutSh) :
    (bankRepairDigitIsDSh (out (R - 1)) = true ∨ out (R - 1) = .U) ∨
      ∃ i, i + 1 < R ∧
        min (bankRepairDigitPhiW R i
              (bankRepairDigitPipeStep (decide (i = 0)) (out i) (out (i + 1))).1)
            (bankRepairDigitPhiW R (i + 1)
              (bankRepairDigitPipeStep (decide (i = 0)) (out i) (out (i + 1))).2) <
          bankRepairDigitPhiOf R out := by
  by_cases hl : bankRepairDigitIsDSh (out (R - 1)) = true ∨ out (R - 1) = .U
  · exact Or.inl hl
  right
  have hE : out (R - 1) = .E := by
    cases h : out (R - 1) with
    | E => rfl
    | U => exact absurd (Or.inr h) hl
    | D T => rw [h] at hl; exact absurd (Or.inl rfl) hl
  have hcap : bankRepairDigitPhiOf R out = 2 * R →
      ∃ i, i + 1 < R ∧
        min (bankRepairDigitPhiW R i
              (bankRepairDigitPipeStep (decide (i = 0)) (out i) (out (i + 1))).1)
            (bankRepairDigitPhiW R (i + 1)
              (bankRepairDigitPipeStep (decide (i = 0)) (out i) (out (i + 1))).2) <
          bankRepairDigitPhiOf R out := by
    intro h
    refine ⟨0, by omega, ?_⟩
    rw [h]
    exact bankRepairDigitPipeCapLocal R hR (out 0) (out 1)
  rcases bankRepairDigitMinCntAttain (fun i => bankRepairDigitPhiW R i (out i)) (2 * R) R with
    h | ⟨i, hi, h⟩
  · exact hcap h
  · by_cases hiE : out i = .E
    · apply hcap
      unfold bankRepairDigitPhiOf
      rw [h]
      show bankRepairDigitPhiW R i (out i) = 2 * R
      rw [hiE]
      rfl
    · have hiR : i + 1 < R := by
        rcases Nat.lt_or_ge (i + 1) R with h' | h'
        · exact h'
        · exfalso
          have : i = R - 1 := by omega
          rw [this] at hiE
          exact hiE hE
      refine ⟨i, hiR, ?_⟩
      have h2 := bankRepairDigitMinCntLe (fun i => bankRepairDigitPhiW R i (out i)) (2 * R) R
        (i + 1) hiR
      unfold bankRepairDigitPhiOf
      rw [h]
      rw [h] at h2
      exact bankRepairDigitPipeMinLocal R i hiR _ (out i) (out (i + 1)) hiE h2

/-! ### Size of the lane rank -/

theorem bankRepairDigitLaneRankLe (R m : Nat) (out : Nat → BankRepairDigitOutSh)
    (inp : Nat → BankRepairDigitInSh) (lv : Nat → Bool) :
    bankRepairDigitLaneRank R m out inp lv ≤
      (2 * R + m + 3) * (m * m) + 2 * R + m * (2 * m + 2) := by
  have hls : bankRepairDigitLastStart m inp lv ≤ m := bankRepairDigitLastOfLe _ m
  have hneed : bankRepairDigitNeedOf m inp lv ≤ m * m := by
    unfold bankRepairDigitNeedOf
    have h1 := bankRepairDigitSumCntExtend (bankRepairDigitNeedG inp lv) (fun _ => m) 0
      (bankRepairDigitLastStart m inp lv) m hls
      (fun i _ h2 => by
        have := bankRepairDigitNeedGLe inp lv i
        show bankRepairDigitNeedG inp lv i ≤ m
        omega)
    have h2 := bankRepairDigitSumCntBound (fun _ => m) 0 m m (fun _ _ _ => Nat.le_refl _)
    omega
  have hphi : bankRepairDigitPhiOf R out ≤ 2 * R := bankRepairDigitMinCntCap _ _ _
  have hlam : ∀ s, bankRepairDigitLamOf m s inp lv ≤ m * (2 * m + 2) := fun s =>
    bankRepairDigitSumCntBound _ 0 _ m (fun j _ _ => bankRepairDigitLamLe m j s _ _)
  have h1 := Nat.mul_le_mul_left (2 * R + m + 3) hneed
  have h2 := hlam (decide (0 < bankRepairDigitLastStart m inp lv))
  unfold bankRepairDigitLaneRank
  split <;> omega

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankRepairDigitLaneRankCongr
#print axioms L3.RenewalReferenceClock.bankRepairDigitClsEPLive
#print axioms L3.RenewalReferenceClock.bankRepairDigitClsOPLive
#print axioms L3.RenewalReferenceClock.bankRepairDigitLamLiveE
#print axioms L3.RenewalReferenceClock.bankRepairDigitLamPLe
#print axioms L3.RenewalReferenceClock.bankRepairDigitLamPOff
#print axioms L3.RenewalReferenceClock.bankRepairDigitPhiWPos
#print axioms L3.RenewalReferenceClock.bankRepairDigitLaneDel
#print axioms L3.RenewalReferenceClock.bankRepairDigitFinIdle
#print axioms L3.RenewalReferenceClock.bankRepairDigitLamIdle
#print axioms L3.RenewalReferenceClock.bankRepairDigitLaneProgress
#print axioms L3.RenewalReferenceClock.bankRepairDigitPipeCapLocal
#print axioms L3.RenewalReferenceClock.bankRepairDigitPipeMinLocal
#print axioms L3.RenewalReferenceClock.bankRepairDigitPipeProgress
#print axioms L3.RenewalReferenceClock.bankRepairDigitLaneRankLe
