import Leader.L3.Bank.RepairDigitFinalLane

/-!
# T18: the lane rank never rises, edge by edge

Each lemma takes the lane before and after one edge, given pointwise on the window, and bounds
the new rank by the old one minus the edge's progress bonus.
-/

namespace L3.RenewalReferenceClock

set_option autoImplicit false

theorem bankRepairDigitStartOfPos (inp : Nat → BankRepairDigitInSh) (lv : Nat → Bool) (k : Nat)
    (hk : 0 < k) :
    bankRepairDigitStartOf inp lv k =
      (bankRepairDigitClsOS (inp k) (lv k) && bankRepairDigitClsEP (inp (k - 1)) (lv (k - 1))) := by
  obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
  rfl

theorem bankRepairDigitStartOfZero (inp : Nat → BankRepairDigitInSh) (lv : Nat → Bool) :
    bankRepairDigitStartOf inp lv 0 = false := rfl

theorem bankRepairDigitClsLiveFalse (i : BankRepairDigitInSh) :
    bankRepairDigitClsOS i true = false ∧ bankRepairDigitClsEP i true = false ∧
      bankRepairDigitClsOP i true = false := by
  rcases i with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> decide

/-- Starts away from a two-point change are unchanged. -/
theorem bankRepairDigitStartFar (m j : Nat) (inp inp' : Nat → BankRepairDigitInSh)
    (lv lv' : Nat → Bool)
    (ho : ∀ k, k < m → k ≠ j → k ≠ j + 1 → inp' k = inp k ∧ lv' k = lv k)
    (k : Nat) (hk : k < m) (a : k ≠ j) (b : k ≠ j + 1) (d : k ≠ j + 2) :
    bankRepairDigitStartOf inp' lv' k = bankRepairDigitStartOf inp lv k := by
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · rw [h0]; rfl
  rw [bankRepairDigitStartOfPos _ _ _ h0, bankRepairDigitStartOfPos _ _ _ h0]
  obtain ⟨c1, c2⟩ := ho k hk a b
  obtain ⟨c3, c4⟩ := ho (k - 1) (by omega) (by omega) (by omega)
  rw [c1, c2, c3, c4]

/-- The need under a two-point change that creates no start and no non-packet. -/
theorem bankRepairDigitNeedTwoPoint (m j : Nat) (hj : j + 1 < m)
    (inp inp' : Nat → BankRepairDigitInSh) (lv lv' : Nat → Bool)
    (ho : ∀ k, k < m → k ≠ j → k ≠ j + 1 → inp' k = inp k ∧ lv' k = lv k)
    (n1 : bankRepairDigitClsOS (inp' j) (lv' j) = true → bankRepairDigitClsOS (inp j) (lv j) = true)
    (n2 : bankRepairDigitClsOS (inp' (j + 1)) (lv' (j + 1)) = true →
      bankRepairDigitClsEP (inp' j) (lv' j) = true →
      bankRepairDigitClsOS (inp (j + 1)) (lv (j + 1)) = true ∧
        bankRepairDigitClsEP (inp j) (lv j) = true)
    (n3 : bankRepairDigitClsEP (inp' (j + 1)) (lv' (j + 1)) = true →
      bankRepairDigitClsEP (inp (j + 1)) (lv (j + 1)) = true)
    (n4 : bankRepairDigitClsOP (inp j) (lv j) = true → bankRepairDigitClsOP (inp' j) (lv' j) = true)
    (n5 : bankRepairDigitClsOP (inp (j + 1)) (lv (j + 1)) = true →
      bankRepairDigitClsOP (inp' (j + 1)) (lv' (j + 1)) = true) :
    bankRepairDigitNeedOf m inp' lv' ≤ bankRepairDigitNeedOf m inp lv ∧
      bankRepairDigitLastStart m inp' lv' ≤ bankRepairDigitLastStart m inp lv := by
  have hs : ∀ k, k < m → bankRepairDigitStartOf inp' lv' k = true →
      bankRepairDigitStartOf inp lv k = true := by
    intro k hk h
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, bankRepairDigitStartOfZero] at h; exact absurd h (by decide)
    rw [bankRepairDigitStartOfPos _ _ _ h0, Bool.and_eq_true] at h ⊢
    obtain ⟨hA, hB⟩ := h
    by_cases a : k = j
    · obtain ⟨c1, c2⟩ := ho (k - 1) (by omega) (by omega) (by omega)
      rw [c1, c2] at hB
      refine ⟨?_, hB⟩
      rw [a] at hA ⊢
      exact n1 hA
    by_cases b : k = j + 1
    · rw [b] at hA hB ⊢
      simp only [Nat.add_sub_cancel] at hB ⊢
      exact n2 hA hB
    by_cases d : k = j + 2
    · rw [d] at hA hB ⊢
      rw [show j + 2 - 1 = j + 1 by omega] at hB ⊢
      obtain ⟨c1, c2⟩ := ho (j + 2) (by omega) (by omega) (by omega)
      rw [c1, c2] at hA
      exact ⟨hA, n3 hB⟩
    obtain ⟨c1, c2⟩ := ho k hk a b
    obtain ⟨c3, c4⟩ := ho (k - 1) (by omega) (by omega) (by omega)
    rw [c1, c2] at hA
    rw [c3, c4] at hB
    exact ⟨hA, hB⟩
  have hg : ∀ k, k < m → bankRepairDigitNeedG inp' lv' k ≤ bankRepairDigitNeedG inp lv k := by
    intro k hk
    have hsk := hs k hk
    have hok : bankRepairDigitClsOP (inp k) (lv k) = true →
        bankRepairDigitClsOP (inp' k) (lv' k) = true := by
      by_cases a : k = j
      · rw [a]; exact n4
      · by_cases b : k = j + 1
        · rw [b]; exact n5
        · obtain ⟨c1, c2⟩ := ho k hk a b
          rw [c1, c2]; exact id
    unfold bankRepairDigitNeedG
    cases h1 : bankRepairDigitStartOf inp' lv' k <;> cases h2 : bankRepairDigitStartOf inp lv k <;>
      cases h3 : bankRepairDigitClsOP (inp' k) (lv' k) <;>
      cases h4 : bankRepairDigitClsOP (inp k) (lv k) <;> simp_all
  exact ⟨bankRepairDigitNeedLe _ _ _ _ m hs hg, bankRepairDigitLastOfMono _ _ m hs⟩

/-- The need when a packet moves right onto an empty input. -/
theorem bankRepairDigitNeedMoveLane (m j : Nat) (hj : j + 1 < m)
    (inp inp' : Nat → BankRepairDigitInSh) (lv lv' : Nat → Bool)
    (ho : ∀ k, k < m → k ≠ j → k ≠ j + 1 → inp' k = inp k ∧ lv' k = lv k) (T : Bool)
    (a1 : inp j = .P T) (a2 : lv j = false) (a3 : inp (j + 1) = .E) (a4 : lv (j + 1) = false)
    (b1 : inp' j = .E) (b2 : lv' j = false) (b3 : inp' (j + 1) = .P T)
    (b4 : lv' (j + 1) = false) :
    bankRepairDigitNeedOf m inp' lv' ≤ bankRepairDigitNeedOf m inp lv ∧
      bankRepairDigitLastStart m inp' lv' ≤ bankRepairDigitLastStart m inp lv := by
  have hs : ∀ k, k < m → bankRepairDigitStartOf inp' lv' k = bankRepairDigitStartOf inp lv k := by
    intro k hk
    by_cases a : k = j
    · rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0]; rfl
      rw [bankRepairDigitStartOfPos _ _ _ h0, bankRepairDigitStartOfPos _ _ _ h0, a, a1, a2, b1, b2]
      rfl
    by_cases b : k = j + 1
    · rw [b, bankRepairDigitStartOfPos _ _ _ (by omega), bankRepairDigitStartOfPos _ _ _ (by omega),
        a3, a4, b3, b4]
      rfl
    by_cases d : k = j + 2
    · rw [d, bankRepairDigitStartOfPos _ _ _ (by omega), bankRepairDigitStartOfPos _ _ _ (by omega),
        show j + 2 - 1 = j + 1 by omega, a3, a4, b3, b4]
      obtain ⟨c1, c2⟩ := ho (j + 2) (by omega) (by omega) (by omega)
      rw [c1, c2]
      rfl
    exact bankRepairDigitStartFar m j inp inp' lv lv' ho k hk a b d
  have hl : bankRepairDigitLastStart m inp' lv' = bankRepairDigitLastStart m inp lv :=
    bankRepairDigitLastOfCongr _ _ m (fun k hk => hs k hk)
  refine ⟨?_, Nat.le_of_eq hl⟩
  have hsj : bankRepairDigitStartOf inp lv j = false := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0]; rfl
    rw [bankRepairDigitStartOfPos _ _ _ h0, a1, a2]; rfl
  have hsj1 : bankRepairDigitStartOf inp lv (j + 1) = false := by
    rw [bankRepairDigitStartOfPos _ _ _ (by omega), a3, a4]; rfl
  refine bankRepairDigitNeedMove _ _ _ _ m j (fun k hk => hs k hk) hsj1 ?_ ?_ ?_
  · unfold bankRepairDigitNeedG
    rw [hs j (by omega), hsj, a1, a2, b1, b2]
    rfl
  · unfold bankRepairDigitNeedG
    rw [hs (j + 1) hj, hsj1, a3, a4, b3, b4]
    rfl
  · intro k hk h1 h2
    unfold bankRepairDigitNeedG
    obtain ⟨c1, c2⟩ := ho k hk h1 h2
    rw [hs k hk, c1, c2]

/-- The need when a packet settles against a settled input. -/
theorem bankRepairDigitNeedSettleLane (m j : Nat) (hj : j + 1 < m)
    (inp inp' : Nat → BankRepairDigitInSh) (lv lv' : Nat → Bool)
    (ho : ∀ k, k < m → k ≠ j → k ≠ j + 1 → inp' k = inp k ∧ lv' k = lv k) (T T' : Bool)
    (a1 : inp j = .P T) (a2 : lv j = false) (a3 : inp (j + 1) = .S T') (a4 : lv (j + 1) = false)
    (b1 : inp' j = .S T) (b2 : lv' j = false) (b3 : inp' (j + 1) = .S T')
    (b4 : lv' (j + 1) = false) :
    bankRepairDigitNeedOf m inp' lv' ≤ bankRepairDigitNeedOf m inp lv ∧
      bankRepairDigitLastStart m inp' lv' ≤ bankRepairDigitLastStart m inp lv := by
  have hso : ∀ k, k < m → k ≠ j → k ≠ j + 1 →
      bankRepairDigitStartOf inp' lv' k = bankRepairDigitStartOf inp lv k := by
    intro k hk a b
    by_cases d : k = j + 2
    · obtain ⟨c1, c2⟩ := ho (j + 2) (by omega) (by omega) (by omega)
      rw [d, bankRepairDigitStartOfPos _ _ _ (by omega), bankRepairDigitStartOfPos _ _ _ (by omega),
        show j + 2 - 1 = j + 1 by omega, a3, a4, b3, b4, c1, c2]
    exact bankRepairDigitStartFar m j inp inp' lv lv' ho k hk a b d
  have hs1 : bankRepairDigitStartOf inp lv (j + 1) = true := by
    rw [bankRepairDigitStartOfPos _ _ _ (by omega), Nat.add_sub_cancel, a3, a4, a1, a2]; rfl
  have hs1' : bankRepairDigitStartOf inp' lv' (j + 1) = false := by
    rw [bankRepairDigitStartOfPos _ _ _ (by omega), Nat.add_sub_cancel, b3, b4, b1, b2]; rfl
  have hsj : bankRepairDigitStartOf inp lv j = false := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0]; rfl
    rw [bankRepairDigitStartOfPos _ _ _ h0, a1, a2]; rfl
  have r := bankRepairDigitNeedSettle (bankRepairDigitStartOf inp lv)
    (bankRepairDigitStartOf inp' lv') (bankRepairDigitNeedG inp lv)
    (bankRepairDigitNeedG inp' lv') m j hj hs1 hs1' hso ?_
    (bankRepairDigitNeedGLe inp' lv' j) ?_ ?_ ?_
  · exact r
  · unfold bankRepairDigitNeedG
    rw [hsj, a1, a2]; rfl
  · unfold bankRepairDigitNeedG
    rw [hs1, a3, a4]; rfl
  · unfold bankRepairDigitNeedG
    rw [hs1', b3, b4]; simp [bankRepairDigitClsOP]
  · intro k hk h1 h2
    unfold bankRepairDigitNeedG
    obtain ⟨c1, c2⟩ := ho k hk h1 h2
    rw [hso k hk h1 h2, c1, c2]

theorem bankRepairDigitIsPShE (x : BankRepairDigitInSh) (h : bankRepairDigitIsPSh x = true) :
    ∃ T, x = .P T := by
  cases x <;> simp_all [bankRepairDigitIsPSh]

theorem bankRepairDigitIsSShE (x : BankRepairDigitInSh) (h : bankRepairDigitIsSSh x = true) :
    ∃ T, x = .S T := by
  cases x <;> simp_all [bankRepairDigitIsSSh]

/-! ### The final-block edge -/

theorem bankRepairDigitLaneFin (R m j : Nat) (hj : j + 1 < m) (out : Nat → BankRepairDigitOutSh)
    (inp inp' : Nat → BankRepairDigitInSh) (lv lv' : Nat → Bool)
    (ho : ∀ k, k < m → k ≠ j → k ≠ j + 1 → inp' k = inp k ∧ lv' k = lv k)
    (hr : (inp' j, lv' j, inp' (j + 1), lv' (j + 1)) =
      bankRepairDigitFinStep (decide (j = 0)) (inp j) (lv j) (inp (j + 1)) (lv (j + 1))) :
    bankRepairDigitLaneRank R m out inp' lv' +
      (if bankRepairDigitFinActive (decide (0 < bankRepairDigitLastStart m inp lv))
          (decide (j = 0)) (inp j) (lv j) (inp (j + 1)) (lv (j + 1)) = true then 1 else 0) ≤
    bankRepairDigitLaneRank R m out inp lv := by
  have e1 : inp' j = (bankRepairDigitFinStep (decide (j = 0)) (inp j) (lv j) (inp (j + 1))
      (lv (j + 1))).1 := by rw [← hr]
  have e2 : lv' j = (bankRepairDigitFinStep (decide (j = 0)) (inp j) (lv j) (inp (j + 1))
      (lv (j + 1))).2.1 := by rw [← hr]
  have e3 : inp' (j + 1) = (bankRepairDigitFinStep (decide (j = 0)) (inp j) (lv j) (inp (j + 1))
      (lv (j + 1))).2.2.1 := by rw [← hr]
  have e4 : lv' (j + 1) = (bankRepairDigitFinStep (decide (j = 0)) (inp j) (lv j) (inp (j + 1))
      (lv (j + 1))).2.2.2 := by rw [← hr]
  have hc := bankRepairDigitFinStepCls (decide (j = 0)) (inp j) (lv j) (inp (j + 1)) (lv (j + 1))
  have hloc := bankRepairDigitFinLamLocal m j (decide (0 < bankRepairDigitLastStart m inp lv)) hj
    (inp j) (lv j) (inp (j + 1)) (lv (j + 1)) (by
      intro h1 h2
      have hst : bankRepairDigitStartOf inp lv (j + 1) = true := by
        rw [bankRepairDigitStartOfPos _ _ _ (by omega), Nat.add_sub_cancel, h2,
          bankRepairDigitClsOPEP _ _ h1]
        rfl
      have := bankRepairDigitLastOfGe _ m (j + 1) hj hst
      simp only [decide_eq_true_eq]
      unfold bankRepairDigitLastStart
      omega)
  rw [← e1, ← e2, ← e3, ← e4] at hc hloc
  have hnl : bankRepairDigitNeedOf m inp' lv' ≤ bankRepairDigitNeedOf m inp lv ∧
      bankRepairDigitLastStart m inp' lv' ≤ bankRepairDigitLastStart m inp lv := by
    rcases hc with ⟨n1, n2, n3, n4, n5⟩ | ⟨p1, p2, p3, p4, q1, q2, q3, q4⟩ |
        ⟨p1, p2, p3, p4, q1, q2, q3, q4⟩
    · exact bankRepairDigitNeedTwoPoint m j hj inp inp' lv lv' ho n1 n2 n3 n4 n5
    · obtain ⟨T, hT⟩ := bankRepairDigitIsPShE _ p1
      rw [hT] at q3
      exact bankRepairDigitNeedMoveLane m j hj inp inp' lv lv' ho T hT p2 p3 p4 q1 q2 q3 q4
    · obtain ⟨T, hT⟩ := bankRepairDigitIsPShE _ p1
      obtain ⟨T', hT'⟩ := bankRepairDigitIsSShE _ p3
      rw [hT] at q1
      rw [hT'] at q3
      exact bankRepairDigitNeedSettleLane m j hj inp inp' lv lv' ho T T' hT p2 hT' p4 q1 q2 q3 q4
  have hlam := bankRepairDigitSumCntPair
    (fun k => bankRepairDigitLam m k (decide (0 < bankRepairDigitLastStart m inp lv)) (inp' k)
      (lv' k))
    (fun k => bankRepairDigitLam m k (decide (0 < bankRepairDigitLastStart m inp lv)) (inp k)
      (lv k)) 0 j
    (if bankRepairDigitFinActive (decide (0 < bankRepairDigitLastStart m inp lv))
          (decide (j = 0)) (inp j) (lv j) (inp (j + 1)) (lv (j + 1)) = true then 1 else 0) m
    (fun k _ hk2 hk3 hk4 => by
      obtain ⟨c1, c2⟩ := ho k (by omega) hk3 hk4
      simp only [c1, c2, Nat.le_refl])
    (Nat.zero_le _) (by omega) hloc
  have := bankRepairDigitLaneRankAssemble R m out out inp inp' lv lv' 0 _ hnl.1 hnl.2
    (by
      have := hnl.2
      split <;> split <;> omega)
    hlam
  omega

/-! ### The reset of the last final position by the leader edge -/

theorem bankRepairDigitLaneReset (R m : Nat) (hm : 1 ≤ m) (out : Nat → BankRepairDigitOutSh)
    (inp inp' : Nat → BankRepairDigitInSh) (lv lv' : Nat → Bool)
    (ho : ∀ k, k < m → k ≠ m - 1 → inp' k = inp k ∧ lv' k = lv k)
    (hx : inp' (m - 1) = .E) (hl0 : lv' (m - 1) = false) :
    bankRepairDigitLaneRank R m out inp' lv' +
      bankRepairDigitLam m (m - 1) (decide (0 < bankRepairDigitLastStart m inp lv)) (inp (m - 1))
        (lv (m - 1)) ≤
    bankRepairDigitLaneRank R m out inp lv := by
  have hs : ∀ k, k < m → bankRepairDigitStartOf inp' lv' k = true →
      bankRepairDigitStartOf inp lv k = true := by
    intro k hk h
    by_cases a : k = m - 1
    · rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0, bankRepairDigitStartOfZero] at h; exact absurd h (by decide)
      rw [bankRepairDigitStartOfPos _ _ _ h0, a, hx, hl0] at h
      simp [bankRepairDigitClsOS] at h
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, bankRepairDigitStartOfZero] at h; exact absurd h (by decide)
    rw [bankRepairDigitStartOfPos _ _ _ h0] at h ⊢
    obtain ⟨c1, c2⟩ := ho k hk a
    obtain ⟨c3, c4⟩ := ho (k - 1) (by omega) (by omega)
    rw [c1, c2, c3, c4] at h
    exact h
  have hg : ∀ k, k + 1 < m → bankRepairDigitNeedG inp' lv' k ≤ bankRepairDigitNeedG inp lv k := by
    intro k hk
    have hsk : bankRepairDigitStartOf inp' lv' k = bankRepairDigitStartOf inp lv k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0]; rfl
      rw [bankRepairDigitStartOfPos _ _ _ h0, bankRepairDigitStartOfPos _ _ _ h0]
      obtain ⟨c1, c2⟩ := ho k (by omega) (by omega)
      obtain ⟨c3, c4⟩ := ho (k - 1) (by omega) (by omega)
      rw [c1, c2, c3, c4]
    unfold bankRepairDigitNeedG
    obtain ⟨c1, c2⟩ := ho k (by omega) (by omega)
    rw [hsk, c1, c2]
    exact Nat.le_refl _
  have hneed := bankRepairDigitNeedLeTop _ _ _ _ m hs hg
  have hlast := bankRepairDigitLastOfMono _ _ m hs
  have hlam := bankRepairDigitSumCntPoint
    (fun k => bankRepairDigitLam m k (decide (0 < bankRepairDigitLastStart m inp lv)) (inp' k)
      (lv' k))
    (fun k => bankRepairDigitLam m k (decide (0 < bankRepairDigitLastStart m inp lv)) (inp k)
      (lv k)) 0 (m - 1)
    (bankRepairDigitLam m (m - 1) (decide (0 < bankRepairDigitLastStart m inp lv)) (inp (m - 1))
        (lv (m - 1))) m
    (fun k _ hk2 hk3 => by
      obtain ⟨c1, c2⟩ := ho k (by omega) hk3
      simp only [c1, c2, Nat.le_refl])
    (Nat.zero_le _) (by omega) (by
      simp only [hx, hl0, bankRepairDigitLamEOff, Nat.zero_add, Nat.le_refl])
  have := bankRepairDigitLaneRankAssemble R m out out inp inp' lv lv' 0 _ hneed hlast
    (by
      unfold bankRepairDigitLastStart
      split <;> split <;> omega)
    hlam
  omega

/-! ### The pipeline edge inside the previous block -/

theorem bankRepairDigitLanePipe (R m i : Nat) (hi : i + 1 < R)
    (out out' : Nat → BankRepairDigitOutSh) (inp : Nat → BankRepairDigitInSh) (lv : Nat → Bool)
    (hoo : ∀ k, k < R → k ≠ i → k ≠ i + 1 → out' k = out k)
    (hr : (out' i, out' (i + 1)) = bankRepairDigitPipeStep (decide (i = 0)) (out i) (out (i + 1))) :
    bankRepairDigitLaneRank R m out' inp lv +
      (if 0 < bankRepairDigitLastStart m inp lv ∧
          min (bankRepairDigitPhiW R i (out' i)) (bankRepairDigitPhiW R (i + 1) (out' (i + 1))) <
            bankRepairDigitPhiOf R out then 1 else 0) ≤
    bankRepairDigitLaneRank R m out inp lv := by
  have hloc := bankRepairDigitPipePhiLocal R i hi (decide (i = 0)) (out i) (out (i + 1))
  rw [← hr] at hloc
  have hphi : bankRepairDigitPhiOf R out' ≤ bankRepairDigitPhiOf R out :=
    bankRepairDigitMinCntPair _ _ (2 * R) R i hi
      (fun k hk h1 h2 => by simp only [hoo k hk h1 h2]) hloc
  have a1 := bankRepairDigitMinCntLe (fun k => bankRepairDigitPhiW R k (out' k)) (2 * R) R i
    (by omega)
  have a2 := bankRepairDigitMinCntLe (fun k => bankRepairDigitPhiW R k (out' k)) (2 * R) R (i + 1)
    hi
  have := bankRepairDigitLaneRankAssemble R m out out' inp inp lv lv
    (if 0 < bankRepairDigitLastStart m inp lv ∧
          min (bankRepairDigitPhiW R i (out' i)) (bankRepairDigitPhiW R (i + 1) (out' (i + 1))) <
            bankRepairDigitPhiOf R out then 1 else 0) 0 (Nat.le_refl _) (Nat.le_refl _)
    (by
      unfold bankRepairDigitPhiOf at hphi ⊢
      split <;> split <;> omega)
    (Nat.le_refl _)
  omega

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankRepairDigitStartOfPos
#print axioms L3.RenewalReferenceClock.bankRepairDigitStartOfZero
#print axioms L3.RenewalReferenceClock.bankRepairDigitClsLiveFalse
#print axioms L3.RenewalReferenceClock.bankRepairDigitStartFar
#print axioms L3.RenewalReferenceClock.bankRepairDigitNeedTwoPoint
#print axioms L3.RenewalReferenceClock.bankRepairDigitNeedMoveLane
#print axioms L3.RenewalReferenceClock.bankRepairDigitNeedSettleLane
#print axioms L3.RenewalReferenceClock.bankRepairDigitIsPShE
#print axioms L3.RenewalReferenceClock.bankRepairDigitIsSShE
#print axioms L3.RenewalReferenceClock.bankRepairDigitLaneFin
#print axioms L3.RenewalReferenceClock.bankRepairDigitLaneReset
#print axioms L3.RenewalReferenceClock.bankRepairDigitLanePipe
