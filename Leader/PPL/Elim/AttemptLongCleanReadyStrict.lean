import Leader.PPL.Elim.AttemptLongCleanReadyRows


namespace PPL.Convergence.LDLocal


set_option autoImplicit false
set_option Elab.async false


private theorem q19770_leastBulletOffset_unique
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    {p q : Nat}
    (hp : LeastBulletOffset A C p)
    (hq : LeastBulletOffset A C q) :
    p = q := by
  by_cases hpq : p < q
  · have hz := hq.2.2 p hpq
    exact False.elim (hp.2.1 hz)
  · by_cases hqp : q < p
    · have hz := hp.2.2 q hqp
      exact False.elim (hq.2.1 hz)
    · omega


private theorem q19770_returnFront_unique
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    {q r : Nat}
    (hq : ReturnFront A C q)
    (hr : ReturnFront A C r) :
    q = r := by
  by_cases hqr : q < r
  · have hqgap : q < A.gap :=
      Nat.lt_of_lt_of_le hqr hr.2.1
    have hz := hr.2.2.1 q hqr
    have ht := hq.2.2.2 hqgap
    rw [ht] at hz
    cases hz
  · by_cases hrq : r < q
    · have hrgap : r < A.gap :=
        Nat.lt_of_lt_of_le hrq hq.2.1
      have hz := hq.2.2.1 r hrq
      have ht := hr.2.2.2 hrgap
      rw [ht] at hz
      cases hz
    · omega


private theorem q19770_fin3_cases (x : Fin 3) :
    x = (0 : Fin 3) ∨
      x = (1 : Fin 3) ∨ x = (2 : Fin 3) := by
  have hx := x.isLt
  have h :
      x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by
    omega
  rcases h with h | h | h
  · exact .inl (Fin.ext h)
  · exact .inr (.inl (Fin.ext h))
  · exact .inr (.inr (Fin.ext h))


private theorem q19770_stepE_initiator
    {n : Nat} (ring : DirectedRing n)
    (C : Config n) (e : Fin n) :
    stepE ring C e e =
      (PPL.Elim.rowE
        (C e) (C (ring.rightNeighbor e))).1 := by
  simp [stepE, PopulationProtocol.step, PPL.Elim.protocolE]


private theorem q19770_rowE_left_bullet_zero
    (l r : PPL.Elim.Cell4) :
    (PPL.Elim.rowE l r).1.bullet = (0 : Fin 3) := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases q19770_fin3_cases lb with h | h | h <;>
    subst lb <;>
  rcases q19770_fin3_cases rb with h | h | h <;>
    subst rb <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp [PPL.Elim.rowE]


private theorem q19770_repair_rank_le_of_holds
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (D : Config n)
    (hrepair : CRModeHolds A D .repair)
    (m : CRMode) (hm : CRModeHolds A D m) :
    crRank A .repair ≤ crRank A m := by
  cases m with
  | drain p =>
      have hs : (D A.left).signalB = false := hm.2.1
      rw [hrepair.2.1] at hs
      cases hs
  | repair =>
      exact Nat.le_refl _
  | sweep p =>
      have hs : (D A.left).signalB = false := hm.2.1
      rw [hrepair.2.1] at hs
      cases hs
  | ret q =>
      have hs : (D A.left).signalB = false := hm.2.2.1
      rw [hrepair.2.1] at hs
      cases hs


private theorem q19770_sweep_rank_le_of_holds
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (D : Config n)
    (p : Nat)
    (hsweep : CRModeHolds A D (.sweep p))
    (m : CRMode) (hm : CRModeHolds A D m) :
    crRank A (.sweep p) ≤ crRank A m := by
  cases m with
  | drain q =>
      have heq :=
        q19770_leastBulletOffset_unique
          A D hsweep.2.2.1 hm.2.2
      subst q
      have hp : p < A.gap := hsweep.2.2.1.1
      simp only [crRank]
      omega
  | repair =>
      have hs : (D A.left).signalB = false := hsweep.2.1
      rw [hm.2.1] at hs
      cases hs
  | sweep q =>
      have heq :=
        q19770_leastBulletOffset_unique
          A D hsweep.2.2.1 hm.2.2.1
      subst q
      exact Nat.le_refl _
  | ret q =>
      have hleast := hsweep.2.2.1
      have hz := hm.2.1 p hleast.1
      exact False.elim (hleast.2.1 hz)


private theorem q19770_ret_rank_le_of_holds
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (D : Config n)
    (q : Nat)
    (hret : CRModeHolds A D (.ret q))
    (m : CRMode) (hm : CRModeHolds A D m) :
    crRank A (.ret q) ≤ crRank A m := by
  cases m with
  | drain p =>
      have hleast := hm.2.2
      have hz := hret.2.1 p hleast.1
      exact False.elim (hleast.2.1 hz)
  | repair =>
      have hs : (D A.left).signalB = false := hret.2.2.1
      rw [hm.2.1] at hs
      cases hs
  | sweep p =>
      have hleast := hm.2.2.1
      have hz := hret.2.1 p hleast.1
      exact False.elim (hleast.2.1 hz)
  | ret r =>
      have heq :=
        q19770_returnFront_unique
          A D hret.2.2.2 hm.2.2.2
      subst r
      exact Nat.le_refl _


theorem longCRChosenRequiredStrict_proved :
    LongCRChosenRequiredStrict := by
  intro n ring C0 A C mode
    hPB hInterior hmode hnotDone
  let next : CRMode :=
    longCRNextModeMirror
      ring A C mode hPB hInterior hmode
      (crRequiredEdge A mode) hnotDone
  have hspec :=
    longCRNextModeMirror_spec
      ring A C mode hPB hInterior hmode
      (crRequiredEdge A mode) hnotDone
  have hnextHold :
      CRModeHolds
        A (stepE ring C (crRequiredEdge A mode))
        next := by
    simpa only [next] using hspec.1
  have hnextLe :
      crRank A next ≤ crRank A mode := by
    simpa only [next] using hspec.2
  change crRank A next < crRank A mode
  rcases
      (crRankStep_proved
        ring A C mode hPB hInterior hmode).2 with
    hdone | ⟨strictMode, hstrictHold, hstrictRank⟩
  · exact False.elim (hnotDone hdone)
  · by_cases hlt :
        crRank A next < crRank A mode
    · exact hlt
    · have heq :
          crRank A next = crRank A mode := by
        omega
      cases hnextMode : next with
      | drain p =>
          have hnextDrain :
              CRModeHolds
                A (stepE ring C (crRequiredEdge A mode))
                (.drain p) := by
            rw [← hnextMode]
            exact hnextHold
          have heqDrain :
              crRank A (.drain p) = crRank A mode := by
            rw [← hnextMode]
            exact heq
          cases mode with
          | drain p0 =>
              have hp : p < A.gap :=
                hnextDrain.2.2.1
              have hp0 : p0 < A.gap :=
                hmode.2.2.1
              have hpp : p = p0 := by
                simp only [crRank] at heqDrain
                omega
              subst p0
              have hzero :
                  (stepE ring C
                    (crRequiredEdge A (.drain p))
                    (advance ring A.left p)).bullet =
                    (0 : Fin 3) := by
                simp only [crRequiredEdge]
                rw [q19770_stepE_initiator]
                exact
                  q19770_rowE_left_bullet_zero _ _
              exact
                False.elim
                  (hnextDrain.2.2.2.1 hzero)
          | repair =>
              have hp : p < A.gap :=
                hnextDrain.2.2.1
              have hg : 0 < A.gap := A.gap_pos
              simp only [crRank] at heqDrain
              omega
          | sweep q =>
              have hp : p < A.gap :=
                hnextDrain.2.2.1
              have hq : q < A.gap :=
                hmode.2.2.1.1
              simp only [crRank] at heqDrain
              omega
          | ret q =>
              have hp : p < A.gap :=
                hnextDrain.2.2.1
              have hq : q ≤ A.gap :=
                hmode.2.2.2.2.1
              have hg : 0 < A.gap := A.gap_pos
              simp only [crRank] at heqDrain
              omega
      | repair =>
          have hnextRepair :
              CRModeHolds
                A (stepE ring C (crRequiredEdge A mode))
                .repair := by
            rw [← hnextMode]
            exact hnextHold
          have heqRepair :
              crRank A .repair = crRank A mode := by
            rw [← hnextMode]
            exact heq
          have hmin :=
            q19770_repair_rank_le_of_holds
              A (stepE ring C (crRequiredEdge A mode))
              hnextRepair strictMode hstrictHold
          omega
      | sweep p =>
          have hnextSweep :
              CRModeHolds
                A (stepE ring C (crRequiredEdge A mode))
                (.sweep p) := by
            rw [← hnextMode]
            exact hnextHold
          have heqSweep :
              crRank A (.sweep p) = crRank A mode := by
            rw [← hnextMode]
            exact heq
          have hmin :=
            q19770_sweep_rank_le_of_holds
              A (stepE ring C (crRequiredEdge A mode))
              p hnextSweep strictMode hstrictHold
          omega
      | ret q =>
          have hnextRet :
              CRModeHolds
                A (stepE ring C (crRequiredEdge A mode))
                (.ret q) := by
            rw [← hnextMode]
            exact hnextHold
          have heqRet :
              crRank A (.ret q) = crRank A mode := by
            rw [← hnextMode]
            exact heq
          have hmin :=
            q19770_ret_rank_le_of_holds
              A (stepE ring C (crRequiredEdge A mode))
              q hnextRet strictMode hstrictHold
          omega


theorem longCRStageRowsSpec_proved :
    LongCRStageRowsSpec :=
  longCRStageRowsSpec_of_chosenRequiredStrict
    longCRChosenRequiredStrict_proved


end PPL.Convergence.LDLocal


#print axioms PPL.Convergence.LDLocal.longCRChosenRequiredStrict_proved
#print axioms PPL.Convergence.LDLocal.longCRStageRowsSpec_proved
