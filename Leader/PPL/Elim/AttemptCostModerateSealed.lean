import Leader.PPL.Elim.AttemptCostModerateStep


namespace PPL.Convergence.LDLocal


set_option autoImplicit false
set_option Elab.async false


open FiniteUniformStoppingTree


/-!
# LD(736): moderate sealed/control stage rows


The three rows are treated literally.


* dummyWait:
  Ready has two distinguished scheduler edges.  The incoming edge enters the
  vulnerable stage and the source edge starts the target live bullet.  Their
  two child budgets add to exactly the parent Ready reserve after paying the
  current interaction.  Every non-Ready target phase has one service edge,
  on which phaseDebt drops by one.


* vulnerable:
  package the current reachable-good witnesses as a VulnerableState.  Away
  from the raw failure port the controlled scheduler is the identity, so the
  physical vulnerable child has the same attacker phase as qStep.  At target
  Ready and raw R_j, the physical kernel enters recovery while Q redirects to
  L_j; the physical child has target phase live 1 and hence potential exactly
  moderateRecoveryBudget.  Therefore each physical child is bounded by the Q
  attacker potential plus that reserve.


* recovery:
  one target-sector service edge decreases phaseDebt by one; reaching Ready
  is a retry and therefore carries zero continuation potential.


No private upstream definition is needed.
-/


/-! ## Generic finite-alphabet Bellman arithmetic -/


theorem moderateSealed_oneExceptionBound
    {n c ca : Nat}
    (a : Fin n) (f : Fin n → Nat)
    (ha : f a ≤ ca)
    (hother : ∀ e, e ≠ a → f e ≤ c)
    (hpay : n + ca ≤ c) :
    n + (List.ofFn f).sum ≤ n * c := by
  let g : Fin n → Nat :=
    fun e => if e = a then ca else c
  have hfg : ∀ e, f e ≤ g e := by
    intro e
    by_cases he : e = a
    · subst e
      simpa [g] using ha
    · simpa [g, he] using hother e he
  have hsum0 :
      (List.ofFn f).sum ≤ (List.ofFn g).sum :=
    ofFn_sum_le f g hfg
  have hsumg :
      (List.ofFn g).sum = ca + (n - 1) * c := by
    have h :=
      PredictableTwoTargetFiniteTree.ofFn_sum_one_value_else_const
        a g c (by
          intro e he
          simp [g, he])
    simpa [g] using h
  have hsum :
      (List.ofFn f).sum ≤ ca + (n - 1) * c := by
    rw [hsumg] at hsum0
    exact hsum0
  have hn : 0 < n := by
    have hlt := a.isLt
    omega
  have hmul :
      n * c = c + (n - 1) * c := by
    obtain ⟨q, hq⟩ :=
      Nat.exists_eq_succ_of_ne_zero
        (show n ≠ 0 by omega)
    rw [hq]
    simp [Nat.succ_mul, Nat.add_comm]
  calc
    n + (List.ofFn f).sum
        ≤ n + (ca + (n - 1) * c) :=
      Nat.add_le_add_left hsum n
    _ = (n + ca) + (n - 1) * c := by omega
    _ ≤ c + (n - 1) * c :=
      Nat.add_le_add_right hpay _
    _ = n * c := hmul.symm


theorem moderateSealed_twoExceptionBound
    {n c ca cb : Nat}
    (a b : Fin n) (f : Fin n → Nat)
    (hab : a ≠ b)
    (ha : f a ≤ ca)
    (hb : f b ≤ cb)
    (hother :
      ∀ e, e ≠ a → e ≠ b → f e ≤ c)
    (hpay : n + ca + cb ≤ c + c) :
    n + (List.ofFn f).sum ≤ n * c := by
  let g : Fin n → Nat :=
    fun e =>
      if e = a then ca
      else if e = b then cb
      else c
  have hfg : ∀ e, f e ≤ g e := by
    intro e
    by_cases hea : e = a
    · subst e
      simp [g, ha]
    · by_cases heb : e = b
      · subst e
        simp [g, hea, hb]
      · simpa [g, hea, heb] using hother e hea heb
  have hsum0 :
      (List.ofFn f).sum ≤ (List.ofFn g).sum :=
    ofFn_sum_le f g hfg
  have hba : b ≠ a := Ne.symm hab
  have hsumg :
      (List.ofFn g).sum =
        ca + cb + (n - 2) * c := by
    have h :=
      PredictableTwoTargetFiniteTree.ofFn_sum_two_values_else_const
        a b g c hab (by
          intro e hea heb
          simp [g, hea, heb])
    simpa [g, hab, hba] using h
  have hsum :
      (List.ofFn f).sum ≤
        ca + cb + (n - 2) * c := by
    rw [hsumg] at hsum0
    exact hsum0
  have hn2 : 2 ≤ n := by
    by_cases hn : 2 ≤ n
    · exact hn
    · have hav : a.val = 0 := by
        have hlt := a.isLt
        omega
      have hbv : b.val = 0 := by
        have hlt := b.isLt
        omega
      apply False.elim
      apply hab
      apply Fin.ext
      omega
  have hmul :
      n * c = (c + c) + (n - 2) * c := by
    have hs : n = 2 + (n - 2) := by omega
    calc
      n * c = (2 + (n - 2)) * c := by rw [← hs]
      _ = 2 * c + (n - 2) * c := by rw [Nat.add_mul]
      _ = (c + c) + (n - 2) * c := by rw [Nat.two_mul]
  calc
    n + (List.ofFn f).sum
        ≤ n + (ca + cb + (n - 2) * c) :=
      Nat.add_le_add_left hsum n
    _ = (n + ca + cb) + (n - 2) * c := by omega
    _ ≤ (c + c) + (n - 2) * c :=
      Nat.add_le_add_right hpay _
    _ = n * c := hmul.symm


/-! ## Sealed-sector witness transport -/


theorem moderateSealed_notEndpointA
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (hgood : AttemptGood ring F C) :
    ¬ EndpointDeleted F.A C := by
  intro h
  exact hgood.2.1 (endpointA_deleted_tagged F C h)


theorem moderateSealed_notEndpointB
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (hgood : AttemptGood ring F C) :
    ¬ EndpointDeleted F.B C := by
  intro h
  exact hgood.2.1 (endpointB_deleted_tagged F C h)


theorem moderateSealed_phaseANext
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (hgood : AttemptGood ring F C)
    (ph : SectorPhase) (hph : PhaseHolds F.A C ph)
    (e : Fin n)
    (hnot : ¬ TaggedDeleted F (stepE ring C e)) :
    PhaseHolds F.A (stepE ring C e)
      (nextSectorPhase F.A ph e) := by
  have hcur := moderateSealed_notEndpointA F C hgood
  have hnext :
      ¬ EndpointDeleted F.A (stepE ring C e) := by
    intro h
    exact hnot
      (endpointA_deleted_tagged
        F (stepE ring C e) h)
  rcases hSealed ring F.A C ph hph hcur e with
    hdel | ⟨ph', hph', htr⟩
  · exact False.elim (hnext hdel)
  · have heq :
        ph' = nextSectorPhase F.A ph e := by
      simpa [PhaseTransition] using htr
    rw [heq] at hph'
    exact hph'


theorem moderateSealed_phaseBNext
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (hgood : AttemptGood ring F C)
    (ph : SectorPhase) (hph : PhaseHolds F.B C ph)
    (e : Fin n)
    (hnot : ¬ TaggedDeleted F (stepE ring C e)) :
    PhaseHolds F.B (stepE ring C e)
      (nextSectorPhase F.B ph e) := by
  have hcur := moderateSealed_notEndpointB F C hgood
  have hnext :
      ¬ EndpointDeleted F.B (stepE ring C e) := by
    intro h
    exact hnot
      (endpointB_deleted_tagged
        F (stepE ring C e) h)
  rcases hSealed ring F.B C ph hph hcur e with
    hdel | ⟨ph', hph', htr⟩
  · exact False.elim (hnext hdel)
  · have heq :
        ph' = nextSectorPhase F.B ph e := by
      simpa [PhaseTransition] using htr
    rw [heq] at hph'
    exact hph'


theorem moderateSealed_dummyZeroUnshielded
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n)
    (h : PhaseHolds F.B C (.dummy 0)) :
    (C F.j).shield = false := by
  have hs :
      (C F.B.left).shield = false :=
    h.2.2.1
  simpa [F.B_left] using hs


/-! ## Recovery-phase mirror -/


def moderateSealedRecoveryPhase : SectorPhase → Prop
  | .live p => 0 < p
  | .ret _ => True
  | .ready => False
  | .dummy _ => False


theorem moderateSealedRecoveryPhase_next
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (ph : SectorPhase)
    (hph : moderateSealedRecoveryPhase ph)
    (e : Fin n)
    (hnotReady :
      nextSectorPhase F.B ph e ≠ SectorPhase.ready) :
    moderateSealedRecoveryPhase
      (nextSectorPhase F.B ph e) := by
  cases ph with
  | ready =>
      exact False.elim hph
  | dummy p =>
      exact False.elim hph
  | live p =>
      have hp : 0 < p := hph
      by_cases hs : e = advance ring F.B.left p
      · subst e
        by_cases hn : p + 1 < F.B.gap
        · simp [nextSectorPhase, hn,
            moderateSealedRecoveryPhase]
        · by_cases hg : F.B.gap = 1
          · have hreadyEq :
                nextSectorPhase F.B (.live p)
                    (advance ring F.B.left p) =
                  SectorPhase.ready := by
              simp [nextSectorPhase, hn, hg]
            exact False.elim (hnotReady hreadyEq)
          · simp [nextSectorPhase, hn, hg,
              moderateSealedRecoveryPhase]
      · simp [nextSectorPhase, hs,
          moderateSealedRecoveryPhase, hp]
  | ret q =>
      by_cases hs :
          e = advance ring F.B.left (q - 1)
      · subst e
        by_cases hq : q = 1
        · have hreadyEq :
              nextSectorPhase F.B (.ret q)
                  (advance ring F.B.left (q - 1)) =
                SectorPhase.ready := by
            simp [nextSectorPhase, hq]
          exact False.elim (hnotReady hreadyEq)
        · simp [nextSectorPhase, hq,
            moderateSealedRecoveryPhase]
      · simp [nextSectorPhase, hs,
          moderateSealedRecoveryPhase]


/-! ## phaseDebt service law on B -/


theorem moderateSealed_phaseDebt_pos
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 ≤ F.b)
    (C : Config n) (ph : SectorPhase)
    (hphase : PhaseHolds F.B C ph)
    (hne : ph ≠ .ready) :
    0 < phaseDebt F.b ph := by
  cases ph with
  | ready =>
      exact False.elim (hne rfl)
  | dummy p =>
      have hp : p < F.b := by
        have h := hphase.2.1.1
        simpa [F.B_gap] using h
      simp [phaseDebt]
      omega
  | live p =>
      have hp : p < F.b := by
        have h := hphase.2.1.1
        simpa [F.B_gap] using h
      simp [phaseDebt]
      omega
  | ret q =>
      have hq : 0 < q := hphase.2.1
      simp [phaseDebt, hq]


theorem moderateSealed_phaseDebt_service
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 ≤ F.b)
    (C : Config n) (ph : SectorPhase)
    (hphase : PhaseHolds F.B C ph)
    (hne : ph ≠ .ready) :
    ∃ service : Fin n,
      And
        (phaseDebt F.b
            (nextSectorPhase F.B ph service) + 1 ≤
          phaseDebt F.b ph)
        (∀ e, e ≠ service →
          phaseDebt F.b
              (nextSectorPhase F.B ph e) =
            phaseDebt F.b ph) := by
  cases ph with
  | ready =>
      exact False.elim (hne rfl)
  | dummy p =>
      let service := advance ring F.B.left p
      refine ⟨service, ?_, ?_⟩
      · have hp : p < F.b := by
          have h := hphase.2.1.1
          simpa [F.B_gap] using h
        have hg : F.B.gap ≠ 1 := by
          intro h
          have hb1 : F.b = 1 := by
            rw [← F.B_gap]
            exact h
          omega
        dsimp [service]
        simp only [nextSectorPhase, if_pos rfl]
        by_cases hn : p + 1 < F.B.gap
        · rw [if_pos hn]
          simp [phaseDebt, F.B_gap]
          omega
        · rw [if_neg hn, if_neg hg]
          simp [phaseDebt, F.B_gap]
          omega
      · intro e he
        dsimp [service] at he
        simp [nextSectorPhase, he, phaseDebt]
  | live p =>
      let service := advance ring F.B.left p
      refine ⟨service, ?_, ?_⟩
      · have hp : p < F.b := by
          have h := hphase.2.1.1
          simpa [F.B_gap] using h
        have hg : F.B.gap ≠ 1 := by
          intro h
          have hb1 : F.b = 1 := by
            rw [← F.B_gap]
            exact h
          omega
        dsimp [service]
        simp only [nextSectorPhase, if_pos rfl]
        by_cases hn : p + 1 < F.B.gap
        · rw [if_pos hn]
          simp [phaseDebt, F.B_gap]
          omega
        · rw [if_neg hn, if_neg hg]
          simp [phaseDebt, F.B_gap]
          omega
      · intro e he
        dsimp [service] at he
        simp [nextSectorPhase, he, phaseDebt]
  | ret q =>
      let service :=
        advance ring F.B.left (q - 1)
      refine ⟨service, ?_, ?_⟩
      · have hq : 0 < q := hphase.2.1
        dsimp [service]
        simp only [nextSectorPhase, if_pos rfl]
        by_cases hq1 : q = 1
        · subst q
          simp [phaseDebt]
        · rw [if_neg hq1]
          simp [phaseDebt]
          omega
      · intro e he
        dsimp [service] at he
        simp [nextSectorPhase, he, phaseDebt]


/-! ## Physical-node elementary bounds -/


theorem moderateSealed_dummyNode_le
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (hgood : AttemptGood ring F C)
    (attackPhase targetPhase : SectorPhase)
    (e : Fin n)
    (hnotHit :
      ¬ And
        (targetPhase = .ready)
        (e = sealedIncomingEdge F.B)) :
    attemptNodePotential
        (moderateLivePotential F)
        ((moderateAttemptKernel ring F).step
          (.live C hgood
            (.dummyWait attackPhase targetPhase)) e) ≤
      n * phaseDebt F.b
          (nextSectorPhase F.B targetPhase e) +
        moderateWaitBudget F := by
  classical
  by_cases htag :
      TaggedDeleted F (stepE ring C e)
  · simp [moderateAttemptKernel, moderateStep,
      htag, attemptNodePotential]
  · simp [moderateAttemptKernel, moderateStep,
      htag, hnotHit, attemptNodePotential,
      moderateLivePotential, moderateStagePotential]


theorem moderateSealed_recoveryNode_le
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (hgood : AttemptGood ring F C)
    (attackPhase targetPhase : SectorPhase)
    (e : Fin n) :
    attemptNodePotential
        (moderateLivePotential F)
        ((moderateAttemptKernel ring F).step
          (.live C hgood
            (.recovery attackPhase targetPhase)) e) ≤
      n * phaseDebt F.b
        (nextSectorPhase F.B targetPhase e) := by
  classical
  by_cases htag :
      TaggedDeleted F (stepE ring C e)
  · simp [moderateAttemptKernel, moderateStep,
      htag, attemptNodePotential]
  · by_cases hready :
      nextSectorPhase F.B targetPhase e = .ready
    · simp [moderateAttemptKernel, moderateStep,
        htag, hready, attemptNodePotential]
    · simp [moderateAttemptKernel, moderateStep,
        htag, hready, attemptNodePotential,
        moderateLivePotential, moderateStagePotential]


/-! ## Controlled vulnerable comparison -/


def moderateSealedVulnerableState
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (hgood : AttemptGood ring F C)
    (attackPhase targetPhase : SectorPhase)
    (hA : PhaseHolds F.A C attackPhase)
    (hB : PhaseHolds F.B C targetPhase)
    (hunshielded : (C F.j).shield = false) :
    VulnerableState F where
  cfg := C
  attackPhase := attackPhase
  targetPhase := targetPhase
  hAttack := hA
  hTarget := hB
  alive := hgood.2.1
  targetUnshielded := hunshielded


theorem moderateSealed_effective_eq_of_not_fail
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n}
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x : VulnerableState F) (e : Fin n)
    (hfail :
      ¬ And (x.targetPhase = .ready)
        (e = R_j F)) :
    (targetRedirection F hb).effective x e = e := by
  by_cases he : e = R_j F
  · subst e
    have hnr : x.targetPhase ≠ .ready := by
      intro hr
      exact hfail (And.intro hr rfl)
    simp [ControlledSchedulerMass.Redirection.effective,
      targetRedirection, hnr]
  · exact
      targetRedirection_effective_of_ne_Rj_rows
        F hb x e he


theorem moderateSealed_vulnerableNode_le
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 ≤ F.b)
    (C : Config n) (hgood : AttemptGood ring F C)
    (attackPhase targetPhase : SectorPhase)
    (hA : PhaseHolds F.A C attackPhase)
    (hB : PhaseHolds F.B C targetPhase)
    (hunshielded : (C F.j).shield = false)
    (e : Fin n) :
    let x :=
      moderateSealedVulnerableState
        F C hgood attackPhase targetPhase
        hA hB hunshielded
    attemptNodePotential
        (moderateLivePotential F)
        ((moderateAttemptKernel ring F).step
          (.live C hgood
            (.vulnerable attackPhase targetPhase)) e) ≤
      attackerPotential F (qStep hSealed F hb x e) +
        moderateRecoveryBudget F := by
  classical
  let x :=
    moderateSealedVulnerableState
      F C hgood attackPhase targetPhase
      hA hB hunshielded
  dsimp only
  by_cases htag :
      TaggedDeleted F (stepE ring C e)
  · have hs :
        (moderateAttemptKernel ring F).step
            (.live C hgood
              (.vulnerable attackPhase targetPhase)) e =
          .success := by
      simp [moderateAttemptKernel, moderateStep, htag]
    rw [hs]
    simp [attemptNodePotential]
  · by_cases hfail :
      And (targetPhase = .ready) (e = R_j F)
    · have hR : R_j F = F.B.left := by
        simpa [R_j] using F.B_left.symm
      have hin :
          F.B.left ≠ sealedIncomingEdge F.B :=
        left_ne_sealedIncomingEdge F.B
      have hg : F.B.gap ≠ 1 := by
        intro h
        have hb1 : F.b = 1 := by
          rw [← F.B_gap]
          exact h
        omega
      have hnextB :
          nextSectorPhase F.B targetPhase e =
            SectorPhase.live 1 := by
        rw [hfail.1, hfail.2, hR]
        simp [nextSectorPhase, hin, hg]
      have hs :
          (moderateAttemptKernel ring F).step
              (.live C hgood
                (.vulnerable attackPhase targetPhase)) e =
            .active
              (.live (stepE ring C e)
                (attemptGood_step ring F C e hgood htag)
                (.recovery
                  (nextSectorPhase F.A attackPhase e)
                  (SectorPhase.live 1))) := by
        simp only [moderateAttemptKernel, moderateStep]
        rw [dif_neg htag, hnextB]
        split
        · rfl
        · rename_i hneg
          exact False.elim (hneg hfail)
      rw [hs]
      have hdebt :
          phaseDebt F.b (SectorPhase.live 1) =
            2 * F.b - 2 := by
        simp only [phaseDebt]
        omega
      simp only [attemptNodePotential,
        moderateLivePotential, moderateStagePotential]
      rw [hdebt]
      change
        moderateRecoveryBudget F ≤
          attackerPotential F (qStep hSealed F hb x e) +
            moderateRecoveryBudget F
      exact Nat.le_add_left _ _
    · have heff :
          (targetRedirection F hb).effective x e = e := by
        apply moderateSealed_effective_eq_of_not_fail
        simpa [x, moderateSealedVulnerableState] using hfail
      cases hq : qStep hSealed F hb x e with
      | success =>
          have hguard :=
            targetRedirection_no_failure_port F hb x e
          have htagx :
              ¬ TaggedDeleted F (stepE ring x.cfg e) := by
            simpa [x, moderateSealedVulnerableState]
              using htag
          have hbad : False := by
            have hnotEff :
                ¬ TaggedDeleted F
                  (stepE ring x.cfg
                    ((targetRedirection F hb).effective x e)) := by
              simpa [heff] using htagx
            have hq' := hq
            simp [qStep,
              ControlledSchedulerMass.controlledStep,
              vulnerableStep, hguard, hnotEff] at hq'
          exact False.elim hbad
      | failure =>
          exact False.elim
            ((qStep_no_failure hSealed F hb x e) hq)
      | active y =>
          have hs :
              (moderateAttemptKernel ring F).step
                  (.live C hgood
                    (.vulnerable attackPhase targetPhase)) e =
                .active
                  (.live (stepE ring C e)
                    (attemptGood_step ring F C e hgood htag)
                    (.vulnerable
                      (nextSectorPhase F.A attackPhase e)
                      (nextSectorPhase F.B targetPhase e))) := by
            simp only [moderateAttemptKernel, moderateStep]
            rw [dif_neg htag]
            split
            · rename_i hpos
              exact False.elim (hfail hpos)
            · rfl
          rw [hs]
          have htr :=
            qStep_active_attack_transition_rows
              (hseal := hSealed) (F := F) (hb := hb)
              (x := x) (y := y) (e := e) hq
          unfold PhaseTransition at htr
          rw [heff] at htr
          have htr' :
              y.attackPhase =
                nextSectorPhase F.A attackPhase e := by
            simpa [x, moderateSealedVulnerableState] using htr
          simp only [attemptNodePotential,
            moderateLivePotential, moderateStagePotential,
            attackerPotential]
          rw [htr']
          exact Nat.le_refl _


theorem moderateSealed_qTrial_cost
    (hSealed : SealedStepSpec)
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 ≤ F.b) (x : VulnerableState F) (T : Nat) :
    truncatedActiveCostNumerator
        (qStep hSealed F hb) (.active x) T ≤
      n ^ T * (5 * n * F.a) :=
  qTrial_cost_five_na
    hSealed F hb
    (controlRowSpec_proved hSealed F hb)
    x T


/-! ## DummyWait Bellman rows -/


theorem moderateSealed_dummyWait_nonready_bellman
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 ≤ F.b)
    (C : Config n) (hgood : AttemptGood ring F C)
    (attackPhase targetPhase : SectorPhase)
    (hB : PhaseHolds F.B C targetPhase)
    (hne : targetPhase ≠ .ready) :
    n +
        (List.ofFn (fun e : Fin n =>
          attemptNodePotential
            (moderateLivePotential F)
            ((moderateAttemptKernel ring F).step
              (.live C hgood
                (.dummyWait attackPhase targetPhase)) e))).sum ≤
      n * moderateLivePotential F
        (.live C hgood
          (.dummyWait attackPhase targetPhase)) := by
  let f : Fin n → Nat :=
    fun e =>
      attemptNodePotential
        (moderateLivePotential F)
        ((moderateAttemptKernel ring F).step
          (.live C hgood
            (.dummyWait attackPhase targetPhase)) e)
  have hpos :=
    moderateSealed_phaseDebt_pos
      F hb C targetPhase hB hne
  obtain ⟨service, hdrop, hstutter⟩ :=
    moderateSealed_phaseDebt_service
      F hb C targetPhase hB hne
  have hservice :
      f service ≤
        n * (phaseDebt F.b targetPhase - 1) +
          moderateWaitBudget F := by
    have hnotHit :
        ¬ And
          (targetPhase = .ready)
          (service = sealedIncomingEdge F.B) := by
      intro h
      exact hne h.1
    have hnode :=
      moderateSealed_dummyNode_le
        ring F C hgood attackPhase targetPhase
        service hnotHit
    have hle :
        phaseDebt F.b
            (nextSectorPhase F.B targetPhase service) ≤
          phaseDebt F.b targetPhase - 1 := by
      omega
    exact
      Nat.le_trans hnode
        (Nat.add_le_add_right
          (Nat.mul_le_mul_left n hle) _)
  have hother :
      ∀ e, e ≠ service →
        f e ≤
          n * phaseDebt F.b targetPhase +
            moderateWaitBudget F := by
    intro e he
    have hnotHit :
        ¬ And
          (targetPhase = .ready)
          (e = sealedIncomingEdge F.B) := by
      intro h
      exact hne h.1
    have hnode :=
      moderateSealed_dummyNode_le
        ring F C hgood attackPhase targetPhase
        e hnotHit
    rw [hstutter e he] at hnode
    exact hnode
  have hdecomp :
      1 + (phaseDebt F.b targetPhase - 1) =
        phaseDebt F.b targetPhase := by
    omega
  have hunit :
      n + n * (phaseDebt F.b targetPhase - 1) =
        n * phaseDebt F.b targetPhase := by
    calc
      n + n * (phaseDebt F.b targetPhase - 1) =
          n * (1 + (phaseDebt F.b targetPhase - 1)) := by
        rw [Nat.mul_add, Nat.mul_one]
      _ = n * phaseDebt F.b targetPhase := by
        rw [hdecomp]
  have hpay :
      n +
          (n * (phaseDebt F.b targetPhase - 1) +
            moderateWaitBudget F) ≤
        n * phaseDebt F.b targetPhase +
          moderateWaitBudget F := by
    apply Nat.le_of_eq
    calc
      n +
          (n * (phaseDebt F.b targetPhase - 1) +
            moderateWaitBudget F) =
          (n + n * (phaseDebt F.b targetPhase - 1)) +
            moderateWaitBudget F := by
        ac_rfl
      _ = n * phaseDebt F.b targetPhase +
          moderateWaitBudget F := by
        exact
          congrArg
            (fun t => t + moderateWaitBudget F)
            hunit
  have hbell :=
    moderateSealed_oneExceptionBound
      service f hservice hother hpay
  simpa [f, moderateLivePotential,
    moderateStagePotential] using hbell


theorem moderateSealed_dummyWait_ready_bellman
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 ≤ F.b)
    (C : Config n) (hgood : AttemptGood ring F C)
    (attackPhase : SectorPhase)
    (hA : PhaseHolds F.A C attackPhase)
    (hB : PhaseHolds F.B C .ready) :
    n +
        (List.ofFn (fun e : Fin n =>
          attemptNodePotential
            (moderateLivePotential F)
            ((moderateAttemptKernel ring F).step
              (.live C hgood
                (.dummyWait attackPhase .ready)) e))).sum ≤
      n * moderateLivePotential F
        (.live C hgood
          (.dummyWait attackPhase .ready)) := by
  let incoming := sealedIncomingEdge F.B
  let source := F.B.left
  have hsourceIncoming : source ≠ incoming := by
    exact left_ne_sealedIncomingEdge F.B
  have hincomingSource : incoming ≠ source :=
    Ne.symm hsourceIncoming
  let f : Fin n → Nat :=
    fun e =>
      attemptNodePotential
        (moderateLivePotential F)
        ((moderateAttemptKernel ring F).step
          (.live C hgood
            (.dummyWait attackPhase .ready)) e)
  have hin :
      f incoming ≤ moderateVulnerableBudget F := by
    classical
    by_cases htag :
        TaggedDeleted F (stepE ring C incoming)
    · simp [f, moderateAttemptKernel,
        moderateStep, htag, attemptNodePotential]
    · have hgoodD :=
        attemptGood_step ring F C incoming hgood htag
      have hA' :=
        moderateSealed_phaseANext
          hSealed ring F C hgood attackPhase hA
          incoming htag
      have hB' :=
        moderateSealed_phaseBNext
          hSealed ring F C hgood .ready hB
          incoming htag
      have hBdummy :
          PhaseHolds F.B
            (stepE ring C incoming) (.dummy 0) := by
        simpa [incoming, nextSectorPhase] using hB'
      have hu :=
        moderateSealed_dummyZeroUnshielded
          F (stepE ring C incoming) hBdummy
      let x :=
        moderateSealedVulnerableState
          F (stepE ring C incoming) hgoodD
          (nextSectorPhase F.A attackPhase incoming)
          (.dummy 0) hA' hBdummy hu
      have hc :=
        attackerCoeff_le_five_a F x
      have hm :
          n * attackerCoeff F
              (nextSectorPhase F.A attackPhase incoming) ≤
            5 * n * F.a := by
        have hmul := Nat.mul_le_mul_left n hc
        simpa [x, moderateSealedVulnerableState,
          Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          using hmul
      have hhit :
          And (SectorPhase.ready = SectorPhase.ready)
            (incoming = sealedIncomingEdge F.B) :=
        And.intro rfl rfl
      have hs :
          (moderateAttemptKernel ring F).step
              (.live C hgood
                (.dummyWait attackPhase .ready)) incoming =
            .active
              (.live (stepE ring C incoming) hgoodD
                (.vulnerable
                  (nextSectorPhase F.A attackPhase incoming)
                  (.dummy 0))) := by
        simp [moderateAttemptKernel, moderateStep,
          htag, hhit, incoming]
      change
        attemptNodePotential
            (moderateLivePotential F)
            ((moderateAttemptKernel ring F).step
              (.live C hgood
                (.dummyWait attackPhase .ready)) incoming) ≤
          moderateVulnerableBudget F
      rw [hs]
      change
        n * attackerCoeff F
              (nextSectorPhase F.A attackPhase incoming) +
            moderateRecoveryBudget F ≤
          moderateVulnerableBudget F
      unfold moderateVulnerableBudget
      exact Nat.add_le_add_right hm _
  have hsource :
      f source ≤
        n * (2 * F.b - 2) +
          moderateWaitBudget F := by
    classical
    by_cases htag :
        TaggedDeleted F (stepE ring C source)
    · simp [f, moderateAttemptKernel,
        moderateStep, htag, attemptNodePotential]
    · have hhit :
          ¬ And (SectorPhase.ready = SectorPhase.ready)
            (source = sealedIncomingEdge F.B) := by
        intro h
        exact hsourceIncoming h.2
      have hs :=
        moderateSealed_dummyNode_le
          ring F C hgood attackPhase .ready
          source hhit
      have hg : F.B.gap ≠ 1 := by
        intro h
        have hb1 : F.b = 1 := by
          rw [← F.B_gap]
          exact h
        omega
      have hleft :
          F.B.left ≠ sealedIncomingEdge F.B :=
        left_ne_sealedIncomingEdge F.B
      have hb1 : F.b ≠ 1 := by
        omega
      have hphase :
          phaseDebt F.b
              (nextSectorPhase F.B .ready source) =
            2 * F.b - 2 := by
        have hnext :
            nextSectorPhase F.B .ready source =
              SectorPhase.live 1 := by
          dsimp [source]
          simp [nextSectorPhase, hleft, F.B_gap, hb1]
        rw [hnext]
        simp only [phaseDebt]
        calc
          2 * F.b - 1 - 1 =
              2 * F.b - (1 + 1) := Nat.sub_sub _ _ _
          _ = 2 * F.b - 2 := rfl
      rw [hphase] at hs
      exact hs
  have hother :
      ∀ e, e ≠ incoming → e ≠ source →
        f e ≤ moderateWaitBudget F := by
    intro e hei hes
    have hhit :
        ¬ And (SectorPhase.ready = SectorPhase.ready)
          (e = sealedIncomingEdge F.B) := by
      intro h
      apply hei
      simpa [incoming] using h.2
    have hs :=
      moderateSealed_dummyNode_le
        ring F C hgood attackPhase .ready e hhit
    have hphase :
        phaseDebt F.b
            (nextSectorPhase F.B .ready e) = 0 := by
      simp [nextSectorPhase, incoming, source,
        hei, hes, phaseDebt]
    rw [hphase] at hs
    simpa using hs
  have hinner :
      1 + (2 * F.b - 2) =
        2 * F.b - 1 := by
    omega
  have hunit :
      n + n * (2 * F.b - 2) =
        n * (2 * F.b - 1) := by
    calc
      n + n * (2 * F.b - 2) =
          n * (1 + (2 * F.b - 2)) := by
        rw [Nat.mul_add, Nat.mul_one]
      _ = n * (2 * F.b - 1) := by
        rw [hinner]
  have hpair :
      n + moderateVulnerableBudget F +
          (n * (2 * F.b - 2) +
            moderateWaitBudget F) ≤
        moderateWaitBudget F +
          moderateWaitBudget F := by
    have heq :
        n + moderateVulnerableBudget F +
            (n * (2 * F.b - 2) +
              moderateWaitBudget F) =
          moderateWaitBudget F +
            moderateWaitBudget F := by
      calc
        n + moderateVulnerableBudget F +
            (n * (2 * F.b - 2) +
              moderateWaitBudget F) =
            (n + n * (2 * F.b - 2)) +
              moderateVulnerableBudget F +
              moderateWaitBudget F := by
          ac_rfl
        _ =
            n * (2 * F.b - 1) +
              moderateVulnerableBudget F +
              moderateWaitBudget F := by
          rw [hunit]
        _ =
            moderateWaitBudget F +
              moderateWaitBudget F := by
          rfl
    exact Nat.le_of_eq heq
  have hbell :=
    moderateSealed_twoExceptionBound
      incoming source f hincomingSource
      hin hsource hother hpair
  simpa [f, moderateLivePotential,
    moderateStagePotential, phaseDebt] using hbell


/-! ## Recovery Bellman -/


theorem moderateSealed_recovery_bellman
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 ≤ F.b)
    (C : Config n) (hgood : AttemptGood ring F C)
    (attackPhase targetPhase : SectorPhase)
    (hB : PhaseHolds F.B C targetPhase)
    (hne : targetPhase ≠ .ready) :
    n +
        (List.ofFn (fun e : Fin n =>
          attemptNodePotential
            (moderateLivePotential F)
            ((moderateAttemptKernel ring F).step
              (.live C hgood
                (.recovery attackPhase targetPhase)) e))).sum ≤
      n * moderateLivePotential F
        (.live C hgood
          (.recovery attackPhase targetPhase)) := by
  let f : Fin n → Nat :=
    fun e =>
      attemptNodePotential
        (moderateLivePotential F)
        ((moderateAttemptKernel ring F).step
          (.live C hgood
            (.recovery attackPhase targetPhase)) e)
  have hpos :=
    moderateSealed_phaseDebt_pos
      F hb C targetPhase hB hne
  obtain ⟨service, hdrop, hstutter⟩ :=
    moderateSealed_phaseDebt_service
      F hb C targetPhase hB hne
  have hservice :
      f service ≤
        n * (phaseDebt F.b targetPhase - 1) := by
    have hnode :=
      moderateSealed_recoveryNode_le
        ring F C hgood attackPhase targetPhase service
    have hle :
        phaseDebt F.b
            (nextSectorPhase F.B targetPhase service) ≤
          phaseDebt F.b targetPhase - 1 := by
      omega
    exact
      Nat.le_trans hnode
        (Nat.mul_le_mul_left n hle)
  have hother :
      ∀ e, e ≠ service →
        f e ≤ n * phaseDebt F.b targetPhase := by
    intro e he
    have hnode :=
      moderateSealed_recoveryNode_le
        ring F C hgood attackPhase targetPhase e
    rw [hstutter e he] at hnode
    exact hnode
  have hdecomp :
      1 + (phaseDebt F.b targetPhase - 1) =
        phaseDebt F.b targetPhase := by
    omega
  have hunit :
      n + n * (phaseDebt F.b targetPhase - 1) =
        n * phaseDebt F.b targetPhase := by
    calc
      n + n * (phaseDebt F.b targetPhase - 1) =
          n * (1 + (phaseDebt F.b targetPhase - 1)) := by
        rw [Nat.mul_add, Nat.mul_one]
      _ = n * phaseDebt F.b targetPhase := by
        rw [hdecomp]
  have hpay :
      n + n * (phaseDebt F.b targetPhase - 1) ≤
        n * phaseDebt F.b targetPhase := by
    exact Nat.le_of_eq hunit
  have hbell :=
    moderateSealed_oneExceptionBound
      service f hservice hother hpay
  simpa [f, moderateLivePotential,
    moderateStagePotential] using hbell


/-! ## Stage closure -/


theorem moderateSealed_dummyWait_closed
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (hgood : AttemptGood ring F C)
    (attackPhase targetPhase : SectorPhase)
    (hreach :
      ModerateReachableGood ring F
        (.live C hgood
          (.dummyWait attackPhase targetPhase))) :
    ∀ e a',
      (moderateAttemptKernel ring F).step
          (.live C hgood
            (.dummyWait attackPhase targetPhase)) e =
        .active a' →
      ModerateReachableGood ring F a' := by
  classical
  intro e a' hstep
  have hA : PhaseHolds F.A C attackPhase := hreach.1
  have hB : PhaseHolds F.B C targetPhase := hreach.2
  by_cases htag :
      TaggedDeleted F (stepE ring C e)
  · have hs :
        (moderateAttemptKernel ring F).step
            (.live C hgood
              (.dummyWait attackPhase targetPhase)) e =
          .success := by
      simp [moderateAttemptKernel, moderateStep, htag]
    have hbad :
        (AttemptNode.success :
          AttemptNode
            (ModerateAttemptState ring F)
            (Config n)) =
          .active a' :=
      hs.symm.trans hstep
    cases hbad
  · have hgoodD :=
      attemptGood_step ring F C e hgood htag
    have hA' :=
      moderateSealed_phaseANext
        hSealed ring F C hgood
        attackPhase hA e htag
    have hB' :=
      moderateSealed_phaseBNext
        hSealed ring F C hgood
        targetPhase hB e htag
    by_cases hhit :
        And (targetPhase = .ready)
          (e = sealedIncomingEdge F.B)
    · have hnextB :
          nextSectorPhase F.B targetPhase e =
            SectorPhase.dummy 0 := by
        rw [hhit.1]
        simp [nextSectorPhase, hhit.2]
      have hBdummy :
          PhaseHolds F.B (stepE ring C e)
            (SectorPhase.dummy 0) := by
        have ht := hB'
        rw [hnextB] at ht
        exact ht
      have hu :=
        moderateSealed_dummyZeroUnshielded
          F (stepE ring C e) hBdummy
      let child : ModerateAttemptState ring F :=
        .live (stepE ring C e) hgoodD
          (.vulnerable
            (nextSectorPhase F.A attackPhase e)
            (.dummy 0))
      have hs :
          (moderateAttemptKernel ring F).step
              (.live C hgood
                (.dummyWait attackPhase targetPhase)) e =
            .active child := by
        simp only [moderateAttemptKernel, moderateStep]
        rw [dif_neg htag]
        split
        · rfl
        · rename_i hneg
          exact False.elim (hneg hhit)
      have hnodes :
          (AttemptNode.active child :
            AttemptNode
              (ModerateAttemptState ring F)
              (Config n)) =
            .active a' :=
        hs.symm.trans hstep
      have ha : child = a' := by
        injection hnodes
      rw [← ha]
      change
        And
          (PhaseHolds F.A (stepE ring C e)
            (nextSectorPhase F.A attackPhase e))
          (And
            (PhaseHolds F.B (stepE ring C e)
              (.dummy 0))
            ((stepE ring C e F.j).shield = false))
      exact And.intro hA' (And.intro hBdummy hu)
    · let child : ModerateAttemptState ring F :=
        .live (stepE ring C e) hgoodD
          (.dummyWait
            (nextSectorPhase F.A attackPhase e)
            (nextSectorPhase F.B targetPhase e))
      have hs :
          (moderateAttemptKernel ring F).step
              (.live C hgood
                (.dummyWait attackPhase targetPhase)) e =
            .active child := by
        simp only [moderateAttemptKernel, moderateStep]
        rw [dif_neg htag]
        split
        · rename_i hpos
          exact False.elim (hhit hpos)
        · rfl
      have hnodes :
          (AttemptNode.active child :
            AttemptNode
              (ModerateAttemptState ring F)
              (Config n)) =
            .active a' :=
        hs.symm.trans hstep
      have ha : child = a' := by
        injection hnodes
      rw [← ha]
      simpa [child, ModerateReachableGood]
        using And.intro hA' hB'


theorem moderateSealed_vulnerable_closed
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 ≤ F.b)
    (C : Config n) (hgood : AttemptGood ring F C)
    (attackPhase targetPhase : SectorPhase)
    (hreach :
      ModerateReachableGood ring F
        (.live C hgood
          (.vulnerable attackPhase targetPhase))) :
    ∀ e a',
      (moderateAttemptKernel ring F).step
          (.live C hgood
            (.vulnerable attackPhase targetPhase)) e =
        .active a' →
      ModerateReachableGood ring F a' := by
  classical
  intro e a' hstep
  have hA : PhaseHolds F.A C attackPhase := hreach.1
  have hB : PhaseHolds F.B C targetPhase := hreach.2.1
  have hu : (C F.j).shield = false := hreach.2.2
  by_cases htag :
      TaggedDeleted F (stepE ring C e)
  · have hs :
        (moderateAttemptKernel ring F).step
            (.live C hgood
              (.vulnerable attackPhase targetPhase)) e =
          .success := by
      simp [moderateAttemptKernel, moderateStep, htag]
    have hbad :
        (AttemptNode.success :
          AttemptNode
            (ModerateAttemptState ring F)
            (Config n)) =
          .active a' :=
      hs.symm.trans hstep
    cases hbad
  · have hgoodD :=
      attemptGood_step ring F C e hgood htag
    have hA' :=
      moderateSealed_phaseANext
        hSealed ring F C hgood
        attackPhase hA e htag
    have hB' :=
      moderateSealed_phaseBNext
        hSealed ring F C hgood
        targetPhase hB e htag
    by_cases hfail :
        And (targetPhase = .ready) (e = R_j F)
    · have hR : R_j F = F.B.left := by
        simpa [R_j] using F.B_left.symm
      have hin :
          F.B.left ≠ sealedIncomingEdge F.B :=
        left_ne_sealedIncomingEdge F.B
      have hg : F.B.gap ≠ 1 := by
        intro h
        have hb1 : F.b = 1 := by
          rw [← F.B_gap]
          exact h
        omega
      have hnextB :
          nextSectorPhase F.B targetPhase e =
            SectorPhase.live 1 := by
        rw [hfail.1, hfail.2, hR]
        simp [nextSectorPhase, hin, hg]
      have hBnext :
          PhaseHolds F.B (stepE ring C e)
            (SectorPhase.live 1) := by
        have ht := hB'
        rw [hnextB] at ht
        exact ht
      let child : ModerateAttemptState ring F :=
        .live (stepE ring C e) hgoodD
          (.recovery
            (nextSectorPhase F.A attackPhase e)
            (.live 1))
      have hs :
          (moderateAttemptKernel ring F).step
              (.live C hgood
                (.vulnerable attackPhase targetPhase)) e =
            .active child := by
        simp only [moderateAttemptKernel, moderateStep]
        rw [dif_neg htag, hnextB]
        split
        · rfl
        · rename_i hneg
          exact False.elim (hneg hfail)
      have hnodes :
          (AttemptNode.active child :
            AttemptNode
              (ModerateAttemptState ring F)
              (Config n)) =
            .active a' :=
        hs.symm.trans hstep
      have ha : child = a' := by
        injection hnodes
      rw [← ha]
      change
        And
          (PhaseHolds F.A (stepE ring C e)
            (nextSectorPhase F.A attackPhase e))
          (And
            (PhaseHolds F.B (stepE ring C e) (.live 1))
            (moderateSealedRecoveryPhase (.live 1)))
      exact
        And.intro hA'
          (And.intro hBnext (by
            simp [moderateSealedRecoveryPhase]))
    · have hport :
          targetPhase = .ready → e ≠ F.j := by
        intro hr he
        apply hfail
        exact And.intro hr (by simpa [R_j] using he)
      let x :=
        moderateSealedVulnerableState
          F C hgood attackPhase targetPhase
          hA hB hu
      have hu' :
          (stepE ring C e F.j).shield = false :=
        targetUnshielded_after_physical
          F x e
          (by
            intro hr he
            apply hfail
            exact
              And.intro
                (by simpa [x, moderateSealedVulnerableState]
                  using hr)
                (by simpa [R_j] using he))
      let child : ModerateAttemptState ring F :=
        .live (stepE ring C e) hgoodD
          (.vulnerable
            (nextSectorPhase F.A attackPhase e)
            (nextSectorPhase F.B targetPhase e))
      have hs :
          (moderateAttemptKernel ring F).step
              (.live C hgood
                (.vulnerable attackPhase targetPhase)) e =
            .active child := by
        simp [moderateAttemptKernel, moderateStep,
          htag, hfail, child]
      have hnodes :
          (AttemptNode.active child :
            AttemptNode
              (ModerateAttemptState ring F)
              (Config n)) =
            .active a' :=
        hs.symm.trans hstep
      have ha : child = a' := by
        injection hnodes
      rw [← ha]
      change
        And
          (PhaseHolds F.A (stepE ring C e)
            (nextSectorPhase F.A attackPhase e))
          (And
            (PhaseHolds F.B (stepE ring C e)
              (nextSectorPhase F.B targetPhase e))
            ((stepE ring C e F.j).shield = false))
      exact And.intro hA' (And.intro hB' hu')


theorem moderateSealed_recovery_closed
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (hgood : AttemptGood ring F C)
    (attackPhase targetPhase : SectorPhase)
    (hreach :
      ModerateReachableGood ring F
        (.live C hgood
          (.recovery attackPhase targetPhase))) :
    ∀ e a',
      (moderateAttemptKernel ring F).step
          (.live C hgood
            (.recovery attackPhase targetPhase)) e =
        .active a' →
      ModerateReachableGood ring F a' := by
  classical
  intro e a' hstep
  have hA : PhaseHolds F.A C attackPhase := hreach.1
  have hB : PhaseHolds F.B C targetPhase := hreach.2.1
  have hrec : moderateSealedRecoveryPhase targetPhase := by
    change moderateSealedRecoveryPhase targetPhase
    exact hreach.2.2
  by_cases htag :
      TaggedDeleted F (stepE ring C e)
  · have hs :
        (moderateAttemptKernel ring F).step
            (.live C hgood
              (.recovery attackPhase targetPhase)) e =
          .success := by
      simp [moderateAttemptKernel, moderateStep, htag]
    have hbad :
        (AttemptNode.success :
          AttemptNode
            (ModerateAttemptState ring F)
            (Config n)) =
          .active a' :=
      hs.symm.trans hstep
    cases hbad
  · have hgoodD :=
      attemptGood_step ring F C e hgood htag
    have hA' :=
      moderateSealed_phaseANext
        hSealed ring F C hgood
        attackPhase hA e htag
    have hB' :=
      moderateSealed_phaseBNext
        hSealed ring F C hgood
        targetPhase hB e htag
    by_cases hready :
        nextSectorPhase F.B targetPhase e = .ready
    · have hs :
          (moderateAttemptKernel ring F).step
              (.live C hgood
                (.recovery attackPhase targetPhase)) e =
            .retry (stepE ring C e) := by
        simp [moderateAttemptKernel, moderateStep,
          htag, hready]
      have hbad :
          (AttemptNode.retry (stepE ring C e) :
            AttemptNode
              (ModerateAttemptState ring F)
              (Config n)) =
            .active a' :=
        hs.symm.trans hstep
      cases hbad
    · have hrec' :=
        moderateSealedRecoveryPhase_next
          F targetPhase hrec e hready
      let child : ModerateAttemptState ring F :=
        .live (stepE ring C e) hgoodD
          (.recovery
            (nextSectorPhase F.A attackPhase e)
            (nextSectorPhase F.B targetPhase e))
      have hs :
          (moderateAttemptKernel ring F).step
              (.live C hgood
                (.recovery attackPhase targetPhase)) e =
            .active child := by
        simp [moderateAttemptKernel, moderateStep,
          htag, hready, child]
      have hnodes :
          (AttemptNode.active child :
            AttemptNode
              (ModerateAttemptState ring F)
              (Config n)) =
            .active a' :=
        hs.symm.trans hstep
      have ha : child = a' := by
        injection hnodes
      rw [← ha]
      change
        And
          (PhaseHolds F.A (stepE ring C e)
            (nextSectorPhase F.A attackPhase e))
          (And
            (PhaseHolds F.B (stepE ring C e)
              (nextSectorPhase F.B targetPhase e))
            (moderateSealedRecoveryPhase
              (nextSectorPhase F.B targetPhase e)))
      exact And.intro hA' (And.intro hB' hrec')


/-! ## Three complete stage rows -/


theorem moderateSealed_dummyWait_rows
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 ≤ F.b)
    (C : Config n) (hgood : AttemptGood ring F C)
    (attackPhase targetPhase : SectorPhase)
    (hreach :
      ModerateReachableGood ring F
        (.live C hgood
          (.dummyWait attackPhase targetPhase))) :
    And
      (∀ e a',
        (moderateAttemptKernel ring F).step
            (.live C hgood
              (.dummyWait attackPhase targetPhase)) e =
          .active a' →
        ModerateReachableGood ring F a')
      (n +
          (List.ofFn (fun e : Fin n =>
            attemptNodePotential
              (moderateLivePotential F)
              ((moderateAttemptKernel ring F).step
                (.live C hgood
                  (.dummyWait attackPhase targetPhase)) e))).sum ≤
        n * moderateLivePotential F
          (.live C hgood
            (.dummyWait attackPhase targetPhase))) := by
  refine And.intro
    (moderateSealed_dummyWait_closed
      hSealed ring F C hgood
      attackPhase targetPhase hreach) ?_
  have hA : PhaseHolds F.A C attackPhase := hreach.1
  have hB : PhaseHolds F.B C targetPhase := hreach.2
  by_cases hr : targetPhase = .ready
  · subst targetPhase
    exact
      moderateSealed_dummyWait_ready_bellman
        hSealed ring F hb C hgood
        attackPhase hA hB
  · exact
      moderateSealed_dummyWait_nonready_bellman
        ring F hb C hgood
        attackPhase targetPhase hB hr


theorem moderateSealed_vulnerable_rows
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 ≤ F.b)
    (C : Config n) (hgood : AttemptGood ring F C)
    (attackPhase targetPhase : SectorPhase)
    (hreach :
      ModerateReachableGood ring F
        (.live C hgood
          (.vulnerable attackPhase targetPhase))) :
    And
      (∀ e a',
        (moderateAttemptKernel ring F).step
            (.live C hgood
              (.vulnerable attackPhase targetPhase)) e =
          .active a' →
        ModerateReachableGood ring F a')
      (n +
          (List.ofFn (fun e : Fin n =>
            attemptNodePotential
              (moderateLivePotential F)
              ((moderateAttemptKernel ring F).step
                (.live C hgood
                  (.vulnerable attackPhase targetPhase)) e))).sum ≤
        n * moderateLivePotential F
          (.live C hgood
            (.vulnerable attackPhase targetPhase))) := by
  refine And.intro
    (moderateSealed_vulnerable_closed
      hSealed ring F hb C hgood
      attackPhase targetPhase hreach) ?_
  have hA : PhaseHolds F.A C attackPhase := hreach.1
  have hB : PhaseHolds F.B C targetPhase := hreach.2.1
  have hu : (C F.j).shield = false := hreach.2.2
  let x :=
    moderateSealedVulnerableState
      F C hgood attackPhase targetPhase hA hB hu
  let f : Fin n → Nat :=
    fun e =>
      attemptNodePotential
        (moderateLivePotential F)
        ((moderateAttemptKernel ring F).step
          (.live C hgood
            (.vulnerable attackPhase targetPhase)) e)
  let g : Fin n → Nat :=
    fun e =>
      attackerPotential F (qStep hSealed F hb x e) +
        moderateRecoveryBudget F
  have hpoint : ∀ e, f e ≤ g e := by
    intro e
    simpa [f, g, x] using
      moderateSealed_vulnerableNode_le
        hSealed ring F hb C hgood
        attackPhase targetPhase hA hB hu e
  have hsum :
      (List.ofFn f).sum ≤ (List.ofFn g).sum :=
    ofFn_sum_le f g hpoint
  have hgsum :
      (List.ofFn g).sum =
        (List.ofFn (fun e : Fin n =>
          attackerPotential F
            (qStep hSealed F hb x e))).sum +
          n * moderateRecoveryBudget F := by
    rw [ofFn_sum_add, ofFn_sum_const]
  have hrows :=
    (controlRowSpec_proved hSealed F hb).attackerBellman x
  calc
    n + (List.ofFn f).sum
        ≤ n + (List.ofFn g).sum :=
      Nat.add_le_add_left hsum n
    _ =
        (n +
          (List.ofFn (fun e : Fin n =>
            attackerPotential F
              (qStep hSealed F hb x e))).sum) +
          n * moderateRecoveryBudget F := by
      rw [hgsum]
      omega
    _ ≤
        n * attackerPotential F (.active x) +
          n * moderateRecoveryBudget F :=
      Nat.add_le_add_right hrows _
    _ =
        n * moderateLivePotential F
          (.live C hgood
            (.vulnerable attackPhase targetPhase)) := by
      simp [x, moderateSealedVulnerableState,
        attackerPotential, moderateLivePotential,
        moderateStagePotential, Nat.mul_add]


theorem moderateSealed_recovery_rows
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 ≤ F.b)
    (C : Config n) (hgood : AttemptGood ring F C)
    (attackPhase targetPhase : SectorPhase)
    (hreach :
      ModerateReachableGood ring F
        (.live C hgood
          (.recovery attackPhase targetPhase))) :
    And
      (∀ e a',
        (moderateAttemptKernel ring F).step
            (.live C hgood
              (.recovery attackPhase targetPhase)) e =
          .active a' →
        ModerateReachableGood ring F a')
      (n +
          (List.ofFn (fun e : Fin n =>
            attemptNodePotential
              (moderateLivePotential F)
              ((moderateAttemptKernel ring F).step
                (.live C hgood
                  (.recovery attackPhase targetPhase)) e))).sum ≤
        n * moderateLivePotential F
          (.live C hgood
            (.recovery attackPhase targetPhase))) := by
  refine And.intro
    (moderateSealed_recovery_closed
      hSealed ring F C hgood
      attackPhase targetPhase hreach) ?_
  have hB : PhaseHolds F.B C targetPhase := hreach.2.1
  have hrec : moderateSealedRecoveryPhase targetPhase := by
    change moderateSealedRecoveryPhase targetPhase
    exact hreach.2.2
  have hne : targetPhase ≠ .ready := by
    intro h
    rw [h] at hrec
    exact hrec
  exact
    moderateSealed_recovery_bellman
      ring F hb C hgood
      attackPhase targetPhase hB hne


/-! ## Requested family -/


theorem moderateSealedControlStageRows :
    ModerateSealedControlStageRows := by
  intro hSealed n ring C0 F hb C hgood stage hstage hreach
  cases stage with
  | attackCR mode =>
      have hf : False := by
        simpa [ModerateSealedControlStage] using hstage
      exact False.elim hf
  | targetCR attackPhase mode =>
      have hf : False := by
        simpa [ModerateSealedControlStage] using hstage
      exact False.elim hf
  | dummyWait attackPhase targetPhase =>
      exact
        moderateSealed_dummyWait_rows
          hSealed ring F hb C hgood
          attackPhase targetPhase hreach
  | vulnerable attackPhase targetPhase =>
      exact
        moderateSealed_vulnerable_rows
          hSealed ring F hb C hgood
          attackPhase targetPhase hreach
  | recovery attackPhase targetPhase =>
      exact
        moderateSealed_recovery_rows
          hSealed ring F hb C hgood
          attackPhase targetPhase hreach
  | stuck =>
      have hf : False := by
        simpa [ModerateSealedControlStage] using hstage
      exact False.elim hf


end PPL.Convergence.LDLocal


#print axioms PPL.Convergence.LDLocal.moderateSealed_oneExceptionBound
#print axioms PPL.Convergence.LDLocal.moderateSealed_twoExceptionBound
#print axioms PPL.Convergence.LDLocal.moderateSealed_notEndpointA
#print axioms PPL.Convergence.LDLocal.moderateSealed_notEndpointB
#print axioms PPL.Convergence.LDLocal.moderateSealed_phaseANext
#print axioms PPL.Convergence.LDLocal.moderateSealed_phaseBNext
#print axioms PPL.Convergence.LDLocal.moderateSealed_dummyZeroUnshielded
#print axioms PPL.Convergence.LDLocal.moderateSealedRecoveryPhase_next
#print axioms PPL.Convergence.LDLocal.moderateSealed_phaseDebt_pos
#print axioms PPL.Convergence.LDLocal.moderateSealed_phaseDebt_service
#print axioms PPL.Convergence.LDLocal.moderateSealed_dummyNode_le
#print axioms PPL.Convergence.LDLocal.moderateSealed_recoveryNode_le
#print axioms PPL.Convergence.LDLocal.moderateSealed_effective_eq_of_not_fail
#print axioms PPL.Convergence.LDLocal.moderateSealed_vulnerableNode_le
#print axioms PPL.Convergence.LDLocal.moderateSealed_qTrial_cost
#print axioms PPL.Convergence.LDLocal.moderateSealed_dummyWait_nonready_bellman
#print axioms PPL.Convergence.LDLocal.moderateSealed_dummyWait_ready_bellman
#print axioms PPL.Convergence.LDLocal.moderateSealed_recovery_bellman
#print axioms PPL.Convergence.LDLocal.moderateSealed_dummyWait_closed
#print axioms PPL.Convergence.LDLocal.moderateSealed_vulnerable_closed
#print axioms PPL.Convergence.LDLocal.moderateSealed_recovery_closed
#print axioms PPL.Convergence.LDLocal.moderateSealed_dummyWait_rows
#print axioms PPL.Convergence.LDLocal.moderateSealed_vulnerable_rows
#print axioms PPL.Convergence.LDLocal.moderateSealed_recovery_rows
#print axioms PPL.Convergence.LDLocal.moderateSealedControlStageRows


#check PPL.Convergence.LDLocal.ModerateSealedControlStageRows




