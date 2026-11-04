import Leader.PPL.Elim.AttemptLongSealedRows
import Leader.PPL.Elim.AttemptLongTargetCleanReadyDone
import Leader.PPL.Elim.AttemptCostModerateSealed
import Leader.PPL.Elim.BoundaryRegime








namespace PPL.Convergence.LDLocal








set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false








open FiniteUniformStoppingTree








/-!
# L17 long recovery post-carrier row


Recovery-only extraction from the corrected post-CR provenance audit.


The first-cut carrier supplies the actual-path semantic invariant that the old
semantic-only package lacked.  The invariant records exactly the facts needed
when a path reaches recovery: the target phase is a genuine sealed B-sector
phase, is not Ready, and carries the bounded recovery debt inherited from the
literal incident/retained entry ports.  It is propagated by the literal
longStep path.


The final Bellman argument is deliberately phrased with the public
longRawPhiCorrected mirror.  No implementation-private name is mentioned and
no change across an upstream private definition is used.
-/








/-! ## Public mirrors and small phase predicates -/








private def longRowsBTargetGood : SectorPhase -> Prop
  | .ready => True
  | .dummy _ => True
  | .live p => 0 < p
  | .ret _ => True








private def longRowsBRetainedTarget : SectorPhase -> Prop
  | .ready => True
  | .dummy _ => True
  | .live _ => False
  | .ret _ => True








private def longRowsBNonLive : SectorPhase -> Prop
  | .ready => True
  | .dummy _ => True
  | .live _ => False
  | .ret _ => True








private def longRowsBExtra
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0) :
    LongStage -> Prop
  | .liveWait targetPhase _ =>
      longRowsBTargetGood targetPhase
  | .advance targetPhase _ =>
      longRowsBTargetGood targetPhase
  | .race targetPhase _ =>
      longRowsBTargetGood targetPhase
  | .incident _ => True
  | .retained targetPhase _ =>
      longRowsBRetainedTarget targetPhase
  | .recovery targetPhase _ =>
      moderateSealedRecoveryPhase targetPhase
  | .targetCR _ => False
  | .attackerCR _ _ => False
  | .stuck => False








private def longRowsBPostInvariant
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0) :
    LongAttemptState ring F -> Prop
  | .junk _ => False
  | .live C _ stage =>
      longStageLegit F C stage ∧
        longRowsBExtra F stage








private def longRowsBPreInvariant
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0) :
    LongAttemptState ring F -> Prop
  | .junk _ => False
  | .live C _ stage =>
      match stage with
      | .targetCR _ => True
      | .attackerCR targetPhase _ =>
          PhaseHolds F.B C targetPhase ∧
            longRowsBTargetGood targetPhase
      | .stuck => True
      | _ => False








private theorem longRowsB_phaseReady
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n)
    (hInterior : CRInteriorFollowers A C)
    (hclean : CleanReady A C) :
    PhaseHolds A C .ready := by
  exact And.intro hInterior hclean








private theorem longRowsBTargetGood_next
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (A : SectorFrame ring C0)
    (ph : SectorPhase)
    (h : longRowsBTargetGood ph)
    (e : Fin n) :
    longRowsBTargetGood (nextSectorPhase A ph e) := by
  cases ph with
  | ready =>
      by_cases hin : e = sealedIncomingEdge A
      · simp [nextSectorPhase, hin, longRowsBTargetGood]
      · by_cases hout : e = A.left
        · have hleft : A.left ≠ sealedIncomingEdge A := by
            intro heq
            exact hin (hout.trans heq)
          by_cases hgap : A.gap = 1
          · simp [nextSectorPhase, hin, hout, hleft, hgap,
              longRowsBTargetGood]
          · simp [nextSectorPhase, hin, hout, hleft, hgap,
              longRowsBTargetGood]
        · simp [nextSectorPhase, hin, hout,
            longRowsBTargetGood]
  | dummy p =>
      by_cases hs : e = advance ring A.left p
      · by_cases hlt : p + 1 < A.gap
        · simp [nextSectorPhase, hs, hlt,
            longRowsBTargetGood]
        · by_cases hgap : A.gap = 1
          · simp [nextSectorPhase, hs, hlt, hgap,
              longRowsBTargetGood]
          · simp [nextSectorPhase, hs, hlt, hgap,
              longRowsBTargetGood]
      · simp [nextSectorPhase, hs, longRowsBTargetGood]
  | live p =>
      have hp : 0 < p := h
      by_cases hs : e = advance ring A.left p
      · by_cases hlt : p + 1 < A.gap
        · have hp1 : 0 < p + 1 := by omega
          simpa [nextSectorPhase, hs, hlt,
            longRowsBTargetGood] using hp1
        · by_cases hgap : A.gap = 1
          · simp [nextSectorPhase, hs, hlt, hgap,
              longRowsBTargetGood]
          · simp [nextSectorPhase, hs, hlt, hgap,
              longRowsBTargetGood]
      · simpa [nextSectorPhase, hs, longRowsBTargetGood]
          using hp
  | ret q =>
      by_cases hs : e = advance ring A.left (q - 1)
      · by_cases hq : q = 1
        · simp [nextSectorPhase, hs, hq,
            longRowsBTargetGood]
        · simp [nextSectorPhase, hs, hq,
            longRowsBTargetGood]
      · simp [nextSectorPhase, hs, longRowsBTargetGood]








private theorem longRowsBNonLive_next
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (A : SectorFrame ring C0)
    (ph : SectorPhase)
    (h : longRowsBNonLive ph)
    (e : Fin n)
    (hfire : Not (ph = .ready ∧ e = A.left)) :
    longRowsBNonLive (nextSectorPhase A ph e) := by
  cases ph with
  | ready =>
      have hsrc : e ≠ A.left := by
        intro he
        exact hfire (And.intro rfl he)
      by_cases hin : e = sealedIncomingEdge A
      · simp [nextSectorPhase, hin, longRowsBNonLive]
      · simp [nextSectorPhase, hin, hsrc,
          longRowsBNonLive]
  | dummy p =>
      by_cases hs : e = advance ring A.left p
      · by_cases hlt : p + 1 < A.gap
        · simp [nextSectorPhase, hs, hlt,
            longRowsBNonLive]
        · by_cases hgap : A.gap = 1
          · simp [nextSectorPhase, hs, hlt, hgap,
              longRowsBNonLive]
          · simp [nextSectorPhase, hs, hlt, hgap,
              longRowsBNonLive]
      · simp [nextSectorPhase, hs, longRowsBNonLive]
  | live p =>
      exact False.elim h
  | ret q =>
      by_cases hs : e = advance ring A.left (q - 1)
      · by_cases hq : q = 1
        · simp [nextSectorPhase, hs, hq,
            longRowsBNonLive]
        · simp [nextSectorPhase, hs, hq,
            longRowsBNonLive]
      · simp [nextSectorPhase, hs, longRowsBNonLive]








private theorem longRowsBLiveNext_bounds
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (p : Nat)
    (hphase : PhaseHolds A C (.live p))
    (e : Fin n)
    (hterminal :
      Not (e = advance ring A.left p ∧ p + 1 = A.gap)) :
    Exists fun p' =>
      And
        (nextSectorPhase A (.live p) e = .live p')
        (And (p <= p') (p' <= p + 1)) := by
  have hp : p < A.gap := hphase.2.1.1
  by_cases hs : e = advance ring A.left p
  · by_cases hn : p + 1 < A.gap
    · refine ⟨p + 1, ?_, ?_, ?_⟩
      · simp [nextSectorPhase, hs, hn]
      · omega
      · omega
    · have heq : p + 1 = A.gap := by omega
      exact False.elim (hterminal (And.intro hs heq))
  · refine ⟨p, ?_, ?_, ?_⟩
    · simp [nextSectorPhase, hs]
    · exact Nat.le_refl p
    · omega








private theorem longRowsB_rightNeighbor_advance
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (p : Nat) :
    ring.rightNeighbor (advance ring i p) =
      advance ring i (p + 1) := by
  change advance ring (advance ring i p) 1 =
    advance ring i (p + 1)
  simpa using advance_add ring i p 1








private theorem longRowsB_Lj_ne_Badvance
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (p : Nat) (hp : p < F.b) :
    L_j F ≠ advance ring F.B.left p := by
  intro h
  have hbN : F.b < n := by
    simpa [F.B_gap] using F.B.gap_lt_n
  have hrnL :
      ring.rightNeighbor (L_j F) = F.B.left := by
    calc
      ring.rightNeighbor (L_j F) =
          F.j := by
            unfold L_j
            exact rightNeighbor_leftNeighbor_twoLeader ring F.j
      _ = F.B.left := F.B_left.symm
  have hh := congrArg ring.rightNeighbor h
  rw [hrnL, longRowsB_rightNeighbor_advance] at hh
  have heq :
      advance ring F.B.left (p + 1) =
        advance ring F.B.left 0 := by
    rw [advance_zero]
    exact hh.symm
  have hpN : p + 1 < n := by omega
  have h0N : 0 < n := ring.hn
  have hbad :=
    advance_injective_below_rows
      ring F.B.left hpN h0N heq
  omega








private theorem longRowsB_terminalEdge_eq_Lj
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (e : Fin n) (p : Nat)
    (hservice : e = advance ring F.A.left p)
    (hend : p + 1 = F.a) :
    e = L_j F := by
  apply rightNeighbor_injective_twoLeader ring
  calc
    ring.rightNeighbor e =
        ring.rightNeighbor (advance ring F.A.left p) := by rw [hservice]
    _ = advance ring F.A.left (p + 1) :=
      longRowsB_rightNeighbor_advance ring F.A.left p
    _ = advance ring F.A.left F.a := by rw [hend]
    _ = F.A.right := by
      simpa [F.A_gap] using F.A.right_eq
    _ = F.j := F.A_right
    _ = ring.rightNeighbor (L_j F) := by
      unfold L_j
      exact (rightNeighbor_leftNeighbor_twoLeader ring F.j).symm








private theorem longRowsB_ready_vulnerable
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n)
    (hB : PhaseHolds F.B C .ready) :
    Or
      ((C F.j).signalB = true)
      (And
        ((C F.j).signalB = false)
        ((C F.j).shield = false)) := by
  exact Or.inl (by
    rw [<- F.B_left]
    exact hB.2.1)








private theorem longRowsB_dummy_vulnerable
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (p : Nat)
    (hB : PhaseHolds F.B C (.dummy p)) :
    Or
      ((C F.j).signalB = true)
      (And
        ((C F.j).signalB = false)
        ((C F.j).shield = false)) := by
  apply Or.inr
  constructor
  · have hz := hB.2.2.2 0 (Nat.zero_le p)
    simpa [advance_zero, F.B_left] using hz
  · rw [<- F.B_left]
    exact hB.2.2.1








private theorem longRowsB_unshielded_vulnerable
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n)
    (hshield : (C F.j).shield = false) :
    Or
      ((C F.j).signalB = true)
      (And
        ((C F.j).signalB = false)
        ((C F.j).shield = false)) := by
  cases hs : (C F.j).signalB with
  | false =>
      exact Or.inr (And.intro rfl hshield)
  | true =>
      exact Or.inl rfl








private theorem longRowsB_terminalTagged
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (hgood : AttemptGood ring F C)
    (p : Nat) (hA : PhaseHolds F.A C (.live p))
    (e : Fin n)
    (hservice : e = advance ring F.A.left p)
    (hend : p + 1 = F.a)
    (hvulnerable :
      Or
        ((C F.j).signalB = true)
        (And
          ((C F.j).signalB = false)
          ((C F.j).shield = false))) :
    TaggedDeleted F (stepE ring C e) := by
  have heL :=
    longRowsB_terminalEdge_eq_Lj
      F e p hservice hend
  have hrn :
      ring.rightNeighbor e = F.j := by
    rw [heL]
    unfold L_j
    exact rightNeighbor_leftNeighbor_twoLeader ring F.j
  have hbullet : (C e).bullet = (2 : Fin 3) := by
    rw [hservice]
    exact hA.2.1.2.1
  have hjLeader : (C F.j).leader = true := by
    cases hj : (C F.j).leader with
    | false =>
        exact False.elim
          (hgood.2.1 (Or.inr (Or.inl hj)))
    | true =>
        rfl
  have hne :
      ring.rightNeighbor e ≠ e :=
    rightNeighbor_ne_self_rows
      ring (frame_two_le_control F) e
  have hrow :=
    rowE_kills_vulnerable_boundary
      (C e) (C (ring.rightNeighbor e))
      (Or.inl hbullet)
      (by simpa [hrn] using hjLeader)
      (by simpa [hrn] using hvulnerable)
  have hresp :=
    stepE_responder_rows ring C e hne
  have hjDeleted :
      ((stepE ring C e) F.j).leader = false := by
    rw [<- hrn, hresp]
    exact hrow
  exact Or.inr (Or.inl hjDeleted)








private theorem longRowsBRecoveryOnLj
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (ph : SectorPhase)
    (hB : PhaseHolds F.B C ph)
    (hrec : moderateSealedRecoveryPhase ph) :
    moderateSealedRecoveryPhase
      (nextSectorPhase F.B ph (L_j F)) := by
  cases ph with
  | ready =>
      exact False.elim hrec
  | dummy p =>
      exact False.elim hrec
  | live p =>
      have hp0 : 0 < p := hrec
      have hp : p < F.b := by
        have h := hB.2.1.1
        simpa [F.B_gap] using h
      have hne :=
        longRowsB_Lj_ne_Badvance F p hp
      simp [nextSectorPhase, hne,
        moderateSealedRecoveryPhase, hp0]
  | ret q =>
      have hq0 : 0 < q := hB.2.1
      have hqlt : q < F.b := by
        have h := hB.2.2.1
        simpa [F.B_gap] using h
      have hpred : q - 1 < F.b := by omega
      have hne :=
        longRowsB_Lj_ne_Badvance F (q - 1) hpred
      simp [nextSectorPhase, hne,
        moderateSealedRecoveryPhase]








private theorem longRowsBRecoveryDebt_le
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 <= F.b)
    (C : Config n) (ph : SectorPhase)
    (hB : PhaseHolds F.B C ph)
    (hrec : moderateSealedRecoveryPhase ph) :
    phaseDebt F.b ph <= longRecoveryReserveUnits F := by
  cases ph with
  | ready =>
      exact False.elim hrec
  | dummy p =>
      exact False.elim hrec
  | live p =>
      have hp0 : 0 < p := hrec
      have hp : p < F.b := by
        have h := hB.2.1.1
        simpa [F.B_gap] using h
      simp [phaseDebt, longRecoveryReserveUnits]
      omega
  | ret q =>
      have hq0 : 0 < q := hB.2.1
      have hqlt : q < F.b := by
        have h := hB.2.2.1
        simpa [F.B_gap] using h
      simp [phaseDebt, longRecoveryReserveUnits]
      omega








private theorem longRowsB_ready_Rj_live1
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 <= F.b) :
    nextSectorPhase F.B .ready (R_j F) = .live 1 := by
  have hR : R_j F = F.B.left := by
    simpa [R_j] using F.B_left.symm
  have hin :
      F.B.left ≠ sealedIncomingEdge F.B :=
    left_ne_sealedIncomingEdge F.B
  have hg : F.B.gap ≠ 1 := by
    intro h
    have hb1 : F.b = 1 := by
      rw [<- F.B_gap]
      exact h
    omega
  rw [hR]
  simp [nextSectorPhase, hin, hg]








private theorem longRowsB_ready_Lj_dummy0
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0) :
    nextSectorPhase F.B .ready (L_j F) = .dummy 0 := by
  rw [<- sealedIncomingEdge_B_eq_L_j F]
  simp [nextSectorPhase]








private theorem longRowsB_ready_other
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (e : Fin n)
    (hL : e ≠ L_j F)
    (hR : e ≠ R_j F) :
    nextSectorPhase F.B .ready e = .ready := by
  have hin : e ≠ sealedIncomingEdge F.B := by
    intro he
    apply hL
    exact he.trans (sealedIncomingEdge_B_eq_L_j F)
  have hout : e ≠ F.B.left := by
    intro he
    apply hR
    calc
      e = F.B.left := he
      _ = F.j := F.B_left
      _ = R_j F := rfl
  simp [nextSectorPhase, hin, hout]








private theorem longRowsBRetainedTarget_next
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (ph : SectorPhase)
    (hph : longRowsBRetainedTarget ph)
    (e : Fin n)
    (hfail : Not (ph = .ready ∧ e = R_j F)) :
    longRowsBRetainedTarget
      (nextSectorPhase F.B ph e) := by
  have hnon : longRowsBNonLive ph := by
    simpa [longRowsBNonLive, longRowsBRetainedTarget]
      using hph
  have hfire : Not (ph = .ready ∧ e = F.B.left) := by
    intro hbad
    apply hfail
    refine And.intro hbad.1 ?_
    calc
      e = F.B.left := hbad.2
      _ = F.j := F.B_left
      _ = R_j F := rfl
  have hnext :=
    longRowsBNonLive_next F.B ph hnon e hfire
  simpa [longRowsBNonLive, longRowsBRetainedTarget]
    using hnext








/-! ## Literal start mirror and pre-cut target-phase carrier -/
/-! ## Literal start mirror and pre-cut target-phase carrier -/








private noncomputable def longRowsBCRInitMode
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (D : Config n)
    (hPB : PPL.Elim.PB ring D)
    (halive : Not (EndpointDeleted A D))
    (hclean : Not (CleanReady A D)) : CRMode :=
  Classical.choose
    (crRankInit ring A D hPB
      (by
        intro hdone
        rcases hdone with hdel | hready
        · exact halive hdel
        · exact hclean hready))








private noncomputable def longRowsBAfterTargetStage
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) : LongStage := by
  classical
  if hA : CleanReady F.A D then
    exact .liveWait .ready .ready
  else
    exact .attackerCR .ready
      (longRowsBCRInitMode ring F.A D hgood.1
        (moderateSealed_notEndpointA F D hgood)
        hA)








private noncomputable def longRowsBInitialStage
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) : LongStage := by
  classical
  if hB : CleanReady F.B D then
    exact longRowsBAfterTargetStage ring F D hgood
  else
    exact .targetCR
      (longRowsBCRInitMode ring F.B D hgood.1
        (moderateSealed_notEndpointB F D hgood)
        hB)








private noncomputable def longRowsBStart
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) : LongAttemptState ring F := by
  classical
  if hgood : AttemptGood ring F D then
    exact .live D hgood
      (longRowsBInitialStage ring F D hgood)
  else
    exact .junk D








private theorem longRowsB_start_eq
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) :
    (longAttemptKernel ring F).start D =
      longRowsBStart ring F D := by
  rfl








private theorem longRowsB_pre_start
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n) (hs : AttemptGood ring F s)
    (hcut :
      longPostCRCutCorrected F
        ((longAttemptKernel ring F).start s) = false) :
    longRowsBPreInvariant F
      ((longAttemptKernel ring F).start s) := by
  classical
  rw [longRowsB_start_eq] at hcut ⊢
  unfold longRowsBStart at hcut ⊢
  rw [dif_pos hs] at hcut ⊢
  unfold longRowsBInitialStage at hcut ⊢
  by_cases hB : CleanReady F.B s
  · rw [dif_pos hB] at hcut ⊢
    unfold longRowsBAfterTargetStage at hcut ⊢
    by_cases hA : CleanReady F.A s
    · rw [dif_pos hA] at hcut ⊢
      simp [longPostCRCutCorrected] at hcut
    · rw [dif_neg hA] at hcut ⊢
      exact
        And.intro
          (longRowsB_phaseReady
            F.B s hs.2.2.2 hB)
          True.intro
  · rw [dif_neg hB] at hcut ⊢
    exact True.intro








private theorem longRowsB_pre_step
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (a : LongAttemptState ring F)
    (ha : longRowsBPreInvariant F a)
    (e : Fin n) (a' : LongAttemptState ring F)
    (hstep :
      (longAttemptKernel ring F).step a e = .active a')
    (hcut : longPostCRCutCorrected F a' = false) :
    longRowsBPreInvariant F a' := by
  classical
  cases a with
  | junk C =>
      exact False.elim ha
  | live C hgood stage =>
      simp only [longAttemptKernel] at hstep
      unfold longStep at hstep
      dsimp only at hstep
      by_cases htag :
          TaggedDeleted F (stepE ring C e)
      · rw [dif_pos htag] at hstep
        cases hstep
      · rw [dif_neg htag] at hstep
        cases stage with
        | targetCR mode =>
            dsimp only at hstep
            by_cases hmode : CRModeHolds F.B C mode
            · rw [dif_pos hmode] at hstep
              by_cases hdone :
                  CRDone F.B (stepE ring C e)
              · rw [dif_pos hdone] at hstep
                cases hstep
                have hcleanB :
                    CleanReady F.B (stepE ring C e) := by
                  rcases hdone with hdel | hclean
                  · exact False.elim
                      (htag
                        (endpointB_deleted_tagged
                          F (stepE ring C e) hdel))
                  · exact hclean
                have hgoodD :=
                  attemptGood_step ring F C e hgood htag
                have hBready :
                    PhaseHolds F.B (stepE ring C e) .ready :=
                  longRowsB_phaseReady
                    F.B (stepE ring C e)
                    hgoodD.2.2.2 hcleanB
                revert hcut
                unfoldLongAfterTargetStage
                by_cases hA :
                    CleanReady F.A (stepE ring C e)
                · rw [dif_pos hA]
                  intro hcut
                  simp [longPostCRCutCorrected] at hcut
                · rw [dif_neg hA]
                  intro hcut
                  exact And.intro hBready True.intro
              · rw [dif_neg hdone] at hstep
                cases hstep
                exact True.intro
            · rw [dif_neg hmode] at hstep
              cases hstep
              exact True.intro
        | attackerCR targetPhase mode =>
            dsimp only at hstep
            change
              PhaseHolds F.B C targetPhase ∧
                longRowsBTargetGood targetPhase at ha
            rcases ha with ⟨hB, htarget⟩
            by_cases hmode : CRModeHolds F.A C mode
            · rw [dif_pos hmode] at hstep
              have hBnext :=
                moderateSealed_phaseBNext
                  hSealed ring F C hgood
                  targetPhase hB e htag
              have htargetNext :=
                longRowsBTargetGood_next
                  F.B targetPhase htarget e
              by_cases hdone :
                  CRDone F.A (stepE ring C e)
              · rw [dif_pos hdone] at hstep
                cases hstep
                simp [longPostCRCutCorrected] at hcut
              · rw [dif_neg hdone] at hstep
                cases hstep
                exact And.intro hBnext htargetNext
            · rw [dif_neg hmode] at hstep
              cases hstep
              exact True.intro
        | liveWait targetPhase attackPhase =>
            exact False.elim ha
        | advance targetPhase attackPhase =>
            exact False.elim ha
        | race targetPhase attackPhase =>
            exact False.elim ha
        | incident attackPhase =>
            exact False.elim ha
        | retained targetPhase attackPhase =>
            exact False.elim ha
        | recovery targetPhase attackPhase =>
            exact False.elim ha
        | stuck =>
            dsimp only at hstep
            cases hstep
            exact True.intro








private theorem longRowsB_pre_before
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n) (hs : AttemptGood ring F s)
    (a : LongAttemptState ring F)
    (h :
      RetryActiveBeforeCutCorrected
        (longAttemptKernel ring F)
        (longPostCRCutCorrected F)
        ((longAttemptKernel ring F).start s)
        a) :
    longRowsBPreInvariant F a := by
  induction h with
  | root hroot =>
      exact longRowsB_pre_start ring F s hs hroot
  | step h e hstep hcut ih =>
      exact
        longRowsB_pre_step
          hSealed ring F _ ih e _ hstep hcut








private theorem longRowsB_start_post
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n) (hs : AttemptGood ring F s)
    (hcut :
      longPostCRCutCorrected F
        ((longAttemptKernel ring F).start s) = true) :
    longRowsBPostInvariant F
      ((longAttemptKernel ring F).start s) := by
  classical
  rw [longRowsB_start_eq] at hcut ⊢
  unfold longRowsBStart at hcut ⊢
  rw [dif_pos hs] at hcut ⊢
  unfold longRowsBInitialStage at hcut ⊢
  by_cases hB : CleanReady F.B s
  · rw [dif_pos hB] at hcut ⊢
    unfold longRowsBAfterTargetStage at hcut ⊢
    by_cases hA : CleanReady F.A s
    · rw [dif_pos hA] at hcut ⊢
      have hBready :=
        longRowsB_phaseReady F.B s hs.2.2.2 hB
      have hAready :=
        longRowsB_phaseReady F.A s hs.2.2.1 hA
      exact
        And.intro
          (And.intro hBready
            (And.intro hAready True.intro))
          True.intro
    · rw [dif_neg hA] at hcut ⊢
      simp [longPostCRCutCorrected] at hcut
  · rw [dif_neg hB] at hcut ⊢
    simp [longPostCRCutCorrected] at hcut








private theorem longRowsB_first_post
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n) (hs : AttemptGood ring F s)
    (carrier : LongAttemptState ring F)
    (hfirst :
      RetryFirstCutReachableCorrected
        (longAttemptKernel ring F)
        (longPostCRCutCorrected F)
        ((longAttemptKernel ring F).start s)
        carrier) :
    longRowsBPostInvariant F carrier := by
  classical
  rcases hfirst with hroot | hstep
  · rcases hroot with ⟨hEq, hcut⟩
    subst carrier
    exact longRowsB_start_post ring F s hs hcut
  · rcases hstep with
      ⟨p, hbefore, e, hstep, hcut⟩
    have hp :=
      longRowsB_pre_before
        hSealed ring F s hs p hbefore
    cases p with
    | junk C =>
        exact False.elim hp
    | live C hgood stage =>
        simp only [longAttemptKernel] at hstep
        unfold longStep at hstep
        dsimp only at hstep
        by_cases htag :
            TaggedDeleted F (stepE ring C e)
        · rw [dif_pos htag] at hstep
          cases hstep
        · rw [dif_neg htag] at hstep
          cases stage with
          | targetCR mode =>
              dsimp only at hstep
              by_cases hmode : CRModeHolds F.B C mode
              · rw [dif_pos hmode] at hstep
                by_cases hdone :
                    CRDone F.B (stepE ring C e)
                · rw [dif_pos hdone] at hstep
                  cases hstep
                  have hcleanB :
                      CleanReady F.B (stepE ring C e) := by
                    rcases hdone with hdel | hclean
                    · exact False.elim
                        (htag
                          (endpointB_deleted_tagged
                            F (stepE ring C e) hdel))
                    · exact hclean
                  have hgoodD :=
                    attemptGood_step ring F C e hgood htag
                  have hBready :=
                    longRowsB_phaseReady
                      F.B (stepE ring C e)
                      hgoodD.2.2.2 hcleanB
                  revert hcut
                  unfoldLongAfterTargetStage
                  by_cases hA :
                      CleanReady F.A (stepE ring C e)
                  · rw [dif_pos hA]
                    intro hcut
                    have hAready :=
                      longRowsB_phaseReady
                        F.A (stepE ring C e)
                        hgoodD.2.2.1 hA
                    exact
                      And.intro
                        (And.intro hBready
                          (And.intro hAready True.intro))
                        True.intro
                  · rw [dif_neg hA]
                    intro hcut
                    simp [longPostCRCutCorrected] at hcut
                · rw [dif_neg hdone] at hstep
                  cases hstep
                  simp [longPostCRCutCorrected] at hcut
              · rw [dif_neg hmode] at hstep
                cases hstep
                simp [longPostCRCutCorrected] at hcut
          | attackerCR targetPhase mode =>
              dsimp only at hstep
              change
                PhaseHolds F.B C targetPhase ∧
                  longRowsBTargetGood targetPhase at hp
              rcases hp with ⟨hB, htarget⟩
              by_cases hmode : CRModeHolds F.A C mode
              · rw [dif_pos hmode] at hstep
                by_cases hdone :
                    CRDone F.A (stepE ring C e)
                · rw [dif_pos hdone] at hstep
                  cases hstep
                  have hgoodD :=
                    attemptGood_step ring F C e hgood htag
                  have hcleanA :
                      CleanReady F.A (stepE ring C e) := by
                    rcases hdone with hdel | hclean
                    · exact False.elim
                        (htag
                          (endpointA_deleted_tagged
                            F (stepE ring C e) hdel))
                    · exact hclean
                  have hBnext :=
                    moderateSealed_phaseBNext
                      hSealed ring F C hgood
                      targetPhase hB e htag
                  have htargetNext :=
                    longRowsBTargetGood_next
                      F.B targetPhase htarget e
                  have hAready :=
                    longRowsB_phaseReady
                      F.A (stepE ring C e)
                      hgoodD.2.2.1 hcleanA
                  exact
                    And.intro
                      (And.intro hBnext
                        (And.intro hAready True.intro))
                      htargetNext
                · rw [dif_neg hdone] at hstep
                  cases hstep
                  simp [longPostCRCutCorrected] at hcut
              · rw [dif_neg hmode] at hstep
                cases hstep
                simp [longPostCRCutCorrected] at hcut
          | liveWait targetPhase attackPhase =>
              exact False.elim hp
          | advance targetPhase attackPhase =>
              exact False.elim hp
          | race targetPhase attackPhase =>
              exact False.elim hp
          | incident attackPhase =>
              exact False.elim hp
          | retained targetPhase attackPhase =>
              exact False.elim hp
          | recovery targetPhase attackPhase =>
              exact False.elim hp
          | stuck =>
              dsimp only at hstep
              cases hstep
              simp [longPostCRCutCorrected] at hcut








/-! ## Post-cut semantic/provenance closure -/








private theorem longRowsB_liveWait_legit
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n)
    (targetPhase attackPhase : SectorPhase)
    (h :
      longStageLegit F C
        (.liveWait targetPhase attackPhase)) :
    PhaseHolds F.B C targetPhase ∧
      PhaseHolds F.A C attackPhase ∧
      longRowsBNonLive attackPhase := by
  rcases h with ⟨hB, hA, hnon⟩
  refine And.intro hB (And.intro hA ?_)
  cases attackPhase <;>
    simpa [longRowsBNonLive] using hnon








private theorem longRowsB_post_step
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 <= F.b)
    (hab : 2 * F.b + 1 <= F.a)
    (a : LongAttemptState ring F)
    (ha : longRowsBPostInvariant F a)
    (e : Fin n) (a' : LongAttemptState ring F)
    (hstep :
      (longAttemptKernel ring F).step a e = .active a') :
    longRowsBPostInvariant F a' := by
  classical
  cases a with
  | junk C =>
      exact False.elim ha
  | live C hgood stage =>
      rcases ha with ⟨hlegit, hextra⟩
      simp only [longAttemptKernel] at hstep
      unfold longStep at hstep
      dsimp only at hstep
      by_cases htag :
          TaggedDeleted F (stepE ring C e)
      · rw [dif_pos htag] at hstep
        cases hstep
      · rw [dif_neg htag] at hstep
        have hgoodD :=
          attemptGood_step ring F C e hgood htag
        cases stage with
        | targetCR mode =>
            exact False.elim hextra
        | attackerCR targetPhase mode =>
            exact False.elim hextra
        | liveWait targetPhase attackPhase =>
            dsimp only at hstep
            have hlegit' :=
              longRowsB_liveWait_legit
                F C targetPhase attackPhase hlegit
            rcases hlegit' with ⟨hB, hA, hnonLive⟩
            have hBnext :=
              moderateSealed_phaseBNext
                hSealed ring F C hgood
                targetPhase hB e htag
            have hAnext :=
              moderateSealed_phaseANext
                hSealed ring F C hgood
                attackPhase hA e htag
            have htargetNext :=
              longRowsBTargetGood_next
                F.B targetPhase hextra e
            by_cases hfire :
                attackPhase = .ready ∧ e = F.A.left
            · rw [dif_pos hfire] at hstep
              have hgap : F.A.gap ≠ 1 := by
                intro hg
                have ha1 : F.a = 1 := by
                  rw [<- F.A_gap]
                  exact hg
                omega
              have hnextA :
                  nextSectorPhase F.A attackPhase e =
                    .live 1 := by
                rw [hfire.1, hfire.2]
                simp [nextSectorPhase,
                  left_ne_sealedIncomingEdge F.A, hgap]
              by_cases hnear : F.a - 2 * F.b <= 1
              · rw [dif_pos hnear] at hstep
                cases hstep
                refine And.intro ?_ htargetNext
                change
                  PhaseHolds F.B (stepE ring C e)
                      (nextSectorPhase F.B targetPhase e) ∧
                    PhaseHolds F.A (stepE ring C e)
                      (nextSectorPhase F.A attackPhase e) ∧
                    Exists fun p =>
                      nextSectorPhase F.A attackPhase e = .live p ∧
                        F.a - p <= 2 * F.b
                exact
                  And.intro hBnext
                    (And.intro hAnext
                      ⟨1, hnextA, by omega⟩)
              · rw [dif_neg hnear] at hstep
                cases hstep
                refine And.intro ?_ htargetNext
                change
                  PhaseHolds F.B (stepE ring C e)
                      (nextSectorPhase F.B targetPhase e) ∧
                    PhaseHolds F.A (stepE ring C e)
                      (nextSectorPhase F.A attackPhase e) ∧
                    Exists fun p =>
                      nextSectorPhase F.A attackPhase e = .live p ∧
                        0 < p ∧
                        p < F.a - 2 * F.b
                exact
                  And.intro hBnext
                    (And.intro hAnext
                      ⟨1, hnextA, by omega, by omega⟩)
            · rw [dif_neg hfire] at hstep
              cases hstep
              have hnonLiveNext :=
                longRowsBNonLive_next
                  F.A attackPhase hnonLive e hfire
              have hnonLiveGoal :
                  match nextSectorPhase F.A attackPhase e with
                  | .live _ => False
                  | _ => True := by
                cases hn :
                    nextSectorPhase F.A attackPhase e <;>
                  simp [hn, longRowsBNonLive] at hnonLiveNext ⊢
              exact
                And.intro
                  (And.intro hBnext
                    (And.intro hAnext hnonLiveGoal))
                  htargetNext
        | advance targetPhase attackPhase =>
            dsimp only at hstep
            change
              PhaseHolds F.B C targetPhase ∧
                PhaseHolds F.A C attackPhase ∧
                Exists fun p =>
                  attackPhase = .live p ∧
                    0 < p ∧
                    p < F.a - 2 * F.b at hlegit
            rcases hlegit with
              ⟨hB, hA, p, hattack, hp0, hpCut⟩
            subst attackPhase
            have hBnext :=
              moderateSealed_phaseBNext
                hSealed ring F C hgood
                targetPhase hB e htag
            have hAnext :=
              moderateSealed_phaseANext
                hSealed ring F C hgood
                (.live p) hA e htag
            have htargetNext :=
              longRowsBTargetGood_next
                F.B targetPhase hextra e
            have hnotTerminal :
                Not
                  (e = advance ring F.A.left p ∧
                    p + 1 = F.A.gap) := by
              intro ht
              have hgap : F.A.gap = F.a := F.A_gap
              omega
            obtain ⟨p', hnextA, hpLower, hpUpper⟩ :=
              longRowsBLiveNext_bounds
                F.A C p hA e hnotTerminal
            by_cases hreach :
                nextSectorPhase F.A (.live p) e =
                  .live (F.a - 2 * F.b)
            · rw [dif_pos hreach] at hstep
              cases hstep
              refine And.intro ?_ htargetNext
              exact
                And.intro hBnext
                  (And.intro hAnext
                    ⟨F.a - 2 * F.b,
                      hreach, by omega⟩)
            · rw [dif_neg hreach] at hstep
              cases hstep
              have hp'Cut :
                  p' < F.a - 2 * F.b := by
                have hle :
                    p' <= F.a - 2 * F.b := by
                  omega
                cases Nat.lt_or_eq_of_le hle with
                | inl hlt => exact hlt
                | inr heq =>
                    apply False.elim
                    apply hreach
                    rw [hnextA, heq]
              refine And.intro ?_ htargetNext
              exact
                And.intro hBnext
                  (And.intro hAnext
                    ⟨p', hnextA, by omega, hp'Cut⟩)
        | race targetPhase attackPhase =>
            dsimp only at hstep
            change
              PhaseHolds F.B C targetPhase ∧
                PhaseHolds F.A C attackPhase ∧
                Exists fun p =>
                  attackPhase = .live p ∧
                    F.a - p <= 2 * F.b at hlegit
            rcases hlegit with
              ⟨hB, hA, p, hattack, hrem⟩
            subst attackPhase
            have hBnext :=
              moderateSealed_phaseBNext
                hSealed ring F C hgood
                targetPhase hB e htag
            have hAnext :=
              moderateSealed_phaseANext
                hSealed ring F C hgood
                (.live p) hA e htag
            by_cases hready : targetPhase = .ready
            · rw [dif_pos hready] at hstep
              subst targetPhase
              by_cases hout : e = R_j F
              · rw [dif_pos hout] at hstep
                cases hstep
                have hnextB :=
                  longRowsB_ready_Rj_live1 F hb
                have hnextBE :
                    nextSectorPhase F.B .ready e = .live 1 := by
                  simpa [hout] using hnextB
                have hdebt :
                    phaseDebt F.b (.live 1) <=
                      longRecoveryReserveUnits F := by
                  simp [phaseDebt, longRecoveryReserveUnits]
                  omega
                have hnotReady :
                    nextSectorPhase F.B .ready e ≠ .ready := by
                  rw [hnextBE]
                  simp
                have hdebtNext :
                    phaseDebt F.b
                        (nextSectorPhase F.B .ready e) <=
                      longRecoveryReserveUnits F := by
                  rw [hnextBE]
                  exact hdebt
                exact
                  And.intro
                    (And.intro hBnext
                      (And.intro hnotReady hdebtNext))
                    (by
                      change
                        moderateSealedRecoveryPhase
                          (nextSectorPhase F.B .ready e)
                      rw [hnextBE]
                      simp [moderateSealedRecoveryPhase])
              · rw [dif_neg hout] at hstep
                by_cases hin : e = L_j F
                · rw [dif_pos hin] at hstep
                  have hnotTerminal :
                      Not
                        (e = advance ring F.A.left p ∧
                          p + 1 = F.A.gap) := by
                    intro ht
                    have hend : p + 1 = F.a := by
                      simpa [F.A_gap] using ht.2
                    have hdel :=
                      longRowsB_terminalTagged
                        ring F C hgood p hA e
                        ht.1 hend
                        (longRowsB_ready_vulnerable F C
                          (by simpa using hB))
                    exact htag hdel
                  obtain ⟨p', hnextA, hpLower, hpUpper⟩ :=
                    longRowsBLiveNext_bounds
                      F.A C p hA e hnotTerminal
                  have hrem' : F.a - p' <= 2 * F.b := by
                    omega
                  cases hstep
                  have hnextB :=
                    longRowsB_ready_Lj_dummy0 F
                  have hnextBE :
                      nextSectorPhase F.B .ready e = .dummy 0 := by
                    simpa [hin] using hnextB
                  have hBdummy :
                      PhaseHolds F.B (stepE ring C e)
                        (.dummy 0) := by
                    simpa [hnextBE] using hBnext
                  have hshield :=
                    moderateSealed_dummyZeroUnshielded
                      F (stepE ring C e) hBdummy
                  refine And.intro ?_ ?_
                  · exact
                      And.intro hBnext
                        (And.intro hAnext
                          (And.intro
                            ⟨p', hnextA, hrem'⟩
                            hshield))
                  · change
                      longRowsBRetainedTarget
                        (nextSectorPhase F.B .ready e)
                    rw [hnextBE]
                    simp [longRowsBRetainedTarget]
                · rw [dif_neg hin] at hstep
                  cases hstep
                  have hreadyB :=
                    longRowsB_ready_other F e hin hout
                  have hnotTerminal :
                      Not
                        (e = advance ring F.A.left p ∧
                          p + 1 = F.A.gap) := by
                    intro ht
                    have hend : p + 1 = F.a := by
                      simpa [F.A_gap] using ht.2
                    have heL :=
                      longRowsB_terminalEdge_eq_Lj
                        F e p ht.1 hend
                    exact hin heL
                  obtain ⟨p', hnextA, hpLower, hpUpper⟩ :=
                    longRowsBLiveNext_bounds
                      F.A C p hA e hnotTerminal
                  have hrem' : F.a - p' <= 2 * F.b := by
                    omega
                  have hBready :
                      PhaseHolds F.B (stepE ring C e) .ready := by
                    simpa [hreadyB] using hBnext
                  exact
                    And.intro
                      (And.intro hBready
                        (And.intro hAnext
                          ⟨p', hnextA, hrem'⟩))
                      True.intro
            · rw [dif_neg hready] at hstep
              by_cases hhit :
                  Exists fun q =>
                    And ((.live p : SectorPhase) = .live q)
                      (And
                        (e = advance ring F.A.left q)
                        (q + 1 = F.a))
              · rw [dif_pos hhit] at hstep
                rcases hhit with
                  ⟨q, hqphase, hservice, hend⟩
                have hqp : q = p := by
                  injection hqphase with hpq
                  exact hpq.symm
                subst q
                have heL :=
                  longRowsB_terminalEdge_eq_Lj
                    F e p hservice hend
                cases targetPhase with
                | ready =>
                    exact False.elim (hready rfl)
                | dummy d =>
                    have hdel :=
                      longRowsB_terminalTagged
                        ring F C hgood p hA e
                        hservice hend
                        (longRowsB_dummy_vulnerable
                          F C d hB)
                    exact False.elim (htag hdel)
                | live d =>
                    have hd0 : 0 < d := hextra
                    have hrec :
                        moderateSealedRecoveryPhase
                          (.live d) := hd0
                    have hrecNext :=
                      longRowsBRecoveryOnLj
                        F C (.live d) hB hrec
                    have hrecNextE :
                        moderateSealedRecoveryPhase
                          (nextSectorPhase F.B (.live d) e) := by
                      simpa [heL] using hrecNext
                    have hdebt :=
                      longRowsBRecoveryDebt_le
                        F hb (stepE ring C e)
                        (nextSectorPhase F.B (.live d) e)
                        hBnext hrecNextE
                    have hnotReady :
                        nextSectorPhase F.B (.live d) e ≠ .ready := by
                      intro hr
                      have hbad :
                          moderateSealedRecoveryPhase
                            SectorPhase.ready := by
                        simpa [hr] using hrecNextE
                      simpa [moderateSealedRecoveryPhase] using hbad
                    cases hstep
                    exact
                      And.intro
                        (And.intro hBnext
                          (And.intro hnotReady hdebt))
                        hrecNextE
                | ret q =>
                    have hrec :
                        moderateSealedRecoveryPhase
                          (.ret q) := by
                      simp [moderateSealedRecoveryPhase]
                    have hrecNext :=
                      longRowsBRecoveryOnLj
                        F C (.ret q) hB hrec
                    have hrecNextE :
                        moderateSealedRecoveryPhase
                          (nextSectorPhase F.B (.ret q) e) := by
                      simpa [heL] using hrecNext
                    have hdebt :=
                      longRowsBRecoveryDebt_le
                        F hb (stepE ring C e)
                        (nextSectorPhase F.B (.ret q) e)
                        hBnext hrecNextE
                    have hnotReady :
                        nextSectorPhase F.B (.ret q) e ≠ .ready := by
                      intro hr
                      have hbad :
                          moderateSealedRecoveryPhase
                            SectorPhase.ready := by
                        simpa [hr] using hrecNextE
                      simpa [moderateSealedRecoveryPhase] using hbad
                    cases hstep
                    exact
                      And.intro
                        (And.intro hBnext
                          (And.intro hnotReady hdebt))
                        hrecNextE
              · rw [dif_neg hhit] at hstep
                have hnotTerminal :
                    Not
                      (e = advance ring F.A.left p ∧
                        p + 1 = F.A.gap) := by
                  intro ht
                  apply hhit
                  refine ⟨p, rfl, ht.1, ?_⟩
                  simpa [F.A_gap] using ht.2
                obtain ⟨p', hnextA, hpLower, hpUpper⟩ :=
                  longRowsBLiveNext_bounds
                    F.A C p hA e hnotTerminal
                have hrem' : F.a - p' <= 2 * F.b := by
                  omega
                by_cases htarget :
                    nextSectorPhase F.B targetPhase e = .ready
                · rw [dif_pos htarget] at hstep
                  cases hstep
                  have hBready :
                      PhaseHolds F.B (stepE ring C e) .ready := by
                    simpa [htarget] using hBnext
                  exact
                    And.intro
                      (And.intro hBready
                        (And.intro hAnext
                          ⟨p', hnextA, hrem'⟩))
                      True.intro
                · rw [dif_neg htarget] at hstep
                  cases hstep
                  have htargetNext :=
                    longRowsBTargetGood_next
                      F.B targetPhase hextra e
                  exact
                    And.intro
                      (And.intro hBnext
                        (And.intro hAnext
                          ⟨p', hnextA, hrem'⟩))
                      htargetNext
        | incident attackPhase =>
            dsimp only at hstep
            change
              PhaseHolds F.B C .ready ∧
                PhaseHolds F.A C attackPhase ∧
                Exists fun p =>
                  attackPhase = .live p ∧
                    F.a - p <= 2 * F.b at hlegit
            rcases hlegit with
              ⟨hB, hA, p, hattack, hrem⟩
            subst attackPhase
            have hBnext :=
              moderateSealed_phaseBNext
                hSealed ring F C hgood
                .ready hB e htag
            have hAnext :=
              moderateSealed_phaseANext
                hSealed ring F C hgood
                (.live p) hA e htag
            by_cases hout : e = R_j F
            · rw [dif_pos hout] at hstep
              cases hstep
              have hnextB :=
                longRowsB_ready_Rj_live1 F hb
              have hnextBE :
                  nextSectorPhase F.B .ready e = .live 1 := by
                simpa [hout] using hnextB
              have hdebt :
                  phaseDebt F.b (.live 1) <=
                    longRecoveryReserveUnits F := by
                simp [phaseDebt, longRecoveryReserveUnits]
                omega
              have hnotReady :
                  nextSectorPhase F.B .ready e ≠ .ready := by
                rw [hnextBE]
                simp
              have hdebtNext :
                  phaseDebt F.b
                      (nextSectorPhase F.B .ready e) <=
                    longRecoveryReserveUnits F := by
                rw [hnextBE]
                exact hdebt
              exact
                And.intro
                  (And.intro hBnext
                    (And.intro hnotReady hdebtNext))
                  (by
                    change
                      moderateSealedRecoveryPhase
                        (nextSectorPhase F.B .ready e)
                    rw [hnextBE]
                    simp [moderateSealedRecoveryPhase])
            · rw [dif_neg hout] at hstep
              by_cases hin : e = L_j F
              · rw [dif_pos hin] at hstep
                have hnotTerminal :
                    Not
                      (e = advance ring F.A.left p ∧
                        p + 1 = F.A.gap) := by
                  intro ht
                  have hend : p + 1 = F.a := by
                    simpa [F.A_gap] using ht.2
                  have hdel :=
                    longRowsB_terminalTagged
                      ring F C hgood p hA e
                      ht.1 hend
                      (longRowsB_ready_vulnerable F C hB)
                  exact htag hdel
                obtain ⟨p', hnextA, hpLower, hpUpper⟩ :=
                  longRowsBLiveNext_bounds
                    F.A C p hA e hnotTerminal
                have hrem' : F.a - p' <= 2 * F.b := by
                  omega
                cases hstep
                have hnextB :=
                  longRowsB_ready_Lj_dummy0 F
                have hnextBE :
                    nextSectorPhase F.B .ready e = .dummy 0 := by
                  simpa [hin] using hnextB
                have hBdummy :
                    PhaseHolds F.B (stepE ring C e)
                      (.dummy 0) := by
                  simpa [hnextBE] using hBnext
                have hshield :=
                  moderateSealed_dummyZeroUnshielded
                    F (stepE ring C e) hBdummy
                exact
                  And.intro
                    (And.intro hBnext
                      (And.intro hAnext
                        (And.intro
                          ⟨p', hnextA, hrem'⟩
                          hshield)))
                    (by
                      change
                        longRowsBRetainedTarget
                          (nextSectorPhase F.B .ready e)
                      rw [hnextBE]
                      simp [longRowsBRetainedTarget])
              · rw [dif_neg hin] at hstep
                have hreadyB :=
                  longRowsB_ready_other F e hin hout
                rw [dif_pos hreadyB] at hstep
                have hnotTerminal :
                    Not
                      (e = advance ring F.A.left p ∧
                        p + 1 = F.A.gap) := by
                  intro ht
                  have hend : p + 1 = F.a := by
                    simpa [F.A_gap] using ht.2
                  have heL :=
                    longRowsB_terminalEdge_eq_Lj
                      F e p ht.1 hend
                  exact hin heL
                obtain ⟨p', hnextA, hpLower, hpUpper⟩ :=
                  longRowsBLiveNext_bounds
                    F.A C p hA e hnotTerminal
                have hrem' : F.a - p' <= 2 * F.b := by
                  omega
                cases hstep
                have hBready :
                    PhaseHolds F.B (stepE ring C e) .ready := by
                  simpa [hreadyB] using hBnext
                exact
                  And.intro
                    (And.intro hBready
                      (And.intro hAnext
                        ⟨p', hnextA, hrem'⟩))
                    True.intro
        | retained targetPhase attackPhase =>
            dsimp only at hstep
            change
              PhaseHolds F.B C targetPhase ∧
                PhaseHolds F.A C attackPhase ∧
                (Exists fun p =>
                  attackPhase = .live p ∧
                    F.a - p <= 2 * F.b) ∧
                (C F.j).shield = false at hlegit
            rcases hlegit with
              ⟨hB, hA, hp, hshield⟩
            rcases hp with ⟨p, hattack, hrem⟩
            subst attackPhase
            have hBnext :=
              moderateSealed_phaseBNext
                hSealed ring F C hgood
                targetPhase hB e htag
            have hAnext :=
              moderateSealed_phaseANext
                hSealed ring F C hgood
                (.live p) hA e htag
            by_cases hfail :
                targetPhase = .ready ∧ e = R_j F
            · rw [dif_pos hfail] at hstep
              cases hstep
              have hnextB :
                  nextSectorPhase F.B targetPhase e =
                    .live 1 := by
                rw [hfail.1, hfail.2]
                exact longRowsB_ready_Rj_live1 F hb
              have hdebt :
                  phaseDebt F.b (.live 1) <=
                    longRecoveryReserveUnits F := by
                simp [phaseDebt, longRecoveryReserveUnits]
                omega
              have hnotReady :
                  nextSectorPhase F.B targetPhase e ≠ .ready := by
                rw [hnextB]
                simp
              have hdebtNext :
                  phaseDebt F.b
                      (nextSectorPhase F.B targetPhase e) <=
                    longRecoveryReserveUnits F := by
                rw [hnextB]
                exact hdebt
              exact
                And.intro
                  (And.intro hBnext
                    (And.intro hnotReady hdebtNext))
                  (by
                    change
                      moderateSealedRecoveryPhase
                        (nextSectorPhase F.B targetPhase e)
                    rw [hnextB]
                    simp [moderateSealedRecoveryPhase])
            · rw [dif_neg hfail] at hstep
              have hnotTerminal :
                  Not
                    (e = advance ring F.A.left p ∧
                      p + 1 = F.A.gap) := by
                intro ht
                have hend : p + 1 = F.a := by
                  simpa [F.A_gap] using ht.2
                have hdel :=
                  longRowsB_terminalTagged
                    ring F C hgood p hA e
                    ht.1 hend
                    (longRowsB_unshielded_vulnerable
                      F C hshield)
                exact htag hdel
              obtain ⟨p', hnextA, hpLower, hpUpper⟩ :=
                longRowsBLiveNext_bounds
                  F.A C p hA e hnotTerminal
              have hrem' : F.a - p' <= 2 * F.b := by
                omega
              have htargetNext :=
                longRowsBRetainedTarget_next
                  F targetPhase hextra e hfail
              let x :=
                moderateSealedVulnerableState
                  F C hgood (.live p) targetPhase
                  hA hB hshield
              have hport :
                  x.targetPhase = .ready -> e ≠ F.j := by
                intro hready he
                apply hfail
                refine And.intro ?_ ?_
                · simpa [x, moderateSealedVulnerableState]
                    using hready
                · simpa [R_j] using he
              have hshieldNext :
                  ((stepE ring C e) F.j).shield = false := by
                exact
                  targetUnshielded_after_physical
                    F x e hport
              cases hstep
              exact
                And.intro
                  (And.intro hBnext
                    (And.intro hAnext
                      (And.intro
                        ⟨p', hnextA, hrem'⟩
                        hshieldNext)))
                  htargetNext
        | recovery targetPhase attackPhase =>
            dsimp only at hstep
            change
              PhaseHolds F.B C targetPhase ∧
                targetPhase ≠ .ready ∧
                phaseDebt F.b targetPhase <=
                  longRecoveryReserveUnits F at hlegit
            rcases hlegit with
              ⟨hB, hnotReady, hdebt⟩
            by_cases hready :
                nextSectorPhase F.B targetPhase e = .ready
            · rw [dif_pos hready] at hstep
              cases hstep
            · rw [dif_neg hready] at hstep
              cases hstep
              have hBnext :=
                moderateSealed_phaseBNext
                  hSealed ring F C hgood
                  targetPhase hB e htag
              have hrecNext :=
                moderateSealedRecoveryPhase_next
                  F targetPhase hextra e hready
              have hdebtNext :=
                longRowsBRecoveryDebt_le
                  F hb (stepE ring C e)
                  (nextSectorPhase F.B targetPhase e)
                  hBnext hrecNext
              exact
                And.intro
                  (And.intro hBnext
                    (And.intro hready hdebtNext))
                  hrecNext
        | stuck =>
            exact False.elim hlegit








private theorem longRowsB_postInvariant_cut
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (a : LongAttemptState ring F)
    (h : longRowsBPostInvariant F a) :
    longPostCRCutCorrected F a = true := by
  cases a with
  | junk C =>
      exact False.elim h
  | live C hgood stage =>
      rcases h with ⟨hlegit, hextra⟩
      cases stage with
      | targetCR mode =>
          exact False.elim hextra
      | attackerCR targetPhase mode =>
          exact False.elim hextra
      | liveWait targetPhase attackPhase =>
          rfl
      | advance targetPhase attackPhase =>
          rfl
      | race targetPhase attackPhase =>
          rfl
      | incident attackPhase =>
          rfl
      | retained targetPhase attackPhase =>
          rfl
      | recovery targetPhase attackPhase =>
          rfl
      | stuck =>
          exact False.elim hextra








private theorem longRowsB_after_path
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 <= F.b)
    (hab : 2 * F.b + 1 <= F.a)
    (s : Config n) (hs : AttemptGood ring F s)
    (carrier a : LongAttemptState ring F)
    (hfirst :
      RetryFirstCutReachableCorrected
        (longAttemptKernel ring F)
        (longPostCRCutCorrected F)
        ((longAttemptKernel ring F).start s)
        carrier)
    (hafter :
      RetryActiveAfterCutCorrected
        (longAttemptKernel ring F)
        (longPostCRCutCorrected F)
        carrier a) :
    longRowsBPostInvariant F a := by
  have hcarrier :=
    longRowsB_first_post
      hSealed ring F s hs carrier hfirst
  induction hafter with
  | root hcut =>
      exact hcarrier
  | step h e hstep hcut ih =>
      exact
        longRowsB_post_step
          hSealed ring F hb hab
          _ ih e _ hstep


/-! ## Recovery-only public-potential Bellman row -/


private theorem longRecoveryNode_le_corrected
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (hgood : AttemptGood ring F C)
    (targetPhase attackPhase : SectorPhase)
    (e : Fin n) :
    attemptNodePotLong
        (longRawPhiCorrected ring F)
        ((longAttemptKernel ring F).step
          (.live C hgood
            (.recovery targetPhase attackPhase)) e) ≤
      n * phaseDebt F.b
        (nextSectorPhase F.B targetPhase e) := by
  classical
  simp only [longAttemptKernel]
  unfold longStep
  dsimp only
  by_cases htag :
      TaggedDeleted F (stepE ring C e)
  · rw [dif_pos htag]
    simp [attemptNodePotLong]
  · rw [dif_neg htag]
    by_cases hready :
        nextSectorPhase F.B targetPhase e = .ready
    · rw [dif_pos hready]
      simp [attemptNodePotLong]
    · rw [dif_neg hready]
      simp [attemptNodePotLong, longRawPhiCorrected,
        longStageUnits]




private theorem longRecovery_bellman_corrected
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 ≤ F.b)
    (C : Config n) (hgood : AttemptGood ring F C)
    (targetPhase attackPhase : SectorPhase)
    (hB : PhaseHolds F.B C targetPhase)
    (hne : targetPhase ≠ .ready) :
    n +
        (List.ofFn (fun e : Fin n =>
          attemptNodePotLong
            (longRawPhiCorrected ring F)
            ((longAttemptKernel ring F).step
              (.live C hgood
                (.recovery targetPhase attackPhase)) e))).sum ≤
      n * longRawPhiCorrected ring F
        (.live C hgood
          (.recovery targetPhase attackPhase)) := by
  let f : Fin n → Nat :=
    fun e =>
      attemptNodePotLong
        (longRawPhiCorrected ring F)
        ((longAttemptKernel ring F).step
          (.live C hgood
            (.recovery targetPhase attackPhase)) e)
  have hpos :=
    moderateSealed_phaseDebt_pos
      F hb C targetPhase hB hne
  obtain ⟨service, hdrop, hstutter⟩ :=
    moderateSealed_phaseDebt_service
      F hb C targetPhase hB hne
  have hservice :
      f service ≤
        n * (phaseDebt F.b targetPhase - 1) := by
    have hn :=
      longRecoveryNode_le_corrected
        ring F C hgood
        targetPhase attackPhase service
    dsimp only [f]
    exact
      Nat.le_trans hn
        (Nat.mul_le_mul_left n (by omega))
  have hother :
      ∀ e, e ≠ service →
        f e ≤ n * phaseDebt F.b targetPhase := by
    intro e he
    have hn :=
      longRecoveryNode_le_corrected
        ring F C hgood
        targetPhase attackPhase e
    dsimp only [f]
    rw [hstutter e he] at hn
    exact hn
  have hpay0 :
      1 + (phaseDebt F.b targetPhase - 1) ≤
        phaseDebt F.b targetPhase := by
    omega
  have hpay :=
    Nat.mul_le_mul_left n hpay0
  have hpay' :
      n + n * (phaseDebt F.b targetPhase - 1) ≤
        n * phaseDebt F.b targetPhase := by
    simpa [Nat.mul_add, Nat.mul_one] using hpay
  have h :=
    moderateSealed_oneExceptionBound
      service f hservice hother hpay'
  simpa [f, longRawPhiCorrected,
    longStageUnits] using h




private def longRecoveryCorePrivateName (stem : String) : Lean.Name :=
  let base :=
    Lean.Name.str Lean.Name.anonymous ("_" ++ "private")
  let modName :=
    (((base.str "Leader").str "PPL").str "Elim").str
      "AttemptCostLongStep"
  let privateRoot := (modName.num 0).str "PPL"
  (((privateRoot.str "Convergence").str "LDLocal").str stem)

elab "unfoldLongRecoveryRawPhi" : tactic => do
  let nm := Lean.mkIdent (longRecoveryCorePrivateName "longRawPhi")
  let tac ← `(tactic| unfold $nm:ident)
  Lean.Elab.Tactic.evalTactic tac



theorem longRecoveryPostCarrierResidual_proved :
    LongRecoveryPostCarrierResidual := by
  unfold LongRecoveryPostCarrierResidual
  intro hSealed n ring C0 F hb hab
  intro s carrier C hgoodC
  intro targetPhase attackPhase
  intro hgoodS hfirst hafter


  have hinv :=
    longRowsB_after_path
      hSealed ring F hb hab
      s hgoodS carrier
      (.live C hgoodC
        (.recovery targetPhase attackPhase))
      hfirst hafter


  have hlegit :
      longStageLegit F C
        (.recovery targetPhase attackPhase) :=
    hinv.1


  refine
    And.intro hlegit
      (And.intro ?_ ?_)


  · intro e a' hstep
    have hchild :=
      longRowsB_post_step
        hSealed ring F hb hab
        (.live C hgoodC
          (.recovery targetPhase attackPhase))
        hinv e a' hstep
    exact
      longRowsB_postInvariant_cut F a' hchild


  · change
      LongLocalStageRow
        ring F C hgoodC
          (.recovery targetPhase attackPhase)
    refine And.intro ?_ ?_


    · intro e a' hstep
      have hchild :=
        longRowsB_post_step
          hSealed ring F hb hab
          (.live C hgoodC
            (.recovery targetPhase attackPhase))
          hinv e a' hstep
      cases a' with
      | junk D =>
          exact False.elim hchild
      | live D hgoodD stage' =>
          exact hchild.1


    · have hbell :=
        longRecovery_bellman_corrected
          ring F hb C hgoodC
          targetPhase attackPhase
          hlegit.1 hlegit.2.1
      unfoldLongRecoveryRawPhi
      try simp only [longRawPhiCorrected, attemptNodePotLong] at hbell
      try simp only [attemptNodePotLong]
      first
      | exact hbell
      | (refine Nat.le_trans (Nat.le_of_eq ?_) hbell
         congr 1
         congr 1
         congr 1
         funext e
         generalize (longAttemptKernel ring F).step _ e = x
         cases x with
         | active a => cases a <;> rfl
         | _ => rfl)




end PPL.Convergence.LDLocal




#print axioms PPL.Convergence.LDLocal.longRecoveryPostCarrierResidual_proved


