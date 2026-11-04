import Leader.PPL.Elim.AttemptLongRetainedBridge
import Leader.PPL.Elim.AttemptLongTargetCleanReadyDone
import Leader.PPL.Elim.AttemptCostModerateSealed
import Leader.PPL.Elim.BoundaryRegime
import Leader.PPL.Elim.AttemptCostLongLive


namespace PPL.Convergence.LDLocal


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


open FiniteUniformStoppingTree


/-!
# First-incident retained root


The first-incident carrier is path-sensitive: the raw LongAttemptState type
also contains synthetic stage constructors.  The small invariant below follows
the literal longStep path from the supplied good start only until the first
retained cut.


Before the post-CR launch, target CR needs no phase witness, while attacker CR
carries the current target phase.  After launch, liveWait/advance/race carry
the ordinary longStageLegit witness plus the fact that a live target phase has
positive offset.  Incident carries longStageLegit.  Recovery and stuck can
never actively return to a retained state, so no stronger payload is required
there.


At the first active retained child, the parent can therefore only be the
literal race-ready/L_j or incident/L_j branch.  Both branches in longStep set
the target phase to


  nextSectorPhase F.B .ready (L_j F) = .dummy 0.


The RetainedState fields are then:
* base.cfg          := the physical child stepE ring C e;
* base.attackPhase  := nextSectorPhase F.A (.live p) e;
* base.targetPhase  := .dummy 0;
* base.hAttack/hTarget are SealedStepSpec transports;
* base.alive        := attemptGood_step(...).2.1;
* base.targetUnshielded comes from moderateSealed_dummyZeroUnshielded;
* p                 := the live coordinate p' after the L_j step;
* phase_eq          := the equality produced by the live-phase transition;
* remaining_le      := F.a - p' <= 2*F.b, inherited from p <= p'.
-/


private def retainedRootTargetGood : SectorPhase -> Prop
  | .ready => True
  | .dummy _ => True
  | .live p => 0 < p
  | .ret _ => True


private def retainedRootNonLive : SectorPhase -> Prop
  | .ready => True
  | .dummy _ => True
  | .live _ => False
  | .ret _ => True


private def retainedRootPreInv
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0) :
    LongAttemptState ring F -> Prop
  | .junk _ => False
  | .live C _ stage =>
      match stage with
      | .targetCR _ => True
      | .attackerCR targetPhase _ =>
          PhaseHolds F.B C targetPhase /\
            retainedRootTargetGood targetPhase
      | .stuck => True
      | _ => False


private def retainedRootPostInv
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0) :
    LongAttemptState ring F -> Prop
  | .junk _ => False
  | .live C _ stage =>
      match stage with
      | .liveWait targetPhase attackPhase =>
          longStageLegit F C (.liveWait targetPhase attackPhase) /\
            retainedRootTargetGood targetPhase
      | .advance targetPhase attackPhase =>
          longStageLegit F C (.advance targetPhase attackPhase) /\
            retainedRootTargetGood targetPhase
      | .race targetPhase attackPhase =>
          longStageLegit F C (.race targetPhase attackPhase) /\
            retainedRootTargetGood targetPhase
      | .incident attackPhase =>
          longStageLegit F C (.incident attackPhase)
      | .recovery _ _ => True
      | .stuck => True
      | _ => False


private def retainedRootInv
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (a : LongAttemptState ring F) : Prop :=
  retainedRootPreInv F a \/ retainedRootPostInv F a


private theorem retainedRoot_phaseReady
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n)
    (hInterior : CRInteriorFollowers A C)
    (hclean : CleanReady A C) :
    PhaseHolds A C .ready := by
  exact And.intro hInterior hclean


private theorem retainedRootTargetGood_next
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (A : SectorFrame ring C0)
    (ph : SectorPhase)
    (h : retainedRootTargetGood ph)
    (e : Fin n) :
    retainedRootTargetGood (nextSectorPhase A ph e) := by
  cases ph with
  | ready =>
      by_cases hin : e = sealedIncomingEdge A
      · simp [nextSectorPhase, hin, retainedRootTargetGood]
      · by_cases hout : e = A.left
        · have hleft : A.left ≠ sealedIncomingEdge A := by
            intro heq
            exact hin (hout.trans heq)
          by_cases hgap : A.gap = 1
          · simp [nextSectorPhase, hin, hout, hleft, hgap,
              retainedRootTargetGood]
          · simp [nextSectorPhase, hin, hout, hleft, hgap,
              retainedRootTargetGood]
        · simp [nextSectorPhase, hin, hout,
            retainedRootTargetGood]
  | dummy p =>
      by_cases hs : e = advance ring A.left p
      · by_cases hlt : p + 1 < A.gap
        · simp [nextSectorPhase, hs, hlt,
            retainedRootTargetGood]
        · by_cases hgap : A.gap = 1
          · simp [nextSectorPhase, hs, hlt, hgap,
              retainedRootTargetGood]
          · simp [nextSectorPhase, hs, hlt, hgap,
              retainedRootTargetGood]
      · simp [nextSectorPhase, hs, retainedRootTargetGood]
  | live p =>
      have hp : 0 < p := h
      by_cases hs : e = advance ring A.left p
      · by_cases hlt : p + 1 < A.gap
        · have hp1 : 0 < p + 1 := by omega
          simpa [nextSectorPhase, hs, hlt,
            retainedRootTargetGood] using hp1
        · by_cases hgap : A.gap = 1
          · simp [nextSectorPhase, hs, hlt, hgap,
              retainedRootTargetGood]
          · simp [nextSectorPhase, hs, hlt, hgap,
              retainedRootTargetGood]
      · simpa [nextSectorPhase, hs, retainedRootTargetGood]
          using hp
  | ret q =>
      by_cases hs : e = advance ring A.left (q - 1)
      · by_cases hq : q = 1
        · simp [nextSectorPhase, hs, hq,
            retainedRootTargetGood]
        · simp [nextSectorPhase, hs, hq,
            retainedRootTargetGood]
      · simp [nextSectorPhase, hs, retainedRootTargetGood]


private theorem retainedRootNonLive_next
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (A : SectorFrame ring C0)
    (ph : SectorPhase)
    (h : retainedRootNonLive ph)
    (e : Fin n)
    (hfire : Not (ph = .ready /\ e = A.left)) :
    retainedRootNonLive (nextSectorPhase A ph e) := by
  cases ph with
  | ready =>
      have hsrc : e ≠ A.left := by
        intro he
        exact hfire (And.intro rfl he)
      by_cases hin : e = sealedIncomingEdge A
      · simp [nextSectorPhase, hin, retainedRootNonLive]
      · simp [nextSectorPhase, hin, hsrc,
          retainedRootNonLive]
  | dummy p =>
      by_cases hs : e = advance ring A.left p
      · by_cases hlt : p + 1 < A.gap
        · simp [nextSectorPhase, hs, hlt,
            retainedRootNonLive]
        · by_cases hgap : A.gap = 1
          · simp [nextSectorPhase, hs, hlt, hgap,
              retainedRootNonLive]
          · simp [nextSectorPhase, hs, hlt, hgap,
              retainedRootNonLive]
      · simp [nextSectorPhase, hs, retainedRootNonLive]
  | live p =>
      exact False.elim h
  | ret q =>
      by_cases hs : e = advance ring A.left (q - 1)
      · by_cases hq : q = 1
        · simp [nextSectorPhase, hs, hq,
            retainedRootNonLive]
        · simp [nextSectorPhase, hs, hq,
            retainedRootNonLive]
      · simp [nextSectorPhase, hs, retainedRootNonLive]


private theorem retainedRootLiveNext_bounds
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (p : Nat)
    (hphase : PhaseHolds A C (.live p))
    (e : Fin n)
    (hterminal :
      Not (e = advance ring A.left p /\ p + 1 = A.gap)) :
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


private theorem retainedRoot_rightNeighbor_advance
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (p : Nat) :
    ring.rightNeighbor (advance ring i p) =
      advance ring i (p + 1) := by
  change advance ring (advance ring i p) 1 =
    advance ring i (p + 1)
  simpa using advance_add ring i p 1


private theorem retainedRoot_terminalEdge_eq_Lj
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
      retainedRoot_rightNeighbor_advance ring F.A.left p
    _ = advance ring F.A.left F.a := by rw [hend]
    _ = F.A.right := by
      simpa [F.A_gap] using F.A.right_eq
    _ = F.j := F.A_right
    _ = ring.rightNeighbor (L_j F) := by
      unfold L_j
      exact (rightNeighbor_leftNeighbor_twoLeader ring F.j).symm


private theorem retainedRoot_ready_vulnerable
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


private theorem retainedRoot_terminalTagged
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
    retainedRoot_terminalEdge_eq_Lj
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


private theorem retainedRoot_ready_Lj_dummy0
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0) :
    nextSectorPhase F.B .ready (L_j F) = .dummy 0 := by
  rw [<- sealedIncomingEdge_B_eq_L_j F]
  simp [nextSectorPhase]


private theorem retainedRoot_ready_other
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


/-! Literal start mirror.  This is source-identical to the private longStart
choice path, so proof irrelevance makes the mirror definitionally equal. -/


private noncomputable def retainedRootCRInitMode
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


private noncomputable def retainedRootAfterTargetStage
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) : LongStage := by
  classical
  if hA : CleanReady F.A D then
    exact .liveWait .ready .ready
  else
    exact .attackerCR .ready
      (retainedRootCRInitMode ring F.A D hgood.1
        (moderateSealed_notEndpointA F D hgood) hA)


private noncomputable def retainedRootInitialStage
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) : LongStage := by
  classical
  if hB : CleanReady F.B D then
    exact retainedRootAfterTargetStage ring F D hgood
  else
    exact .targetCR
      (retainedRootCRInitMode ring F.B D hgood.1
        (moderateSealed_notEndpointB F D hgood) hB)


private noncomputable def retainedRootStart
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) : LongAttemptState ring F := by
  classical
  if hgood : AttemptGood ring F D then
    exact .live D hgood
      (retainedRootInitialStage ring F D hgood)
  else
    exact .junk D


private theorem retainedRoot_start_eq
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) :
    (longAttemptKernel ring F).start D =
      retainedRootStart ring F D := by
  rfl


private theorem retainedRoot_start_inv
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n) (hs : AttemptGood ring F s) :
    retainedRootInv F
      ((longAttemptKernel ring F).start s) := by
  classical
  rw [retainedRoot_start_eq]
  unfold retainedRootStart
  rw [dif_pos hs]
  unfold retainedRootInitialStage
  by_cases hB : CleanReady F.B s
  · rw [dif_pos hB]
    unfold retainedRootAfterTargetStage
    by_cases hA : CleanReady F.A s
    · rw [dif_pos hA]
      right
      exact
        And.intro
          (And.intro
            (retainedRoot_phaseReady F.B s hs.2.2.2 hB)
            (And.intro
              (retainedRoot_phaseReady F.A s hs.2.2.1 hA)
              True.intro))
          True.intro
    · rw [dif_neg hA]
      left
      exact
        And.intro
          (retainedRoot_phaseReady F.B s hs.2.2.2 hB)
          True.intro
  · rw [dif_neg hB]
    left
    exact True.intro


private theorem retainedRoot_inv_cut_false
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (a : LongAttemptState ring F)
    (h : retainedRootInv F a) :
    longIncidentWonCut ring F a = false := by
  cases a with
  | junk C =>
      rfl
  | live C hgood stage =>
      cases stage with
      | targetCR mode => rfl
      | attackerCR targetPhase mode => rfl
      | liveWait targetPhase attackPhase => rfl
      | advance targetPhase attackPhase => rfl
      | race targetPhase attackPhase => rfl
      | incident attackPhase => rfl
      | retained targetPhase attackPhase =>
          have hf : False := by
            rcases h with hpre | hpost
            · exact hpre
            · exact hpost
          exact False.elim hf
      | recovery targetPhase attackPhase => rfl
      | stuck => rfl


private theorem retainedRoot_pre_step
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (a : LongAttemptState ring F)
    (ha : retainedRootPreInv F a)
    (e : Fin n) (a' : LongAttemptState ring F)
    (hstep :
      (longAttemptKernel ring F).step a e = .active a') :
    retainedRootInv F a' := by
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
                  retainedRoot_phaseReady
                    F.B (stepE ring C e)
                    hgoodD.2.2.2 hcleanB
                unfoldLongAfterTargetStage
                by_cases hA :
                    CleanReady F.A (stepE ring C e)
                · rw [dif_pos hA]
                  right
                  have hAready :=
                    retainedRoot_phaseReady
                      F.A (stepE ring C e)
                      hgoodD.2.2.1 hA
                  exact
                    And.intro
                      (And.intro hBready
                        (And.intro hAready True.intro))
                      True.intro
                · rw [dif_neg hA]
                  left
                  exact And.intro hBready True.intro
              · rw [dif_neg hdone] at hstep
                cases hstep
                left
                exact True.intro
            · rw [dif_neg hmode] at hstep
              cases hstep
              left
              exact True.intro
        | attackerCR targetPhase mode =>
            dsimp only at hstep
            change
              PhaseHolds F.B C targetPhase /\
                retainedRootTargetGood targetPhase at ha
            rcases ha with ⟨hB, htarget⟩
            by_cases hmode : CRModeHolds F.A C mode
            · rw [dif_pos hmode] at hstep
              have hBnext :=
                moderateSealed_phaseBNext
                  hSealed ring F C hgood
                  targetPhase hB e htag
              have htargetNext :=
                retainedRootTargetGood_next
                  F.B targetPhase htarget e
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
                have hAready :=
                  retainedRoot_phaseReady
                    F.A (stepE ring C e)
                    hgoodD.2.2.1 hcleanA
                right
                exact
                  And.intro
                    (And.intro hBnext
                      (And.intro hAready True.intro))
                    htargetNext
              · rw [dif_neg hdone] at hstep
                cases hstep
                left
                exact And.intro hBnext htargetNext
            · rw [dif_neg hmode] at hstep
              cases hstep
              left
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
            left
            exact True.intro


private theorem retainedRoot_liveWait_legit
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n)
    (targetPhase attackPhase : SectorPhase)
    (h :
      longStageLegit F C
        (.liveWait targetPhase attackPhase)) :
    PhaseHolds F.B C targetPhase /\
      PhaseHolds F.A C attackPhase /\
      retainedRootNonLive attackPhase := by
  rcases h with ⟨hB, hA, hnon⟩
  refine And.intro hB (And.intro hA ?_)
  cases attackPhase <;>
    simpa [retainedRootNonLive] using hnon


private theorem retainedRoot_post_step
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 <= F.b)
    (hab : 2 * F.b + 1 <= F.a)
    (a : LongAttemptState ring F)
    (ha : retainedRootPostInv F a)
    (e : Fin n) (a' : LongAttemptState ring F)
    (hstep :
      (longAttemptKernel ring F).step a e = .active a')
    (hcut : longIncidentWonCut ring F a' = false) :
    retainedRootPostInv F a' := by
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
            exact False.elim ha
        | attackerCR targetPhase mode =>
            exact False.elim ha
        | liveWait targetPhase attackPhase =>
            change
              longStageLegit F C
                  (.liveWait targetPhase attackPhase) /\
                retainedRootTargetGood targetPhase at ha
            rcases ha with ⟨hlegit, htarget⟩
            dsimp only at hstep
            have hlegit' :=
              retainedRoot_liveWait_legit
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
              retainedRootTargetGood_next
                F.B targetPhase htarget e
            by_cases hfire :
                attackPhase = .ready /\ e = F.A.left
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
                exact
                  And.intro hBnext
                    (And.intro hAnext
                      ⟨1, hnextA, by omega⟩)
              · rw [dif_neg hnear] at hstep
                cases hstep
                refine And.intro ?_ htargetNext
                exact
                  And.intro hBnext
                    (And.intro hAnext
                      ⟨1, hnextA, by omega, by omega⟩)
            · rw [dif_neg hfire] at hstep
              cases hstep
              have hnonLiveNext :=
                retainedRootNonLive_next
                  F.A attackPhase hnonLive e hfire
              have hshape :
                  match nextSectorPhase F.A attackPhase e with
                  | .live _ => False
                  | _ => True := by
                cases hph :
                    nextSectorPhase F.A attackPhase e <;>
                  simp [hph, retainedRootNonLive] at hnonLiveNext ⊢
              exact
                And.intro
                  (And.intro hBnext
                    (And.intro hAnext hshape))
                  htargetNext
        | advance targetPhase attackPhase =>
            change
              longStageLegit F C
                  (.advance targetPhase attackPhase) /\
                retainedRootTargetGood targetPhase at ha
            rcases ha with ⟨hlegit, htarget⟩
            dsimp only at hstep
            change
              PhaseHolds F.B C targetPhase /\
                PhaseHolds F.A C attackPhase /\
                Exists fun p =>
                  attackPhase = .live p /\
                    0 < p /\
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
              retainedRootTargetGood_next
                F.B targetPhase htarget e
            have hnotTerminal :
                Not
                  (e = advance ring F.A.left p /\
                    p + 1 = F.A.gap) := by
              intro ht
              have hgap : F.A.gap = F.a := F.A_gap
              omega
            obtain ⟨p', hnextA, hpLower, hpUpper⟩ :=
              retainedRootLiveNext_bounds
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
            change
              longStageLegit F C
                  (.race targetPhase attackPhase) /\
                retainedRootTargetGood targetPhase at ha
            rcases ha with ⟨hlegit, htarget⟩
            dsimp only at hstep
            change
              PhaseHolds F.B C targetPhase /\
                PhaseHolds F.A C attackPhase /\
                Exists fun p =>
                  attackPhase = .live p /\
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
                exact True.intro
              · rw [dif_neg hout] at hstep
                by_cases hin : e = L_j F
                · rw [dif_pos hin] at hstep
                  cases hstep
                  simp [longIncidentWonCut] at hcut
                · rw [dif_neg hin] at hstep
                  cases hstep
                  have hreadyB :=
                    retainedRoot_ready_other F e hin hout
                  have hnotTerminal :
                      Not
                        (e = advance ring F.A.left p /\
                          p + 1 = F.A.gap) := by
                    intro ht
                    have hend : p + 1 = F.a := by
                      simpa [F.A_gap] using ht.2
                    have heL :=
                      retainedRoot_terminalEdge_eq_Lj
                        F e p ht.1 hend
                    exact hin heL
                  obtain ⟨p', hnextA, hpLower, hpUpper⟩ :=
                    retainedRootLiveNext_bounds
                      F.A C p hA e hnotTerminal
                  have hrem' : F.a - p' <= 2 * F.b := by
                    omega
                  have hBready :
                      PhaseHolds F.B (stepE ring C e) .ready := by
                    simpa [hreadyB] using hBnext
                  exact
                    And.intro hBready
                      (And.intro hAnext
                        ⟨p', hnextA, hrem'⟩)
            · rw [dif_neg hready] at hstep
              by_cases hhit :
                  Exists fun q =>
                    And ((.live p : SectorPhase) = .live q)
                      (And
                        (e = advance ring F.A.left q)
                        (q + 1 = F.a))
              · rw [dif_pos hhit] at hstep
                cases hstep
                exact True.intro
              · rw [dif_neg hhit] at hstep
                have hnotTerminal :
                    Not
                      (e = advance ring F.A.left p /\
                        p + 1 = F.A.gap) := by
                  intro ht
                  apply hhit
                  refine ⟨p, rfl, ht.1, ?_⟩
                  simpa [F.A_gap] using ht.2
                obtain ⟨p', hnextA, hpLower, hpUpper⟩ :=
                  retainedRootLiveNext_bounds
                    F.A C p hA e hnotTerminal
                have hrem' : F.a - p' <= 2 * F.b := by
                  omega
                by_cases hready :
                    nextSectorPhase F.B targetPhase e = .ready
                · rw [dif_pos hready] at hstep
                  cases hstep
                  have hBready :
                      PhaseHolds F.B (stepE ring C e) .ready := by
                    simpa [hready] using hBnext
                  exact
                    And.intro hBready
                      (And.intro hAnext
                        ⟨p', hnextA, hrem'⟩)
                · rw [dif_neg hready] at hstep
                  cases hstep
                  have htargetNext :=
                    retainedRootTargetGood_next
                      F.B targetPhase htarget e
                  exact
                    And.intro
                      (And.intro hBnext
                        (And.intro hAnext
                          ⟨p', hnextA, hrem'⟩))
                      htargetNext
        | incident attackPhase =>
            change
              longStageLegit F C
                (.incident attackPhase) at ha
            dsimp only at hstep
            change
              PhaseHolds F.B C .ready /\
                PhaseHolds F.A C attackPhase /\
                Exists fun p =>
                  attackPhase = .live p /\
                    F.a - p <= 2 * F.b at ha
            rcases ha with
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
              exact True.intro
            · rw [dif_neg hout] at hstep
              by_cases hin : e = L_j F
              · rw [dif_pos hin] at hstep
                cases hstep
                simp [longIncidentWonCut] at hcut
              · rw [dif_neg hin] at hstep
                have hreadyB :=
                  retainedRoot_ready_other F e hin hout
                rw [dif_pos hreadyB] at hstep
                have hnotTerminal :
                    Not
                      (e = advance ring F.A.left p /\
                        p + 1 = F.A.gap) := by
                  intro ht
                  have hend : p + 1 = F.a := by
                    simpa [F.A_gap] using ht.2
                  have heL :=
                    retainedRoot_terminalEdge_eq_Lj
                      F e p ht.1 hend
                  exact hin heL
                obtain ⟨p', hnextA, hpLower, hpUpper⟩ :=
                  retainedRootLiveNext_bounds
                    F.A C p hA e hnotTerminal
                have hrem' : F.a - p' <= 2 * F.b := by
                  omega
                cases hstep
                have hBready :
                    PhaseHolds F.B (stepE ring C e) .ready := by
                  simpa [hreadyB] using hBnext
                exact
                  And.intro hBready
                    (And.intro hAnext
                      ⟨p', hnextA, hrem'⟩)
        | retained targetPhase attackPhase =>
            exact False.elim ha
        | recovery targetPhase attackPhase =>
            change True at ha
            dsimp only at hstep
            by_cases hready :
                nextSectorPhase F.B targetPhase e = .ready
            · rw [dif_pos hready] at hstep
              cases hstep
            · rw [dif_neg hready] at hstep
              cases hstep
              exact True.intro
        | stuck =>
            change True at ha
            dsimp only at hstep
            cases hstep
            exact True.intro


private theorem retainedRoot_before_inv
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 <= F.b)
    (hab : 2 * F.b + 1 <= F.a)
    (s : Config n) (hs : AttemptGood ring F s)
    (a : LongAttemptState ring F)
    (h :
      RetryActiveBeforeCut
        (longAttemptKernel ring F)
        (longIncidentWonCut ring F)
        ((longAttemptKernel ring F).start s)
        a) :
    retainedRootInv F a := by
  induction h with
  | root hroot =>
      exact retainedRoot_start_inv ring F s hs
  | step h e hstep hcut ih =>
      rcases ih with hpre | hpost
      · exact
          retainedRoot_pre_step
            hSealed ring F _ hpre e _ hstep
      · exact Or.inr
          (retainedRoot_post_step
            hSealed ring F hb hab
            _ hpost e _ hstep hcut)


/-! The exact payload constructor at either first winning branch. -/


private theorem retainedRoot_ready_left_payload
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (hgood : AttemptGood ring F C)
    (p : Nat)
    (hB : PhaseHolds F.B C .ready)
    (hA : PhaseHolds F.A C (.live p))
    (hrem : F.a - p <= 2 * F.b)
    (e : Fin n)
    (htag : Not (TaggedDeleted F (stepE ring C e)))
    (hin : e = L_j F) :
    Exists fun r : RetainedState F =>
      And
        (r.base.targetPhase = .dummy 0)
        (longRetainedVulnerableRel F
          (.live
            (stepE ring C e)
            (attemptGood_step ring F C e hgood htag)
            (.retained
              (nextSectorPhase F.B .ready e)
              (nextSectorPhase F.A (.live p) e)))
          r.base) := by
  let D := stepE ring C e
  have hgoodD :
      AttemptGood ring F D := by
    exact attemptGood_step ring F C e hgood htag
  have hBnext :=
    moderateSealed_phaseBNext
      hSealed ring F C hgood .ready hB e htag
  have hAnext :=
    moderateSealed_phaseANext
      hSealed ring F C hgood (.live p) hA e htag
  have hnotTerminal :
      Not
        (e = advance ring F.A.left p /\
          p + 1 = F.A.gap) := by
    intro ht
    have hend : p + 1 = F.a := by
      simpa [F.A_gap] using ht.2
    have hdel :=
      retainedRoot_terminalTagged
        ring F C hgood p hA e
        ht.1 hend
        (retainedRoot_ready_vulnerable F C hB)
    exact htag hdel
  obtain ⟨p', hnextA, hpLower, hpUpper⟩ :=
    retainedRootLiveNext_bounds
      F.A C p hA e hnotTerminal
  have hrem' : F.a - p' <= 2 * F.b := by
    omega
  have hnextB0 :
      nextSectorPhase F.B .ready e = .dummy 0 := by
    simpa [hin] using retainedRoot_ready_Lj_dummy0 F
  have hA' :
      PhaseHolds F.A D (.live p') := by
    simpa [D, hnextA] using hAnext
  have hB' :
      PhaseHolds F.B D (.dummy 0) := by
    simpa [D, hnextB0] using hBnext
  have hshield :
      (D F.j).shield = false :=
    moderateSealed_dummyZeroUnshielded F D hB'
  let x : VulnerableState F :=
    moderateSealedVulnerableState
      F D hgoodD (.live p') (.dummy 0)
      hA' hB' hshield
  let r : RetainedState F := {
    base := x
    p := p'
    phase_eq := rfl
    remaining_le := hrem'
  }
  refine ⟨r, ?_, ?_⟩
  · rfl
  · change
      And
        (x.cfg = stepE ring C e)
        (And
          (x.attackPhase =
            nextSectorPhase F.A (.live p) e)
          (x.targetPhase =
            nextSectorPhase F.B .ready e))
    exact
      And.intro rfl
        (And.intro hnextA.symm hnextB0.symm)


private theorem retainedRoot_post_first_cut
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (a : LongAttemptState ring F)
    (ha : retainedRootPostInv F a)
    (e : Fin n) (a' : LongAttemptState ring F)
    (hstep :
      (longAttemptKernel ring F).step a e = .active a')
    (hcut : longIncidentWonCut ring F a' = true) :
    Exists fun r : RetainedState F =>
      And
        (r.base.targetPhase = .dummy 0)
        (longRetainedVulnerableRel F a' r.base) := by
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
            exact False.elim ha
        | attackerCR targetPhase mode =>
            exact False.elim ha
        | liveWait targetPhase attackPhase =>
            dsimp only at hstep
            by_cases hfire :
                attackPhase = .ready /\ e = F.A.left
            · rw [dif_pos hfire] at hstep
              by_cases hnear : F.a - 2 * F.b <= 1
              · rw [dif_pos hnear] at hstep
                cases hstep
                simp [longIncidentWonCut] at hcut
              · rw [dif_neg hnear] at hstep
                cases hstep
                simp [longIncidentWonCut] at hcut
            · rw [dif_neg hfire] at hstep
              cases hstep
              simp [longIncidentWonCut] at hcut
        | advance targetPhase attackPhase =>
            dsimp only at hstep
            by_cases hreach :
                nextSectorPhase F.A attackPhase e =
                  .live (F.a - 2 * F.b)
            · rw [dif_pos hreach] at hstep
              cases hstep
              simp [longIncidentWonCut] at hcut
            · rw [dif_neg hreach] at hstep
              cases hstep
              simp [longIncidentWonCut] at hcut
        | race targetPhase attackPhase =>
            change
              longStageLegit F C
                  (.race targetPhase attackPhase) /\
                retainedRootTargetGood targetPhase at ha
            rcases ha with ⟨hlegit, htarget⟩
            change
              PhaseHolds F.B C targetPhase /\
                PhaseHolds F.A C attackPhase /\
                Exists fun p =>
                  attackPhase = .live p /\
                    F.a - p <= 2 * F.b at hlegit
            rcases hlegit with
              ⟨hB, hA, p, hattack, hrem⟩
            subst attackPhase
            dsimp only at hstep
            by_cases hready : targetPhase = .ready
            · rw [dif_pos hready] at hstep
              subst targetPhase
              by_cases hout : e = R_j F
              · rw [dif_pos hout] at hstep
                cases hstep
                simp [longIncidentWonCut] at hcut
              · rw [dif_neg hout] at hstep
                by_cases hin : e = L_j F
                · rw [dif_pos hin] at hstep
                  cases hstep
                  exact
                    retainedRoot_ready_left_payload
                      hSealed ring F C hgood p
                      hB hA hrem e htag hin
                · rw [dif_neg hin] at hstep
                  cases hstep
                  simp [longIncidentWonCut] at hcut
            · rw [dif_neg hready] at hstep
              by_cases hhit :
                  Exists fun q =>
                    And ((.live p : SectorPhase) = .live q)
                      (And
                        (e = advance ring F.A.left q)
                        (q + 1 = F.a))
              · rw [dif_pos hhit] at hstep
                cases hstep
                simp [longIncidentWonCut] at hcut
              · rw [dif_neg hhit] at hstep
                by_cases htarget :
                    nextSectorPhase F.B targetPhase e = .ready
                · rw [dif_pos htarget] at hstep
                  cases hstep
                  simp [longIncidentWonCut] at hcut
                · rw [dif_neg htarget] at hstep
                  cases hstep
                  simp [longIncidentWonCut] at hcut
        | incident attackPhase =>
            change
              longStageLegit F C
                (.incident attackPhase) at ha
            change
              PhaseHolds F.B C .ready /\
                PhaseHolds F.A C attackPhase /\
                Exists fun p =>
                  attackPhase = .live p /\
                    F.a - p <= 2 * F.b at ha
            rcases ha with
              ⟨hB, hA, p, hattack, hrem⟩
            subst attackPhase
            dsimp only at hstep
            by_cases hout : e = R_j F
            · rw [dif_pos hout] at hstep
              cases hstep
              simp [longIncidentWonCut] at hcut
            · rw [dif_neg hout] at hstep
              by_cases hin : e = L_j F
              · rw [dif_pos hin] at hstep
                cases hstep
                exact
                  retainedRoot_ready_left_payload
                    hSealed ring F C hgood p
                    hB hA hrem e htag hin
              · rw [dif_neg hin] at hstep
                by_cases hready :
                    nextSectorPhase F.B .ready e = .ready
                · rw [dif_pos hready] at hstep
                  cases hstep
                  simp [longIncidentWonCut] at hcut
                · rw [dif_neg hready] at hstep
                  cases hstep
                  simp [longIncidentWonCut] at hcut
        | retained targetPhase attackPhase =>
            exact False.elim ha
        | recovery targetPhase attackPhase =>
            dsimp only at hstep
            by_cases hready :
                nextSectorPhase F.B targetPhase e = .ready
            · rw [dif_pos hready] at hstep
              cases hstep
            · rw [dif_neg hready] at hstep
              cases hstep
              simp [longIncidentWonCut] at hcut
        | stuck =>
            dsimp only at hstep
            cases hstep
            simp [longIncidentWonCut] at hcut


theorem longRetainedControlBridge_proved :
    LongRetainedControlBridge := by
  unfold LongRetainedControlBridge
  intro hSealed n ring C0 F hb hab
  intro s a hfirst hcut
  rcases hfirst with ⟨hs, hfirst⟩
  rcases hfirst with hroot | hstepCase
  · rcases hroot with ⟨ha, hrootCut⟩
    subst a
    have hinv :=
      retainedRoot_start_inv ring F s hs
    have hfalse :=
      retainedRoot_inv_cut_false
        ring F ((longAttemptKernel ring F).start s) hinv
    rw [hrootCut] at hfalse
    cases hfalse
  · rcases hstepCase with
      ⟨pstate, hbefore, e, hstep, hchildCut⟩
    have hp :=
      retainedRoot_before_inv
        hSealed ring F hb hab
        s hs pstate hbefore
    rcases hp with hpre | hpost
    · have hchildInv :=
        retainedRoot_pre_step
          hSealed ring F pstate hpre e a hstep
      have hfalse :=
        retainedRoot_inv_cut_false
          ring F a hchildInv
      rw [hchildCut] at hfalse
      cases hfalse
    · exact
        retainedRoot_post_first_cut
          hSealed ring F pstate hpost
          e a hstep hchildCut


theorem longFullFactor_closed :
    forall (hSealed : SealedStepSpec),
      forall {n : Nat} (ring : DirectedRing n)
        {C0 : Config n} (F : TripleFrame ring C0),
        2 <= F.b ->
        2 * F.b + 1 <= F.a ->
        forall s a,
          LongAttemptFirstIncidentGood
            ring F s a ->
          longIncidentWonCut ring F a = true ->
          forall T,
            n ^ T <=
              4 * longFullMassFrom ring F a T := by
  exact
    longFullFactor_of_bridge
      longRetainedControlBridge_proved


end PPL.Convergence.LDLocal


#print axioms PPL.Convergence.LDLocal.longRetainedControlBridge_proved
#print axioms PPL.Convergence.LDLocal.longFullFactor_closed
