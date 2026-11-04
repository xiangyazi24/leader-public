import Leader.PPL.ReachCPB.WordBound
import Leader.PPL.TransitionFacts


namespace PPL.Convergence.ReachCPB

instance instDecidableDetectReadyRun
    {n psi kappa : Nat} (ring : DirectedRing n)
    (C : Config n psi kappa) (word : DetSchedule n) :
    Decidable (DetectReady ring (PPL.Probability.runPPL ring C word)) :=
  instDecidableDetectReady ring
    (PPL.Probability.runPPL ring C word : Config n psi kappa)


set_option autoImplicit false
set_option Elab.async false


open PPL.Probability


/-!
# Lemma 16 detect / C_d residuals


The first requested residual is false as currently stated.  DetectReady records
only the stored mode bit; it does not require the clock to be at kappa.  The
literal DetermineMode transition recomputes mode from clock.val == kappa, so a
leaderless, signal-free, all-Detect Cartesian state with a non-maximal clock can
leave Detect in one interaction without creating a leader.


The second residual is reduced to one literal single-interaction geometry fact.
The global schedule induction, CPB stopping branch, and C_d trace plumbing are
proved below.
-/


/-! ## TransitionFacts consequence used by the C_d row -/


/-- Algorithm 3 changes neither dist nor last on either endpoint. -/
private theorem moveToken_dist_last
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : PPL.TokenKind)
    (l r : PPL.State psi kappa) :
    let q := PPL.moveToken hpsi kind l r
    q.1.dist = l.dist ∧
      q.1.last = l.last ∧
      q.2.dist = r.dist ∧
      q.2.last = r.last := by
  dsimp only
  have hi :=
    PPL.moveToken_initiator_fields hpsi kind l r
  rcases
      PPL.moveToken_responder_fields hpsi kind l r with
    hr | hr
  · cases kind <;>
      simp_all
        [PPL.eraseKindToken, PPL.eraseKindTokenId]
  · cases kind <;>
      simp_all
        [PPL.eraseKindToken, PPL.eraseKindTokenId,
          PPL.birthFields]


/-! ## Concrete counterexample to Lemma16DetectPersistence -/


private theorem detectCounterexampleRing : DirectedRing 3 :=
  ⟨by omega⟩


private def detectCounterexampleState : PPL.State 2 1 :=
  { leader := false
    id := false
    dist := ⟨0, by omega⟩
    last := true
    tokenB := none
    tokenW := none
    mode := true
    clock := ⟨0, by omega⟩
    signalR := ⟨0, by omega⟩
    hits := ⟨0, by omega⟩
    bullet := ⟨0, by omega⟩
    shield := false
    signalB := false }


private def detectCounterexampleConfig : Config 3 2 1 :=
  fun _ => detectCounterexampleState


private def detectCounterexampleEdge : Fin 3 :=
  ⟨0, by omega⟩


private def detectCounterexampleWord : DetSchedule 3 :=
  [detectCounterexampleEdge]


/--
The initial configuration is leaderless, signal-free, all-Detect, and has no
live bullets.  After edge 0, DetermineMode rewrites the two participating mode
bits to Construct because their clocks are 0 < kappa = 1.  No leader is born.
-/
theorem lemma16DetectPersistence_counterexample :
    DetectReady
        detectCounterexampleRing
        detectCounterexampleConfig ∧
      ¬ PPL.CPB detectCounterexampleRing
          (PPL.Probability.runPPL
            detectCounterexampleRing
            detectCounterexampleConfig
            detectCounterexampleWord) ∧
      ¬ DetectReady detectCounterexampleRing
          (PPL.Probability.runPPL
            detectCounterexampleRing
            detectCounterexampleConfig
            detectCounterexampleWord) := by
  decide


theorem lemma16DetectPersistence_not :
    ¬ Lemma16DetectPersistence := by
  intro h
  have hout :=
    h (n := 3) (psi := 2) (kappa := 1)
      (by omega) (by omega)
      detectCounterexampleRing
      detectCounterexampleConfig
      detectCounterexampleWord
      lemma16DetectPersistence_counterexample.1
  rcases hout with hcpb | hdetect
  · exact
      lemma16DetectPersistence_counterexample.2.1 hcpb
  · exact
      lemma16DetectPersistence_counterexample.2.2 hdetect


/-! ## One remaining literal row for C_d -/


/--
Single-interaction geometry leaf.


Under the exact leaderless cyclic-distance/all-false-last frame, one physical
P_PL interaction preserves dist and last at every site.  The intended direct
proof is:


* determineMode writes only timer/mode fields;
* createLeaderThroughLine6 computes tmp as the current responder distance, so
  Algorithm-2 line 6 cannot birth and line 8 is idempotent;
* line 9 rewrites the initiator last bit to the same false value;
* moveToken_dist_last above handles both Algorithm-3 passes;
* PPL.Elim.otherView_eliminateLeaders_left/right handle Algorithm 5.


This is the only open physical row retained in this bounded round.
-/
def Lemma16CdGeometryStepSpec : Prop :=
  ∀ {n psi kappa : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa)
      (e : Fin n),
    (∀ i : Fin n, (C i).leader = false) →
    (∀ i : Fin n,
      (C (ring.rightNeighbor i)).dist.val =
        ((C i).dist.val + 1) % (2 * psi)) →
    (∀ i : Fin n, (C i).last = false) →
      ∀ i : Fin n,
        let D :=
          PopulationProtocol.step
            (PPL.protocol psi kappa) ring C e
        (D i).dist = (C i).dist ∧
          (D i).last = (C i).last


private theorem cdTraceUntilSuccess_of_geometryStep
    (hStep : Lemma16CdGeometryStepSpec)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : PPL.TokenKind) :
    ∀ (C : Config n psi kappa)
      (schedule : DetSchedule n),
      AllLivePeaceful ring C →
      (∀ i : Fin n, (C i).leader = false) →
      (∀ i : Fin n,
        (C (ring.rightNeighbor i)).dist.val =
          ((C i).dist.val + 1) % (2 * psi)) →
      (∀ i : Fin n, (C i).last = false) →
      PPL.Cd ring k kind C →
        PPL.CPB ring
            (PPL.Probability.runPPL ring C schedule) ∨
          PPL.CdTrace hpsi ring k kind C schedule := by
  intro C schedule
  induction schedule generalizing C with
  | nil =>
      intro _ _ _ _ hCd
      exact Or.inr hCd
  | cons e rest ih =>
      intro hpeace hleaderless hdist hlast hCd
      let D : Config n psi kappa :=
        PopulationProtocol.step
          (PPL.protocol psi kappa) ring C e
      have hfields :
          ∀ i : Fin n,
            (D i).dist = (C i).dist ∧
              (D i).last = (C i).last := by
        intro i
        simpa [D] using
          hStep hn3 hpsi ring C e
            hleaderless hdist hlast i
      have hdistD :
          ∀ i : Fin n,
            (D (ring.rightNeighbor i)).dist.val =
              ((D i).dist.val + 1) % (2 * psi) := by
        intro i
        rw [(hfields (ring.rightNeighbor i)).1,
          (hfields i).1]
        exact hdist i
      have hlastD :
          ∀ i : Fin n, (D i).last = false := by
        intro i
        calc
          (D i).last = (C i).last := (hfields i).2
          _ = false := hlast i
      have hCdD : PPL.Cd ring k kind D := by
        unfold PPL.Cd at hCd ⊢
        intro x
        dsimp only
        have hx := hCd x
        dsimp only at hx
        have hv :=
          hfields
            (PPL.shiftRight ring k x.val)
        constructor
        · rw [hv.1]
          exact hx.1
        · rw [hv.2]
          exact hx.2
      have hpeaceD :
          AllLivePeaceful ring D := by
        simpa [D] using
          allLivePeaceful_step_closed
            hn3 hpsi ring C e hpeace
      by_cases hleaderD :
          ∃ i : Fin n, (D i).leader = true
      · have hCPBD : PPL.CPB ring D :=
          cpb_of_allLivePeaceful_hasLeader
            ring D hpeaceD hleaderD
        have hend :=
          cpb_run_closed
            hn3 hpsi ring D rest hCPBD
        exact Or.inl (by
          simpa
            [D, PPL.Probability.runPPL,
              PPL.Probability.runPopulationSchedule]
            using hend)
      · have hleaderlessD :
            ∀ i : Fin n, (D i).leader = false := by
          intro i
          cases hi : (D i).leader with
          | false =>
              rfl
          | true =>
              exact False.elim
                (hleaderD ⟨i, hi⟩)
        have htail :=
          ih D hpeaceD hleaderlessD
            hdistD hlastD hCdD
        rcases htail with hcpb | htrace
        · exact Or.inl (by
            simpa
              [D, PPL.Probability.runPPL,
                PPL.Probability.runPopulationSchedule]
              using hcpb)
        · exact Or.inr (by
            change
              PPL.Cd ring k kind C ∧
                PPL.CdTrace hpsi ring k kind D rest
            exact ⟨hCd, htrace⟩)


/--
The full second requested residual follows from the one physical geometry row.
-/
theorem lemma16CdTraceUntilSuccess
    (hStep : Lemma16CdGeometryStepSpec) :
    Lemma16CdTraceUntilSuccessSpec := by
  unfold Lemma16CdTraceUntilSuccessSpec
  intro n psi kappa hn3 hpsi ring C k kind
    hready hCd schedule
  obtain ⟨hdistReady, hlast⟩ := hready
  obtain ⟨hdetectReady, hdist⟩ := hdistReady
  obtain ⟨hpeace, hrest⟩ := hdetectReady
  obtain ⟨hleaderless, hrest⟩ := hrest
  obtain ⟨_hsignalFree, _hallDetect⟩ := hrest
  exact
    cdTraceUntilSuccess_of_geometryStep
      hStep hn3 hpsi ring k kind
      C schedule hpeace hleaderless
      hdist hlast hCd


end PPL.Convergence.ReachCPB


#print axioms PPL.Convergence.ReachCPB.moveToken_dist_last
#print axioms PPL.Convergence.ReachCPB.lemma16DetectPersistence_counterexample
#print axioms PPL.Convergence.ReachCPB.lemma16DetectPersistence_not
#print axioms PPL.Convergence.ReachCPB.lemma16CdTraceUntilSuccess


