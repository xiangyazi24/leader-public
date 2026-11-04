import Leader.PPL.ReachCPB.WordBound


namespace PPL.Convergence.ReachCPB

instance instDecidableDistReadyRun
    {n psi kappa : Nat} (ring : DirectedRing n)
    (C : Config n psi kappa) (word : DetSchedule n) :
    Decidable (DistReady ring (PPL.Probability.runPPL ring C word)) :=
  instDecidableDistReady ring
    (PPL.Probability.runPPL ring C word : Config n psi kappa)

instance instDecidableLastReadyRun
    {n psi kappa : Nat} (ring : DirectedRing n)
    (C : Config n psi kappa) (word : DetSchedule n) :
    Decidable (LastReady ring (PPL.Probability.runPPL ring C word)) :=
  instDecidableLastReady ring
    (PPL.Probability.runPPL ring C word : Config n psi kappa)


set_option autoImplicit false
set_option Elab.async false


/-!
The two requested forcing Specs are false on the literal Cartesian carrier.


The missing invariant is the semantic relation between the stored mode bit and
the clock.  DetectReady currently asks only for mode = true.  It does not ask
for clock = kappa.  Hence a legal configuration may claim Detect while its
clock is below the cap; the next DetermineMode call then writes Construct.


The closed finite counterexamples below use only the literal transition and
the existing decidable predicates.  They are intentionally small.
-/


/-! ## Counterexample to Lemma16DistForcingSpec


n=3, psi=2, kappa=1.
Every agent is stored as Detect, but every clock is 0 < kappa.
All leaders/signals/elimination bullets are absent, so DetectReady holds.


On any one scheduler letter, DetermineMode leaves both clocks at 0 and writes
both scheduled endpoints to Construct.  Therefore line 6 is disabled.  The
endpoint is leaderless, hence not CPB, and it is not DetectReady, hence not
DistReady.  Since every candidate forcing word has length one, taking the word
itself as the supersequence refutes the Spec.
-/


private def forcingRing3 : DirectedRing 3 :=
  ⟨by decide⟩


private def falseDetectState3 : PPL.State 2 1 :=
  {
    leader := false
    id := false
    dist := 0
    last := true
    tokenB := none
    tokenW := none
    mode := true
    clock := 0
    signalR := 0
    hits := 0
    bullet := 0
    shield := false
    signalB := false
  }


private def falseDetectConfig3 : Config 3 2 1 :=
  fun _ => falseDetectState3


private theorem falseDetectConfig3_ready :
    DetectReady forcingRing3 falseDetectConfig3 := by
  decide


private theorem falseDetectConfig3_one_step_bad :
    ∀ e : Fin 3,
      ¬ PPL.CPB forcingRing3
          (PPL.Probability.runPPL forcingRing3 falseDetectConfig3 [e] : Config 3 2 1) ∧
        ¬ DistReady forcingRing3
          (PPL.Probability.runPPL forcingRing3 falseDetectConfig3 [e] : Config 3 2 1) := by
  decide


theorem lemma16DistForcing_refuted :
    ¬ Lemma16DistForcingSpec := by
  intro hspec
  obtain ⟨word, hlen, hforce⟩ :=
    hspec
      (n := 3) (psi := 2) (kappa := 1)
      (by decide) (by decide)
      forcingRing3 falseDetectConfig3
      falseDetectConfig3_ready
  cases word with
  | nil =>
      simp only [List.length_nil] at hlen
      omega
  | cons e rest =>
      cases rest with
      | nil =>
          have hor :=
            hforce [e] (List.Sublist.refl [e])
          have hbad :=
            falseDetectConfig3_one_step_bad e
          exact Or.elim hor hbad.1 hbad.2
      | cons e' rest' =>
          simp only [List.length_cons] at hlen
          omega


/-! ## Counterexample to Lemma16LastForcingSpec


n=4, psi=2, kappa=5.
The distances are 0,1,2,3 cyclically, so DistReady holds, but the stored
Detect modes again have clock 0.


For every four-letter word, every scheduled endpoint still has clock < 5 when
it is processed, so DetermineMode writes Construct.  The cyclic distance
assignment is rewritten only to the same correct successor value; token
comparisons, when enabled, see Construct; therefore no leader is created.
After the fourth letter at least its scheduled endpoints are Construct, so the
endpoint is neither CPB nor LastReady.  Taking the candidate word itself as
the supersequence refutes the Spec.
-/


private def forcingRing4 : DirectedRing 4 :=
  ⟨by decide⟩


private def falseDetectConfig4 : Config 4 2 5 :=
  fun i =>
    {
      leader := false
      id := false
      dist := i
      last := true
      tokenB := none
      tokenW := none
      mode := true
      clock := 0
      signalR := 0
      hits := 0
      bullet := 0
      shield := false
      signalB := false
    }


private theorem falseDetectConfig4_distReady :
    DistReady forcingRing4 falseDetectConfig4 := by
  decide


set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem falseDetectConfig4_four_step_bad :
    ∀ e0 e1 e2 e3 : Fin 4,
      ¬ PPL.CPB forcingRing4
          (PPL.Probability.runPPL forcingRing4 falseDetectConfig4
            [e0, e1, e2, e3] : Config 4 2 5) ∧
        ¬ LastReady forcingRing4
          (PPL.Probability.runPPL forcingRing4 falseDetectConfig4
            [e0, e1, e2, e3] : Config 4 2 5) := by
  decide


theorem lemma16LastForcing_refuted :
    ¬ Lemma16LastForcingSpec := by
  intro hspec
  obtain ⟨word, hlen, hforce⟩ :=
    hspec
      (n := 4) (psi := 2) (kappa := 5)
      (by decide) (by decide)
      forcingRing4 falseDetectConfig4
      falseDetectConfig4_distReady
  cases word with
  | nil =>
      simp only [List.length_nil] at hlen
      omega
  | cons e0 r0 =>
      cases r0 with
      | nil =>
          simp only [List.length_cons, List.length_nil] at hlen
          omega
      | cons e1 r1 =>
          cases r1 with
          | nil =>
              simp only [List.length_cons, List.length_nil] at hlen
              omega
          | cons e2 r2 =>
              cases r2 with
              | nil =>
                  simp only [List.length_cons, List.length_nil] at hlen
                  omega
              | cons e3 r3 =>
                  cases r3 with
                  | nil =>
                      have hor :=
                        hforce [e0, e1, e2, e3]
                          (List.Sublist.refl [e0, e1, e2, e3])
                      have hbad :=
                        falseDetectConfig4_four_step_bad e0 e1 e2 e3
                      exact Or.elim hor hbad.1 hbad.2
                  | cons e4 r4 =>
                      simp only [List.length_cons] at hlen
                      omega


/-! ## Minimal corrected interface


The intended paper argument needs C_det, not an arbitrary stored Detect bit.
On the present carrier the smallest direct repair is to require all DetectReady
agents to be at the clock cap.  Since DetectReady already requires every mode
bit to be Detect, this is simply clock = kappa at every site.


With signalFree and leaderless in scope, DetermineMode then keeps scheduled
agents Detect until a leader is born.  The intended "dist frozen" and line-9
sweep proofs can be carried out against these capped predicates.
-/


def DetectReadyCapped
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Prop :=
  DetectReady ring C ∧
    ∀ i : Fin n, (C i).clock.val = kappa


def DistReadyCapped
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Prop :=
  DetectReadyCapped ring C ∧
    ∀ i : Fin n,
      (C (ring.rightNeighbor i)).dist.val =
        ((C i).dist.val + 1) % (2 * psi)


def LastReadyCapped
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Prop :=
  DistReadyCapped ring C ∧
    ∀ i : Fin n, (C i).last = false


def Lemma16DistForcingCappedSpec : Prop :=
  ∀ {n psi kappa : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    DetectReadyCapped ring C →
      ∃ word : DetSchedule n,
        word.length = 1 ∧
          ∀ schedule : DetSchedule n,
            word.Sublist schedule →
              PPL.CPB ring
                  (PPL.Probability.runPPL ring C schedule) ∨
                DistReadyCapped ring
                  (PPL.Probability.runPPL ring C schedule)


def Lemma16LastForcingCappedSpec : Prop :=
  ∀ {n psi kappa : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    DistReadyCapped ring C →
      ∃ word : DetSchedule n,
        word.length = n ∧
          ∀ schedule : DetSchedule n,
            word.Sublist schedule →
              PPL.CPB ring
                  (PPL.Probability.runPPL ring C schedule) ∨
                LastReadyCapped ring
                  (PPL.Probability.runPPL ring C schedule)


end PPL.Convergence.ReachCPB


#print axioms PPL.Convergence.ReachCPB.lemma16DistForcing_refuted
#print axioms PPL.Convergence.ReachCPB.lemma16LastForcing_refuted


