import Leader.PPL.TokenCorrectness.Persistence
import Init.Omega

/-!
# P_PL Lemma 4: deterministic ordered-subsequence reduction

The headline source statement in TokenCorrectness.lean is true as stated.
This file does three things without editing that file:

1. gives a closed non-vacuity witness for CdTrace + the full Lemma-4 word;
2. proves the scheduler/trace plumbing that splits H^(2*psi) into two
   H^psi occurrences while retaining every inserted interaction;
3. isolates the only remaining literal Algorithm-3 dynamics in one Prop,
   Lemma4HalfPowerDynamics.

No axiom, sorry, admit, or native_decide is used.
-/

namespace PPL

set_option autoImplicit false
set_option Elab.async false

/-! ## 1. A concrete non-vacuous C_d trace -/

private def lemma4WitnessRing : DirectedRing 4 :=
  ⟨by omega⟩

private def lemma4WitnessK : Fin 4 :=
  ⟨0, by omega⟩

private def lemma4WitnessState (i : Fin 4) : State 2 32 :=
  { leader := false
    id := false
    dist := ⟨i.val, by omega⟩
    last := false
    tokenB := none
    tokenW := none
    mode := false
    clock := (0 : Fin 33)
    signalR := (0 : Fin 33)
    hits := (0 : Fin 3)
    bullet := (0 : Fin 3)
    shield := false
    signalB := false }

private def lemma4WitnessC : Config 4 2 32 :=
  lemma4WitnessState

private def lemma4WitnessSchedule : DetSchedule 4 :=
  lemma4Word lemma4WitnessRing lemma4WitnessK 2

/-- Decidability of C_d, by unfolding to a bounded Fin quantifier. -/
private instance lemma4CdDecidable {n psi kappa : Nat} (ring : DirectedRing n)
    (k : Fin n) (kind : TokenKind) (C : Config n psi kappa) :
    Decidable (Cd ring k kind C) := by
  unfold Cd
  infer_instance

/-- Decidability of CdTrace, by recursion on the schedule. -/
private def lemma4CdTraceDecidable {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind) :
    (C : Config n psi kappa) -> (s : DetSchedule n) ->
      Decidable (CdTrace hpsi ring k kind C s)
  | C, [] => by
      unfold CdTrace
      infer_instance
  | C, e :: es => by
      unfold CdTrace
      have := lemma4CdTraceDecidable hpsi ring k kind
        (PopulationProtocol.step (protocol psi kappa) ring C e) es
      infer_instance

private instance lemma4CdTraceDecInst {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind)
    (C : Config n psi kappa) (s : DetSchedule n) :
    Decidable (CdTrace hpsi ring k kind C s) :=
  lemma4CdTraceDecidable hpsi ring k kind C s

theorem lemma4_premises_nonvacuous :
    CdTrace (by decide : 2 <= 2)
        lemma4WitnessRing lemma4WitnessK .black
        lemma4WitnessC lemma4WitnessSchedule ∧
      (lemma4Word lemma4WitnessRing lemma4WitnessK 2).Sublist
        lemma4WitnessSchedule := by
  constructor
  · decide
  · exact List.Sublist.refl _

/-! ## 2. Exact half-word arithmetic -/

def lemma4HalfWord {n : Nat}
    (ring : DirectedRing n) (k : Fin n) (psi : Nat) :
    DetSchedule n :=
  wordPower psi (lemma4Block ring k psi)

theorem lemma4_wordPower_add
    {n : Nat} (a b : Nat) (w : DetSchedule n) :
    wordPower (a + b) w =
      wordPower a w ++ wordPower b w := by
  induction a with
  | zero =>
      simp [wordPower]
  | succ a ih =>
      rw [Nat.succ_add]
      simp [wordPower, ih, List.append_assoc]

theorem lemma4Word_eq_two_halves
    {n psi : Nat}
    (ring : DirectedRing n) (k : Fin n) :
    lemma4Word ring k psi =
      lemma4HalfWord ring k psi ++
        lemma4HalfWord ring k psi := by
  unfold lemma4Word lemma4HalfWord
  rw [show 2 * psi = psi + psi by omega]
  exact lemma4_wordPower_add psi psi (lemma4Block ring k psi)

/-! ## 3. Trace and ghost concatenation plumbing -/

theorem lemma4_cdTrace_start
    {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind)
    (C : Config n psi kappa) (schedule : DetSchedule n)
    (h : CdTrace hpsi ring k kind C schedule) :
    Cd ring k kind C := by
  cases schedule with
  | nil =>
      simpa [CdTrace] using h
  | cons e es =>
      change
        Cd ring k kind C ∧
          CdTrace hpsi ring k kind
            (PopulationProtocol.step (protocol psi kappa) ring C e) es
        at h
      exact h.1

theorem lemma4_cdTrace_append
    {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind)
    (C : Config n psi kappa)
    (a b : DetSchedule n)
    (h : CdTrace hpsi ring k kind C (a ++ b)) :
    CdTrace hpsi ring k kind C a ∧
      CdTrace hpsi ring k kind
        (PPL.Probability.runPopulationSchedule
          (protocol psi kappa) ring C a) b := by
  induction a generalizing C with
  | nil =>
      constructor
      · exact lemma4_cdTrace_start hpsi ring k kind C b h
      · simpa [PPL.Probability.runPopulationSchedule] using h
  | cons e es ih =>
      change
        Cd ring k kind C ∧
          CdTrace hpsi ring k kind
            (PopulationProtocol.step (protocol psi kappa) ring C e)
            (es ++ b)
        at h
      rcases h with ⟨hC, hrest⟩
      rcases
        ih
          (C :=
            PopulationProtocol.step
              (protocol psi kappa) ring C e)
          hrest
        with ⟨ha, hb⟩
      constructor
      · change
          Cd ring k kind C ∧
            CdTrace hpsi ring k kind
              (PopulationProtocol.step
                (protocol psi kappa) ring C e) es
        exact ⟨hC, ha⟩
      · simpa [PPL.Probability.runPopulationSchedule] using hb

theorem lemma4_erase_initialGhost
    {n psi kappa : Nat} (C : Config n psi kappa) :
    eraseGhost (initialGhost C) = C := by
  rfl

theorem lemma4_ghostRun_append
    {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (t : Nat) (G : GhostConfig n psi kappa)
    (a b : DetSchedule n) :
    ghostRun hpsi ring t G (a ++ b) =
      ghostRun hpsi ring (t + a.length)
        (ghostRun hpsi ring t G a) b := by
  induction a generalizing t G with
  | nil =>
      rfl
  | cons e es ih =>
      simp only [List.cons_append, ghostRun, List.length_cons]
      rw [ih]
      congr 1
      omega

/-! ## 4. The one remaining local Algorithm-3 fact -/

def Lemma4InWindow {n : Nat}
    (ring : DirectedRing n) (k : Fin n)
    (psi : Nat) (i : Fin n) : Prop :=
  ∃ x : Fin (2 * psi), i = shiftRight ring k x.val

/--
Every live selected-color ghost in the local 2*psi window is fresh and was
born at the selected border k.  Invalid physical residues are intentionally
absent from the ghost owner maps.
-/
def Lemma4FreshWindow
    {n psi kappa : Nat}
    (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind) (G : GhostConfig n psi kappa) : Prop :=
  ∀ i z,
    Lemma4InWindow ring k psi i ->
    ghostTokenAt kind G i = some z ->
    FreshAt kind k z.lmeta

/--
The only remaining protocol-semantic leaf of source Lemma 4.

Clause (1) is the first-half purge: H^psi removes every start-old valid owner;
any live selected-color owner left in the C_d window is a word-local birth at
k.  This includes the no-valid-boundary-entry fact.

Clause (2) is the protected-frontier second half: starting from an actual
pre ghost run satisfying that freshness property, another H^psi occurrence
under trace-wide C_d produces a completed lineage born at k.

The eventual proof is by the source macro-stage in [psi,2*psi-1]:
ordinary moves preserve stage, a left-target refresh raises it, the final
right-target hit completes, and a younger contender cannot kill the rightmost
fresh owner because Algorithm 3 deletes the left token on collision.

No probability, CorrectToken, SPLAt, mode coupling, or P_PL-prime semantics
are hidden in this Prop.
-/
def Lemma4HalfPowerDynamics : Prop :=
  ∀ {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind),
    (∀ (C : Config n psi kappa)
       (schedule : DetSchedule n),
      CdTrace hpsi ring k kind C schedule ->
      (lemma4HalfWord ring k psi).Sublist schedule ->
      Lemma4FreshWindow ring k kind
        (ghostRun hpsi ring 0 (initialGhost C) schedule)) ∧
    (∀ (C0 : Config n psi kappa)
       (pre : DetSchedule n)
       (G : GhostConfig n psi kappa)
       (schedule : DetSchedule n),
      G = ghostRun hpsi ring 0 (initialGhost C0) pre ->
      Lemma4FreshWindow ring k kind G ->
      CdTrace hpsi ring k kind G.phys schedule ->
      (lemma4HalfWord ring k psi).Sublist schedule ->
      HasFreshCompletion kind k
        (ghostRun hpsi ring pre.length G schedule))

/-! ## 5. Full deterministic core from the local half-power law -/

theorem lemma4_deterministic_core_of_halfPowerDynamics
    (hdyn : Lemma4HalfPowerDynamics) :
    lemma4_deterministic_core := by
  intro n psi kappa hpsi ring k kind C schedule hCd hsub

  have hword :
      lemma4Word ring k psi =
        lemma4HalfWord ring k psi ++
          lemma4HalfWord ring k psi :=
    lemma4Word_eq_two_halves ring k
  rw [hword] at hsub

  rcases List.append_sublist_iff.mp hsub with
    ⟨pre, post, hschedule, hpre, hpost⟩
  subst schedule

  rcases
    lemma4_cdTrace_append
      hpsi ring k kind C pre post hCd
    with ⟨hCdPre, hCdPost⟩

  let Gmid : GhostConfig n psi kappa :=
    ghostRun hpsi ring 0 (initialGhost C) pre

  have hFresh :
      Lemma4FreshWindow ring k kind Gmid := by
    simpa [Gmid] using
      (hdyn hpsi ring k kind).1 C pre hCdPre hpre

  have hmidPhys :
      Gmid.phys =
        PPL.Probability.runPopulationSchedule
          (protocol psi kappa) ring C pre := by
    have h :=
      ghostRun_erases hpsi ring 0 (initialGhost C) pre
    rw [lemma4_erase_initialGhost C] at h
    simpa [Gmid, eraseGhost] using h

  have hCdPost' :
      CdTrace hpsi ring k kind Gmid.phys post := by
    rw [hmidPhys]
    exact hCdPost

  have hfinish :
      HasFreshCompletion kind k
        (ghostRun hpsi ring pre.length Gmid post) := by
    exact
      (hdyn hpsi ring k kind).2
        C pre Gmid post rfl hFresh hCdPost' hpost

  rw [lemma4_ghostRun_append
    hpsi ring 0 (initialGhost C) pre post]
  simpa [Gmid] using hfinish

end PPL

#print axioms PPL.lemma4_premises_nonvacuous
#print axioms PPL.lemma4_wordPower_add
#print axioms PPL.lemma4Word_eq_two_halves
#print axioms PPL.lemma4_cdTrace_start
#print axioms PPL.lemma4_cdTrace_append
#print axioms PPL.lemma4_erase_initialGhost
#print axioms PPL.lemma4_ghostRun_append
#print axioms PPL.lemma4_deterministic_core_of_halfPowerDynamics
