import Leader.PPL.Modes.ConstructionMode
import Leader.PPL.Modes.SignalLineageLocal
import Leader.PPL.TransitionFacts


/-!
# P_PL / P_PL' Construct coupling


The auxiliary protocol P_PL' is the one frozen by R7/R10.


Source convention (R7, paper.txt lines 1137--1148):
* DetermineMode (Algorithm 4) is unchanged;
* Algorithm 2 always takes the Construct behavior: line 6 birth is disabled
  and line 8 writes the distance temporary;
* Algorithm 3 always takes the Construct behavior: line 20 birth is disabled
  and line 22 writes the identifier bit;
* EliminateLeaders (Algorithm 5) is unchanged.


Important: "forced Construct" refers only to those branch choices.  The
physical mode field is still the value written by DetermineMode and is
restored after the forced Algorithm-3 calls.


There was no Prime/PPLPrime/protocolPrime definition on current main when this
file was written.
-/


namespace PPL.Convergence.ConstructCoupling


set_option autoImplicit false


open PPL.Probability


abbrev Config (n psi kappa : Nat) :=
  PPL.Probability.PPLConfig n psi kappa


/-- The exact R7 boundary: immediately after DetermineMode, before the
mode-dependent Algorithm-2/3 branches, both scheduled endpoints are Construct.
Recall that mode=false is Construct. -/
def PostDetermineModeConstructPair {psi kappa : Nat}
    (l r : PPL.State psi kappa) : Prop :=
  let q := PPL.determineMode l r
  q.1.mode = false ∧ q.2.mode = false


/-- Configuration form of the post-DetermineMode Construct condition. -/
def PostDetermineModeConstructAt {n psi kappa : Nat}
    (ring : DirectedRing n) (C : Config n psi kappa)
    (e : Fin n) : Prop :=
  PostDetermineModeConstructPair
    (C e) (C (ring.rightNeighbor e))


/-!
The next two facts deliberately use the public APIs requested by this file's
architecture instead of reopening private helpers from Transition.lean.
-/


/-- The public DetermineMode projection pins the same post-DetermineMode
boundary used by the coupling.  In particular the initiator's reset signal and
hit counter are already zero there. -/
theorem determineMode_initiator_signal_hits_zero
    {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    let q := PPL.determineMode l r
    q.1.signalR.val = 0 ∧ q.1.hits.val = 0 := by
  have h :=
    PPL.Modes.SignalLineage.determineModeSignalProjection
      (psi := psi) (kappa := kappa) hpsi l r
  dsimp only at h ⊢
  exact ⟨h.1, h.2.1⟩


/-- Algorithm 3 never changes either endpoint's physical mode field.
This is derived from the public field-frame lemmas in TransitionFacts.lean. -/
theorem moveToken_modes
    {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (kind : PPL.TokenKind)
    (l r : PPL.State psi kappa) :
    (PPL.moveToken hpsi kind l r).1.mode = l.mode ∧
      (PPL.moveToken hpsi kind l r).2.mode = r.mode := by
  constructor
  · have h :=
      congrArg (fun q : PPL.State psi kappa => q.mode)
        (PPL.moveToken_initiator_fields hpsi kind l r)
    cases kind <;>
      simpa [PPL.eraseKindToken] using h
  · rcases PPL.moveToken_responder_fields hpsi kind l r with h | h
    · have hm :=
        congrArg (fun q : PPL.State psi kappa => q.mode) h
      cases kind <;>
        simpa [PPL.eraseKindTokenId, PPL.eraseKindToken] using hm
    · have hm :=
        congrArg (fun q : PPL.State psi kappa => q.mode) h
      cases kind <;>
        simpa [PPL.eraseKindTokenId, PPL.eraseKindToken,
          PPL.birthFields] using hm


/-!
Exact P_PL' CreateLeader suffix.


For a post-DetermineMode Construct responder we reuse literal CreateLeader:
its Detect guards are already false, so it is exactly the forced-Construct
branch.  For a post-DetermineMode Detect responder, we execute the Construct
writes explicitly.  We temporarily put the responder mode at false solely so
the existing literal MoveToken takes line 22 instead of line 20; moveToken_modes
certifies that MoveToken itself does not otherwise rewrite mode, and the real
DetermineMode value is restored at the end.
-/


private def createLeaderForcedConstruct
    {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    PPL.State psi kappa × PPL.State psi kappa :=
  let d := PPL.determineMode l r
  -- Public structure field: this is exactly Algorithm-2 line-4 tmp.
  let tmp := (PPL.createLeaderThroughLine6 hpsi l r).tmp
  -- Forced line 8; false is only the branch-control value used below.
  let r0 : PPL.State psi kappa :=
    { d.2 with dist := tmp, mode := false }
  -- Literal line 9.
  let l0 : PPL.State psi kappa :=
    if r0.leader = true then
      { d.1 with last := true }
    else if r0.dist.val = 0 ∨ r0.dist.val = psi then
      { d.1 with last := false }
    else
      { d.1 with last := r0.last }
  -- Literal lines 10--11, with Algorithm-3 Detect branches disabled.
  let b := PPL.moveToken hpsi .black l0 r0
  let w := PPL.moveToken hpsi .white b.1 b.2
  -- P_PL' does not alter DetermineMode's stored mode.
  (w.1, { w.2 with mode := d.2.mode })


/-- Algorithm 2/3 of P_PL': always use Construct semantics. -/
def createLeaderPrime
    {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    PPL.State psi kappa × PPL.State psi kappa :=
  let d := PPL.determineMode l r
  if d.2.mode = false then
    -- Here literal P_PL already executes precisely the Construct branches.
    PPL.createLeader hpsi l r
  else
    createLeaderForcedConstruct hpsi l r


/-- One local P_PL' interaction: forced-Construct Algorithms 2/3 followed by
the unchanged literal Algorithm 5. -/
def pplPrime
    {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    PPL.State psi kappa × PPL.State psi kappa :=
  let q := createLeaderPrime hpsi l r
  PPL.eliminateLeaders q.1 q.2


/-- Public totalized P_PL' local transition, matching PPL.transition outside
the paper domain as well. -/
def transitionPrime (psi kappa : Nat) :
    PPL.State psi kappa →
      PPL.State psi kappa →
      PPL.State psi kappa × PPL.State psi kappa :=
  fun l r =>
    if hpsi : 2 ≤ psi then
      pplPrime hpsi l r
    else
      (l, r)


/-- The auxiliary protocol P_PL' used by paper Lemmas 17--19. -/
def protocolPrime (psi kappa : Nat) : PopulationProtocol where
  Q := PPL.State psi kappa
  Y := Bool
  transition := transitionPrime psi kappa
  output := fun q => q.leader


def primeStep {n psi kappa : Nat}
    (ring : DirectedRing n) (C : Config n psi kappa)
    (e : Fin n) : Config n psi kappa :=
  (protocolPrime psi kappa).step ring C e


def runPrime {n psi kappa : Nat}
    (ring : DirectedRing n) (C : Config n psi kappa)
    (word : DetSchedule n) : Config n psi kappa :=
  PPL.Probability.runPopulationSchedule
    (protocolPrime psi kappa) ring C word


/-- If the literal post-DetermineMode responder is already Construct, the
optimized P_PL' CreateLeader definition reuses literal CreateLeader exactly. -/
theorem createLeaderPrime_eq_createLeader_of_postConstruct
    {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa)
    (hr : (PPL.determineMode l r).2.mode = false) :
    createLeaderPrime hpsi l r = PPL.createLeader hpsi l r := by
  simp [createLeaderPrime, hr]


/-- Pair-level one-interaction coupling.  R7 asks for both endpoints
post-DetermineMode Construct.  The literal source is actually slightly
stronger: only the responder mode is consulted by the mode-dependent
Algorithm-2/3 branches, so hconstruct.1 is not needed below. -/
theorem pairCoupling
    {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa)
    (hconstruct : PostDetermineModeConstructPair l r) :
    PPL.ppl hpsi l r = pplPrime hpsi l r := by
  change
    (PPL.determineMode l r).1.mode = false ∧
      (PPL.determineMode l r).2.mode = false
    at hconstruct
  have hc :=
    createLeaderPrime_eq_createLeader_of_postConstruct
      hpsi l r hconstruct.2
  simpa [PPL.ppl, pplPrime, hc]


/-- Public totalized local-transition coupling in the paper domain. -/
theorem transitionCoupling
    {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa)
    (hconstruct : PostDetermineModeConstructPair l r) :
    PPL.transition psi kappa l r =
      transitionPrime psi kappa l r := by
  rw [PPL.transition_eq_ppl hpsi]
  have hp := pairCoupling hpsi l r hconstruct
  simpa [transitionPrime, hpsi] using hp


/-- Requested one-step configuration coupling. -/
theorem oneStepCoupling
    {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (C : Config n psi kappa)
    (e : Fin n)
    (hconstruct : PostDetermineModeConstructAt ring C e) :
    PPL.Probability.pplStep ring C e =
      primeStep ring C e := by
  have hpair :
      PostDetermineModeConstructPair
        (C e) (C (ring.rightNeighbor e)) := by
    simpa [PostDetermineModeConstructAt] using hconstruct
  have hp :=
    transitionCoupling hpsi
      (C e) (C (ring.rightNeighbor e)) hpair
  unfold PPL.Probability.pplStep primeStep
  unfold PopulationProtocol.step
  simp only [PPL.protocol, protocolPrime]
  rw [hp]


/-- The exact trace-side condition needed by the run coupling.
It follows the actual P_PL prefix state; once coupling is known, the P_PL'
prefix is the same state. -/
def PostDetermineModeConstructAlong
    {n psi kappa : Nat} (ring : DirectedRing n) :
    Config n psi kappa → DetSchedule n → Prop
  | _, [] => True
  | C, e :: rest =>
      PostDetermineModeConstructAt ring C e ∧
        PostDetermineModeConstructAlong ring
          (PPL.Probability.pplStep ring C e) rest


/-- Requested run-level coupling: same start, same schedule, and the
post-DetermineMode Construct condition at every scheduled interaction imply
identical final configurations. -/
theorem runCoupling
    {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (C : Config n psi kappa)
    (word : DetSchedule n)
    (hconstruct : PostDetermineModeConstructAlong ring C word) :
    PPL.Probability.runPPL ring C word =
      runPrime ring C word := by
  induction word generalizing C with
  | nil =>
      rfl
  | cons e rest ih =>
      change
        PostDetermineModeConstructAt ring C e ∧
          PostDetermineModeConstructAlong ring
            (PPL.Probability.pplStep ring C e) rest
        at hconstruct
      rcases hconstruct with ⟨hhead, htail⟩
      have hs := oneStepCoupling hpsi ring C e hhead
      change
        PPL.Probability.runPopulationSchedule
            (PPL.protocol psi kappa) ring
            (PPL.Probability.pplStep ring C e) rest =
          PPL.Probability.runPopulationSchedule
            (protocolPrime psi kappa) ring
            (primeStep ring C e) rest
      rw [← hs]
      exact
        ih
          (C := PPL.Probability.pplStep ring C e)
          htail


/-!
Lemma5.constructAlong is deliberately stronger than
PostDetermineModeConstructAlong:


* constructAlong checks EVERY agent's stored mode at EVERY configuration
  boundary, including the initial and final boundary;
* coupling checks only the two scheduled endpoints, and checks them at the
  post-DetermineMode / pre-Algorithm-2 boundary.


The implication is the deterministic bridge needed after Lemma5iiWordBound.
Its proof is intentionally left as a named Prop in this Wave-3 file: it needs
the mode analogue of the already-public post-DetermineMode signal/hits
stability plus the n>=3 non-self-edge fact.  Lemma 5(ii) supplies the
constructAlong count; no new scheduler probability statement belongs here.
-/


/-- Quiet-window bridge consumed by Lemma 19.  T5 is exactly
lemma5iiHorizon = (n*kappa/16)*2^psi. -/
def Lemma5iiQuietWindowCoupling : Prop :=
  ∀ {n psi kappa c : Nat},
    3 ≤ n →
    2 ≤ psi →
    3 ≤ c →
    kappa = 16 * c * psi →
    n ≤ 2 ^ psi →
    ∀ (ring : DirectedRing n)
      (C : Config n psi kappa)
      (word : DetSchedule n),
      PPL.Modes.Lemma5.midPhysicalB C = true →
      word.length =
        PPL.Modes.Lemma5.lemma5iiHorizon n psi kappa →
      PPL.Modes.Lemma5.constructAlong ring C word = true →
      PostDetermineModeConstructAlong ring C word


end PPL.Convergence.ConstructCoupling


#print axioms PPL.Convergence.ConstructCoupling.determineMode_initiator_signal_hits_zero
#print axioms PPL.Convergence.ConstructCoupling.moveToken_modes
#print axioms PPL.Convergence.ConstructCoupling.createLeaderPrime_eq_createLeader_of_postConstruct
#print axioms PPL.Convergence.ConstructCoupling.pairCoupling
#print axioms PPL.Convergence.ConstructCoupling.transitionCoupling
#print axioms PPL.Convergence.ConstructCoupling.oneStepCoupling
#print axioms PPL.Convergence.ConstructCoupling.runCoupling
