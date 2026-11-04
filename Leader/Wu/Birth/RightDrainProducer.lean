import Leader.Wu.Birth.RightDrainCollar

namespace BirthB1RightDrainProducer

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLWallSweepRepair
open BirthWaitPassive
open BirthShortDoneTerminalB1EntranceR2
open Q11632RightDrainCollar

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {n psi kappa tau : Nat}

abbrev FC (n psi kappa tau : Nat) :=
  Q11632RightDrainCollar.FullConfig n psi kappa tau

/-- Offset zero is the protected tail `a+2`; positive offsets are the
    right-drain corridor.  The no-wrap side condition used below is
    `2 + corridorLen < n`. -/
def drainSite (ring : DirectedRing n) (a : Fin n) (k : Nat) : Fin n :=
  groupOffset ring a (2 + k)

/-- Moving clockwise reset front.  The front carries `reset_cmd`; every site
    already crossed by the front has lost its reset command; sites strictly
    ahead are still the initial full expiring states.  We deliberately do NOT
    require the crossed prefix to be echo-free: the literal SUPPRESS row below
    proves that such a strengthening is false. -/
def ResetFrontAt
    (ring : DirectedRing n)
    (initial current : FC n psi kappa tau)
    (a : Fin n) (k : Nat) : Prop :=
  2 + k < n ∧
    (raw (current (drainSite ring a k))).reset_cmd = true ∧
    (∀ j, j < k →
      (raw (current (drainSite ring a j))).reset_cmd = false) ∧
    (∀ j, k < j → 2 + j < n →
      current (drainSite ring a j) = initial (drainSite ring a j))

/-- The tempting but false strengthening: no echo is left behind the reset
    front.  A SUPPRESS row refutes this after one step. -/
def EchoFreeBehind
    (ring : DirectedRing n) (current : FC n psi kappa tau)
    (a : Fin n) (k : Nat) : Prop :=
  ∀ j, j < k → (raw (current (drainSite ring a j))).echo = false

def StrictResetFrontAt
    (ring : DirectedRing n)
    (initial current : FC n psi kappa tau)
    (a : Fin n) (k : Nat) : Prop :=
  ResetFrontAt ring initial current a k ∧
    EchoFreeBehind ring current a k

/-- Explicit clockwise word for the moving front. -/
def rightDrainWord
    (ring : DirectedRing n) (a : Fin n) : Nat → List (Fin n)
  | 0 => []
  | k + 1 => rightDrainWord ring a k ++ [drainSite ring a k]

/-- Reset-front trace under the literal width-two terminal consumer. -/
def ResetFrontTrace
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (initial : FC n psi kappa tau)
    (a : Fin n) (corridorLen : Nat) : Prop :=
  0 < corridorLen ∧
    2 + corridorLen < n ∧
    ∀ k, k ≤ corridorLen →
      ResetFrontAt ring initial
        (currentRun hpsi h2 ring initial (rightDrainWord ring a k)) a k

/-- The reset-phase termination measure. -/
def resetFrontMeasure (corridorLen k : Nat) : Nat :=
  corridorLen - k

theorem resetFrontMeasure_step
    {corridorLen k : Nat} (hk : k < corridorLen) :
    resetFrontMeasure corridorLen (k + 1) <
      resetFrontMeasure corridorLen k := by
  unfold resetFrontMeasure
  omega

/-- A two-phase lexicographic shell.  The reset phase has rank 1; any later
    cleanup/absorption phase has rank 0.  This records formally why reaching
    the end of the reset corridor is only a phase transition, not sanitation. -/
def LexDrops (after before : Nat × Nat) : Prop :=
  after.1 < before.1 ∨
    (after.1 = before.1 ∧ after.2 < before.2)

def resetPhaseMeasure (corridorLen k : Nat) : Nat × Nat :=
  (1, resetFrontMeasure corridorLen k)

def cleanupPhaseMeasure (debt : Nat) : Nat × Nat :=
  (0, debt)

theorem resetPhaseMeasure_step
    {corridorLen k : Nat} (hk : k < corridorLen) :
    LexDrops (resetPhaseMeasure corridorLen (k + 1))
      (resetPhaseMeasure corridorLen k) := by
  unfold LexDrops resetPhaseMeasure
  exact Or.inr ⟨rfl, resetFrontMeasure_step hk⟩

theorem switch_to_cleanup_measure_drops
    (corridorLen k debt : Nat) :
    LexDrops (cleanupPhaseMeasure debt)
      (resetPhaseMeasure corridorLen k) := by
  unfold LexDrops cleanupPhaseMeasure resetPhaseMeasure
  exact Or.inl Nat.zero_lt_one

/-- Literal-consumer prefix used for temporal safety predicates. -/
def runPrefix
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (w : List (Fin n)) (t : Nat) : FC n psi kappa tau :=
  currentRun hpsi h2 ring C (w.take t)

def HasLeaderAlong
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (w : List (Fin n)) : Prop :=
  ∃ t, t ≤ w.length ∧
    HasLeader (runPrefix hpsi h2 ring C w t)

def LeaderlessAlong
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (w : List (Fin n)) : Prop :=
  ∀ t, t ≤ w.length →
    BirthShortDoneTerminalFirstHit.Leaderless
      (runPrefix hpsi h2 ring C w t)

def AlignedAlong
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (w : List (Fin n)) (a : Fin n) : Prop :=
  ∀ t, t ≤ w.length →
    TripleLabels hpsi ring (runPrefix hpsi h2 ring C w t) a

/-- The finite non-wrapping geometric region: protected triple plus the
    clockwise/right corridor. -/
def InDrainRegion
    (ring : DirectedRing n) (a : Fin n)
    (corridorLen : Nat) (i : Fin n) : Prop :=
  ∃ q, q ≤ 2 + corridorLen ∧ i = groupOffset ring a q

/-- Every scheduled interaction has both endpoints inside that non-wrapping
    region.  This excludes using the wrap edge as a hidden reset/echo sink. -/
def WordSupported
    (ring : DirectedRing n) (a : Fin n)
    (corridorLen : Nat) (w : List (Fin n)) : Prop :=
  ∀ e, e ∈ w →
    InDrainRegion ring a corridorLen e ∧
      InDrainRegion ring a corridorLen (ring.rightNeighbor e)

def ProtectedSite
    (ring : DirectedRing n) (a i : Fin n) : Prop :=
  i = a ∨
    i = ring.rightNeighbor a ∨
    i = ring.rightNeighbor (ring.rightNeighbor a)

/-- Once a protected site has actually reached `Passive`, no later step of the
    producer word may re-introduce reset/echo/comparison/WRITE/K2 metadata.
    `Passive` is intentionally used rather than a hand-picked field list. -/
def PassiveNoReentry
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (w : List (Fin n)) (a : Fin n) : Prop :=
  ∀ s t, s ≤ t → t ≤ w.length →
    ∀ i, ProtectedSite ring a i →
      Passive (raw ((runPrefix hpsi h2 ring C w s) i)) →
      Passive (raw ((runPrefix hpsi h2 ring C w t) i))

/-- No exported raw protocol material remains in a corridor cell.  `Metadata`
    forces reset/echo, comparison carriers, WRITE actions and K2 signal fields
    to their cell values; `InertWriter` also constrains `write_state`. -/
def DrainQuiescent (u : AgentState psi) : Prop :=
  Metadata u ∧ InertWriter u

def CorridorTerminated
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (a : Fin n) (corridorLen : Nat) : Prop :=
  ∀ k, k ≤ corridorLen →
    DrainQuiescent (raw (C (drainSite ring a k)))

/-- LDR-BIRTH-ROUTE-B1-RIGHT-DRAIN-PRODUCER, stated over the literal current
    consumer.  The birth alternative is temporal (`HasLeaderAlong`), so a
    physical birth is not lost merely because a later row could remove it.

    In the no-birth branch the finite word is confined to the protected triple
    plus a non-wrapping right corridor; the ruler stays aligned; the reset
    front is witnessed while it moves right; already-Passive protected sites
    cannot be dirtied again; the corridor eventually contains no exported
    protocol material; and the protected triple is finally Passive with labels
    0,1,2 mod psi. -/
def RightDrainProducer
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (_hn : 4 ≤ n)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (a : Fin n) : Prop :=
  BirthShortDoneTerminalFirstHit.Leaderless C →
  TripleLabels hpsi ring C a →
  ∃ corridorLen : Nat, ∃ pre finish : List (Fin n),
    0 < corridorLen ∧
    2 + corridorLen < n ∧
    (let armed := currentRun hpsi h2 ring C pre
     let drain := rightDrainWord ring a corridorLen
     let full := pre ++ drain ++ finish
     let D := currentRun hpsi h2 ring C full
     WordSupported ring a corridorLen full ∧
       (HasLeaderAlong hpsi h2 ring C full ∨
         (LeaderlessAlong hpsi h2 ring C full ∧
          AlignedAlong hpsi h2 ring C full a ∧
          ResetFrontTrace hpsi h2 ring armed a corridorLen ∧
          PassiveNoReentry hpsi h2 ring C full a ∧
          CorridorTerminated ring D a corridorLen ∧
          ThreeSiteSanitized hpsi ring D a)))

/-! ## Exact remaining theorem statements

These are definitions of Props, not unproved theorem declarations.  This keeps
R1 free of `sorry` while fixing the exact interfaces for the next rounds. -/

/-- Phase A: manufacture a reset front at the protected tail, or birth first. -/
def ArmFrontStatement
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (_hn : 4 ≤ n)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (a : Fin n) : Prop :=
  BirthShortDoneTerminalFirstHit.Leaderless C →
  TripleLabels hpsi ring C a →
  ∃ corridorLen : Nat, ∃ pre : List (Fin n),
    0 < corridorLen ∧
    2 + corridorLen < n ∧
    WordSupported ring a corridorLen pre ∧
    (HasLeaderAlong hpsi h2 ring C pre ∨
      (let B := currentRun hpsi h2 ring C pre
       LeaderlessAlong hpsi h2 ring C pre ∧
       AlignedAlong hpsi h2 ring C pre a ∧
       ResetFrontAt ring B B a 0))

/-- Phase B one-step obligation for *all the other literal consumer rows around
    SUPPRESS*.  The frontier fixture proves only the concrete SUPPRESS-breaking fixture below;
    this is the exact generic lift still required. -/
def FullConsumerFrontStepStatement
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (corridorLen : Nat) : Prop :=
  ∀ (initial current : FC n psi kappa tau) (a : Fin n) (k : Nat),
    k < corridorLen →
    2 + corridorLen < n →
    BirthShortDoneTerminalFirstHit.Leaderless current →
    TripleLabels hpsi ring current a →
    ResetFrontAt ring initial current a k →
    PreparedOrdinaryOpen hpsi
      (current (drainSite ring a k))
      (current (ring.rightNeighbor (drainSite ring a k))) →
    let e := drainSite ring a k
    let D := BirthShortDoneTerminalConsumer.step
      hpsi (by decide : 0 < 2) h2 ring current e
    HasLeader D ∨
      (BirthShortDoneTerminalFirstHit.Leaderless D ∧
        TripleLabels hpsi ring D a ∧
        ResetFrontAt ring initial D a (k + 1))

/-- Phase B finite termination obtained by iterating the preceding step with
    measure `corridorLen-k`.  Notice that this only moves the reset front to the
    corridor end; it does not claim sanitation. -/
def ResetFrontTerminationStatement
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) : Prop :=
  ∀ (initial : FC n psi kappa tau) (a : Fin n) (corridorLen : Nat),
    0 < corridorLen →
    2 + corridorLen < n →
    BirthShortDoneTerminalFirstHit.Leaderless initial →
    TripleLabels hpsi ring initial a →
    ResetFrontAt ring initial initial a 0 →
    let w := rightDrainWord ring a corridorLen
    let D := currentRun hpsi h2 ring initial w
    HasLeaderAlong hpsi h2 ring initial w ∨
      (LeaderlessAlong hpsi h2 ring initial w ∧
        ResetFrontAt ring initial D a corridorLen)

/-- Phase C, the real unresolved termination obligation.  Starting from a
    reset front at the right boundary, find a finite supported suffix which
    either births or absorbs every exported reset/echo/writer/K2/comparison
    carrier without wrapping through the protected triple and leaves the
    triple sanitized.  The literal fixture and `WallSweepEchoDrain` direction
    make this the critical theorem to prove or refute next. -/
def CorridorAbsorptionStatement
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) : Prop :=
  ∀ (current : FC n psi kappa tau) (a : Fin n) (corridorLen : Nat),
    0 < corridorLen →
    2 + corridorLen < n →
    BirthShortDoneTerminalFirstHit.Leaderless current →
    TripleLabels hpsi ring current a →
    ResetFrontAt ring current current a corridorLen →
    ∃ finish : List (Fin n),
      WordSupported ring a corridorLen finish ∧
      (let D := currentRun hpsi h2 ring current finish
       HasLeaderAlong hpsi h2 ring current finish ∨
        (LeaderlessAlong hpsi h2 ring current finish ∧
          AlignedAlong hpsi h2 ring current finish a ∧
          PassiveNoReentry hpsi h2 ring current finish a ∧
          CorridorTerminated ring D a corridorLen ∧
          ThreeSiteSanitized hpsi ring D a))

/-! ## Literal SUPPRESS/front audit from the frontier geometry -/

private theorem hTwo : 0 < 2 := by decide
private theorem hTwoLe : 2 ≤ 2 := by decide

def fixtureRingFour : DirectedRing 4 := ⟨by decide⟩

abbrev E := ExpiringAgentState 2 2 0
abbrev FC4 := Fin 4 → E

private theorem fin4_cases (i : Fin 4) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  omega

private def d0 : Registers 2 where
  label := 0
  h := false
  carry := false
  reset := false
  count := 0
  wait := true
  bit := false
  phase := false
  writer := .none

private def d1 : Registers 2 where
  label := 1
  h := false
  carry := false
  reset := false
  count := 0
  wait := true
  bit := false
  phase := false
  writer := .none

private def fixtureRaw (i : Fin 4) : AgentState 2 :=
  if i = 0 then cell d0
  else if i = 1 then cell d1
  else if i = 2 then { cell d0 with reset_cmd := true }
  else cell d1

private theorem fixtureRaw_domain (i : Fin 4) :
    (fixtureRaw i).inProtocolDomain 2 := by
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
    simp [fixtureRaw, d0, d1, AgentState.inProtocolDomain,
      BirthWaitPassive.cell]

private def fixtureSource : FC4 := fun i =>
  ⟨⟨BoundedAgentState.ofDomain
      (fixtureRaw i) (fixtureRaw_domain i), false⟩, 0⟩

private def fixtureAfter : FC4 :=
  currentRun hTwo hTwoLe fixtureRingFour fixtureSource [(2 : Fin 4)]

private theorem fixture_front0 :
    ResetFrontAt fixtureRingFour fixtureSource fixtureSource
      (0 : Fin 4) 0 := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro j hj
    omega
  · intro j hj hbound
    rfl

private theorem fixture_strict0 :
    StrictResetFrontAt fixtureRingFour fixtureSource fixtureSource
      (0 : Fin 4) 0 := by
  refine ⟨fixture_front0, ?_⟩
  intro j hj
  omega

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem fixture_front1 :
    ResetFrontAt fixtureRingFour fixtureSource fixtureAfter
      (0 : Fin 4) 1 := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    decide
  · intro j hj hbound
    omega

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem fixture_not_strict1 :
    ¬ StrictResetFrontAt fixtureRingFour fixtureSource fixtureAfter
      (0 : Fin 4) 1 := by
  intro h
  have hfalse := h.2 0 (by omega)
  have htrue :
      (raw (fixtureAfter
        (drainSite fixtureRingFour (0 : Fin 4) 0))).echo = true := by
    decide
  have hbad : true = false := htrue.symm.trans hfalse
  cases hbad

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem fixture_after_not_sanitized :
    ¬ ThreeSiteSanitized hTwo fixtureRingFour fixtureAfter (0 : Fin 4) := by
  intro h
  unfold ThreeSiteSanitized at h
  have hp := h.2.2.1
  have htail :
      fixtureRingFour.rightNeighbor
        (fixtureRingFour.rightNeighbor (0 : Fin 4)) = (2 : Fin 4) := by
    decide
  rw [htail] at hp
  have hfalse := Q11632RightDrainCollar.passive_echo_false hp
  have htrue : (raw (fixtureAfter 2)).echo = true := by decide
  have hbad : true = false := htrue.symm.trans hfalse
  cases hbad

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
/-- The exact phenomenon that kills an echo-free right-front invariant.

The literal current consumer advances the reset token from site 2 to site 3,
so the reset cursor reaches the end of a one-site corridor and its measure
strictly decreases to zero.  Nevertheless site 2 is left with `echo=true`, the
strict front invariant fails, and the protected triple is not sanitized. -/
theorem suppress_row_literal_front_audit :
    StrictResetFrontAt fixtureRingFour fixtureSource fixtureSource
        (0 : Fin 4) 0 ∧
      ResetFrontAt fixtureRingFour fixtureSource fixtureAfter
        (0 : Fin 4) 1 ∧
      resetFrontMeasure 1 1 < resetFrontMeasure 1 0 ∧
      (raw (fixtureAfter 2)).reset_cmd = false ∧
      (raw (fixtureAfter 2)).echo = true ∧
      (raw (fixtureAfter 3)).reset_cmd = true ∧
      (raw (fixtureAfter 3)).echo = false ∧
      ¬ StrictResetFrontAt fixtureRingFour fixtureSource fixtureAfter
        (0 : Fin 4) 1 ∧
      ¬ ThreeSiteSanitized hTwo fixtureRingFour fixtureAfter (0 : Fin 4) := by
  exact ⟨fixture_strict0, fixture_front1,
    resetFrontMeasure_step (corridorLen := 1) (k := 0) (by decide),
    by decide, by decide, by decide, by decide,
    fixture_not_strict1, fixture_after_not_sanitized⟩

end BirthB1RightDrainProducer

#print axioms BirthB1RightDrainProducer.resetFrontMeasure_step
#print axioms BirthB1RightDrainProducer.resetPhaseMeasure_step
#print axioms BirthB1RightDrainProducer.switch_to_cleanup_measure_drops
#print axioms BirthB1RightDrainProducer.suppress_row_literal_front_audit
