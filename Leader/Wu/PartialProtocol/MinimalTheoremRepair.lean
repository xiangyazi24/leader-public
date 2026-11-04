import Leader.Wu.PartialProtocol.LocalLegitimacyCounterexample
import Leader.Wu.Safety.NoCheckBirthOutputLegitimacy

/-!
# Minimal theorem repair for the exact `P_partial` protocol

The accepted six-agent counterexample separates two specifications that the
old `PPartialLocalLegitimacy` interface conflated.  Its exact successor still
has one leader, but that leader migrates to another agent, so the pointwise
output vector changes.

This file consequently exposes two disjoint theorem layers without changing
the protocol transition.

* `PPartialPerpetualUniquenessStep` asks only that one current leader remain
  one current leader.  Together with the existing rank producers it yields a
  deterministic schedule after which every reachable configuration continues
  to have exactly one leader.  It deliberately says nothing about which agent
  is the leader.
* `PPartialStableLegit` is the logically minimal semantic strengthening: current
  unique leadership plus `OutputStableFrom`.  It is exactly Definition-1
  `IsSafe`, so it is a conclusion, not an admissible convergence premise.
  For a noncircular operational route, `PPartialOutputLegit` reuses the existing
  four-field output kernel.  That predicate has an explicit inhabitant.  Its
  exact one-step closure/output-frame obligation and its rank-zero/rank-one
  producer remain separately named protocol obligations.

The proved numeric-domain theorem is internalized throughout.  No copied
or shadow transition is introduced.
-/

namespace PPLLCompleteMultiLeaderCleanup

open PPLL PPLLResearchFormulation
open PPLLNoCheckBirthOutputLegitimacy
open PPLLNoCheckBirthPhysicalConditionOne

set_option autoImplicit false

variable {n psi kappa tau : Nat}

/-- One canonical proof term for the already discharged numeric-domain
obligation.  Keeping this proof-dependent parameter named prevents Lean from
constructing distinct (propositionally equal but not definitionally equal)
protocol packages at schedule endpoints. -/
private abbrev pPartialDomainSol
    (hpsi : psi > 0) (kappa : Nat) :
    PPartialAuthorizedDomainClosure hpsi kappa :=
  PPartialAuthorizedDomainClosure_q5776 hpsi kappa

/-- The existing packaged protocol at the canonical domain proof.  This is
only an abbreviation of `P_partialProtocol`, never a replacement transition. -/
private abbrev pPartialProtocolSol
    (hpsi : psi > 0) (kappa tau : Nat) : PopulationProtocol :=
  P_partialProtocol hpsi kappa tau (pPartialDomainSol hpsi kappa)

/-! ## A. Perpetual uniqueness, without output stabilization -/

/-- The accepted nondegenerate six-agent instance refutes the old combined
local obligation for the exact unconditional `P_partial` protocol. -/
theorem P_partial_old_localLegitimacy_refuted_n6 :
    ¬ PPartialLocalLegitimacyUnconditional
      (n := 6) (by omega : (3 : Nat) > 0) 1 1
      (⟨by omega⟩ : DirectedRing 6) := by
  simpa using
    Q5804.PPartialLocalLegitimacyUnconditional_false_q5804

/-- The exact weakened local obligation left after removing the refuted
pointwise-output conjunct from `PPartialLocalLegitimacy`.

This permits the unique leader to migrate between agents. -/
def PPartialPerpetualUniquenessStep
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) : Prop :=
  ∀ C : PPartialConfig n psi kappa tau,
    PPartialLegit hpsi kappa tau (pPartialDomainSol hpsi kappa) C →
    ∀ e : Fin n,
      PPartialLegit hpsi kappa tau (pPartialDomainSol hpsi kappa)
        ((pPartialProtocolSol hpsi kappa tau).step ring C e)

/-- Every old local-legitimacy proof would imply the weakened uniqueness-only
obligation.  The converse is intentionally absent: the counterfamily refutes its
pointwise-output component. -/
theorem PPartialLocalLegitimacyUnconditional.toPerpetualUniquenessStep
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (hLocal : PPartialLocalLegitimacyUnconditional
      hpsi kappa tau ring) :
    PPartialPerpetualUniquenessStep hpsi kappa tau ring := by
  intro C hC e
  exact (hLocal C hC e).1

/-- The weakened local obligation is exactly enough to make current unique
leadership a closed predicate. -/
theorem P_partial_perpetualUniqueness_closed
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (hUnique : PPartialPerpetualUniquenessStep
      hpsi kappa tau ring) :
    PopulationProtocol.ClosedPred
      (pPartialProtocolSol hpsi kappa tau)
      ring
      (PPartialLegit hpsi kappa tau
        (pPartialDomainSol hpsi kappa)) := by
  intro C hC C' hstep
  obtain ⟨e, rfl⟩ := hstep
  exact hUnique C hC e

/-- From a configuration with one current leader, every reachable future still
has one current leader.  No equality of output vectors occurs in this type. -/
def PPartialPerpetuallyUniqueFrom
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : PPartialConfig n psi kappa tau) : Prop :=
  ∀ C' : PPartialConfig n psi kappa tau,
    PopulationProtocol.Reachable
      (pPartialProtocolSol hpsi kappa tau) ring C C' →
    PPartialLegit hpsi kappa tau (pPartialDomainSol hpsi kappa) C'

/-- Closedness lifts the local uniqueness-only obligation through arbitrary
finite reachability. -/
theorem P_partial_perpetuallyUniqueFrom
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (hUnique : PPartialPerpetualUniquenessStep
      hpsi kappa tau ring)
    (C : PPartialConfig n psi kappa tau)
    (hC : PPartialLegit hpsi kappa tau
      (pPartialDomainSol hpsi kappa) C) :
    PPartialPerpetuallyUniqueFrom hpsi kappa tau ring C := by
  intro C' hreach
  exact (P_partial_perpetualUniqueness_closed
    hpsi kappa tau ring hUnique).reachable hC hreach

/-- Existing base and strict-descent producers converge to perpetual unique
leadership once the weakened local closure obligation is supplied.

The conclusion is strictly the uniqueness specification: it does not contain
`OutputStableFrom`, `IsSafe`, or `ReachesSafeWithinSchedule`. -/
theorem P_partial_exists_perpetuallyUnique_schedule
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (baseBound roundBound : Nat)
    (hUnique : PPartialPerpetualUniquenessStep
      hpsi kappa tau ring)
    (hBase : PPartialBaseProducerUnconditional
      hpsi kappa tau ring baseBound)
    (hDescent : PPartialStrictDescentProducerUnconditional
      hpsi kappa tau ring roundBound)
    (C : PPartialConfig n psi kappa tau) :
    ∃ word : DetSchedule n,
      word.length ≤ baseBound + n * roundBound ∧
      let D := runLocalSchedule ring
        (P_partial hpsi kappa tau
          (pPartialDomainSol hpsi kappa)) C word
      PPartialLegit hpsi kappa tau
          (pPartialDomainSol hpsi kappa) D ∧
        PPartialPerpetuallyUniqueFrom hpsi kappa tau ring D := by
  obtain ⟨word, hword, hlegit⟩ :=
    P_partial_exists_legit_schedule
      hpsi kappa tau
      (pPartialDomainSol hpsi kappa)
      ring baseBound roundBound hBase hDescent C
  refine ⟨word, hword, ?_⟩
  have hlegit' :
      PPartialLegit hpsi kappa tau
        (pPartialDomainSol hpsi kappa)
        (runLocalSchedule ring
          (P_partial hpsi kappa tau
            (pPartialDomainSol hpsi kappa))
          C word) :=
    hlegit
  exact ⟨hlegit', P_partial_perpetuallyUniqueFrom
    hpsi kappa tau ring hUnique _ hlegit'⟩

/-! ## B. Definition-1 safety and its noncircular operational route -/

/-- The logically smallest semantic strengthening of current unique
leadership: add exactly the missing Definition-1 output-stability conjunct.

Because this predicate is equivalent to `IsSafe`, it must not be carried as a
producer hypothesis in a convergence theorem. -/
def PPartialStableLegit
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : PPartialConfig n psi kappa tau) : Prop :=
  PPartialLegit hpsi kappa tau (pPartialDomainSol hpsi kappa) C ∧
    OutputStableFrom
      (pPartialProtocolSol hpsi kappa tau) ring C

/-- `PPartialStableLegit` is exactly Definition-1 semantic safety, not a new
operational approximation. -/
theorem PPartialStableLegit_iff_isSafe
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : PPartialConfig n psi kappa tau) :
    PPartialStableLegit hpsi kappa tau ring C ↔
      PopulationProtocol.IsSafe
        (pPartialProtocolSol hpsi kappa tau)
        ring C isLeaderOutput := by
  change
    (UniqueLeaderOutput
        (pPartialProtocolSol hpsi kappa tau)
        n C isLeaderOutput ∧
      OutputStableFrom
        (pPartialProtocolSol hpsi kappa tau) ring C) ↔
      PopulationProtocol.IsSafe
        (pPartialProtocolSol hpsi kappa tau)
        ring C isLeaderOutput
  exact (isSafe_iff_unique_and_outputStable
    (pPartialProtocolSol hpsi kappa tau)
    ring C isLeaderOutput).symm

/-- The exact semantic predicate is closed for the exact `P_partial` protocol.
This is the generic transitivity theorem for `IsSafe`; it is not a convergence
or protocol-analysis result. -/
theorem PPartialStableLegit_closed
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred
      (pPartialProtocolSol hpsi kappa tau)
      ring
      (PPartialStableLegit hpsi kappa tau ring) := by
  intro C hC C' hstep
  have hsafe : PopulationProtocol.IsSafe
      (pPartialProtocolSol hpsi kappa tau)
      ring C isLeaderOutput :=
    (PPartialStableLegit_iff_isSafe
      hpsi kappa tau ring C).1 hC
  have hsafe' : PopulationProtocol.IsSafe
      (pPartialProtocolSol hpsi kappa tau)
      ring C' isLeaderOutput :=
    isSafe_closed
      (pPartialProtocolSol hpsi kappa tau)
      ring isLeaderOutput C hsafe C' hstep
  exact (PPartialStableLegit_iff_isSafe
    hpsi kappa tau ring C').2 hsafe'

/-! ### A nonempty operational strengthening -/

/-- The smallest existing source-backed output kernel: one leader, that
leader at label zero, peaceful bullets, and no free barrier.

The predicate is interpreted under the exact `P_partial` carrier.  It does not
silently reuse the no-CHECK transition; only the state predicate is shared. -/
def PPartialOutputLegit
    (hpsi : psi > 0) (ring : DirectedRing n)
    (C : PPartialConfig n psi kappa tau) : Prop :=
  OutputSafeConfig hpsi ring (eraseExpiringConfig C)

/-- The operational output kernel strengthens current unique leadership for
the exact packaged `P_partial` output map. -/
theorem PPartialOutputLegit.toLegit
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : PPartialConfig n psi kappa tau)
    (hC : PPartialOutputLegit hpsi ring C) :
    PPartialLegit hpsi kappa tau
      (pPartialDomainSol hpsi kappa) C := by
  obtain ⟨leader, hleader, honly⟩ := hC.unique_leader
  refine ⟨leader, ?_, ?_⟩
  · change (C leader).core.core.leader = true at hleader
    simp [pPartialProtocolSol, P_partialProtocol,
      isLeaderOutput, hleader]
  · intro i hi
    apply honly i
    change (C i).core.core.leader = true
    cases h : (C i).core.core.leader
    · simp [pPartialProtocolSol, P_partialProtocol,
        isLeaderOutput, h] at hi
    · rfl

/-- The stronger current-state predicate is genuinely inhabited for every
parameter choice.  This reuses only the canonical finite state from the
no-CHECK baseline; no theorem about the no-CHECK transition is transported. -/
theorem PPartialOutputLegit_inhabited
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) :
    ∃ C : PPartialConfig n psi kappa tau,
      PPartialOutputLegit hpsi ring C := by
  refine ⟨outputFinite (n := n) hpsi kappa tau, ?_⟩
  simpa [PPartialOutputLegit, OutputLegit] using
    (outputLegit_inhabited hpsi kappa tau ring)

/-- The exact remaining local proof obligation for the operational kernel.
It is strictly transition-local: preserve the four current-state fields and
the pointwise output vector across one actual `P_partial` interaction. -/
def PPartialOutputLegitimacyStepObligation
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) : Prop :=
  ∀ C : PPartialConfig n psi kappa tau,
    PPartialOutputLegit hpsi ring C →
    ∀ e : Fin n,
      let D :=
        (pPartialProtocolSol hpsi kappa tau).step ring C e
      PPartialOutputLegit hpsi ring D ∧
        ∀ i : Fin n,
          (pPartialProtocolSol hpsi kappa tau).output (D i) =
            (pPartialProtocolSol hpsi kappa tau).output (C i)

/-- The exact local obligation yields closure of the nonempty operational
kernel. -/
theorem PPartialOutputLegit_closed
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (hStep : PPartialOutputLegitimacyStepObligation
      hpsi kappa tau ring) :
    PopulationProtocol.ClosedPred
      (pPartialProtocolSol hpsi kappa tau)
      ring (PPartialOutputLegit hpsi ring) := by
  intro C hC C' hone
  obtain ⟨e, rfl⟩ := hone
  exact (hStep C hC e).1

/-- The same local obligation supplies the missing one-step output frame. -/
theorem PPartialOutputLegit_stepOutputPreserving
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (hStep : PPartialOutputLegitimacyStepObligation
      hpsi kappa tau ring) :
    StepOutputPreservingOn
      (pPartialProtocolSol hpsi kappa tau)
      ring (PPartialOutputLegit hpsi ring) := by
  intro C hC C' hone i
  obtain ⟨e, rfl⟩ := hone
  exact (hStep C hC e).2 i

/-- Under the explicit one-step obligation, membership in the nonempty
operational kernel implies genuine Definition-1 safety. -/
theorem PPartialOutputLegit_isSafe
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (hStep : PPartialOutputLegitimacyStepObligation
      hpsi kappa tau ring)
    (C : PPartialConfig n psi kappa tau)
    (hC : PPartialOutputLegit hpsi ring C) :
    PopulationProtocol.IsSafe
      (pPartialProtocolSol hpsi kappa tau)
      ring C isLeaderOutput := by
  exact isSafe_of_operational_legitimacy
    (pPartialProtocolSol hpsi kappa tau)
    ring isLeaderOutput
    (PPartialOutputLegit hpsi ring)
    (PPartialOutputLegit_closed
      hpsi kappa tau ring hStep)
    (fun C hC =>
      PPartialOutputLegit.toLegit
        hpsi kappa tau ring C hC)
    (PPartialOutputLegit_stepOutputPreserving
      hpsi kappa tau ring hStep)
    hC

/-- Operational membership, after the local obligation is discharged, gives
the exact semantic strengthened predicate. -/
theorem PPartialOutputLegit_toStableLegit
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (hStep : PPartialOutputLegitimacyStepObligation
      hpsi kappa tau ring)
    (C : PPartialConfig n psi kappa tau)
    (hC : PPartialOutputLegit hpsi ring C) :
    PPartialStableLegit hpsi kappa tau ring C := by
  exact (PPartialStableLegit_iff_isSafe
    hpsi kappa tau ring C).2
      (PPartialOutputLegit_isSafe
        hpsi kappa tau ring hStep C hC)

/-! ### Exact residual producers for global Definition-1 convergence -/

/-- The only strengthened base producer used below.  It is restricted to
leader-count rank zero or one and targets the concrete four-field kernel, not
semantic `IsSafe`. -/
def PPartialOutputBaseProducer
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) (baseBound : Nat) : Prop :=
  ∀ C : PPartialConfig n psi kappa tau,
    P_partialLeaderCount C ≤ 1 →
    ∃ word : DetSchedule n,
      word.length ≤ baseBound ∧
      PPartialOutputLegit hpsi ring
        (runLocalSchedule ring
          (P_partial hpsi kappa tau
            (pPartialDomainSol hpsi kappa))
          C word)

private theorem pPartial_runLocalSchedule_append_sol
    {Q : Type} (ring : DirectedRing n)
    (T : Q → Q → Q × Q)
    (C : Fin n → Q) (xs ys : DetSchedule n) :
    runLocalSchedule ring T C (xs ++ ys) =
      runLocalSchedule ring T
        (runLocalSchedule ring T C xs) ys := by
  induction xs generalizing C with
  | nil =>
      rfl
  | cons e xs ih =>
      simp only [List.cons_append, runLocalSchedule]
      exact ih (localStep ring T C e)

/-- Strong induction composes the strengthened base producer with the already
named positive strict-descent producer.  Neither premise assumes semantic
safety or arbitrary-state convergence. -/
theorem P_partial_output_fuel_compose
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (baseBound roundBound fuel : Nat)
    (hBase : PPartialOutputBaseProducer
      hpsi kappa tau ring baseBound)
    (hDescent : PPartialStrictDescentProducerUnconditional
      hpsi kappa tau ring roundBound)
    (C : PPartialConfig n psi kappa tau)
    (hCount : P_partialLeaderCount C ≤ fuel) :
    ∃ word : DetSchedule n,
      word.length ≤ baseBound + fuel * roundBound ∧
      PPartialOutputLegit hpsi ring
        (runLocalSchedule ring
          (P_partial hpsi kappa tau
            (pPartialDomainSol hpsi kappa))
          C word) := by
  induction fuel generalizing C with
  | zero =>
      have hSmall : P_partialLeaderCount C ≤ 1 := by
        omega
      obtain ⟨word, hWord, hLegit⟩ := hBase C hSmall
      refine ⟨word, ?_, hLegit⟩
      simpa using hWord
  | succ fuel ih =>
      by_cases hSmall : P_partialLeaderCount C ≤ 1
      · obtain ⟨word, hWord, hLegit⟩ := hBase C hSmall
        refine ⟨word, ?_, hLegit⟩
        exact Nat.le_trans hWord
          (Nat.le_add_right baseBound
            (Nat.succ fuel * roundBound))
      · have hLarge : 1 < P_partialLeaderCount C := by
          omega
        obtain ⟨head, hHead, _hPositive, hDrop⟩ :=
          hDescent C hLarge
        let D := runLocalSchedule ring
          (P_partial hpsi kappa tau
            (pPartialDomainSol hpsi kappa))
          C head
        have hDropD :
            P_partialLeaderCount D < P_partialLeaderCount C := by
          simpa only [D] using hDrop
        have hDCount : P_partialLeaderCount D ≤ fuel := by
          omega
        obtain ⟨tail, hTail, hLegit⟩ := ih D hDCount
        refine ⟨head ++ tail, ?_, ?_⟩
        · simp only [List.length_append]
          calc
            head.length + tail.length ≤
                roundBound +
                  (baseBound + fuel * roundBound) :=
              Nat.add_le_add hHead hTail
            _ = baseBound + Nat.succ fuel * roundBound := by
              simp [Nat.succ_mul, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm]
        · rw [pPartial_runLocalSchedule_append_sol]
          exact hLegit

/-- The physical leader-count bound removes explicit fuel from the exact
operational-kernel producer composition. -/
theorem P_partial_exists_outputLegit_schedule
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (baseBound roundBound : Nat)
    (hBase : PPartialOutputBaseProducer
      hpsi kappa tau ring baseBound)
    (hDescent : PPartialStrictDescentProducerUnconditional
      hpsi kappa tau ring roundBound)
    (C : PPartialConfig n psi kappa tau) :
    ∃ word : DetSchedule n,
      word.length ≤ baseBound + n * roundBound ∧
      PPartialOutputLegit hpsi ring
        (runLocalSchedule ring
          (P_partial hpsi kappa tau
            (pPartialDomainSol hpsi kappa))
          C word) := by
  exact P_partial_output_fuel_compose
    hpsi kappa tau ring baseBound roundBound n
    hBase hDescent C (P_partialLeaderCount_le C)

/-- Corrected deterministic Definition-1 interface for the unchanged exact
`P_partial` protocol.

The three remaining premises are local/output-kernel closure, a rank-zero/
rank-one output-kernel producer, and the already named positive strict-descent
producer.  None is Definition-1 safety or arbitrary-state convergence under a
different name. -/
theorem P_partial_outputLegit_deterministic_interface
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (baseBound roundBound : Nat)
    (hStep : PPartialOutputLegitimacyStepObligation
      hpsi kappa tau ring)
    (hBase : PPartialOutputBaseProducer
      hpsi kappa tau ring baseBound)
    (hDescent : PPartialStrictDescentProducerUnconditional
      hpsi kappa tau ring roundBound) :
    PopulationProtocol.ClosedPred
        (pPartialProtocolSol hpsi kappa tau)
        ring (PPartialOutputLegit hpsi ring) ∧
      (∀ C : PPartialConfig n psi kappa tau,
        PPartialOutputLegit hpsi ring C →
        PopulationProtocol.IsSafe
          (pPartialProtocolSol hpsi kappa tau)
          ring C isLeaderOutput) ∧
      (∀ C : PPartialConfig n psi kappa tau,
        ∃ word : DetSchedule n,
          word.length ≤ baseBound + n * roundBound ∧
          ReachesSafeWithinSchedule
            (pPartialProtocolSol hpsi kappa tau)
            ring isLeaderOutput C word) := by
  refine ⟨PPartialOutputLegit_closed
      hpsi kappa tau ring hStep, ?_, ?_⟩
  · intro C hC
    exact PPartialOutputLegit_isSafe
      hpsi kappa tau ring hStep C hC
  · intro C
    obtain ⟨word, hWord, hLegit⟩ :=
      P_partial_exists_outputLegit_schedule
        hpsi kappa tau ring baseBound roundBound
        hBase hDescent C
    have hSafe : PopulationProtocol.IsSafe
        (pPartialProtocolSol hpsi kappa tau)
        ring
        (runLocalSchedule ring
          (P_partial hpsi kappa tau
            (pPartialDomainSol hpsi kappa))
          C word)
        isLeaderOutput :=
      PPartialOutputLegit_isSafe
        hpsi kappa tau ring hStep _ hLegit
    refine ⟨word, hWord, ?_⟩
    refine ⟨word.length, Nat.le_refl word.length, ?_⟩
    simp only [List.take_length]
    change PopulationProtocol.IsSafe
      (pPartialProtocolSol hpsi kappa tau)
      ring
      (runSchedule
        (pPartialProtocolSol hpsi kappa tau)
        ring C word)
      isLeaderOutput
    rw [← P_partial_runLocalSchedule_eq_runSchedule
      hpsi kappa tau
      (pPartialDomainSol hpsi kappa)
      ring C word]
    exact hSafe

end PPLLCompleteMultiLeaderCleanup
