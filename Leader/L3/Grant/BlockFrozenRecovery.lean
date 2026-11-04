import Leader.L3.Grant.BlockFrozenColdClock
import Leader.L3.Bank.TrialRenewal

/-!
G16 C.17: the authentic C.2 RESET recovery stage on the protected
reference fields.  A recovering root's first root service is a
launch (RWAIT, digit one RR), which the C.2 observer sends to the
launch/retry constructor; a stateless phase reading of the new
fields would call it cold.  The two-state recovery mark keeps that
launch history.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

open Classical
open K2ArbitraryElimination.FiniteAccounting

/-! Authentic C.2 recovery stages on protected reference fields. -/

inductive GrantBlockFrozenColdRecoveryMark where
  | recovering
  | launched
  deriving DecidableEq

structure GrantBlockFrozenColdRecoveryView (q : Nat) where
  bank : GrantBankReference.BankLocalReference (compileAdvice q).b
  phase : GrantBlockFrozenColdRecoveryMark

/-- The safe RESET/recovery skeleton retains the C.2 launch history.
It is intentionally not an unguarded grant/defect observer. -/
noncomputable def grantBlockFrozenColdRecoverySafeNext
    {n q : Nat} (ring : DirectedRing n)
    (root : Fin n) (z : GrantBlockFrozenColdRecoveryView q)
    (edge : Fin n) : GrantBlockFrozenColdRecoveryView q :=
  match z.phase with
  | .launched => z
  | .recovering =>
      { bank :=
          GrantBankReference.bankLocalReferenceStepClamped
            ring root z.bank edge
        phase := if edge = root then .launched else .recovering }

/-- C.2's real RESET service at the root becomes a retry/launch,
not an ordinary first-stage cold continuation. The protected
fields agree with the actual postservice launch configuration. -/
theorem grantBlockFrozenColdRecoveryRootLaunch
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : Counter.ResetClockBankRecovery (q := q) ring root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hfields : GrantBankReference.bankLocalReferenceFieldsAgree
      ring x.val root S)
    (hfalse : S.success = false)
    (hno : ¬ Counter.ResetClockBankDefectEntry
      ring x.val root root)
    (hgrant : Counter.GrantFree
      ((protocol q).step ring x.val root) root) :
    ∃ seed : Counter.ResetClockBankLaunchSeed (q := q) ring root,
      Counter.resetClockBankRenewalNext ring root hsp
        (.inl (.inr x)) root =
          .inl (Counter.resetClockBankAttemptStart ring root seed) ∧
      GrantBankReference.bankLocalReferenceFieldsAgree ring
        seed.val root
        (grantBlockFrozenColdRecoverySafeNext ring root
          ⟨S, .recovering⟩ root).bank ∧
      (grantBlockFrozenColdRecoverySafeNext ring root
        ⟨S, .recovering⟩ root).phase = .launched := by
  obtain ⟨seed, hservice, hphysical⟩ :=
    Counter.resetClockBankAttemptServiceRecoverRetry
      ring root hsp x root hno hgrant rfl
  have hproject :=
    GrantBankReference.bankLocalReferenceSupportStep
      ring x.val root root S hsp x.property.1
      x.property.2.1 hfields hfalse hno
  refine ⟨seed, ?_, ?_, ?_⟩
  · change Counter.resetClockBankResultObserve ring root
      (Counter.resetClockBankAttemptService
        ring root hsp (.inr x) root) =
      .inl (Counter.resetClockBankAttemptStart ring root seed)
    rw [hservice]
    rfl
  · change GrantBankReference.bankLocalReferenceFieldsAgree
      ring seed.val root
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root S root)
    rw [hphysical]
    exact hproject.1
  · change (if root = root then
        GrantBlockFrozenColdRecoveryMark.launched
      else GrantBlockFrozenColdRecoveryMark.recovering) =
        .launched
    simp

/-- A nonroot safe C.2 recovery service remains an actual
Recovery subtype, with its postservice fields synchronized. -/
theorem grantBlockFrozenColdRecoveryNonroot
    {n q : Nat} (ring : DirectedRing n) (root edge : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : Counter.ResetClockBankRecovery (q := q) ring root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hfields : GrantBankReference.bankLocalReferenceFieldsAgree
      ring x.val root S)
    (hfalse : S.success = false)
    (hne : edge ≠ root)
    (hno : ¬ Counter.ResetClockBankDefectEntry
      ring x.val root edge)
    (hgrant : Counter.GrantFree
      ((protocol q).step ring x.val edge) root) :
    ∃ y : Counter.ResetClockBankRecovery (q := q) ring root,
      Counter.resetClockBankRenewalNext ring root hsp
        (.inl (.inr x)) edge = .inl (.inr y) ∧
      GrantBankReference.bankLocalReferenceFieldsAgree ring
        y.val root
        (grantBlockFrozenColdRecoverySafeNext ring root
          ⟨S, .recovering⟩ edge).bank ∧
      (grantBlockFrozenColdRecoverySafeNext ring root
        ⟨S, .recovering⟩ edge).phase = .recovering := by
  obtain ⟨y, hservice, hphysical⟩ :=
    Counter.resetClockBankAttemptServiceRecoverContinue
      ring root hsp x edge hno hgrant hne
  have hproject :=
    GrantBankReference.bankLocalReferenceSupportStep
      ring x.val root edge S hsp x.property.1
      x.property.2.1 hfields hfalse hno
  refine ⟨y, ?_, ?_, ?_⟩
  · change Counter.resetClockBankResultObserve ring root
      (Counter.resetClockBankAttemptService
        ring root hsp (.inr x) edge) = .inl (.inr y)
    rw [hservice]
    rfl
  · change GrantBankReference.bankLocalReferenceFieldsAgree
      ring y.val root
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root S edge)
    rw [hphysical]
    exact hproject.1
  · change (if edge = root then
        GrantBlockFrozenColdRecoveryMark.launched
      else GrantBlockFrozenColdRecoveryMark.recovering) =
        .recovering
    simp [hne]

/-! C.3 credit projections: the reference only stores BANK fields. -/

/-- Worker occupancy from the actual fixed digit slots. The
dependent guard restricts the Fin constructor, not the scheduler. -/
noncomputable def grantBlockFrozenColdLocalWorkers
    (q : Nat)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Nat :=
  ((List.range (compileAdvice q).b).map (fun j =>
    if hj : j < (compileAdvice q).b then
      if (S.fields (⟨j + 1, by omega⟩ :
          Fin ((compileAdvice q).b + 1))).2.2.1 = .E then
        0 else 1
    else 0)).sum

/-- Physical digit occupancy agrees exactly with a four-field
BANK reference at every site 1,...,b. -/
theorem grantBlockFrozenColdWorkerProjection
    {n q : Nat} (ring : DirectedRing n)
    (C : Counter.Config q n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hfields : GrantBankReference.bankLocalReferenceFieldsAgree
      ring C root S) :
    Counter.resetColdWorkerCount ring C root =
      grantBlockFrozenColdLocalWorkers q S := by
  unfold Counter.resetColdWorkerCount
    grantBlockFrozenColdLocalWorkers
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  have hlt : j < (compileAdvice q).b := by
    simpa only [List.mem_range] using hj
  simp only [dif_pos hlt]
  exact congrArg (fun t : BTok => if t = .E then 0 else 1)
    (congrArg (fun p : Mode × Bool × BTok × Nat =>
      p.2.2.1) (hfields (j + 1) (by omega)))

/-- Local mode/lease plus occupied digit slots: the active C.3
potential, before application of the physical stopping classifier. -/
noncomputable def grantBlockFrozenColdLocalActiveCredit
    (n q : Nat)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Nat :=
  Counter.resetColdModeCredit n (compileAdvice q).bankLeaseCap
    (S.fields (0 : Fin ((compileAdvice q).b + 1))).1
    (S.fields (0 : Fin ((compileAdvice q).b + 1))).2.2.2 +
  n * grantBlockFrozenColdLocalWorkers q S

/-- STOP means the success latch or the C.3 RESET handoff;
these branches have zero first-stage credit. -/
noncomputable def grantBlockFrozenColdLocalStoppedCredit
    (n q : Nat)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Nat :=
  if S.success then 0
  else if (S.fields (0 : Fin ((compileAdvice q).b + 1))).1 =
      .RESET then 0
  else grantBlockFrozenColdLocalActiveCredit n q S

/-- The active physical C.3 credit is determined entirely by
the four protected BANK fields; no worker provenance is assumed. -/
theorem grantBlockFrozenColdActiveCreditProjection
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (x : Counter.ResetClockBankColdCarrier (q := q) ring root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hfields : GrantBankReference.bankLocalReferenceFieldsAgree
      ring x.val root S) :
    Counter.resetColdUncappedCredit ring root (.inl x) =
      grantBlockFrozenColdLocalActiveCredit n q S := by
  have hzero := hfields 0 (by omega)
  have hmode :
      (x.val root).mode =
        (S.fields (0 : Fin ((compileAdvice q).b + 1))).1 :=
    congrArg (fun p : Mode × Bool × BTok × Nat => p.1) hzero
  have hlease :
      (x.val root).lease.val =
        (S.fields (0 : Fin ((compileAdvice q).b + 1))).2.2.2 :=
    congrArg (fun p : Mode × Bool × BTok × Nat => p.2.2.2) hzero
  have hworkers :=
    grantBlockFrozenColdWorkerProjection ring x.val root S hfields
  change Counter.resetColdModeCredit n
      (compileAdvice q).bankLeaseCap
      (x.val root).mode (x.val root).lease.val +
      n * Counter.resetColdWorkerCount ring x.val root =
    Counter.resetColdModeCredit n (compileAdvice q).bankLeaseCap
      (S.fields (0 : Fin ((compileAdvice q).b + 1))).1
      (S.fields (0 : Fin ((compileAdvice q).b + 1))).2.2.2 +
      n * grantBlockFrozenColdLocalWorkers q S
  rw [hmode, hlease, hworkers]

/-- A zero-time RESET handoff has exactly zero physical C.3
credit, equal to the local stopped classification. -/
theorem grantBlockFrozenColdRecoveryStartCredit
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (x : Counter.ResetClockBankColdCarrier (q := q) ring root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hfields : GrantBankReference.bankLocalReferenceFieldsAgree
      ring x.val root S)
    (hfalse : S.success = false)
    (hreset :
      (S.fields (0 : Fin ((compileAdvice q).b + 1))).1 =
        .RESET) :
    Counter.resetColdUncappedCredit ring root
      (Counter.resetClockBankColdStart ring root x) =
      grantBlockFrozenColdLocalStoppedCredit n q S := by
  have hmode :=
    congrArg (fun p : Mode × Bool × BTok × Nat => p.1)
      (hfields 0 (by omega))
  have hphysicalReset : (x.val root).mode = .RESET :=
    hmode.trans hreset
  have hphysical :
      Counter.resetColdUncappedCredit ring root
        (Counter.resetClockBankColdStart ring root x) = 0 := by
    change Counter.resetColdUncappedCredit ring root
      (Counter.resetClockBankColdLift ring root
        x.val x.property.1 x.property.2) = 0
    rw [Counter.resetClockBankColdLiftReset
      ring root x.val x.property.1 x.property.2 hphysicalReset]
    rfl
  have hlocal :
      grantBlockFrozenColdLocalStoppedCredit n q S = 0 := by
    simp [grantBlockFrozenColdLocalStoppedCredit, hfalse, hreset]
  rw [hphysical, hlocal]

/-- For a non-RESET unlatched cold carrier the zero-time physical
credit equals the active local reference credit. -/
theorem grantBlockFrozenColdActiveStartCredit
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (x : Counter.ResetClockBankColdCarrier (q := q) ring root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hfields : GrantBankReference.bankLocalReferenceFieldsAgree
      ring x.val root S)
    (hfalse : S.success = false)
    (hactive :
      (S.fields (0 : Fin ((compileAdvice q).b + 1))).1 ≠
        .RESET) :
    Counter.resetColdUncappedCredit ring root
      (Counter.resetClockBankColdStart ring root x) =
      grantBlockFrozenColdLocalStoppedCredit n q S := by
  have hmode :=
    congrArg (fun p : Mode × Bool × BTok × Nat => p.1)
      (hfields 0 (by omega))
  have hphysicalActive : (x.val root).mode ≠ .RESET := by
    intro hr
    exact hactive (hmode.symm.trans hr)
  have hstart :
      Counter.resetClockBankColdStart ring root x = .inl x := by
    unfold Counter.resetClockBankColdStart
      Counter.resetClockBankColdLift
    simp only [dif_neg hphysicalActive]
  rw [hstart]
  rw [grantBlockFrozenColdActiveCreditProjection
    ring root x S hfields]
  simp [grantBlockFrozenColdLocalStoppedCredit, hfalse, hactive]

/-- Physical terminal states and the latched local success
have identical zero C.3 credit (credit level only; the event
correspondence of latches and physical terminals is a separate
step). -/
theorem grantBlockFrozenColdTerminalSuccessCredit
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (z : Counter.ResetClockBankRenewalState (q := q) ring root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hwin : S.success = true) :
    Counter.resetColdUncappedCredit ring root (.inr z) =
      grantBlockFrozenColdLocalStoppedCredit n q S := by
  simp [Counter.resetColdUncappedCredit,
    grantBlockFrozenColdLocalStoppedCredit, hwin]

/-- One safe nonterminal service: the real physical successor
has exactly the stopped local credit of the frozen field successor.
The no-new-grant and no-local-success hypotheses name real rows. -/
theorem grantBlockFrozenColdOneServiceActiveCredit
    {n q : Nat} (ring : DirectedRing n) (root edge : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier (q := q) ring root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hfields : GrantBankReference.bankLocalReferenceFieldsAgree
      ring x.val root S)
    (hfalse : S.success = false)
    (hno : ¬ Counter.ResetClockBankDefectEntry
      ring x.val root edge)
    (hgrant : Counter.GrantFree
      ((protocol q).step ring x.val edge) root)
    (hmode : (((protocol q).step ring x.val edge) root).mode ≠
      .RESET)
    (hnewFalse :
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root S edge).success = false) :
    Counter.resetColdUncappedCredit ring root
      (Counter.resetClockBankColdNext ring root hsp (.inl x) edge) =
      grantBlockFrozenColdLocalStoppedCredit n q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root S edge) := by
  have hproject :=
    GrantBankReference.bankLocalReferenceSupportStep
      ring x.val root edge S hsp x.property.1 x.property.2
      hfields hfalse hno
  have hlocalMode :=
    congrArg (fun p : Mode × Bool × BTok × Nat => p.1)
      (hproject.1 0 (by omega))
  have hlocalActive :
      ((GrantBankReference.bankLocalReferenceStepClamped
          ring root S edge).fields
          (0 : Fin ((compileAdvice q).b + 1))).1 ≠ .RESET := by
    intro hr
    exact hmode (hlocalMode.trans hr)
  rw [Counter.resetClockBankColdNextContinue
    ring root hsp x edge hno hgrant]
  simp only [Counter.resetClockBankColdLift, dif_neg hmode]
  have hnewFields := hproject.1
  rw [grantBlockFrozenColdActiveCreditProjection
    ring root
    (⟨(protocol q).step ring x.val edge,
      ⟨Counter.resetClockBankColdCompleteStep
        ring root x edge hno, hgrant⟩⟩ :
      Counter.ResetClockBankColdCarrier (q := q) ring root)
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root S edge) hnewFields]
  simp [grantBlockFrozenColdLocalStoppedCredit,
    hnewFalse, hlocalActive]

/-- A nondefective service entering RESET is exactly a physical
zero-credit handoff, independently of its new grant classification. -/
theorem grantBlockFrozenColdOneServiceResetCredit
    {n q : Nat} (ring : DirectedRing n) (root edge : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier (q := q) ring root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hfields : GrantBankReference.bankLocalReferenceFieldsAgree
      ring x.val root S)
    (hfalse : S.success = false)
    (hno : ¬ Counter.ResetClockBankDefectEntry
      ring x.val root edge)
    (hreset : (((protocol q).step ring x.val edge) root).mode =
      .RESET) :
    Counter.resetColdUncappedCredit ring root
      (Counter.resetClockBankColdNext ring root hsp (.inl x) edge) =
      grantBlockFrozenColdLocalStoppedCredit n q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root S edge) := by
  have hproject :=
    GrantBankReference.bankLocalReferenceSupportStep
      ring x.val root edge S hsp x.property.1 x.property.2
      hfields hfalse hno
  have hlocalMode :=
    congrArg (fun p : Mode × Bool × BTok × Nat => p.1)
      (hproject.1 0 (by omega))
  have hlocalReset :
      ((GrantBankReference.bankLocalReferenceStepClamped
          ring root S edge).fields
          (0 : Fin ((compileAdvice q).b + 1))).1 = .RESET :=
    hlocalMode.symm.trans hreset
  have hphysical := Counter.resetColdNextResetCreditZero
    ring root hsp x edge hreset
  have hlocal :
      grantBlockFrozenColdLocalStoppedCredit n q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root S edge) = 0 := by
    by_cases hwin :
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root S edge).success = true
    · simp [grantBlockFrozenColdLocalStoppedCredit, hwin]
    · have hnewFalse :
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root S edge).success = false := by
        cases hb : (GrantBankReference.bankLocalReferenceStepClamped
          ring root S edge).success with
        | false => rfl
        | true => exact False.elim (hwin hb)
      simp [grantBlockFrozenColdLocalStoppedCredit,
        hnewFalse, hlocalReset]
  rw [hphysical, hlocal]

/-- On an actual grant stop matching a successful local latch,
both classifications are terminal and have zero first-stage credit. -/
theorem grantBlockFrozenColdOneServiceGrantSuccess
    {n q : Nat} (ring : DirectedRing n) (root edge : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier (q := q) ring root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hno : ¬ Counter.ResetClockBankDefectEntry
      ring x.val root edge)
    (hgrant : ¬ Counter.GrantFree
      ((protocol q).step ring x.val edge) root)
    (hwin :
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root S edge).success = true) :
    Counter.resetColdUncappedCredit ring root
        (Counter.resetClockBankColdNext ring root hsp (.inl x) edge) =
      grantBlockFrozenColdLocalStoppedCredit n q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root S edge) ∧
    Counter.resetClockBankColdTerminal ring root
      (Counter.resetClockBankColdNext ring root hsp (.inl x) edge) := by
  constructor
  · rw [Counter.resetClockBankColdNextGrant
      ring root hsp x edge hno hgrant]
    simp [Counter.resetColdUncappedCredit,
      grantBlockFrozenColdLocalStoppedCredit, hwin]
  · exact Counter.resetClockBankColdNextGrantStop
      ring root hsp x edge hno hgrant

/-- C.3 local Bellman inequality from the real all-edges theorem,
provided the three genuine service-row cases cover every edge.
This is conditional, not the missing unconditional G13 marginal. -/
theorem grantBlockFrozenColdLocalBellmanOfCoveredRows
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (x : Counter.ResetClockBankColdCarrier (q := q) ring root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hfields : GrantBankReference.bankLocalReferenceFieldsAgree
      ring x.val root S)
    (hfalse : S.success = false)
    (hmode : (x.val root).mode ≠ .RESET)
    (hno : ∀ edge : Fin n,
      ¬ Counter.ResetClockBankDefectEntry ring x.val root edge)
    (hrows : ∀ edge : Fin n,
      (((protocol q).step ring x.val edge) root).mode = .RESET ∨
      (Counter.GrantFree
         ((protocol q).step ring x.val edge) root ∧
       (((protocol q).step ring x.val edge) root).mode ≠ .RESET ∧
       (GrantBankReference.bankLocalReferenceStepClamped
         ring root S edge).success = false) ∨
      (¬ Counter.GrantFree
         ((protocol q).step ring x.val edge) root ∧
       (GrantBankReference.bankLocalReferenceStepClamped
         ring root S edge).success = true)) :
    n +
      (List.ofFn (fun edge : Fin n =>
        grantBlockFrozenColdLocalStoppedCredit n q
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root S edge))).sum ≤
    n * grantBlockFrozenColdLocalActiveCredit n q S := by
  have hp := Counter.resetColdPhysicalBellmanAllEdges
    ring root hsp hlarge x hmode
  have hcurrent := grantBlockFrozenColdActiveCreditProjection
    ring root x S hfields
  have heq (edge : Fin n) :
      Counter.resetColdUncappedCredit ring root
        (Counter.resetClockBankColdNext ring root hsp
          (.inl x) edge) =
      grantBlockFrozenColdLocalStoppedCredit n q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root S edge) := by
    rcases hrows edge with hr | ha | hs
    · exact grantBlockFrozenColdOneServiceResetCredit
        ring root edge hsp x S hfields hfalse (hno edge) hr
    · exact grantBlockFrozenColdOneServiceActiveCredit
        ring root edge hsp x S hfields hfalse (hno edge)
        ha.1 ha.2.1 ha.2.2
    · exact (grantBlockFrozenColdOneServiceGrantSuccess
        ring root edge hsp x S (hno edge) hs.1 hs.2).1
  have hsum :
      (List.ofFn (fun edge : Fin n =>
        Counter.resetColdUncappedCredit ring root
          (Counter.resetClockBankColdNext ring root hsp
            (.inl x) edge))).sum =
      (List.ofFn (fun edge : Fin n =>
        grantBlockFrozenColdLocalStoppedCredit n q
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root S edge))).sum := by
    exact congrArg List.sum (congrArg List.ofFn (funext heq))
  rw [hsum, hcurrent] at hp
  exact hp

end L3

#print axioms L3.grantBlockFrozenColdRecoveryRootLaunch
#print axioms L3.grantBlockFrozenColdRecoveryNonroot
#print axioms L3.grantBlockFrozenColdWorkerProjection
#print axioms L3.grantBlockFrozenColdActiveCreditProjection
#print axioms L3.grantBlockFrozenColdRecoveryStartCredit
#print axioms L3.grantBlockFrozenColdActiveStartCredit
#print axioms L3.grantBlockFrozenColdTerminalSuccessCredit
#print axioms L3.grantBlockFrozenColdOneServiceActiveCredit
#print axioms L3.grantBlockFrozenColdOneServiceResetCredit
#print axioms L3.grantBlockFrozenColdOneServiceGrantSuccess
#print axioms L3.grantBlockFrozenColdLocalBellmanOfCoveredRows
