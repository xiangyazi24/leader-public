import Leader.L3.Grant.BankReference
import Leader.L3.Bank.CounterCold

/-!
Local, fixed-role BANK trial observer.

Observer for the C.4--C.8 regenerative trial.
It makes no change to the physical protocol.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- A zero, empty, ARMED local BANK cut with a representable lease
at every protected slot. The fixed roles are supplied by the
BankLocalReference reconstruction, not by an Agent field. -/
def BankTrialLocalClean (q : Nat)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Prop :=
  S.success = false ∧
  (S.fields ⟨0, by omega⟩).1 = .ARMED ∧
  (∀ j : Nat, 1 ≤ j → (hjb : j ≤ (compileAdvice q).b) →
    (S.fields ⟨j, Nat.lt_succ_of_le hjb⟩).2.1 = false ∧
    (S.fields ⟨j, Nat.lt_succ_of_le hjb⟩).2.2.1 = .E) ∧
  (∀ j : Nat, (hj : j ≤ (compileAdvice q).b) →
    (S.fields ⟨j, Nat.lt_succ_of_le hj⟩).2.2.2 ≤
      (compileAdvice q).bankLeaseCap)

/-- The live Boolean records whether a root-incident orientation
has already occurred. Recovery counts toward the losing trial. -/
inductive BankTrialLocalPhase where
  | live : Bool → BankTrialLocalPhase
  | recovery | won | lost
  deriving DecidableEq

structure BankTrialLocalState (q : Nat) where
  bank : GrantBankReference.BankLocalReference (compileAdvice q).b
  phase : BankTrialLocalPhase

def bankTrialLocalStart {q : Nat}
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : BankTrialLocalState q :=
  ⟨S, .live false⟩

def bankTrialLocalTerminal {q : Nat}
    (z : BankTrialLocalState q) : Prop :=
  z.phase = .won ∨ z.phase = .lost

/-- A trial uses the original Fin n edge alphabet. The reference
uses the clamped BANK row, including both boundary orientations.
The OLD-state success latch is examined before Clean/recovery. -/
noncomputable def bankTrialLocalNext {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    BankTrialLocalState q → Fin n → BankTrialLocalState q := by
  classical
  intro z e
  exact
    (fun (S' : GrantBankReference.BankLocalReference
        (compileAdvice q).b) =>
      match z.phase with
      | .won => z
      | .lost => z
      | .recovery =>
          if S'.success = true then ⟨S', .won⟩
          else if BankTrialLocalClean q S' then ⟨S', .lost⟩
          else ⟨S', .recovery⟩
      | .live begun =>
          if S'.success = true then ⟨S', .won⟩
          else if BankTrialLocalClean q S' ∧
              (begun = true ∨ e = root ∨
                ring.rightNeighbor e = root) then
            ⟨S', .lost⟩
          else if (S'.fields ⟨0, by omega⟩).1 = .RESET then
            ⟨S', .recovery⟩
          else
            ⟨S', .live (begun ||
              decide (e = root ∨ ring.rightNeighbor e = root))⟩)
      (GrantBankReference.bankLocalReferenceStepClamped
        (q := q) ring root z.bank e)

/-- Evolve the same observer on the same physical scheduler word. -/
noncomputable def bankTrialLocalRun {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    List (Fin n) → BankTrialLocalState q → BankTrialLocalState q
  | [], z => z
  | e :: w, z =>
      bankTrialLocalRun ring root w
        (bankTrialLocalNext ring root z e)

/-- Both outcomes are fully absorbing, including the BANK fields. -/
theorem bankTrialLocalTerminalAbsorbs {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialLocalState q)
    (hz : bankTrialLocalTerminal z) :
    bankTrialLocalNext ring root z e = z := by
  cases z with
  | mk bank phase =>
    cases phase with
    | live begun =>
        rcases hz with h | h
        · cases h
        · cases h
    | recovery =>
        rcases hz with h | h
        · cases h
        · cases h
    | won => rfl
    | lost => rfl

/-- The original-clock run respects concatenation of edge words. -/
theorem bankTrialLocalRunAppend {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (u v : List (Fin n)) (z : BankTrialLocalState q),
      bankTrialLocalRun ring root (u ++ v) z =
        bankTrialLocalRun ring root v
          (bankTrialLocalRun ring root u z) := by
  intro u
  induction u with
  | nil =>
      intro v z
      rfl
  | cons e es ih =>
      intro v z
      change bankTrialLocalRun ring root (es ++ v)
          (bankTrialLocalNext ring root z e) =
        bankTrialLocalRun ring root v
          (bankTrialLocalRun ring root es
            (bankTrialLocalNext ring root z e))
      exact ih v _

/-- No later edge word can alter a terminal state. -/
theorem bankTrialLocalRunTerminalAbsorbs {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (w : List (Fin n)) (z : BankTrialLocalState q),
      bankTrialLocalTerminal z →
        bankTrialLocalRun ring root w z = z := by
  intro w
  induction w with
  | nil =>
      intro z hz
      rfl
  | cons e es ih =>
      intro z hz
      change bankTrialLocalRun ring root es
        (bankTrialLocalNext ring root z e) = z
      rw [bankTrialLocalTerminalAbsorbs ring root e z hz]
      exact ih z hz

/-- In particular terminality persists under an arbitrary word. -/
theorem bankTrialLocalRunTerminal {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (w : List (Fin n)) (z : BankTrialLocalState q)
    (hz : bankTrialLocalTerminal z) :
    bankTrialLocalTerminal
      (bankTrialLocalRun ring root w z) := by
  rw [bankTrialLocalRunTerminalAbsorbs ring root w z hz]
  exact hz

/-- An authenticated physical Clean/GrantFree cut projects to
the clean, role-frozen BANK reference. GrantFree is recorded in the
interface; the start reference itself already forces success=false. -/
theorem bankTrialLocalCleanSeed {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hc : Counter.ResetClockBankClean ring C root)
    (hg : Counter.GrantFree C root) :
    BankTrialLocalClean q
      (GrantBankReference.bankLocalReferenceStart ring root C) := by
  unfold BankTrialLocalClean
  refine ⟨rfl, ?_, ?_, ?_⟩
  · change (C root).mode = .ARMED
    exact hc.2.1
  · intro j hj hbound
    change (C (Counter.site ring root j)).bit = false ∧
      (C (Counter.site ring root j)).tok = .E
    exact hc.2.2 j hj hbound
  · intro j hj
    change (C (Counter.site ring root j)).lease.val ≤
      (compileAdvice q).bankLeaseCap
    have hlt :
        (C (Counter.site ring root j)).lease.val <
          (compileAdvice q).bankLeaseCap + 1 :=
      (C (Counter.site ring root j)).lease.isLt
    omega

end L3

/-!
Local BANK row and observer obligations.

The exact, all-word RecoveryNoWin target is NOT asserted in this
section. The existing recovery observer already retains an
exceptional OLD success, with higher priority than a Clean/loss
classification; the local source-row claims below reduce the
remaining reachability question to a root CWAIT/CL1 guard.
-/

namespace L3

/-- One-step physical/frozen agreement on all protected BANK fields.
This is the field component of the existing
bankLocalReferenceSupportStep, without any assertion of whole-Agent
equality. -/
theorem bankTrialLocalPhysicalPrefix {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (C : Counter.Config q n)
    (hc : Counter.Complete ring C root)
    (hg : Counter.GrantFree C root)
    (e : Fin n)
    (hno : ¬ Counter.ResetClockBankDefectEntry
      ring C root e)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hagree :
      GrantBankReference.bankLocalReferenceFieldsAgree
        ring C root S)
    (hs : S.success = false) :
    GrantBankReference.bankLocalReferenceFieldsAgree
      ring ((protocol q).step ring C e) root
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root S e) := by
  exact (GrantBankReference.bankLocalReferenceSupportStep
    ring C root e S hsp hc hg hagree hs hno).1

/-- A live-to-lost step has an actual postservice Clean snapshot,
no OLD success latch, and either a previously begun trial or
a root-incident scheduler orientation. This is an exact observer
guard statement; it makes no unsupported reset-authentication
claim about an arbitrary predecessor BANK state. -/
theorem bankTrialLocalLiveLossWitness {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (begun : Bool)
    (hlost :
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) e).phase =
          .lost) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).success = false ∧
    BankTrialLocalClean q
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) ∧
    (begun = true ∨ e = root ∨
      ring.rightNeighbor e = root) := by
  classical
  by_cases hwin :
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).success = true
  · simp [bankTrialLocalNext, hwin] at hlost
  · have hfalse :
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e).success = false := by
      cases hv :
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B e).success with
      | false => rfl
      | true => exact False.elim (hwin hv)
    by_cases hguard :
        BankTrialLocalClean q
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B e) ∧
        (begun = true ∨ e = root ∨
          ring.rightNeighbor e = root)
    · exact ⟨hfalse, hguard.1, hguard.2⟩
    · simp [bankTrialLocalNext, hwin, hguard] at hlost
      split at hlost <;> simp at hlost

/-- Before the first root-incident service, a non-incident letter
cannot create a loss solely because the local fields still satisfy
Clean. This holds for any BANK fields, without a history premise. -/
theorem bankTrialLocalIdleNonincidentNotLost {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hout : e ≠ root)
    (hin : ring.rightNeighbor e ≠ root) :
    (bankTrialLocalNext ring root
      (⟨B, .live false⟩ : BankTrialLocalState q) e).phase ≠
        .lost := by
  intro hlost
  have hguard := (bankTrialLocalLiveLossWitness
    ring root e B false hlost).2.2
  rcases hguard with hbegun | he | hp
  · cases hbegun
  · exact hout he
  · exact hin hp

/-- An unlatched reference can register OLD success only on the
outgoing root orientation. Incoming and interior services cannot
turn the success latch on, even if they mutate the BANK fields. -/
theorem bankTrialLocalUnlatchedNonrootNoWin {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hfalse : B.success = false)
    (hne : e ≠ root) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).success = false := by
  classical
  have hev :
      GrantBankReference.bankLocalReferenceSuccessEvent
        ring root B e = false := by
    simp [GrantBankReference.bankLocalReferenceSuccessEvent, hne]
  by_cases hs : Counter.Support q ring root e
  · simp [GrantBankReference.bankLocalReferenceStepClamped,
      hs, hfalse, hev]
  · simp [GrantBankReference.bankLocalReferenceStepClamped,
      hs, hfalse]

/-- The OLD root mode must be CWAIT for a new root-nominated
success. This is the local (not physical) version of the mode
barrier; it does not assume that recovery is always in this band. -/
theorem bankTrialLocalUnlatchedNonCWaitNoWin {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hfalse : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 ≠ .CWAIT) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).success = false := by
  classical
  have hev :
      GrantBankReference.bankLocalReferenceSuccessEvent
        ring root B e = false := by
    by_cases he : e = root
    · subst e
      simp [GrantBankReference.bankLocalReferenceSuccessEvent,
        GrantBankReference.bankLocalReferenceCell, bankSuccess]
      intro hz hcw _
      rw [hz] at hcw
      have h0 : (0 : Fin ((compileAdvice q).b + 1)) =
          ⟨0, by omega⟩ := Fin.ext (by simp)
      rw [h0] at hcw
      exact absurd hcw hm
    · simp [GrantBankReference.bankLocalReferenceSuccessEvent, he]
  by_cases hs : Counter.Support q ring root e
  · simp [GrantBankReference.bankLocalReferenceStepClamped,
      hs, hfalse, hev]
  · simp [GrantBankReference.bankLocalReferenceStepClamped,
      hs, hfalse]

/-- Recovery already implements the safe precedence demanded by
the design audit: an exceptional OLD success becomes WON before
any Clean/loss classification. In particular it cannot be silently
reclassified as a failed regenerative trial. -/
theorem bankTrialLocalRecoverySuccessPriority {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsuccess :
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).success = true) :
    bankTrialLocalNext ring root
      (⟨B, .recovery⟩ : BankTrialLocalState q) e =
        ⟨GrantBankReference.bankLocalReferenceStepClamped
          ring root B e, .won⟩ := by
  classical
  simp [bankTrialLocalNext, hsuccess]

end L3

/-!
The first recovery entry, its one-step
no-success barrier, and an exact specification of the remaining
authenticated-reset producer obligation.

The mode-only band below is NOT a complete reset-front certificate.
A RWAIT state with a forged RL at digit one and dirty later digits
can return to a non-Clean ARMED state. Reachability of such a state
from a genuine Clean seed is not asserted.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- Minimal mode consequence of an authenticated local reset front:
the success latch is false, and the root is in RESET or RWAIT.
This is weaker than the full RR/RL front authentication required
to prove preservation over arbitrary recovery words. -/
def BankTrialLocalRecoveryModeBand (q : Nat)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Prop :=
  B.success = false ∧
    ((B.fields ⟨0, by omega⟩).1 = .RESET ∨
      (B.fields ⟨0, by omega⟩).1 = .RWAIT)

/-- At the first entry from LIVE into RECOVERY the clamped root
is literally RESET; the success latch was not set on that service.
No history or source-row assumption is required for this statement. -/
theorem bankTrialLocalLiveEntersRecoveryReset {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (begun : Bool)
    (hphase :
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) e).phase =
          .recovery) :
    BankTrialLocalRecoveryModeBand q
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) e).bank := by
  classical
  by_cases hwin :
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).success = true
  · simp [bankTrialLocalNext, hwin] at hphase
  · by_cases hclean :
        BankTrialLocalClean q
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B e) ∧
        (begun = true ∨ e = root ∨
          ring.rightNeighbor e = root)
    · simp [bankTrialLocalNext, hwin, hclean] at hphase
    · have h0 : (0 : Fin ((compileAdvice q).b + 1)) =
          ⟨0, by omega⟩ := Fin.ext (by simp)
      by_cases hreset :
          ((GrantBankReference.bankLocalReferenceStepClamped
            ring root B e).fields 0).1 = .RESET
      · have hfalse :
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root B e).success = false := by
          cases hv :
              (GrantBankReference.bankLocalReferenceStepClamped
                ring root B e).success with
          | false => rfl
          | true => exact False.elim (hwin hv)
        have hnext :
            bankTrialLocalNext ring root
              (⟨B, .live begun⟩ : BankTrialLocalState q) e =
              ⟨GrantBankReference.bankLocalReferenceStepClamped
                ring root B e, .recovery⟩ := by
          simp [bankTrialLocalNext, hwin, hclean, hreset]
        rw [hnext]
        refine ⟨hfalse, Or.inl ?_⟩
        rw [← h0]
        exact hreset
      · simp [bankTrialLocalNext, hwin, hclean, hreset] at hphase

/-- A local RESET/RWAIT-band snapshot cannot generate an OLD
BANK success at any edge: this is the CWAIT-only root guard. -/
theorem bankTrialLocalRecoveryModeBandNoWin {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hband : BankTrialLocalRecoveryModeBand q B) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).success = false := by
  apply bankTrialLocalUnlatchedNonCWaitNoWin
    ring root e B hband.1
  intro hm
  rcases hband.2 with hreset | hrwait
  · rw [hreset] at hm
    cases hm
  · rw [hrwait] at hm
    cases hm

/-- The first recovery snapshot is safe for one further service,
even if the live cut before it had arbitrary BANK scratch. -/
theorem bankTrialLocalFirstRecoveryNoWin {n q : Nat}
    (ring : DirectedRing n) (root e nextEdge : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (begun : Bool)
    (hphase :
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) e).phase =
          .recovery) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) e).bank
      nextEdge).success = false := by
  exact bankTrialLocalRecoveryModeBandNoWin ring root nextEdge
    (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) e).bank
    (bankTrialLocalLiveEntersRecoveryReset ring root e B begun hphase)

/-- Exact fallback when a recovery state is not known to have
a genuine reset-front certificate: either the next OLD-success
latch is false or the observer records WON, not LOST. -/
theorem bankTrialLocalRecoveryNextNoWinOrWon {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).success = false ∨
    (bankTrialLocalNext ring root
      (⟨B, .recovery⟩ : BankTrialLocalState q) e).phase =
        .won := by
  cases hsuccess :
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).success with
  | false =>
      exact Or.inl rfl
  | true =>
      exact Or.inr
        (congrArg BankTrialLocalState.phase
          (bankTrialLocalRecoverySuccessPriority
            ring root e B hsuccess))

/-- The exact missing *reachable* consequence of the C.2 local
RR/RL authentication invariant. This is a proof obligation (Prop),
not a theorem and not an axiom. Mode-only safety is insufficient
to prove this by arbitrary-state induction. -/
def BankTrialLocalRecoveryBandReachable {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b),
    BankTrialLocalClean q S →
      ∀ (w : List (Fin n))
      (B : GrantBankReference.BankLocalReference
        (compileAdvice q).b),
      bankTrialLocalRun ring root w (bankTrialLocalStart S) =
        ⟨B, .recovery⟩ →
      BankTrialLocalRecoveryModeBand q B

/-- If the authentic local reset-front invariant produces the
reachable mode band, then the originally requested all-word
RecoveryNoWin statement follows from the CWAIT guard.
This theorem does NOT discharge the reachable-band premise. -/
theorem bankTrialLocalRecoveryNoWinOfBandReachable {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hband : BankTrialLocalRecoveryBandReachable
      (q := q) ring root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (w : List (Fin n))
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hrun : bankTrialLocalRun ring root w
      (bankTrialLocalStart S) = ⟨B, .recovery⟩)
    (e : Fin n) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).success = false := by
  exact bankTrialLocalRecoveryModeBandNoWin ring root e B
    (hband S hclean w B hrun)

end L3

/-!
State-only reset-front certificates and their entry producer.

The completed RESET and outside-support cases below do not assert the
remaining RWAIT digit-array preservation theorem.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- F_j. The suffix strictly beyond j is unrestricted. -/
def BankTrialLocalFrontOut (q : Nat)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (j : Nat) : Prop :=
  ∃ hjb : j ≤ (compileAdvice q).b,
    1 ≤ j ∧
    (B.fields ⟨j, Nat.lt_succ_of_le hjb⟩).2.1 = false ∧
    (B.fields ⟨j, Nat.lt_succ_of_le hjb⟩).2.2.1 = .RR ∧
    (∀ i : Nat, 1 ≤ i → i < j →
      (hib : i ≤ (compileAdvice q).b) →
      (B.fields ⟨i, Nat.lt_succ_of_le hib⟩).2.1 = false ∧
      (B.fields ⟨i, Nat.lt_succ_of_le hib⟩).2.2.1 = .E)

/-- G_j, allowing j=b as permitted in the paper proof.
All digits other than the single return location are zero/empty. -/
def BankTrialLocalFrontBack (q : Nat)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (j : Nat) : Prop :=
  ∃ hjb : j ≤ (compileAdvice q).b,
    1 ≤ j ∧
    (B.fields ⟨j, Nat.lt_succ_of_le hjb⟩).2.1 = false ∧
    (B.fields ⟨j, Nat.lt_succ_of_le hjb⟩).2.2.1 = .RL ∧
    (∀ i : Nat, 1 ≤ i →
      (hib : i ≤ (compileAdvice q).b) → i ≠ j →
      (B.fields ⟨i, Nat.lt_succ_of_le hib⟩).2.1 = false ∧
      (B.fields ⟨i, Nat.lt_succ_of_le hib⟩).2.2.1 = .E)

/-- Representable leases at every protected slot, including zero. -/
def BankTrialLocalLeaseCap (q : Nat)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Prop :=
  ∀ j : Nat, (hjb : j ≤ (compileAdvice q).b) →
    (B.fields ⟨j, Nat.lt_succ_of_le hjb⟩).2.2.2 ≤
      (compileAdvice q).bankLeaseCap

/-- RecoveryCert. RESET imposes no condition on digit scratch.
RWAIT carries a positive lease and an outward or return certificate. -/
def BankTrialLocalRecoveryCert (q : Nat)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Prop :=
  BankTrialLocalLeaseCap q B ∧
  B.success = false ∧
  ((B.fields ⟨0, by omega⟩).1 = .RESET ∨
    ((B.fields ⟨0, by omega⟩).1 = .RWAIT ∧
      1 ≤ (B.fields ⟨0, by omega⟩).2.2.2 ∧
      (B.fields ⟨0, by omega⟩).2.2.2 ≤
        (compileAdvice q).bankLeaseCap ∧
      ((∃ j : Nat, BankTrialLocalFrontOut q B j) ∨
        (∃ j : Nat, BankTrialLocalFrontBack q B j))))

/-- The Clean definition already contains the entire cap premise. -/
theorem bankTrialLocalCleanLeaseCap {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLocalClean q B) :
    BankTrialLocalLeaseCap q B := by
  exact hc.2.2.2

/-- Every selected field is a clamped output or an old framed field. -/
theorem bankTrialLocalFieldLeaseCap {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLocalLeaseCap q B)
    (i : Fin ((compileAdvice q).b + 1)) :
    (GrantBankReference.bankLocalReferenceFieldStepClamped
      ring root e B i).2.2.2 ≤ (compileAdvice q).bankLeaseCap := by
  classical
  unfold GrantBankReference.bankLocalReferenceFieldStepClamped
  split
  · exact Nat.le_of_lt_succ
      (GrantBankReference.bankLocalReferenceClampedQuadLeaseBound q _)
  · split
    · exact Nat.le_of_lt_succ
        (GrantBankReference.bankLocalReferenceClampedQuadLeaseBound q _)
    · split
      · exact Nat.le_of_lt_succ
          (GrantBankReference.bankLocalReferenceClampedQuadLeaseBound q _)
      · split
        · exact Nat.le_of_lt_succ
            (GrantBankReference.bankLocalReferenceClampedQuadLeaseBound q _)
        · exact hc i.val (Nat.le_of_lt_succ i.isLt)

/-- Cap preservation includes supported letters, unsupported letters,
and the absorbing-success branch. -/
theorem bankTrialLocalLeaseCapStep {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLocalLeaseCap q B) :
    BankTrialLocalLeaseCap q
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) := by
  classical
  unfold GrantBankReference.bankLocalReferenceStepClamped
  split
  · split
    · exact hc
    · intro j hjb
      exact bankTrialLocalFieldLeaseCap ring root e B hc
        ⟨j, Nat.lt_succ_of_le hjb⟩
  · exact hc

/-- LIVE always stores the clamped successor, independently of its
choice of next observer phase. -/
theorem bankTrialLocalNextLiveBank {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool) :
    (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) e).bank =
      GrantBankReference.bankLocalReferenceStepClamped
        ring root B e := by
  classical
  by_cases hwin :
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).success = true
  · simp [bankTrialLocalNext, hwin]
  · by_cases hclean :
        BankTrialLocalClean q
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B e) ∧
        (begun = true ∨ e = root ∨ ring.rightNeighbor e = root)
    · simp [bankTrialLocalNext, hwin, hclean]
    · by_cases hreset :
          ((GrantBankReference.bankLocalReferenceStepClamped
            ring root B e).fields
              (0 : Fin ((compileAdvice q).b + 1))).1 = .RESET
      · simp [bankTrialLocalNext, hwin, hclean, hreset]
      · simp [bankTrialLocalNext, hwin, hclean, hreset]
/-- RECOVERY also stores the clamped successor in all three cases. -/
theorem bankTrialLocalNextRecoveryBank {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    (bankTrialLocalNext ring root
      (⟨B, .recovery⟩ : BankTrialLocalState q) e).bank =
      GrantBankReference.bankLocalReferenceStepClamped
        ring root B e := by
  classical
  by_cases hwin :
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).success = true
  · simp [bankTrialLocalNext, hwin]
  · by_cases hclean :
        BankTrialLocalClean q
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B e)
    · simp [bankTrialLocalNext, hwin, hclean]
    · simp [bankTrialLocalNext, hwin, hclean]
/-- The terminal observer branches frame their banks; the other
branches use the clamped step. -/
theorem bankTrialLocalLeaseCapNext {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialLocalState q)
    (hc : BankTrialLocalLeaseCap q z.bank) :
    BankTrialLocalLeaseCap q
      (bankTrialLocalNext ring root z e).bank := by
  cases z with
  | mk B phase =>
    cases phase with
    | live begun =>
        rw [bankTrialLocalNextLiveBank]
        exact bankTrialLocalLeaseCapStep ring root e B hc
    | recovery =>
        rw [bankTrialLocalNextRecoveryBank]
        exact bankTrialLocalLeaseCapStep ring root e B hc
    | won => exact hc
    | lost => exact hc

/-- Lease representability persists along every actual observer word. -/
theorem bankTrialLocalLeaseCapRun {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (w : List (Fin n)) (z : BankTrialLocalState q),
      BankTrialLocalLeaseCap q z.bank →
      BankTrialLocalLeaseCap q
        (bankTrialLocalRun ring root w z).bank := by
  intro w
  induction w with
  | nil =>
      intro z hc
      exact hc
  | cons e es ih =>
      intro z hc
      change BankTrialLocalLeaseCap q
        (bankTrialLocalRun ring root es
          (bankTrialLocalNext ring root z e)).bank
      exact ih _ (bankTrialLocalLeaseCapNext ring root e z hc)

/-- Strengthen the entry guard to its literal RESET equality.
The existing theorem supplies the separate latch conclusion. -/
theorem bankTrialLocalLiveRecoveryRoot {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hphase :
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) e).phase =
          .recovery) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨0, by omega⟩).1 = .RESET := by
  classical
  by_cases hwin :
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).success = true
  · simp [bankTrialLocalNext, hwin] at hphase
  · by_cases hclean :
        BankTrialLocalClean q
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B e) ∧
        (begun = true ∨ e = root ∨ ring.rightNeighbor e = root)
    · simp [bankTrialLocalNext, hwin, hclean] at hphase
    · by_cases hreset :
          ((GrantBankReference.bankLocalReferenceStepClamped
            ring root B e).fields
              (0 : Fin ((compileAdvice q).b + 1))).1 = .RESET
      · have hzero : (0 : Fin ((compileAdvice q).b + 1)) =
            ⟨0, by omega⟩ := Fin.ext (by rfl)
        rw [hzero] at hreset
        exact hreset
      · simp [bankTrialLocalNext, hwin, hclean, hreset] at hphase
/-- Item (2): first LIVE-to-RECOVERY entry has the unrestricted
RESET certificate. No front hypothesis on the old bank is needed. -/
theorem bankTrialLocalLiveEntersRecoveryCert {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hc : BankTrialLocalLeaseCap q B)
    (hphase :
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) e).phase =
          .recovery) :
    BankTrialLocalRecoveryCert q
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) e).bank := by
  refine ⟨bankTrialLocalLeaseCapNext ring root e
      (⟨B, .live begun⟩ : BankTrialLocalState q) hc,
    (bankTrialLocalLiveEntersRecoveryReset
      ring root e B begun hphase).1, Or.inl ?_⟩
  rw [bankTrialLocalNextLiveBank]
  exact bankTrialLocalLiveRecoveryRoot ring root e B begun hphase

/-- The cap premise at an entry cut is produced from an arbitrary
Clean seed and its actual finite LIVE prefix. -/
theorem bankTrialLocalCleanRunRecoveryEntry {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (w : List (Fin n))
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hrun : bankTrialLocalRun ring root w (bankTrialLocalStart S) =
      ⟨B, .live begun⟩)
    (e : Fin n)
    (hphase :
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) e).phase =
          .recovery) :
    BankTrialLocalRecoveryCert q
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) e).bank := by
  have hcap := bankTrialLocalLeaseCapRun ring root w
    (bankTrialLocalStart S) (bankTrialLocalCleanLeaseCap S hclean)
  rw [hrun] at hcap
  exact bankTrialLocalLiveEntersRecoveryCert
    ring root e B begun hcap hphase

/-- Forget the front certificate, retaining exactly the band. -/
theorem bankTrialLocalRecoveryCertModeBand {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLocalRecoveryCert q B) :
    BankTrialLocalRecoveryModeBand q B := by
  refine ⟨hc.2.1, ?_⟩
  rcases hc.2.2 with hreset | hrwait
  · exact Or.inl hreset
  · exact Or.inr hrwait.1

/-- One certified recovery snapshot is success-free for one service.
This theorem alone does not establish reachable preservation. -/
theorem bankTrialLocalRecoveryCertNoWin {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLocalRecoveryCert q B) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).success = false := by
  exact bankTrialLocalRecoveryModeBandNoWin ring root e B
    (bankTrialLocalRecoveryCertModeBand B hc)

/-- Family G: the whole bank, not merely its certificate, is framed. -/
theorem bankTrialLocalStepOutside {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hout : ¬ Counter.Support q ring root e) :
    GrantBankReference.bankLocalReferenceStepClamped
      ring root B e = B := by
  classical
  simp [GrantBankReference.bankLocalReferenceStepClamped, hout]

/-- Family G lifted to the state-only recovery certificate. -/
theorem bankTrialLocalRecoveryCertOutside {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hout : ¬ Counter.Support q ring root e)
    (hc : BankTrialLocalRecoveryCert q B) :
    BankTrialLocalRecoveryCert q
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) := by
  rw [bankTrialLocalStepOutside ring root e B hout]
  exact hc

/-- Field equation before success at a supported service. -/
theorem bankTrialLocalStepField {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hs : Counter.Support q ring root e)
    (hf : B.success = false)
    (i : Fin ((compileAdvice q).b + 1)) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields i =
      GrantBankReference.bankLocalReferenceFieldStepClamped
        ring root e B i := by
  classical
  simp [GrantBankReference.bankLocalReferenceStepClamped, hs, hf]

private theorem bankTrialLocalWidthLarge (q : Nat) :
    1 < (compileAdvice q).b := by
  change 1 < (compileAdvice q).s + 11
  omega

/-- Only the lease coordinate is clamped; in-range leases are exact. -/
theorem bankTrialLocalClampedLease (q : Nat) (z : BankCell)
    (hc : z.lease ≤ (compileAdvice q).bankLeaseCap) :
    (GrantBankReference.bankLocalReferenceClampedQuad q z).2.2.2 =
      z.lease := by
  have hlt : z.lease < (compileAdvice q).bankLeaseCap + 1 := by
    omega
  simp [GrantBankReference.bankLocalReferenceClampedQuad,
    GrantBankReference.bankAgentLeaseQuad, copyBank, hlt]

/-- No adjacent logical edges share a scheduler letter when n>=2. -/
private theorem bankTrialLocalNeighborNe {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n) (i : Fin n) :
    ring.rightNeighbor i ≠ i := by
  intro he
  have hv := congrArg Fin.val he
  change (i.val + 1) % n = i.val at hv
  have hi := i.isLt
  by_cases hlt : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : i.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega

/-- The root always takes the internal-source projection on e_0. -/
theorem bankTrialLocalFieldRootOutgoing {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    GrantBankReference.bankLocalReferenceFieldStepClamped
      ring root root B ⟨0, by omega⟩ =
      GrantBankReference.bankLocalReferenceClampedQuad q
        ((GrantBankReference.bankLocalReferenceInternalPair q B
          ⟨0, by change 0 < (compileAdvice q).s + 11; omega⟩).1) := by
  classical
  have hb : 0 < (compileAdvice q).b := by
    have h := bankTrialLocalWidthLarge q
    omega
  simp [GrantBankReference.bankLocalReferenceFieldStepClamped,
    Counter.site, hb]

/-- At n>=2, digit one takes the matching responder projection.
Other nonadjacent logical edges may still fire simultaneously. -/
theorem bankTrialLocalFieldOneOutgoing {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) (hn : 2 ≤ n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    GrantBankReference.bankLocalReferenceFieldStepClamped
      ring root root B
        ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩ =
      GrantBankReference.bankLocalReferenceClampedQuad q
        ((GrantBankReference.bankLocalReferenceInternalPair q B
          ⟨0, by change 0 < (compileAdvice q).s + 11; omega⟩).2) := by
  classical
  have hne : root ≠ ring.rightNeighbor root :=
    Ne.symm (bankTrialLocalNeighborNe ring hn root)
  simp [GrantBankReference.bankLocalReferenceFieldStepClamped,
    Counter.site, hne]

/-- Family A endpoint calculation. RESET is tested before all
first-digit worker cases, so the old token is unrestricted. -/
theorem bankTrialLocalRawRootLaunch
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 ≤ b) (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false) (hm : x.mode = .RESET) :
    (bankPair x y 1 b theta).1.mode = .RWAIT ∧
    (bankPair x y 1 b theta).1.lease = 13 * (b + 2) ∧
    (bankPair x y 1 b theta).2.bit = false ∧
    (bankPair x y 1 b theta).2.tok = .RR := by
  exact Counter.resetClockBankRestartLaunchSymbolic
    x y b theta hx hy hg hm hb
/-- Family A, e_0: a genuine RESET launch produces F_1 regardless
of arbitrary abandoned workers and bits in the entire suffix. -/
theorem bankTrialLocalRecoveryCertLaunch {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) (hn : 2 ≤ n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLocalLeaseCap q B)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RESET) :
    BankTrialLocalRecoveryCert q
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B root) := by
  have hb : 1 ≤ (compileAdvice q).b :=
    Nat.le_of_lt (bankTrialLocalWidthLarge q)
  have hs : Counter.Support q ring root root :=
    Or.inr ⟨0, Nat.zero_le _, rfl⟩
  have hrow := bankTrialLocalRawRootLaunch
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B ⟨0, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩)
    hb rfl rfl rfl hm
  have hmode :
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B root).fields ⟨0, by omega⟩).1 = .RWAIT := by
    rw [bankTrialLocalStepField ring root root B hs hf,
      bankTrialLocalFieldRootOutgoing ring root B]
    change (GrantBankReference.bankLocalReferenceInternalPair q B
      ⟨0, by change 0 < (compileAdvice q).s + 11; omega⟩).1.mode = .RWAIT
    exact hrow.1
  have hrawLease :
      (GrantBankReference.bankLocalReferenceInternalPair q B
        ⟨0, by change 0 < (compileAdvice q).s + 11; omega⟩).1.lease =
        (compileAdvice q).bankLeaseCap := by
    exact hrow.2.1
  have hlease :
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B root).fields ⟨0, by omega⟩).2.2.2 =
        (compileAdvice q).bankLeaseCap := by
    rw [bankTrialLocalStepField ring root root B hs hf,
      bankTrialLocalFieldRootOutgoing ring root B]
    exact (bankTrialLocalClampedLease q
      ((GrantBankReference.bankLocalReferenceInternalPair q B
        ⟨0, by change 0 < (compileAdvice q).s + 11; omega⟩).1)
      (by omega)).trans hrawLease
  have hbit :
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B root).fields
        ⟨1, Nat.lt_succ_of_le hb⟩).2.1 = false := by
    rw [bankTrialLocalStepField ring root root B hs hf,
      bankTrialLocalFieldOneOutgoing ring root hn B]
    change (GrantBankReference.bankLocalReferenceInternalPair q B
      ⟨0, by change 0 < (compileAdvice q).s + 11; omega⟩).2.bit = false
    exact hrow.2.2.1
  have htok :
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B root).fields
        ⟨1, Nat.lt_succ_of_le hb⟩).2.2.1 = .RR := by
    rw [bankTrialLocalStepField ring root root B hs hf,
      bankTrialLocalFieldOneOutgoing ring root hn B]
    change (GrantBankReference.bankLocalReferenceInternalPair q B
      ⟨0, by change 0 < (compileAdvice q).s + 11; omega⟩).2.tok = .RR
    exact hrow.2.2.2
  have hout : BankTrialLocalFrontOut q
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B root) 1 := by
    refine ⟨hb, Nat.le_refl _, hbit, htok, ?_⟩
    intro i hi hij hib
    omega
  have hpos : 1 ≤ (compileAdvice q).bankLeaseCap := by
    change 1 ≤ 13 * ((compileAdvice q).b + 2)
    omega
  exact ⟨bankTrialLocalLeaseCapStep ring root root B hc,
    bankTrialLocalRecoveryModeBandNoWin ring root root B
      ⟨hf, Or.inl hm⟩,
    Or.inr ⟨hmode, (by omega), (by omega), Or.inl ⟨1, hout⟩⟩⟩

/-- Family A away from e_0. Any simultaneously selected digit rows
are harmless because the RESET disjunct constrains no digit fields. -/
theorem bankTrialLocalRecoveryCertResetOffEdge {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLocalLeaseCap q B)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RESET)
    (hne : e ≠ root) :
    BankTrialLocalRecoveryCert q
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) := by
  classical
  have hb := bankTrialLocalWidthLarge q
  have hlocal :
      (GrantBankReference.bankLocalReferenceFieldStepClamped
        ring root e B ⟨0, by omega⟩).1 = .RESET := by
    unfold GrantBankReference.bankLocalReferenceFieldStepClamped
    split
    · rename_i hx
      have he : e = root := by
        simpa only [Counter.site] using hx.2
      exact False.elim (hne he)
    · split
      · rename_i hy
        have hbad : (0 : Nat) < 0 := hy.1
        omega
      · split
        · rename_i ht
          have hbad : (0 : Nat) = (compileAdvice q).b := ht.1
          omega
        · split
          · have hzero :
                (B.fields (0 : Fin ((compileAdvice q).b + 1))).1 =
                  .RESET := by
                have h0 : (0 : Fin ((compileAdvice q).b + 1)) =
                    ⟨0, by omega⟩ := Fin.ext (by rfl)
                rw [h0]
                exact hm
            change (GrantBankReference.incomingRootBankMap
              (GrantBankReference.bankLocalReferenceCell B
                ⟨0, by omega⟩)).mode = .RESET
            simp [GrantBankReference.incomingRootBankMap,
              GrantBankReference.bankLocalReferenceCell, hzero, hm, isWaitMode]
          · exact hm
  have hmode :
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨0, by omega⟩).1 = .RESET := by
    by_cases hs : Counter.Support q ring root e
    · rw [bankTrialLocalStepField ring root e B hs hf]
      exact hlocal
    · rw [bankTrialLocalStepOutside ring root e B hs]
      exact hm
  exact ⟨bankTrialLocalLeaseCapStep ring root e B hc,
    bankTrialLocalRecoveryModeBandNoWin ring root e B
      ⟨hf, Or.inl hm⟩, Or.inl hmode⟩

/-- Complete family A, with no injectivity assumption on the entire
protected interval: n>=2 is needed only at the launch responder. -/
theorem bankTrialLocalRecoveryCertResetStep {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n) (hn : 2 ≤ n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLocalRecoveryCert q B)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RESET) :
    BankTrialLocalRecoveryCert q
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) := by
  by_cases he : e = root
  · subst e
    exact bankTrialLocalRecoveryCertLaunch
      ring root hn B hc.1 hc.2.1 hm
  · exact bankTrialLocalRecoveryCertResetOffEdge
      ring root e B hc.1 hc.2.1 hm he

/-- Family B's scalar incoming-root row, including the physical clamp.
This does not assert preservation of simultaneously updated digits. -/
theorem bankTrialLocalIncomingWaitRow
    (q : Nat) (z : BankCell)
    (hm : z.mode = .RWAIT)
    (hc : z.lease ≤ (compileAdvice q).bankLeaseCap) :
    (1 < z.lease →
      (GrantBankReference.bankLocalReferenceClampedQuad q
        (GrantBankReference.incomingRootBankMap z)).1 = .RWAIT ∧
      (GrantBankReference.bankLocalReferenceClampedQuad q
        (GrantBankReference.incomingRootBankMap z)).2.2.2 = z.lease - 1) ∧
    (z.lease ≤ 1 →
      (GrantBankReference.bankLocalReferenceClampedQuad q
        (GrantBankReference.incomingRootBankMap z)).1 = .RESET ∧
      (GrantBankReference.bankLocalReferenceClampedQuad q
        (GrantBankReference.incomingRootBankMap z)).2.2.2 = 0) := by
  constructor
  · intro hl
    have hlt : z.lease - 1 < (compileAdvice q).bankLeaseCap + 1 := by
      omega
    simp [GrantBankReference.bankLocalReferenceClampedQuad,
      GrantBankReference.bankAgentLeaseQuad, copyBank,
      GrantBankReference.incomingRootBankMap, hm, isWaitMode, hl, hlt]
  · intro hl
    have hnot : ¬ 1 < z.lease := by omega
    simp [GrantBankReference.bankLocalReferenceClampedQuad,
      GrantBankReference.bankAgentLeaseQuad, copyBank,
      GrantBankReference.incomingRootBankMap, hm, isWaitMode, hnot]

/-- Family C's matching RWAIT/RL endpoint calculation. The full-array
G_1-to-Clean theorem still needs the simultaneous digit-frame proof. -/
theorem bankTrialLocalRawRootReturn
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 ≤ b) (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false) (hm : x.mode = .RWAIT)
    (ht : y.tok = .RL) :
    (bankPair x y 1 b theta).1.mode = .ARMED ∧
    (bankPair x y 1 b theta).1.lease = 0 ∧
    (bankPair x y 1 b theta).2.bit = y.bit ∧
    (bankPair x y 1 b theta).2.tok = .E := by
  simp [bankPair, hx, hy, hg, hm, ht, hb, isRetTok, Id.run]
  all_goals exact ⟨rfl, rfl, rfl, rfl⟩
/-- Family F's unary top row. It preserves every non-IR token and
all bits; it is not the RR-to-RL turnaround row. -/
theorem bankTrialLocalTopDataRow
    (q : Nat) (z : BankCell) (ht : z.tok ≠ .IR) :
    (GrantBankReference.bankLocalReferenceClampedQuad q
      (GrantBankReference.topBoundaryBankMap z)).2.1 = z.bit ∧
    (GrantBankReference.bankLocalReferenceClampedQuad q
      (GrantBankReference.topBoundaryBankMap z)).2.2.1 = z.tok := by
  simp [GrantBankReference.bankLocalReferenceClampedQuad,
    GrantBankReference.bankAgentLeaseQuad, copyBank,
    GrantBankReference.topBoundaryBankMap, ht]

/-- Once an actual postservice Clean has been established, the
recovery observer records loss, not an unproved continued recovery. -/
theorem bankTrialLocalRecoveryCleanLoss {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLocalClean q
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e)) :
    bankTrialLocalNext ring root
      (⟨B, .recovery⟩ : BankTrialLocalState q) e =
      ⟨GrantBankReference.bankLocalReferenceStepClamped
        ring root B e, .lost⟩ := by
  classical
  simp [bankTrialLocalNext, hc.1, hc]


/-!
Pointwise selectors for the clamped BANK reference and
symbolic C.2 reset-front rows.  These do not claim the missing
whole-array invariant.
-/

/-- Actual source selection at one logical field. -/
theorem bankTrialLocalSelectedSource {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (i : Fin ((compileAdvice q).b + 1))
    (hs : i.val < (compileAdvice q).b ∧
      e = Counter.site ring root i.val) :
    GrantBankReference.bankLocalReferenceFieldStepClamped
      ring root e B i =
      GrantBankReference.bankLocalReferenceClampedQuad q
        ((GrantBankReference.bankLocalReferenceInternalPair q B
          ⟨i.val, hs.1⟩).1) := by
  classical
  simp [GrantBankReference.bankLocalReferenceFieldStepClamped, hs]

/-- Actual responder selection with the earlier source guard excluded. -/
theorem bankTrialLocalSelectedResponder {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (i : Fin ((compileAdvice q).b + 1))
    (hsource : ¬ (i.val < (compileAdvice q).b ∧
      e = Counter.site ring root i.val))
    (htarget : 0 < i.val ∧
      e = Counter.site ring root (i.val - 1)) :
    GrantBankReference.bankLocalReferenceFieldStepClamped
      ring root e B i =
      GrantBankReference.bankLocalReferenceClampedQuad q
        ((GrantBankReference.bankLocalReferenceInternalPair q B
          ⟨i.val - 1, by omega⟩).2) := by
  classical
  unfold GrantBankReference.bankLocalReferenceFieldStepClamped
  rw [dif_neg hsource, dif_pos htarget]

/-- Actual top unary selection. -/
theorem bankTrialLocalSelectedTop {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (i : Fin ((compileAdvice q).b + 1))
    (hsource : ¬ (i.val < (compileAdvice q).b ∧
      e = Counter.site ring root i.val))
    (htarget : ¬ (0 < i.val ∧
      e = Counter.site ring root (i.val - 1)))
    (htop : i.val = (compileAdvice q).b ∧
      e = Counter.site ring root (compileAdvice q).b) :
    GrantBankReference.bankLocalReferenceFieldStepClamped
      ring root e B i =
      GrantBankReference.bankLocalReferenceClampedQuad q
        (GrantBankReference.topBoundaryBankMap
          (GrantBankReference.bankLocalReferenceCell B i)) := by
  classical
  unfold GrantBankReference.bankLocalReferenceFieldStepClamped
  rw [dif_neg hsource, dif_neg htarget, dif_pos htop]

/-- Actual incoming-root unary selection. -/
theorem bankTrialLocalSelectedIncoming {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (i : Fin ((compileAdvice q).b + 1))
    (hsource : ¬ (i.val < (compileAdvice q).b ∧
      e = Counter.site ring root i.val))
    (htarget : ¬ (0 < i.val ∧
      e = Counter.site ring root (i.val - 1)))
    (htop : ¬ (i.val = (compileAdvice q).b ∧
      e = Counter.site ring root (compileAdvice q).b))
    (hincoming : i.val = 0 ∧
      ring.rightNeighbor e = root) :
    GrantBankReference.bankLocalReferenceFieldStepClamped
      ring root e B i =
      GrantBankReference.bankLocalReferenceClampedQuad q
        (GrantBankReference.incomingRootBankMap
          (GrantBankReference.bankLocalReferenceCell B i)) := by
  classical
  unfold GrantBankReference.bankLocalReferenceFieldStepClamped
  rw [dif_neg hsource, dif_neg htarget, dif_neg htop, dif_pos hincoming]

/-- A slot not selected by any owner is framed.  Other slots may
still update simultaneously on a short ring. -/
theorem bankTrialLocalSelectedFrame {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (i : Fin ((compileAdvice q).b + 1))
    (hsource : ¬ (i.val < (compileAdvice q).b ∧
      e = Counter.site ring root i.val))
    (htarget : ¬ (0 < i.val ∧
      e = Counter.site ring root (i.val - 1)))
    (htop : ¬ (i.val = (compileAdvice q).b ∧
      e = Counter.site ring root (compileAdvice q).b))
    (hincoming : ¬ (i.val = 0 ∧
      ring.rightNeighbor e = root)) :
    GrantBankReference.bankLocalReferenceFieldStepClamped
      ring root e B i = B.fields i := by
  classical
  unfold GrantBankReference.bankLocalReferenceFieldStepClamped
  rw [dif_neg hsource, dif_neg htarget, dif_neg htop, dif_neg hincoming]

/-- D: RR advance has priority over arbitrary destination scratch. -/
theorem bankTrialLocalRawForward
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (htx : x.tok = .RR) (hbx : x.bit = false) :
    (bankPair x y y.role b theta).1.tok = .E ∧
    (bankPair x y y.role b theta).1.bit = false ∧
    (bankPair x y y.role b theta).2.tok = .RR ∧
    (bankPair x y y.role b theta).2.bit = false := by
  exact Counter.resetTrialBankForwardSymbolic
    x y b theta hx hlt hy htx hbx

/-- D: the zero/empty predecessor cannot absorb a non-top RR. -/
theorem bankTrialLocalRawPredecessorHold
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1) (hyn : y.role < b)
    (htx : x.tok = .E) (hty : y.tok = .RR)
    (hbx : x.bit = false) (hby : y.bit = false) :
    (bankPair x y y.role b theta).1.tok = .E ∧
    (bankPair x y y.role b theta).1.bit = false ∧
    (bankPair x y y.role b theta).2.tok = .RR ∧
    (bankPair x y y.role b theta).2.bit = false := by
  exact Counter.resetTrialBankPredecessorHoldsSymbolic
    x y b theta hx hlt hy hyn htx hty hbx hby

/-- F_b: the literal pair transition from top RR to predecessor RL.
The entire G_(b-1) array still requires its own proof. -/
theorem bankTrialLocalRawTopTurn
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1) (htop : y.role = b)
    (htx : x.tok = .E) (hty : y.tok = .RR)
    (hby : y.bit = false) :
    (bankPair x y y.role b theta).1.tok = .RL ∧
    (bankPair x y y.role b theta).1.bit = false ∧
    (bankPair x y y.role b theta).2.tok = .E ∧
    (bankPair x y y.role b theta).2.bit = false := by
  exact Counter.resetTrialBankTopTurnSymbolic
    x y b theta hx hlt hy htop htx hty hby

/-- E: the returning RL moves one slot left. -/
theorem bankTrialLocalRawRetreat
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (htx : x.tok = .E) (hty : y.tok = .RL)
    (hby : y.bit = false) :
    (bankPair x y y.role b theta).1.tok = .RL ∧
    (bankPair x y y.role b theta).1.bit = false ∧
    (bankPair x y y.role b theta).2.tok = .E ∧
    (bankPair x y y.role b theta).2.bit = false := by
  exact Counter.resetTrialBankRetreatSymbolic
    x y b theta hx hlt hy htx hty hby

/-- The unrelated zero/empty internal digit pair remains zero/empty. -/
theorem bankTrialLocalRawEmptyHold
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (htx : x.tok = .E) (hty : y.tok = .E)
    (hbx : x.bit = false) (hby : y.bit = false) :
    (bankPair x y y.role b theta).1.tok = .E ∧
    (bankPair x y y.role b theta).1.bit = false ∧
    (bankPair x y y.role b theta).2.tok = .E ∧
    (bankPair x y y.role b theta).2.bit = false := by
  exact Counter.resetTrialBankEmptyHoldsSymbolic
    x y b theta hx hlt hy htx hty hbx hby

/-- E: returning RL as the forward source holds its position. -/
theorem bankTrialLocalRawReturnSourceHold
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (htx : x.tok = .RL) (hbx : x.bit = false)
    (hty : y.tok = .E) (hby : y.bit = false) :
    (bankPair x y y.role b theta).1.tok = .RL ∧
    (bankPair x y y.role b theta).1.bit = false ∧
    (bankPair x y y.role b theta).2.tok = .E ∧
    (bankPair x y y.role b theta).2.bit = false := by
  exact Counter.resetTrialBankReturnSourceHoldSymbolic
    x y b theta hx hlt hy htx hbx hty hby

/-- Root RWAIT with an empty digit-one token preserves the digit. -/
theorem bankTrialLocalRawRootWaitEmpty
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : x.role = 0) (hg : x.grant = false)
    (hy : y.role = 1) (hm : x.mode = .RWAIT)
    (hb : 1 < b) (ht : y.tok = .E)
    (hbit : y.bit = false) :
    (bankPair x y 1 b theta).2.tok = .E ∧
    (bankPair x y 1 b theta).2.bit = false := by
  exact Counter.resetTrialBankRootWaitEmptySymbolic
    x y b theta hx hg hy hm hb ht hbit

/-- Root RWAIT cannot consume an outward RR in digit one. -/
theorem bankTrialLocalRawRootWaitOutward
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : x.role = 0) (hg : x.grant = false)
    (hy : y.role = 1) (hm : x.mode = .RWAIT)
    (hb : 1 < b) (ht : y.tok = .RR)
    (hbit : y.bit = false) :
    (bankPair x y 1 b theta).2.tok = .RR ∧
    (bankPair x y 1 b theta).2.bit = false := by
  exact Counter.resetTrialBankRootWaitOutwardSymbolic
    x y b theta hx hg hy hm hb ht hbit


/-!
All-word implications of the remaining full-array C.2
closure obligation, exposed as a Prop rather than an axiom.
-/

/-- The necessary one-step full-array theorem is still to be proved;
the genuine G_1 acceptance must yield Clean, not another Cert. -/
def BankTrialLocalRecoveryCertStepPremise {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (e : Fin n),
    BankTrialLocalRecoveryCert q B →
      (BankTrialLocalRecoveryCert q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e) ∨
       BankTrialLocalClean q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e))

/-- A recovery certificate is required only in RECOVERY, while
lease representability is tracked through every observer phase. -/
def BankTrialLocalObserverSafe {q : Nat}
    (z : BankTrialLocalState q) : Prop :=
  BankTrialLocalLeaseCap q z.bank ∧
    (z.phase = .recovery →
      BankTrialLocalRecoveryCert q z.bank)

/-- Conditional one-letter observer preservation, respecting
the Clean-to-LOST exit rather than assuming Cert persists. -/
theorem bankTrialLocalObserverSafeNext {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hclosed : BankTrialLocalRecoveryCertStepPremise
      (q := q) ring root)
    (z : BankTrialLocalState q)
    (hz : BankTrialLocalObserverSafe z) :
    BankTrialLocalObserverSafe
      (bankTrialLocalNext ring root z e) := by
  cases z with
  | mk B phase =>
      refine ⟨bankTrialLocalLeaseCapNext ring root e
        (⟨B, phase⟩ : BankTrialLocalState q) hz.1, ?_⟩
      cases phase with
      | live begun =>
          intro hrec
          exact bankTrialLocalLiveEntersRecoveryCert
            ring root e B begun hz.1 hrec
      | recovery =>
          intro hrec
          have hprior : BankTrialLocalRecoveryCert q B := hz.2 rfl
          by_cases hclean :
              BankTrialLocalClean q
                (GrantBankReference.bankLocalReferenceStepClamped
                  ring root B e)
          · have hlos := bankTrialLocalRecoveryCleanLoss
              ring root e B hclean
            rw [hlos] at hrec
            cases hrec
          · rcases hclosed B e hprior with hcert | hpostClean
            · rw [bankTrialLocalNextRecoveryBank ring root e B]
              exact hcert
            · exact False.elim (hclean hpostClean)
      | won =>
          intro hrec
          have hterminal :
              bankTrialLocalTerminal
                (⟨B, .won⟩ : BankTrialLocalState q) :=
            Or.inl rfl
          rw [bankTrialLocalTerminalAbsorbs ring root e
            (⟨B, .won⟩ : BankTrialLocalState q) hterminal] at hrec
          cases hrec
      | lost =>
          intro hrec
          have hterminal :
              bankTrialLocalTerminal
                (⟨B, .lost⟩ : BankTrialLocalState q) :=
            Or.inr rfl
          rw [bankTrialLocalTerminalAbsorbs ring root e
            (⟨B, .lost⟩ : BankTrialLocalState q) hterminal] at hrec
          cases hrec

/-- Conditional finite-word invariant of the actual observer. -/
theorem bankTrialLocalObserverSafeRun {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hclosed : BankTrialLocalRecoveryCertStepPremise
      (q := q) ring root) :
    ∀ (w : List (Fin n)) (z : BankTrialLocalState q),
      BankTrialLocalObserverSafe z →
      BankTrialLocalObserverSafe
        (bankTrialLocalRun ring root w z) := by
  intro w
  induction w with
  | nil =>
      intro z hz
      exact hz
  | cons e es ih =>
      intro z hz
      change BankTrialLocalObserverSafe
        (bankTrialLocalRun ring root es
          (bankTrialLocalNext ring root z e))
      exact ih _ (bankTrialLocalObserverSafeNext
        ring root e hclosed z hz)

/-- Reachable recovery cuts are certified after the outstanding
F/G array-closure premise is supplied. -/
theorem bankTrialLocalRecoveryCertReachableOfStepPremise {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hclosed : BankTrialLocalRecoveryCertStepPremise
      (q := q) ring root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (w : List (Fin n))
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hrun : bankTrialLocalRun ring root w
      (bankTrialLocalStart S) = ⟨B, .recovery⟩) :
    BankTrialLocalRecoveryCert q B := by
  have hseed :
      BankTrialLocalObserverSafe (bankTrialLocalStart S) := by
    refine ⟨bankTrialLocalCleanLeaseCap S hclean, ?_⟩
    intro h
    cases h
  have hrunSafe := bankTrialLocalObserverSafeRun
    ring root hclosed w (bankTrialLocalStart S) hseed
  rw [hrun] at hrunSafe
  exact hrunSafe.2 rfl

/-- The existing BandReachable Prop is inhabited conditionally. -/
theorem bankTrialLocalRecoveryBandReachableOfStepPremise {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hclosed : BankTrialLocalRecoveryCertStepPremise
      (q := q) ring root) :
    BankTrialLocalRecoveryBandReachable (q := q) ring root := by
  intro S hclean w B hrun
  exact bankTrialLocalRecoveryCertModeBand B
    (bankTrialLocalRecoveryCertReachableOfStepPremise
      ring root hclosed S hclean w B hrun)

/-- No recovery success, under the very same explicit closure premise. -/
theorem bankTrialLocalRecoveryNoWinOfStepPremise {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hclosed : BankTrialLocalRecoveryCertStepPremise
      (q := q) ring root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (w : List (Fin n))
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hrun : bankTrialLocalRun ring root w
      (bankTrialLocalStart S) = ⟨B, .recovery⟩)
    (e : Fin n) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).success = false := by
  exact bankTrialLocalRecoveryNoWinOfBandReachable ring root
    (bankTrialLocalRecoveryBandReachableOfStepPremise
      ring root hclosed) S hclean w B hrun e

end L3

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
One root case at a time, starting with the complete
RESET case and the matching G_1 return endpoint.
-/

/-- The RESET arm of the missing certificate-step lemma is
unconditionally closed for n at least two. -/
theorem bankTrialLocalRecoveryCertStepReset {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hn : 2 ≤ n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLocalRecoveryCert q B)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RESET) :
    BankTrialLocalRecoveryCert q
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) ∨
    BankTrialLocalClean q
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) := by
  exact Or.inl
    (bankTrialLocalRecoveryCertResetStep ring root e hn B hc hm)

/-- The physical Fin lease clamp does not alter bit or token
coordinates, even when it changes the numeric lease. -/
theorem bankTrialLocalClampedData (q : Nat) (z : BankCell) :
    (GrantBankReference.bankLocalReferenceClampedQuad q z).2.1 =
        z.bit ∧
    (GrantBankReference.bankLocalReferenceClampedQuad q z).2.2.1 =
        z.tok := by
  simp [GrantBankReference.bankLocalReferenceClampedQuad,
    GrantBankReference.bankAgentLeaseQuad, copyBank]

/-- Adjacent logical sites do not alias for n at least two. The
logical site map may still repeat at larger separations. -/
theorem bankTrialLocalAdjacentSitesDistinct {n : Nat}
    (ring : DirectedRing n) (root : Fin n) (hn : 2 ≤ n)
    (j : Nat) :
    Counter.site ring root j ≠
      Counter.site ring root (j + 1) := by
  change Counter.site ring root j ≠
    ring.rightNeighbor (Counter.site ring root j)
  exact Ne.symm
    (bankTrialLocalNeighborNe ring hn
      (Counter.site ring root j))

/-- The scalar G_1 root-return edge really arms the root, clears
the first digit bit, and consumes its RL. This lemma does NOT
assert Clean of the other digits; that is an array theorem. -/
theorem bankTrialLocalRootReturnFields {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RWAIT)
    (hfront : BankTrialLocalFrontBack q B 1) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B root).fields ⟨0, by omega⟩).1 = .ARMED ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B root).fields
        ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.1 = false ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B root).fields
        ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.2.1 = .E := by
  obtain ⟨hb, _, hbit, htok, _⟩ := hfront
  have hs : Counter.Support q ring root root :=
    Or.inr ⟨0, Nat.zero_le _, rfl⟩
  have hrow := bankTrialLocalRawRootReturn
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B ⟨0, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩)
    hb rfl rfl rfl hm htok
  refine ⟨?_, ?_, ?_⟩
  · rw [bankTrialLocalStepField ring root root B hs hf,
      bankTrialLocalFieldRootOutgoing ring root B]
    change (GrantBankReference.bankLocalReferenceInternalPair q B
      ⟨0, by change 0 < (compileAdvice q).s + 11; omega⟩).1.mode =
        .ARMED
    exact hrow.1
  · rw [bankTrialLocalStepField ring root root B hs hf,
      bankTrialLocalFieldOneOutgoing ring root hn B]
    change (GrantBankReference.bankLocalReferenceInternalPair q B
      ⟨0, by change 0 < (compileAdvice q).s + 11; omega⟩).2.bit =
        false
    calc
      (GrantBankReference.bankLocalReferenceInternalPair q B
        ⟨0, by change 0 < (compileAdvice q).s + 11; omega⟩).2.bit =
          (GrantBankReference.bankLocalReferenceCell B
            ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).bit :=
        hrow.2.2.1
      _ = false := hbit
  · rw [bankTrialLocalStepField ring root root B hs hf,
      bankTrialLocalFieldOneOutgoing ring root hn B]
    change (GrantBankReference.bankLocalReferenceInternalPair q B
      ⟨0, by change 0 < (compileAdvice q).s + 11; omega⟩).2.tok =
        .E
    exact hrow.2.2.2



/-- A zero/empty pair at two consecutive internal digit roles
leaves both of the corresponding clamped bit/token fields zero/empty. -/
theorem bankTrialLocalInternalEmptyData {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Fin (compileAdvice q).b)
    (hj : 1 ≤ j.val)
    (hx : (B.fields ⟨j.val, by omega⟩).2.1 = false ∧
      (B.fields ⟨j.val, by omega⟩).2.2.1 = .E)
    (hy : (B.fields ⟨j.val + 1, by omega⟩).2.1 = false ∧
      (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .E) :
    ((GrantBankReference.bankLocalReferenceClampedQuad q
      ((GrantBankReference.bankLocalReferenceInternalPair q B j).1)
      ).2.1 = false ∧
     (GrantBankReference.bankLocalReferenceClampedQuad q
      ((GrantBankReference.bankLocalReferenceInternalPair q B j).1)
      ).2.2.1 = .E) ∧
    ((GrantBankReference.bankLocalReferenceClampedQuad q
      ((GrantBankReference.bankLocalReferenceInternalPair q B j).2)
      ).2.1 = false ∧
     (GrantBankReference.bankLocalReferenceClampedQuad q
      ((GrantBankReference.bankLocalReferenceInternalPair q B j).2)
      ).2.2.1 = .E) := by
  have hrow := bankTrialLocalRawEmptyHold
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val + 1, by omega⟩)
    (by change 1 ≤ j.val; exact hj)
    (by change j.val < (compileAdvice q).b; exact j.isLt)
    rfl hx.2 hy.2 hx.1 hy.1
  have hleft := bankTrialLocalClampedData q
    ((GrantBankReference.bankLocalReferenceInternalPair q B j).1)
  have hright := bankTrialLocalClampedData q
    ((GrantBankReference.bankLocalReferenceInternalPair q B j).2)
  exact ⟨⟨hleft.1.trans hrow.2.1,
      hleft.2.trans hrow.1⟩,
    ⟨hright.1.trans hrow.2.2.2,
      hright.2.trans hrow.2.2.1⟩⟩

/-- In the authentic G_1 return step, every digit other than one
remains zero/empty, even if the scheduler letter aliases several
nonadjacent logical edges of a short ring. -/
theorem bankTrialLocalGOneOtherDigits {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hback : BankTrialLocalFrontBack q B 1) :
    ∀ i : Nat, 2 ≤ i →
      (hib : i ≤ (compileAdvice q).b) →
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B root).fields
        ⟨i, Nat.lt_succ_of_le hib⟩).2.1 = false ∧
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B root).fields
        ⟨i, Nat.lt_succ_of_le hib⟩).2.2.1 = .E := by
  obtain ⟨_, _, _, _, hother⟩ := hback
  have hs : Counter.Support q ring root root :=
    Or.inr ⟨0, Nat.zero_le _, rfl⟩
  intro i hi hib
  have hnotOne : i ≠ 1 := by omega
  have hold := hother i (by omega) hib hnotOne
  rw [bankTrialLocalStepField ring root root B hs hf]
  by_cases hsource :
      i < (compileAdvice q).b ∧
      root = Counter.site ring root i
  · rw [bankTrialLocalSelectedSource ring root root B
      ⟨i, Nat.lt_succ_of_le hib⟩ hsource]
    have hright : (B.fields ⟨i + 1, by omega⟩).2.1 =
          false ∧
        (B.fields ⟨i + 1, by omega⟩).2.2.1 = .E :=
      hother (i + 1) (by omega) (by omega) (by omega)
    exact (bankTrialLocalInternalEmptyData B
      ⟨i, hsource.1⟩ (by change 1 ≤ i; omega) hold hright).1
  · by_cases htarget :
        0 < i ∧ root = Counter.site ring root (i - 1)
    · have hnotTwo : i ≠ 2 := by
        intro htwo
        subst i
        apply bankTrialLocalAdjacentSitesDistinct ring root hn 0
        change root = Counter.site ring root 1
        exact htarget.2
      have hprev : 2 ≤ i - 1 := by omega
      have hprevData :
          (B.fields ⟨i - 1, by omega⟩).2.1 = false ∧
          (B.fields ⟨i - 1, by omega⟩).2.2.1 = .E :=
        hother (i - 1) (by omega) (by omega) (by omega)
      rw [bankTrialLocalSelectedResponder ring root root B
        ⟨i, Nat.lt_succ_of_le hib⟩ hsource htarget]
      have hfin : (⟨i - 1 + 1, by omega⟩ : Fin ((compileAdvice q).b + 1)) =
          ⟨i, Nat.lt_succ_of_le hib⟩ := Fin.ext (by
        show i - 1 + 1 = i
        omega)
      have hold' :
          (B.fields ⟨i - 1 + 1, by omega⟩).2.1 = false ∧
          (B.fields ⟨i - 1 + 1, by omega⟩).2.2.1 = .E := by
        rw [hfin]
        exact hold
      exact (bankTrialLocalInternalEmptyData B
        ⟨i - 1, by omega⟩ (by change 1 ≤ i - 1; omega) hprevData hold').2
    · by_cases htop :
          i = (compileAdvice q).b ∧
          root = Counter.site ring root (compileAdvice q).b
      · rw [bankTrialLocalSelectedTop ring root root B
          ⟨i, Nat.lt_succ_of_le hib⟩ hsource htarget htop]
        have hnotIR :
            (GrantBankReference.bankLocalReferenceCell B
              ⟨i, Nat.lt_succ_of_le hib⟩).tok ≠ .IR := by
          intro hir
          have he : (B.fields ⟨i, Nat.lt_succ_of_le hib⟩).2.2.1 =
              .IR := hir
          rw [hold.2] at he
          cases he
        have htrow := bankTrialLocalTopDataRow q
          (GrantBankReference.bankLocalReferenceCell B
            ⟨i, Nat.lt_succ_of_le hib⟩) hnotIR
        exact ⟨htrow.1.trans hold.1, htrow.2.trans hold.2⟩
      · have hincoming :
            ¬ (i = 0 ∧ ring.rightNeighbor root = root) := by
          intro hh
          omega
        rw [bankTrialLocalSelectedFrame ring root root B
          ⟨i, Nat.lt_succ_of_le hib⟩
          hsource htarget htop hincoming]
        exact hold

/-- G_1 acceptance on the ENTIRE clamped reference: the root
becomes ARMED and every digit is zero/empty. The observer's LOST
classification follows from the existing priority lemma. -/
theorem bankTrialLocalRecoveryGOneClean {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLocalRecoveryCert q B)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RWAIT)
    (hback : BankTrialLocalFrontBack q B 1) :
    BankTrialLocalClean q
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B root) := by
  have hret := bankTrialLocalRootReturnFields
    ring root hn B hc.2.1 hm hback
  refine ⟨bankTrialLocalRecoveryCertNoWin ring root root B hc,
    hret.1, ?_, bankTrialLocalLeaseCapStep ring root root B hc.1⟩
  intro i hi hib
  by_cases hfirst : i = 1
  · subst i
    exact ⟨hret.2.1, hret.2.2⟩
  · have hge : 2 ≤ i := by omega
    exact bankTrialLocalGOneOtherDigits
      ring root hn B hc.2.1 hback i hge hib


/-- A non-root-incident scheduler edge frames the exact root quad.
This also applies when the letter updates many other logical slots. -/
theorem bankTrialLocalRootNonincidentFrame {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hne : e ≠ root)
    (hnotIncoming : ring.rightNeighbor e ≠ root) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨0, by omega⟩ =
      B.fields ⟨0, by omega⟩ := by
  classical
  have hsource :
      ¬ (0 < (compileAdvice q).b ∧
        e = Counter.site ring root 0) := by
    intro h
    exact hne (by simpa [Counter.site] using h.2)
  have htarget :
      ¬ (0 < (0 : Nat) ∧
        e = Counter.site ring root (0 - 1)) := by
    intro h
    omega
  have htop :
      ¬ ((0 : Nat) = (compileAdvice q).b ∧
        e = Counter.site ring root (compileAdvice q).b) := by
    intro h
    have hb := bankTrialLocalWidthLarge q
    omega
  have hincoming :
      ¬ ((0 : Nat) = 0 ∧ ring.rightNeighbor e = root) := by
    intro h
    exact hnotIncoming h.2
  by_cases hs : Counter.Support q ring root e
  · rw [bankTrialLocalStepField ring root e B hs hf]
    exact bankTrialLocalSelectedFrame ring root e B
      ⟨0, by omega⟩ hsource htarget htop hincoming
  · rw [bankTrialLocalStepOutside ring root e B hs]

/-- A genuinely incoming-root RWAIT service either keeps RWAIT
or expires its lease and enters RESET, with no assumption about
simultaneously serviced digits. -/
theorem bankTrialLocalRootIncomingWaitModes {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RWAIT)
    (hc : BankTrialLocalLeaseCap q B)
    (hne : e ≠ root)
    (hincoming : ring.rightNeighbor e = root) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨0, by omega⟩).1 = .RWAIT ∨
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨0, by omega⟩).1 = .RESET := by
  classical
  have hsource :
      ¬ (0 < (compileAdvice q).b ∧
        e = Counter.site ring root 0) := by
    intro h
    exact hne (by simpa [Counter.site] using h.2)
  have htarget :
      ¬ (0 < (0 : Nat) ∧
        e = Counter.site ring root (0 - 1)) := by
    intro h
    omega
  have htop :
      ¬ ((0 : Nat) = (compileAdvice q).b ∧
        e = Counter.site ring root (compileAdvice q).b) := by
    intro h
    have hb := bankTrialLocalWidthLarge q
    omega
  have hselected :
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨0, by omega⟩ =
        GrantBankReference.bankLocalReferenceClampedQuad q
          (GrantBankReference.incomingRootBankMap
            (GrantBankReference.bankLocalReferenceCell B
              ⟨0, by omega⟩)) := by
    rw [bankTrialLocalStepField ring root e B
      (Or.inl hincoming) hf]
    exact bankTrialLocalSelectedIncoming ring root e B
      ⟨0, by omega⟩ hsource htarget htop ⟨rfl, hincoming⟩
  have hrow := bankTrialLocalIncomingWaitRow q
    (GrantBankReference.bankLocalReferenceCell B ⟨0, by omega⟩)
    hm (hc 0 (by omega))
  by_cases hl : 1 <
      (B.fields ⟨0, by omega⟩).2.2.2
  · apply Or.inl
    rw [hselected]
    exact (hrow.1 hl).1
  · have hle :
        (GrantBankReference.bankLocalReferenceCell B
          ⟨0, by omega⟩).lease ≤ 1 := by
        change (B.fields ⟨0, by omega⟩).2.2.2 ≤ 1
        omega
    apply Or.inr
    rw [hselected]
    exact (hrow.2 hle).1

/-- A root-outgoing RWAIT service with E or RR in digit one
uses the existing symbolic WAIT row; there is no spurious
return-token acceptance. -/
theorem bankTrialLocalRootOutgoingWaitMode {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RWAIT)
    (htok :
      (B.fields ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.2.1 = .E ∨
      (B.fields ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.2.1 = .RR) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B root).fields ⟨0, by omega⟩).1 =
      Counter.resetClockWaitMode
        ((B.fields ⟨0, by omega⟩).2.2.2) := by
  have hs : Counter.Support q ring root root :=
    Or.inr ⟨0, Nat.zero_le _, rfl⟩
  have hrow := Counter.resetClockOutgoingWaitSymbolic
    (GrantBankReference.bankLocalReferenceCell B ⟨0, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩)
    (compileAdvice q).b (compileAdvice q).theta
    rfl rfl rfl hm (bankTrialLocalWidthLarge q) htok
  rw [bankTrialLocalStepField ring root root B hs hf,
    bankTrialLocalFieldRootOutgoing ring root B]
  change (GrantBankReference.bankLocalReferenceInternalPair q B
    ⟨0, by change 0 < (compileAdvice q).s + 11; omega⟩).1.mode =
      Counter.resetClockWaitMode
        ((B.fields ⟨0, by omega⟩).2.2.2)
  exact hrow.1


/-- F_j: an actual service of the forward edge at digit j clears
the source bit/token and writes a zero/RR at digit j+1. The target
selector is justified using only adjacent-site separation, so
nonadjacent aliases on short rings are retained. -/
theorem bankTrialLocalOutwardAdvancePair {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hn : 2 ≤ n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Nat)
    (hfront : BankTrialLocalFrontOut q B j)
    (hj : j < (compileAdvice q).b)
    (he : e = Counter.site ring root j) :
    (((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨j, by omega⟩).2.1 = false ∧
     ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨j, by omega⟩).2.2.1 = .E) ∧
    (((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨j + 1, by omega⟩).2.1 = false ∧
     ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨j + 1, by omega⟩).2.2.1 = .RR) := by
  obtain ⟨hjb, hjpos, hbit, htok, _⟩ := hfront
  have hs : Counter.Support q ring root e :=
    Or.inr ⟨j, hjb, he⟩
  have hrow := bankTrialLocalRawForward
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j + 1, by omega⟩)
    (by change 1 ≤ j; exact hjpos)
    (by change j < (compileAdvice q).b; exact hj)
    rfl htok hbit
  have hleftData := bankTrialLocalClampedData q
    ((GrantBankReference.bankLocalReferenceInternalPair q B
      ⟨j, hj⟩).1)
  have hrightData := bankTrialLocalClampedData q
    ((GrantBankReference.bankLocalReferenceInternalPair q B
      ⟨j, hj⟩).2)
  have hsource :
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨j, by omega⟩ =
        GrantBankReference.bankLocalReferenceClampedQuad q
          ((GrantBankReference.bankLocalReferenceInternalPair q B
            ⟨j, hj⟩).1) := by
    rw [bankTrialLocalStepField ring root e B hs hf]
    exact bankTrialLocalSelectedSource ring root e B
      ⟨j, by omega⟩ ⟨hj, he⟩
  have hnotSource :
      ¬ (j + 1 < (compileAdvice q).b ∧
          e = Counter.site ring root (j + 1)) := by
    intro hx
    apply bankTrialLocalAdjacentSitesDistinct ring root hn j
    exact he.symm.trans hx.2
  have hsub : j + 1 - 1 = j := by omega
  have htarget :
      0 < j + 1 ∧
        e = Counter.site ring root (j + 1 - 1) := by
    refine ⟨by omega, ?_⟩
    rw [hsub]
    exact he
  have hresponder :
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨j + 1, by omega⟩ =
        GrantBankReference.bankLocalReferenceClampedQuad q
          ((GrantBankReference.bankLocalReferenceInternalPair q B
            ⟨j, hj⟩).2) := by
    rw [bankTrialLocalStepField ring root e B hs hf]
    have hselected := bankTrialLocalSelectedResponder ring root e B
      ⟨j + 1, by omega⟩ hnotSource htarget
    simpa only [Fin.val_mk, hsub] using hselected
  rw [hsource, hresponder]
  exact ⟨⟨hleftData.1.trans hrow.2.1,
        hleftData.2.trans hrow.1⟩,
    ⟨hrightData.1.trans hrow.2.2.2,
      hrightData.2.trans hrow.2.2.1⟩⟩

/-- G_j: on the edge immediately left of an RL front, the
predecessor becomes zero/RL and the old return slot becomes
zero/empty. Again only adjacent-site distinctness is used. -/
theorem bankTrialLocalReturnRetreatPair {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hn : 2 ≤ n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Nat)
    (hback : BankTrialLocalFrontBack q B j)
    (hj : 1 < j)
    (he : e = Counter.site ring root (j - 1)) :
    (((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨j - 1, by rcases hback with ⟨hjb, _⟩; omega⟩).2.1 = false ∧
     ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields
        ⟨j - 1, by rcases hback with ⟨hjb, _⟩; omega⟩).2.2.1 = .RL) ∧
    (((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨j, by rcases hback with ⟨hjb, _⟩; omega⟩).2.1 = false ∧
     ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields
        ⟨j, by rcases hback with ⟨hjb, _⟩; omega⟩).2.2.1 = .E) := by
  obtain ⟨hjb, _, hbit, htok, hother⟩ := hback
  have hprevBound : j - 1 < (compileAdvice q).b := by omega
  have hprevData :
      (B.fields ⟨j - 1, by omega⟩).2.1 = false ∧
      (B.fields ⟨j - 1, by omega⟩).2.2.1 = .E :=
    hother (j - 1) (by omega) (by omega) (by omega)
  have hs : Counter.Support q ring root e :=
    Or.inr ⟨j - 1, by omega, he⟩
  have hstep : j - 1 + 1 = j := by omega
  have hretBit :
      (B.fields ⟨j - 1 + 1, by omega⟩).2.1 = false := by
    simpa only [hstep] using hbit
  have hretTok :
      (B.fields ⟨j - 1 + 1, by omega⟩).2.2.1 = .RL := by
    simpa only [hstep] using htok
  have hrow := bankTrialLocalRawRetreat
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j - 1, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j - 1 + 1, by omega⟩)
    (by change 1 ≤ j - 1; omega)
    (by change j - 1 < (compileAdvice q).b; exact hprevBound)
    rfl hprevData.2 hretTok hretBit
  have hleftData := bankTrialLocalClampedData q
    ((GrantBankReference.bankLocalReferenceInternalPair q B
      ⟨j - 1, hprevBound⟩).1)
  have hrightData := bankTrialLocalClampedData q
    ((GrantBankReference.bankLocalReferenceInternalPair q B
      ⟨j - 1, hprevBound⟩).2)
  have hsource :
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨j - 1, by omega⟩ =
        GrantBankReference.bankLocalReferenceClampedQuad q
          ((GrantBankReference.bankLocalReferenceInternalPair q B
            ⟨j - 1, hprevBound⟩).1) := by
    rw [bankTrialLocalStepField ring root e B hs hf]
    exact bankTrialLocalSelectedSource ring root e B
      ⟨j - 1, by omega⟩ ⟨hprevBound, he⟩
  have hnotSource :
      ¬ (j < (compileAdvice q).b ∧
          e = Counter.site ring root j) := by
    intro hx
    have hne := bankTrialLocalAdjacentSitesDistinct ring root hn (j - 1)
    apply hne
    have hstep : j - 1 + 1 = j := by omega
    rw [hstep]
    exact he.symm.trans hx.2
  have htarget :
      0 < j ∧ e = Counter.site ring root (j - 1) :=
    ⟨by omega, he⟩
  have hresponder :
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨j, by omega⟩ =
        GrantBankReference.bankLocalReferenceClampedQuad q
          ((GrantBankReference.bankLocalReferenceInternalPair q B
            ⟨j - 1, hprevBound⟩).2) := by
    rw [bankTrialLocalStepField ring root e B hs hf]
    exact bankTrialLocalSelectedResponder ring root e B
      ⟨j, by omega⟩ hnotSource htarget
  rw [hsource, hresponder]
  exact ⟨⟨hleftData.1.trans hrow.2.1,
        hleftData.2.trans hrow.1⟩,
    ⟨hrightData.1.trans hrow.2.2.2,
      hrightData.2.trans hrow.2.2.1⟩⟩


/-- The authenticated G_1 root service is the Clean alternative in
the requested certificate-step disjunction. -/
theorem bankTrialLocalRecoveryCertStepGOne {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLocalRecoveryCert q B)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RWAIT)
    (hback : BankTrialLocalFrontBack q B 1) :
    BankTrialLocalRecoveryCert q
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B root) ∨
    BankTrialLocalClean q
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B root) := by
  exact Or.inr
    (bankTrialLocalRecoveryGOneClean ring root hn B hc hm hback)

/-- The observer classifies the actual authenticated G_1 return as
LOST, not as a continuing recovery phase. -/
theorem bankTrialLocalRecoveryGOneLoss {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLocalRecoveryCert q B)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RWAIT)
    (hback : BankTrialLocalFrontBack q B 1) :
    bankTrialLocalNext ring root
      (⟨B, .recovery⟩ : BankTrialLocalState q) root =
      ⟨GrantBankReference.bankLocalReferenceStepClamped
        ring root B root, .lost⟩ := by
  exact bankTrialLocalRecoveryCleanLoss ring root root B
    (bankTrialLocalRecoveryGOneClean ring root hn B hc hm hback)

end L3

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
Decomposing the two RWAIT certificate-step cases into
root-mode/watchdog facts and full-array front preservation.
-/

/-- If a certified prestate has a RESET root after service, the
clamped successor is certified without restrictions on digit scratch. -/
theorem bankTrialLocalRecoveryNextReset {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLocalRecoveryCert q B)
    (hm : ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨0, by omega⟩).1 = .RESET) :
    BankTrialLocalRecoveryCert q
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) := by
  exact ⟨bankTrialLocalLeaseCapStep ring root e B hc.1,
    bankTrialLocalRecoveryCertNoWin ring root e B hc,
    Or.inl hm⟩

/-- A surviving RWAIT root with positive lease and a certified
outward/return front also carries the full successor certificate. -/
theorem bankTrialLocalRecoveryNextWait {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLocalRecoveryCert q B)
    (hm : ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨0, by omega⟩).1 = .RWAIT)
    (hp : 1 ≤
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨0, by omega⟩).2.2.2)
    (hfront :
      (∃ j : Nat, BankTrialLocalFrontOut q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e) j) ∨
      (∃ j : Nat, BankTrialLocalFrontBack q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e) j)) :
    BankTrialLocalRecoveryCert q
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) := by
  have hcap := bankTrialLocalLeaseCapStep ring root e B hc.1
  refine ⟨hcap, bankTrialLocalRecoveryCertNoWin ring root e B hc,
    Or.inr ⟨hm, hp, ?_, hfront⟩⟩
  exact hcap 0 (by omega)


/-- The outgoing RWAIT watchdog's numerical lease also agrees with
the scalar BANK row, after the physical clamp. -/
theorem bankTrialLocalRootOutgoingWaitLease {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hc : BankTrialLocalLeaseCap q B)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RWAIT)
    (htok :
      (B.fields ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.2.1 = .E ∨
      (B.fields ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.2.1 = .RR) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B root).fields ⟨0, by omega⟩).2.2.2 =
      Counter.resetClockWaitLease
        ((B.fields ⟨0, by omega⟩).2.2.2) := by
  have hs : Counter.Support q ring root root :=
    Or.inr ⟨0, Nat.zero_le _, rfl⟩
  have hrow := Counter.resetClockOutgoingWaitSymbolic
    (GrantBankReference.bankLocalReferenceCell B ⟨0, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩)
    (compileAdvice q).b (compileAdvice q).theta
    rfl rfl rfl hm (bankTrialLocalWidthLarge q) htok
  have hrawCap :
      (GrantBankReference.bankLocalReferenceInternalPair q B
        ⟨0, by change 0 < (compileAdvice q).s + 11; omega⟩).1.lease ≤
        (compileAdvice q).bankLeaseCap := by
    calc
      (GrantBankReference.bankLocalReferenceInternalPair q B
        ⟨0, by change 0 < (compileAdvice q).s + 11; omega⟩).1.lease =
          Counter.resetClockWaitLease
            ((B.fields ⟨0, by omega⟩).2.2.2) := hrow.2
      _ ≤ (compileAdvice q).bankLeaseCap := by
        have hcap : (B.fields ⟨0, by omega⟩).2.2.2 ≤
            (compileAdvice q).bankLeaseCap := hc 0 (by omega)
        unfold Counter.resetClockWaitLease
        split <;> omega
  calc
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B root).fields ⟨0, by omega⟩).2.2.2 =
        (GrantBankReference.bankLocalReferenceClampedQuad q
          ((GrantBankReference.bankLocalReferenceInternalPair q B
            ⟨0, by change 0 < (compileAdvice q).s + 11; omega⟩).1)).2.2.2 := by
        rw [bankTrialLocalStepField ring root root B hs hf,
          bankTrialLocalFieldRootOutgoing ring root B]
    _ = (GrantBankReference.bankLocalReferenceInternalPair q B
          ⟨0, by change 0 < (compileAdvice q).s + 11; omega⟩).1.lease :=
      bankTrialLocalClampedLease q _ hrawCap
    _ = Counter.resetClockWaitLease
          ((B.fields ⟨0, by omega⟩).2.2.2) := hrow.2

/-- On a root-incoming service, RWAIT either has a positive
successor lease or expires into RESET. -/
theorem bankTrialLocalRootIncomingWaitSafe {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLocalRecoveryCert q B)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RWAIT)
    (hne : e ≠ root)
    (hin : ring.rightNeighbor e = root) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨0, by omega⟩).1 = .RESET ∨
    (((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨0, by omega⟩).1 = .RWAIT ∧
      1 ≤ ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨0, by omega⟩).2.2.2) := by
  have hb : 1 < (compileAdvice q).b := bankTrialLocalWidthLarge q
  have hs : Counter.Support q ring root e := Or.inl hin
  have hsource :
      ¬ (0 < (compileAdvice q).b ∧
        e = Counter.site ring root 0) := by
    intro h
    exact hne (by simpa [Counter.site] using h.2)
  have htarget :
      ¬ (0 < (0 : Nat) ∧
        e = Counter.site ring root (0 - 1)) := by
    intro h
    omega
  have htop :
      ¬ ((0 : Nat) = (compileAdvice q).b ∧
        e = Counter.site ring root (compileAdvice q).b) := by
    intro h
    omega
  have hselected :
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨0, by omega⟩ =
        GrantBankReference.bankLocalReferenceClampedQuad q
          (GrantBankReference.incomingRootBankMap
            (GrantBankReference.bankLocalReferenceCell B
              ⟨0, by omega⟩)) := by
    rw [bankTrialLocalStepField ring root e B hs hc.2.1]
    exact bankTrialLocalSelectedIncoming ring root e B
      ⟨0, by omega⟩ hsource htarget htop ⟨rfl, hin⟩
  have hrow := bankTrialLocalIncomingWaitRow q
    (GrantBankReference.bankLocalReferenceCell B ⟨0, by omega⟩)
    hm (hc.1 0 (by omega))
  by_cases hl : 1 < (B.fields ⟨0, by omega⟩).2.2.2
  · have hlraw :
        1 < (GrantBankReference.bankLocalReferenceCell B
          ⟨0, by omega⟩).lease := by
      change 1 < (B.fields ⟨0, by omega⟩).2.2.2
      exact hl
    have hr := hrow.1 hlraw
    apply Or.inr
    refine ⟨?_, ?_⟩
    · rw [hselected]
      exact hr.1
    · rw [hselected, hr.2]
      omega
  · have hle :
        (GrantBankReference.bankLocalReferenceCell B
          ⟨0, by omega⟩).lease ≤ 1 := by
      change (B.fields ⟨0, by omega⟩).2.2.2 ≤ 1
      omega
    apply Or.inl
    rw [hselected]
    exact (hrow.2 hle).1


/-- The least positive outward front is either already at digit one
(with RR), or digit one lies in the cleared prefix (with E). -/
theorem bankTrialLocalFrontOutFirstToken {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (j : Nat)
    (hfront : BankTrialLocalFrontOut q B j) :
    (B.fields ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.2.1 = .E ∨
    (B.fields ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.2.1 = .RR := by
  obtain ⟨hjb, hjpos, _, htok, hpre⟩ := hfront
  by_cases hfirst : j = 1
  · subst j
    exact Or.inr htok
  · apply Or.inl
    have hlt : 1 < j := by omega
    exact (hpre 1 (by omega) hlt (by omega)).2

/-- In a returning front past digit one, the first digit
remains empty until the actual last return service. -/
theorem bankTrialLocalFrontBackFirstEmpty {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (j : Nat)
    (hfront : BankTrialLocalFrontBack q B j)
    (hj : 1 < j) :
    (B.fields ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.2.1 = .E := by
  obtain ⟨_, _, _, _, hother⟩ := hfront
  exact (hother 1 (by omega) (by omega) (by omega)).2

/-- A certified RWAIT root served on an edge whose outgoing
first-digit token is E or RR remains a valid waiting root with
positive lease, unless its watchdog expires into RESET.
This is a root-only theorem; it does not assume site injectivity. -/
theorem bankTrialLocalRootWaitSafe {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLocalRecoveryCert q B)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RWAIT)
    (hfirst :
      (B.fields ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.2.1 = .E ∨
      (B.fields ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.2.1 = .RR) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨0, by omega⟩).1 = .RESET ∨
    (((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨0, by omega⟩).1 = .RWAIT ∧
      1 ≤ ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨0, by omega⟩).2.2.2) := by
  have holdPositive :
      1 ≤ (B.fields ⟨0, by omega⟩).2.2.2 := by
    rcases hc.2.2 with hr | hw
    · rw [hm] at hr
      cases hr
    · exact hw.2.1
  by_cases he : e = root
  · subst e
    have hmode := bankTrialLocalRootOutgoingWaitMode
      ring root B hc.2.1 hm hfirst
    have hlease := bankTrialLocalRootOutgoingWaitLease
      ring root B hc.2.1 hc.1 hm hfirst
    by_cases hl :
        1 < (B.fields ⟨0, by omega⟩).2.2.2
    · apply Or.inr
      refine ⟨?_, ?_⟩
      · rw [hmode]
        exact if_pos hl
      · rw [hlease]
        simp only [Counter.resetClockWaitLease, if_pos hl]
        omega
    · apply Or.inl
      rw [hmode]
      exact if_neg hl
  · by_cases hin : ring.rightNeighbor e = root
    · exact bankTrialLocalRootIncomingWaitSafe
        ring root e B hc hm he hin
    · have hframe := bankTrialLocalRootNonincidentFrame
        ring root e B hc.2.1 he hin
      apply Or.inr
      refine ⟨?_, ?_⟩
      · rw [hframe]
        exact hm
      · rw [hframe]
        exact holdPositive


/-- A digit with zero/empty old data at itself and both available
internal neighbors remains zero/empty after *any* scheduler edge.
Every logical selector is checked separately, so the result does
not assume that the site map is injective on short rings. -/
theorem bankTrialLocalEmptyDigitSafe {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (i : Nat) (hi : 2 ≤ i) (hib : i ≤ (compileAdvice q).b)
    (hprev :
      (B.fields ⟨i - 1, by omega⟩).2.1 = false ∧
      (B.fields ⟨i - 1, by omega⟩).2.2.1 = .E)
    (hhere :
      (B.fields ⟨i, Nat.lt_succ_of_le hib⟩).2.1 = false ∧
      (B.fields ⟨i, Nat.lt_succ_of_le hib⟩).2.2.1 = .E)
    (hnext : ∀ hlt : i < (compileAdvice q).b,
      (B.fields ⟨i + 1, Nat.succ_lt_succ hlt⟩).2.1 = false ∧
      (B.fields ⟨i + 1, Nat.succ_lt_succ hlt⟩).2.2.1 = .E) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields
      ⟨i, Nat.lt_succ_of_le hib⟩).2.1 = false ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields
      ⟨i, Nat.lt_succ_of_le hib⟩).2.2.1 = .E := by
  classical
  by_cases hs : Counter.Support q ring root e
  · rw [bankTrialLocalStepField ring root e B hs hf]
    by_cases hsource :
        i < (compileAdvice q).b ∧
          e = Counter.site ring root i
    · rw [bankTrialLocalSelectedSource ring root e B
        ⟨i, Nat.lt_succ_of_le hib⟩ hsource]
      exact (bankTrialLocalInternalEmptyData B
        ⟨i, hsource.1⟩ (by change 1 ≤ i; omega)
        hhere (hnext hsource.1)).1
    · by_cases htarget :
          0 < i ∧ e = Counter.site ring root (i - 1)
      · rw [bankTrialLocalSelectedResponder ring root e B
          ⟨i, Nat.lt_succ_of_le hib⟩ hsource htarget]
        have hfin :
            (⟨i - 1 + 1, by omega⟩ :
              Fin ((compileAdvice q).b + 1)) =
              ⟨i, Nat.lt_succ_of_le hib⟩ := Fin.ext (by
                show i - 1 + 1 = i
                omega)
        have hhere' :
            (B.fields ⟨i - 1 + 1, by omega⟩).2.1 = false ∧
            (B.fields ⟨i - 1 + 1, by omega⟩).2.2.1 = .E := by
          rw [hfin]
          exact hhere
        exact (bankTrialLocalInternalEmptyData B
          ⟨i - 1, by omega⟩
          (by change 1 ≤ i - 1; omega) hprev hhere').2
      · by_cases htop :
            i = (compileAdvice q).b ∧
              e = Counter.site ring root (compileAdvice q).b
        · rw [bankTrialLocalSelectedTop ring root e B
            ⟨i, Nat.lt_succ_of_le hib⟩ hsource htarget htop]
          have hnotIR :
              (GrantBankReference.bankLocalReferenceCell B
                ⟨i, Nat.lt_succ_of_le hib⟩).tok ≠ .IR := by
            intro hir
            have he :
                (B.fields ⟨i, Nat.lt_succ_of_le hib⟩).2.2.1 =
                  .IR := hir
            rw [hhere.2] at he
            cases he
          have htrow := bankTrialLocalTopDataRow q
            (GrantBankReference.bankLocalReferenceCell B
              ⟨i, Nat.lt_succ_of_le hib⟩) hnotIR
          exact ⟨htrow.1.trans hhere.1, htrow.2.trans hhere.2⟩
        · have hincoming :
              ¬ (i = 0 ∧ ring.rightNeighbor e = root) := by
            intro h
            omega
          rw [bankTrialLocalSelectedFrame ring root e B
            ⟨i, Nat.lt_succ_of_le hib⟩
            hsource htarget htop hincoming]
          exact hhere
  · rw [bankTrialLocalStepOutside ring root e B hs]
    exact hhere


/-- Every outward-sweep prefix slot at distance at least two from
the RR front stays cleared under any physical scheduler letter. -/
theorem bankTrialLocalFrontOutDeepPrefix {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j i : Nat) (hfront : BankTrialLocalFrontOut q B j)
    (hi : 2 ≤ i) (hdeep : i + 1 < j)
    (hib : i ≤ (compileAdvice q).b) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨i, Nat.lt_succ_of_le hib⟩).2.1 =
        false ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨i, Nat.lt_succ_of_le hib⟩).2.2.1 =
        .E := by
  obtain ⟨hjb, _, _, _, hprefix⟩ := hfront
  exact bankTrialLocalEmptyDigitSafe ring root e B hf i hi hib
    (hprefix (i - 1) (by omega) (by omega) (by omega))
    (hprefix i (by omega) (by omega) hib)
    (fun _ => hprefix (i + 1) (by omega) hdeep (by omega))

/-- A returning sweep cannot disturb a remote empty digit whose
two logical neighbors are also disjoint from the unique RL front. -/
theorem bankTrialLocalFrontBackFarDigit {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j i : Nat) (hfront : BankTrialLocalFrontBack q B j)
    (hi : 2 ≤ i) (hib : i ≤ (compileAdvice q).b)
    (hleft : i + 1 ≠ j) (hhere : i ≠ j)
    (hright : i - 1 ≠ j) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨i, Nat.lt_succ_of_le hib⟩).2.1 =
        false ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨i, Nat.lt_succ_of_le hib⟩).2.2.1 =
        .E := by
  obtain ⟨_, _, _, _, hother⟩ := hfront
  exact bankTrialLocalEmptyDigitSafe ring root e B hf i hi hib
    (hother (i - 1) (by omega) (by omega) hright)
    (hother i (by omega) hib hhere)
    (fun hil => hother (i + 1) (by omega) (by omega) hleft)


/-- Completing the outward case now reduces exactly to exhibiting
a successor F/G array front. The watchdog and lease proof are
unconditional and independent of short-ring site multiplicities. -/
theorem bankTrialLocalRecoveryCertStepOutwardOfArray {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLocalRecoveryCert q B)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RWAIT)
    (j : Nat) (hout : BankTrialLocalFrontOut q B j)
    (harray :
      (∃ k : Nat, BankTrialLocalFrontOut q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e) k) ∨
      (∃ k : Nat, BankTrialLocalFrontBack q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e) k)) :
    BankTrialLocalRecoveryCert q
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) := by
  rcases bankTrialLocalRootWaitSafe ring root e B hc hm
      (bankTrialLocalFrontOutFirstToken B j hout) with hr | hw
  · exact bankTrialLocalRecoveryNextReset ring root e B hc hr
  · exact bankTrialLocalRecoveryNextWait
      ring root e B hc hw.1 hw.2 harray

/-- Returning G_j with j>1 likewise reduces precisely to full-array
G-front preservation; the root cannot consume a return at digit one
before the front reaches it. -/
theorem bankTrialLocalRecoveryCertStepReturnOfArray {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLocalRecoveryCert q B)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RWAIT)
    (j : Nat) (hback : BankTrialLocalFrontBack q B j)
    (hj : 1 < j)
    (harray : ∃ k : Nat, BankTrialLocalFrontBack q
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) k) :
    BankTrialLocalRecoveryCert q
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) := by
  rcases bankTrialLocalRootWaitSafe ring root e B hc hm
      (Or.inl (bankTrialLocalFrontBackFirstEmpty B j hback hj)) with
    hr | hw
  · exact bankTrialLocalRecoveryNextReset ring root e B hc hr
  · exact bankTrialLocalRecoveryNextWait
      ring root e B hc hw.1 hw.2 (Or.inr harray)

/-- Exact last logical cases for the currently defined certificate
premise. Besides general F_j and G_j>1, G_1 on a non-root scheduler
letter must be handled separately: the imported G_1 theorem assumes
e=root. These are mathematical premises, NOT axioms. -/
theorem bankTrialLocalRecoveryCertStepPremiseOfCases {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) (hn : 2 ≤ n)
    (hout : ∀ (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (e : Fin n) (j : Nat),
      BankTrialLocalRecoveryCert q B →
      (B.fields ⟨0, by omega⟩).1 = .RWAIT →
      BankTrialLocalFrontOut q B j →
      (BankTrialLocalRecoveryCert q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e) ∨
       BankTrialLocalClean q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e)))
    (hreturn : ∀ (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (e : Fin n) (j : Nat),
      BankTrialLocalRecoveryCert q B →
      (B.fields ⟨0, by omega⟩).1 = .RWAIT →
      1 < j → BankTrialLocalFrontBack q B j →
      (BankTrialLocalRecoveryCert q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e) ∨
       BankTrialLocalClean q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e)))
    (hfirstOff : ∀ (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (e : Fin n),
      BankTrialLocalRecoveryCert q B →
      (B.fields ⟨0, by omega⟩).1 = .RWAIT →
      BankTrialLocalFrontBack q B 1 → e ≠ root →
      (BankTrialLocalRecoveryCert q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e) ∨
       BankTrialLocalClean q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e))) :
    BankTrialLocalRecoveryCertStepPremise (q := q) ring root := by
  intro B e hc
  rcases hc.2.2 with hr | hw
  · exact bankTrialLocalRecoveryCertStepReset ring root e hn B hc hr
  · obtain ⟨hm, _, _, hfront⟩ := hw
    rcases hfront with hfo | hfb
    · obtain ⟨j, hj⟩ := hfo
      exact hout B e j hc hm hj
    · obtain ⟨j, hj⟩ := hfb
      by_cases hfirst : j = 1
      · subst j
        by_cases he : e = root
        · subst e
          exact bankTrialLocalRecoveryCertStepGOne
            ring root hn B hc hm hj
        · exact hfirstOff B e hc hm hj he
      · have hgt : 1 < j := by
          obtain ⟨_, hjpos, _, _, _⟩ := hj
          omega
        exact hreturn B e j hc hm hgt hj


/-- G_j: on an edge *leaving* an RL front, the source keeps RL
and its zero/empty right neighbor stays zero/empty. The matching
responder cannot also be a source on an n>=2 short ring. -/
theorem bankTrialLocalReturnSourcePair {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hn : 2 ≤ n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Nat) (hback : BankTrialLocalFrontBack q B j)
    (hj : j < (compileAdvice q).b)
    (he : e = Counter.site ring root j) :
    (((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨j, by omega⟩).2.1 = false ∧
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨j, by omega⟩).2.2.1 = .RL) ∧
    (((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨j + 1, by omega⟩).2.1 = false ∧
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨j + 1, by omega⟩).2.2.1 = .E) := by
  obtain ⟨hjb, hjpos, hbit, htok, hother⟩ := hback
  have hright :
      (B.fields ⟨j + 1, by omega⟩).2.1 = false ∧
      (B.fields ⟨j + 1, by omega⟩).2.2.1 = .E :=
    hother (j + 1) (by omega) (by omega) (by omega)
  have hs : Counter.Support q ring root e :=
    Or.inr ⟨j, hjb, he⟩
  have hrow := bankTrialLocalRawReturnSourceHold
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j + 1, by omega⟩)
    (by change 1 ≤ j; exact hjpos)
    (by change j < (compileAdvice q).b; exact hj)
    rfl htok hbit hright.2 hright.1
  have hleftData := bankTrialLocalClampedData q
    ((GrantBankReference.bankLocalReferenceInternalPair q B
      ⟨j, hj⟩).1)
  have hrightData := bankTrialLocalClampedData q
    ((GrantBankReference.bankLocalReferenceInternalPair q B
      ⟨j, hj⟩).2)
  have hsource :
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨j, by omega⟩ =
        GrantBankReference.bankLocalReferenceClampedQuad q
          ((GrantBankReference.bankLocalReferenceInternalPair q B
            ⟨j, hj⟩).1) := by
    rw [bankTrialLocalStepField ring root e B hs hf]
    exact bankTrialLocalSelectedSource ring root e B
      ⟨j, by omega⟩ ⟨hj, he⟩
  have hnotSource :
      ¬ (j + 1 < (compileAdvice q).b ∧
          e = Counter.site ring root (j + 1)) := by
    intro hx
    apply bankTrialLocalAdjacentSitesDistinct ring root hn j
    exact he.symm.trans hx.2
  have hsub : j + 1 - 1 = j := by omega
  have htarget :
      0 < j + 1 ∧ e = Counter.site ring root (j + 1 - 1) := by
    refine ⟨by omega, ?_⟩
    rw [hsub]
    exact he
  have hresponder :
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨j + 1, by omega⟩ =
        GrantBankReference.bankLocalReferenceClampedQuad q
          ((GrantBankReference.bankLocalReferenceInternalPair q B
            ⟨j, hj⟩).2) := by
    rw [bankTrialLocalStepField ring root e B hs hf]
    have hselected := bankTrialLocalSelectedResponder ring root e B
      ⟨j + 1, by omega⟩ hnotSource htarget
    simpa only [Fin.val_mk, hsub] using hselected
  rw [hsource, hresponder]
  exact ⟨⟨hleftData.1.trans hrow.2.1,
      hleftData.2.trans hrow.1⟩,
    ⟨hrightData.1.trans hrow.2.2.2,
      hrightData.2.trans hrow.2.2.1⟩⟩


/-- A positive-indexed empty digit is safe without any assumption
on its left neighbor, provided the scheduler letter does not select
that left neighbor as its responder source. -/
theorem bankTrialLocalEmptyDigitNoResponder {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (i : Nat) (hi : 1 ≤ i) (hib : i ≤ (compileAdvice q).b)
    (hhere :
      (B.fields ⟨i, Nat.lt_succ_of_le hib⟩).2.1 = false ∧
      (B.fields ⟨i, Nat.lt_succ_of_le hib⟩).2.2.1 = .E)
    (hnext : ∀ hlt : i < (compileAdvice q).b,
      (B.fields ⟨i + 1, Nat.succ_lt_succ hlt⟩).2.1 = false ∧
      (B.fields ⟨i + 1, Nat.succ_lt_succ hlt⟩).2.2.1 = .E)
    (hnotResponder : e ≠ Counter.site ring root (i - 1)) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨i, Nat.lt_succ_of_le hib⟩).2.1 =
        false ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨i, Nat.lt_succ_of_le hib⟩).2.2.1 =
        .E := by
  classical
  by_cases hs : Counter.Support q ring root e
  · rw [bankTrialLocalStepField ring root e B hs hf]
    by_cases hsource :
        i < (compileAdvice q).b ∧
          e = Counter.site ring root i
    · rw [bankTrialLocalSelectedSource ring root e B
        ⟨i, Nat.lt_succ_of_le hib⟩ hsource]
      exact (bankTrialLocalInternalEmptyData B
        ⟨i, hsource.1⟩ (by change 1 ≤ i; exact hi)
        hhere (hnext hsource.1)).1
    · have htarget :
          ¬ (0 < i ∧ e = Counter.site ring root (i - 1)) := by
        intro h
        exact hnotResponder h.2
      by_cases htop :
          i = (compileAdvice q).b ∧
            e = Counter.site ring root (compileAdvice q).b
      · rw [bankTrialLocalSelectedTop ring root e B
          ⟨i, Nat.lt_succ_of_le hib⟩ hsource htarget htop]
        have hnotIR :
            (GrantBankReference.bankLocalReferenceCell B
              ⟨i, Nat.lt_succ_of_le hib⟩).tok ≠ .IR := by
          intro hir
          have htok :
              (B.fields ⟨i, Nat.lt_succ_of_le hib⟩).2.2.1 =
                .IR := hir
          rw [hhere.2] at htok
          cases htok
        have htopRow := bankTrialLocalTopDataRow q
          (GrantBankReference.bankLocalReferenceCell B
            ⟨i, Nat.lt_succ_of_le hib⟩) hnotIR
        exact ⟨htopRow.1.trans hhere.1,
          htopRow.2.trans hhere.2⟩
      · have hincoming :
            ¬ (i = 0 ∧ ring.rightNeighbor e = root) := by
          intro h
          omega
        rw [bankTrialLocalSelectedFrame ring root e B
          ⟨i, Nat.lt_succ_of_le hib⟩
          hsource htarget htop hincoming]
        exact hhere
  · rw [bankTrialLocalStepOutside ring root e B hs]
    exact hhere


/-- Under a G_1 front, all digits numbered at least two stay
zero/empty on every service. Digit two uses the separate RL-source
HOLD row when necessary; farther digits use empty-neighbor framing. -/
theorem bankTrialLocalGOneAllOtherDigits {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n) (hn : 2 ≤ n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hback : BankTrialLocalFrontBack q B 1) :
    ∀ i : Nat, 2 ≤ i → (hib : i ≤ (compileAdvice q).b) →
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields
        ⟨i, Nat.lt_succ_of_le hib⟩).2.1 = false ∧
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields
        ⟨i, Nat.lt_succ_of_le hib⟩).2.2.1 = .E := by
  have hbackCopy := hback
  obtain ⟨_, _, _, _, hother⟩ := hbackCopy
  intro i hi hib
  by_cases htwo : i = 2
  · subst i
    by_cases he : e = Counter.site ring root 1
    · exact (bankTrialLocalReturnSourcePair ring root e hn
        B hf 1 hback (bankTrialLocalWidthLarge q) he).2
    · have hhere :
          (B.fields ⟨2, by omega⟩).2.1 = false ∧
          (B.fields ⟨2, by omega⟩).2.2.1 = .E :=
        hother 2 (by omega) (by omega) (by omega)
      have hnext :
          ∀ hlt : 2 < (compileAdvice q).b,
          (B.fields ⟨2 + 1, Nat.succ_lt_succ hlt⟩).2.1 = false ∧
          (B.fields ⟨2 + 1, Nat.succ_lt_succ hlt⟩).2.2.1 = .E := by
        intro hlt
        exact hother (2 + 1) (by omega) (by omega) (by omega)
      exact bankTrialLocalEmptyDigitNoResponder ring root e B
        hf 2 (by omega) (by omega) hhere hnext (by
          change e ≠ Counter.site ring root 1
          exact he)
  · have hthree : 3 ≤ i := by omega
    exact bankTrialLocalEmptyDigitSafe ring root e B
      hf i hi hib
      (hother (i - 1) (by omega) (by omega) (by omega))
      (hother i (by omega) hib (by omega))
      (fun _ => hother (i + 1) (by omega) (by omega) (by omega))

/-- The only G_1 active digit cannot lose its RL except on the
root-outgoing acceptance edge. In particular, incoming watchdog
events on short rings do not consume the return token. -/
theorem bankTrialLocalGOneDigitOneOff {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n) (hn : 2 ≤ n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hback : BankTrialLocalFrontBack q B 1)
    (hne : e ≠ root) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields
      ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.1 =
        false ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields
      ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.2.1 =
        .RL := by
  have hbackCopy := hback
  obtain ⟨_, _, hbit, htok, _⟩ := hbackCopy
  by_cases he : e = Counter.site ring root 1
  · exact (bankTrialLocalReturnSourcePair ring root e hn
      B hf 1 hback (bankTrialLocalWidthLarge q) he).1
  · by_cases hs : Counter.Support q ring root e
    · rw [bankTrialLocalStepField ring root e B hs hf]
      have hsource :
          ¬ (1 < (compileAdvice q).b ∧
            e = Counter.site ring root 1) := by
        intro h
        exact he h.2
      have htarget :
          ¬ (0 < (1 : Nat) ∧
            e = Counter.site ring root (1 - 1)) := by
        intro h
        exact hne (by simpa [Counter.site] using h.2)
      have htop :
          ¬ ((1 : Nat) = (compileAdvice q).b ∧
            e = Counter.site ring root (compileAdvice q).b) := by
        intro h
        have hb := bankTrialLocalWidthLarge q
        omega
      have hincoming :
          ¬ ((1 : Nat) = 0 ∧
            ring.rightNeighbor e = root) := by
        intro h
        omega
      rw [bankTrialLocalSelectedFrame ring root e B
        ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩
        hsource htarget htop hincoming]
      exact ⟨hbit, htok⟩
    · rw [bankTrialLocalStepOutside ring root e B hs]
      exact ⟨hbit, htok⟩

/-- A G_1 front stays certified on every NON-root scheduler
letter. The actual root-outgoing acceptance is the separate
G_1-to-Clean theorem. -/
theorem bankTrialLocalRecoveryCertStepGOneOff {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n) (hn : 2 ≤ n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLocalRecoveryCert q B)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RWAIT)
    (hback : BankTrialLocalFrontBack q B 1)
    (hne : e ≠ root) :
    BankTrialLocalRecoveryCert q
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) := by
  have hmode :
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨0, by omega⟩).1 = .RESET ∨
      (((GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨0, by omega⟩).1 = .RWAIT ∧
        1 ≤ ((GrantBankReference.bankLocalReferenceStepClamped
          ring root B e).fields ⟨0, by omega⟩).2.2.2) := by
    by_cases hin : ring.rightNeighbor e = root
    · exact bankTrialLocalRootIncomingWaitSafe
        ring root e B hc hm hne hin
    · have hframe := bankTrialLocalRootNonincidentFrame
        ring root e B hc.2.1 hne hin
      have hpositive : 1 ≤ (B.fields ⟨0, by omega⟩).2.2.2 := by
        rcases hc.2.2 with hreset | hwait
        · rw [hm] at hreset
          cases hreset
        · exact hwait.2.1
      apply Or.inr
      refine ⟨?_, ?_⟩
      · rw [hframe]
        exact hm
      · rw [hframe]
        exact hpositive
  rcases hmode with hreset | hwait
  · exact bankTrialLocalRecoveryNextReset ring root e B hc hreset
  · apply bankTrialLocalRecoveryNextWait
      ring root e B hc hwait.1 hwait.2
    apply Or.inr
    refine ⟨1, ?_⟩
    have hb : 1 ≤ (compileAdvice q).b := by
      have hh := bankTrialLocalWidthLarge q
      omega
    have hone := bankTrialLocalGOneDigitOneOff
      ring root e hn B hc.2.1 hback hne
    refine ⟨hb, Nat.le_refl _, hone.1, hone.2, ?_⟩
    intro i hi hib hneq
    have hge : 2 ≤ i := by omega
    exact bankTrialLocalGOneAllOtherDigits
      ring root e hn B hc.2.1 hback i hge hib


/-- Having discharged the root RESET case and BOTH G_1 edge
orientations, the entire original recovery certificate-step premise
reduces to precisely the two named outward/return families. -/
theorem bankTrialLocalRecoveryCertStepPremiseOfMainCases {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) (hn : 2 ≤ n)
    (hout : ∀ (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (e : Fin n) (j : Nat),
      BankTrialLocalRecoveryCert q B →
      (B.fields ⟨0, by omega⟩).1 = .RWAIT →
      BankTrialLocalFrontOut q B j →
      (BankTrialLocalRecoveryCert q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e) ∨
       BankTrialLocalClean q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e)))
    (hreturn : ∀ (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (e : Fin n) (j : Nat),
      BankTrialLocalRecoveryCert q B →
      (B.fields ⟨0, by omega⟩).1 = .RWAIT →
      1 < j → BankTrialLocalFrontBack q B j →
      (BankTrialLocalRecoveryCert q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e) ∨
       BankTrialLocalClean q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e))) :
    BankTrialLocalRecoveryCertStepPremise (q := q) ring root := by
  exact bankTrialLocalRecoveryCertStepPremiseOfCases
    ring root hn hout hreturn (by
      intro B e hc hm hfront hne
      exact Or.inl (bankTrialLocalRecoveryCertStepGOneOff
        ring root e hn B hc hm hfront hne))

end L3

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
Repaired returning-front family G_j, j > 1.
All proofs concern the clamped local reference on the original
physical Fin n edge alphabet. Nonadjacent logical indices may alias.
-/

/-- The physical root-outgoing row preserves an empty first digit
while the root is RWAIT. -/
theorem bankTrialLocalReturnRootFirstEmpty {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) (hn : 2 ≤ n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RWAIT)
    (hbit :
      (B.fields ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.1 = false)
    (htok :
      (B.fields ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.2.1 = .E) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B root).fields ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.1 = false ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B root).fields ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.2.1 = .E := by
  have hs : Counter.Support q ring root root :=
    Or.inr ⟨0, Nat.zero_le _, rfl⟩
  have hrow := bankTrialLocalRawRootWaitEmpty
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨0, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩)
    rfl rfl rfl hm (bankTrialLocalWidthLarge q) htok hbit
  have hdata := bankTrialLocalClampedData q
    ((GrantBankReference.bankLocalReferenceInternalPair q B
      ⟨0, by change 0 < (compileAdvice q).s + 11; omega⟩).2)
  rw [bankTrialLocalStepField ring root root B hs hf,
    bankTrialLocalFieldOneOutgoing ring root hn B]
  exact ⟨hdata.1.trans hrow.2, hdata.2.trans hrow.1⟩

/-- A digit which is neither a selected internal endpoint nor
the selected top source is fully framed. -/
theorem bankTrialLocalReturnDigitFrame {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (i : Nat) (hi : 1 ≤ i) (hib : i ≤ (compileAdvice q).b)
    (hsource : e ≠ Counter.site ring root i)
    (hresponder : e ≠ Counter.site ring root (i - 1))
    (htop : i = (compileAdvice q).b →
      e ≠ Counter.site ring root (compileAdvice q).b) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨i, Nat.lt_succ_of_le hib⟩ =
      B.fields ⟨i, Nat.lt_succ_of_le hib⟩ := by
  classical
  have hx :
      ¬ (i < (compileAdvice q).b ∧
        e = Counter.site ring root i) := by
    intro h
    exact hsource h.2
  have hy :
      ¬ (0 < i ∧
        e = Counter.site ring root (i - 1)) := by
    intro h
    exact hresponder h.2
  have ht :
      ¬ (i = (compileAdvice q).b ∧
        e = Counter.site ring root (compileAdvice q).b) := by
    intro h
    exact (htop h.1) h.2
  have hr :
      ¬ (i = 0 ∧ ring.rightNeighbor e = root) := by
    intro h
    omega
  by_cases hs : Counter.Support q ring root e
  · rw [bankTrialLocalStepField ring root e B hs hf]
    exact bankTrialLocalSelectedFrame ring root e B
      ⟨i, Nat.lt_succ_of_le hib⟩ hx hy ht hr
  · rw [bankTrialLocalStepOutside ring root e B hs]

/-- When j is beyond digit two, digit one remains empty under
every scheduler letter. The source may be the root, and the
logical site map need not be injective. -/
theorem bankTrialLocalReturnFirstSafe {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n) (hn : 2 ≤ n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RWAIT)
    (j : Nat) (hback : BankTrialLocalFrontBack q B j)
    (hj : 2 < j) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.1 = false ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.2.1 = .E := by
  obtain ⟨_, _, _, _, hother⟩ := hback
  have hfirst :
      (B.fields ⟨1, by omega⟩).2.1 = false ∧
      (B.fields ⟨1, by omega⟩).2.2.1 = .E :=
    hother 1 (by omega) (by omega) (by omega)
  have hsecond :
      (B.fields ⟨2, by omega⟩).2.1 = false ∧
      (B.fields ⟨2, by omega⟩).2.2.1 = .E :=
    hother 2 (by omega) (by omega) (by omega)
  by_cases he : e = root
  · subst e
    exact bankTrialLocalReturnRootFirstEmpty ring root hn
      B hf hm hfirst.1 hfirst.2
  · exact bankTrialLocalEmptyDigitNoResponder
      ring root e B hf 1 (by omega) (by omega)
      hfirst (fun _ => hsecond)
      (by simpa only [Nat.sub_self, Counter.site] using he)

/-- With an RL at j > 1, a scheduler edge other than the edge
immediately left of j preserves the empty first digit. -/
theorem bankTrialLocalReturnFirstOff {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n) (hn : 2 ≤ n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RWAIT)
    (j : Nat) (hback : BankTrialLocalFrontBack q B j)
    (hj : 1 < j)
    (hne : e ≠ Counter.site ring root (j - 1)) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.1 = false ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.2.1 = .E := by
  by_cases htwo : j = 2
  · have hcopy := hback
    obtain ⟨_, _, _, _, hother⟩ := hcopy
    have hfirst :
        (B.fields ⟨1, by omega⟩).2.1 = false ∧
        (B.fields ⟨1, by omega⟩).2.2.1 = .E :=
      hother 1 (by omega) (by omega) (by omega)
    have hnotOne : e ≠ Counter.site ring root 1 := by
      have hh : j - 1 = 1 := by omega
      rw [hh] at hne
      exact hne
    by_cases he : e = root
    · subst e
      exact bankTrialLocalReturnRootFirstEmpty ring root hn
        B hf hm hfirst.1 hfirst.2
    · have hframe := bankTrialLocalReturnDigitFrame
        ring root e B hf 1 (by omega) (by omega)
        hnotOne (by simpa only [Nat.sub_self, Counter.site] using he)
        (by
          intro hb
          have hw := bankTrialLocalWidthLarge q
          omega)
      rw [hframe]
      exact hfirst
  · have hlarge : 2 < j := by omega
    exact bankTrialLocalReturnFirstSafe ring root e hn
      B hf hm j hback hlarge

/-- Digit j-1 is empty unless its own outgoing edge is selected.
Its incoming edge has two empty endpoints, even if this physical
letter simultaneously updates other logical sites. -/
theorem bankTrialLocalReturnPredecessorSafe {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Nat) (hback : BankTrialLocalFrontBack q B j)
    (hj : 2 < j)
    (hne : e ≠ Counter.site ring root (j - 1)) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨j - 1, by rcases hback with ⟨hjb, _⟩; omega⟩).2.1 =
      false ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨j - 1, by rcases hback with ⟨hjb, _⟩; omega⟩).2.2.1 =
      .E := by
  have hcopy := hback
  obtain ⟨hjb, _, _, _, hother⟩ := hcopy
  have hbefore :
      (B.fields ⟨j - 2, by omega⟩).2.1 = false ∧
      (B.fields ⟨j - 2, by omega⟩).2.2.1 = .E :=
    hother (j - 2) (by omega) (by omega) (by omega)
  have hhere :
      (B.fields ⟨j - 1, by omega⟩).2.1 = false ∧
      (B.fields ⟨j - 1, by omega⟩).2.2.1 = .E :=
    hother (j - 1) (by omega) (by omega) (by omega)
  by_cases he : e = Counter.site ring root (j - 2)
  · have hbound : j - 2 < (compileAdvice q).b := by omega
    have hindex : j - 2 + 1 = j - 1 := by omega
    have hhere' :
        (B.fields ⟨j - 2 + 1, by omega⟩).2.1 = false ∧
        (B.fields ⟨j - 2 + 1, by omega⟩).2.2.1 = .E := by
      simpa only [hindex] using hhere
    have hrow := bankTrialLocalInternalEmptyData B
      ⟨j - 2, hbound⟩ (by change 1 ≤ j - 2; omega) hbefore hhere'
    have hs : Counter.Support q ring root e :=
      Or.inr ⟨j - 2, by omega, he⟩
    have hx :
        ¬ (j - 1 < (compileAdvice q).b ∧
          e = Counter.site ring root (j - 1)) := by
      intro h
      exact hne h.2
    have hy :
        0 < j - 1 ∧
          e = Counter.site ring root (j - 1 - 1) := by
      refine ⟨by omega, ?_⟩
      have hsub : j - 1 - 1 = j - 2 := by omega
      rw [hsub]
      exact he
    rw [bankTrialLocalStepField ring root e B hs hf,
      bankTrialLocalSelectedResponder ring root e B
        ⟨j - 1, by omega⟩ hx hy]
    have hfin :
        (⟨j - 1 - 1, by omega⟩ :
          Fin (compileAdvice q).b) =
          ⟨j - 2, hbound⟩ := Fin.ext (by show j - 1 - 1 = j - 2; omega)
    rw [hfin]
    exact hrow.2
  · have hnotResponder :
        e ≠ Counter.site ring root (j - 1 - 1) := by
      intro h
      have hsub : j - 1 - 1 = j - 2 := by omega
      rw [hsub] at h
      exact he h
    have hframe := bankTrialLocalReturnDigitFrame
      ring root e B hf (j - 1) (by omega) (by omega)
      hne hnotResponder (by
        intro hh
        omega)
    rw [hframe]
    exact hhere

/-- The digit right of a returning RL stays empty. A selected
outgoing front edge uses the literal RL-source HOLD pair; every
other letter avoids that digit's responder selector. -/
theorem bankTrialLocalReturnSuccessorSafe {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n) (hn : 2 ≤ n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Nat) (hback : BankTrialLocalFrontBack q B j)
    (hj : j < (compileAdvice q).b) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨j + 1, by omega⟩).2.1 =
      false ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨j + 1, by omega⟩).2.2.1 =
      .E := by
  have hcopy := hback
  obtain ⟨_, _, _, _, hother⟩ := hcopy
  by_cases he : e = Counter.site ring root j
  · exact (bankTrialLocalReturnSourcePair ring root e hn
      B hf j hback hj he).2
  · have hhere :
        (B.fields ⟨j + 1, by omega⟩).2.1 = false ∧
        (B.fields ⟨j + 1, by omega⟩).2.2.1 = .E :=
      hother (j + 1) (by omega) (by omega) (by omega)
    have hnext :
        ∀ hlt : j + 1 < (compileAdvice q).b,
          (B.fields ⟨j + 1 + 1,
            Nat.succ_lt_succ hlt⟩).2.1 = false ∧
          (B.fields ⟨j + 1 + 1,
            Nat.succ_lt_succ hlt⟩).2.2.1 = .E := by
      intro hlt
      exact hother (j + 1 + 1) (by omega) (by omega)
        (by omega)
    have hnotResponder :
        e ≠ Counter.site ring root (j + 1 - 1) := by
      have hsub : j + 1 - 1 = j := by omega
      rw [hsub]
      exact he
    exact bankTrialLocalEmptyDigitNoResponder ring root e
      B hf (j + 1) (by omega) (by omega)
      hhere hnext hnotResponder

/-- If the return edge immediately left of j is not selected,
the old RL and its zero bit remain at j. Handles the top unary
selector j=b as a separate branch. -/
theorem bankTrialLocalReturnFrontSafe {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n) (hn : 2 ≤ n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Nat) (hback : BankTrialLocalFrontBack q B j)
    (hne : e ≠ Counter.site ring root (j - 1)) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨j, by rcases hback with ⟨hjb, _⟩; omega⟩).2.1 = false ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨j, by rcases hback with ⟨hjb, _⟩; omega⟩).2.2.1 = .RL := by
  have hcopy := hback
  obtain ⟨hjb, hjpos, hbit, htok, _⟩ := hcopy
  by_cases he : e = Counter.site ring root j
  · by_cases hjlt : j < (compileAdvice q).b
    · exact (bankTrialLocalReturnSourcePair ring root e hn
        B hf j hback hjlt he).1
    · have hjtop : j = (compileAdvice q).b := by omega
      have hs : Counter.Support q ring root e :=
        Or.inr ⟨j, hjb, he⟩
      have hx :
          ¬ (j < (compileAdvice q).b ∧
            e = Counter.site ring root j) := by
        intro hh
        exact hjlt hh.1
      have hy :
          ¬ (0 < j ∧
            e = Counter.site ring root (j - 1)) := by
        intro hh
        exact hne hh.2
      have ht :
          j = (compileAdvice q).b ∧
            e = Counter.site ring root (compileAdvice q).b := by
        refine ⟨hjtop, ?_⟩
        rw [← hjtop]
        exact he
      rw [bankTrialLocalStepField ring root e B hs hf,
        bankTrialLocalSelectedTop ring root e B
          ⟨j, by omega⟩ hx hy ht]
      have hnotIR :
          (GrantBankReference.bankLocalReferenceCell B
            ⟨j, by omega⟩).tok ≠ .IR := by
        intro h
        have hbad :
            (B.fields ⟨j, by omega⟩).2.2.1 = .IR := h
        rw [htok] at hbad
        cases hbad
      have hrow := bankTrialLocalTopDataRow q
        (GrantBankReference.bankLocalReferenceCell B
          ⟨j, by omega⟩) hnotIR
      exact ⟨hrow.1.trans hbit, hrow.2.trans htok⟩
  · have hframe := bankTrialLocalReturnDigitFrame
      ring root e B hf j hjpos hjb he hne (by
        intro hh
        rw [hh] at he
        exact he)
    rw [hframe]
    exact ⟨hbit, htok⟩

/-- Complete G_j array transition, retaining all aliases of
nonadjacent logical sites on short rings. The distinguished
physical letter either retreats j to j-1, or preserves j. -/
theorem bankTrialLocalReturnArrayStep {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n) (hn : 2 ≤ n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RWAIT)
    (j : Nat) (hback : BankTrialLocalFrontBack q B j)
    (hj : 1 < j) :
    ∃ k : Nat, BankTrialLocalFrontBack q
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) k := by
  have hcopy := hback
  obtain ⟨hjb, hjpos, hbit, htok, hother⟩ := hcopy
  by_cases he : e = Counter.site ring root (j - 1)
  · have hpair := bankTrialLocalReturnRetreatPair
      ring root e hn B hf j hback hj he
    refine ⟨j - 1, ?_⟩
    refine ⟨(by omega), (by omega),
      hpair.1.1, hpair.1.2, ?_⟩
    intro i hi hib hneq
    by_cases hone : i = 1
    · have hlarge : 2 < j := by omega
      subst i
      exact bankTrialLocalReturnFirstSafe ring root e hn
        B hf hm j hback hlarge
    · by_cases hsame : i = j
      · have hfin :
            (⟨j, by omega⟩ :
              Fin ((compileAdvice q).b + 1)) =
              ⟨i, Nat.lt_succ_of_le hib⟩ :=
          Fin.ext (by show j = i; exact hsame.symm)
        rw [← hfin]
        exact hpair.2
      · by_cases hsucc : i = j + 1
        · have hjlt : j < (compileAdvice q).b := by omega
          have hfin :
              (⟨j + 1, by omega⟩ :
                Fin ((compileAdvice q).b + 1)) =
                ⟨i, Nat.lt_succ_of_le hib⟩ :=
            Fin.ext (by show j + 1 = i; exact hsucc.symm)
          rw [← hfin]
          exact bankTrialLocalReturnSuccessorSafe ring root e
            hn B hf j hback hjlt
        · exact bankTrialLocalFrontBackFarDigit ring root e
            B hf j i hback (by omega) hib
            (by omega) hsame (by omega)
  · have hfront := bankTrialLocalReturnFrontSafe
      ring root e hn B hf j hback he
    refine ⟨j, ⟨hjb, hjpos, hfront.1, hfront.2, ?_⟩⟩
    intro i hi hib hneq
    by_cases hone : i = 1
    · subst i
      exact bankTrialLocalReturnFirstOff ring root e hn
        B hf hm j hback hj he
    · by_cases hpred : i + 1 = j
      · have hlarge : 2 < j := by omega
        have hdata := bankTrialLocalReturnPredecessorSafe
          ring root e B hf j hback hlarge he
        have hfin :
            (⟨j - 1, by omega⟩ :
              Fin ((compileAdvice q).b + 1)) =
              ⟨i, Nat.lt_succ_of_le hib⟩ :=
          Fin.ext (by show j - 1 = i; omega)
        rw [← hfin]
        exact hdata
      · by_cases hsucc : i = j + 1
        · have hjlt : j < (compileAdvice q).b := by omega
          have hfin :
              (⟨j + 1, by omega⟩ :
                Fin ((compileAdvice q).b + 1)) =
                ⟨i, Nat.lt_succ_of_le hib⟩ :=
            Fin.ext (by show j + 1 = i; exact hsucc.symm)
          rw [← hfin]
          exact bankTrialLocalReturnSuccessorSafe ring root e
            hn B hf j hback hjlt
        · exact bankTrialLocalFrontBackFarDigit ring root e
            B hf j i hback (by omega) hib
            hpred hneq (by omega)

/-- The exact binder type hreturn in
bankTrialLocalRecoveryCertStepPremiseOfMainCases. -/
theorem bankTrialLocalRecoveryCertStepReturn {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) (hn : 2 ≤ n) :
    ∀ (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (e : Fin n) (j : Nat),
      BankTrialLocalRecoveryCert q B →
      (B.fields ⟨0, by omega⟩).1 = .RWAIT →
      1 < j → BankTrialLocalFrontBack q B j →
      (BankTrialLocalRecoveryCert q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e) ∨
       BankTrialLocalClean q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e)) := by
  intro B e j hc hm hj hback
  have harray := bankTrialLocalReturnArrayStep ring root e hn
    B hc.2.1 hm j hback hj
  exact Or.inl (bankTrialLocalRecoveryCertStepReturnOfArray
    ring root e B hc hm j hback hj harray)

end L3

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
Outward-front closure and the full recovery certificate-step premise.
All array arguments allow nonadjacent logical sites to share a physical site.
-/

/-- The root-outgoing row preserves an RR at digit one while
the old root mode is RWAIT. -/
theorem bankTrialLocalOutwardRootFirst {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) (hn : 2 ≤ n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RWAIT)
    (hbit :
      (B.fields ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.1 = false)
    (htok :
      (B.fields ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.2.1 = .RR) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B root).fields ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.1 = false ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B root).fields ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.2.1 = .RR := by
  have hs : Counter.Support q ring root root :=
    Or.inr ⟨0, Nat.zero_le _, rfl⟩
  have hrow := bankTrialLocalRawRootWaitOutward
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨0, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩)
    rfl rfl rfl hm (bankTrialLocalWidthLarge q) htok hbit
  have hdata := bankTrialLocalClampedData q
    ((GrantBankReference.bankLocalReferenceInternalPair q B
      ⟨0, by change 0 < (compileAdvice q).s + 11; omega⟩).2)
  rw [bankTrialLocalStepField ring root root B hs hf,
    bankTrialLocalFieldOneOutgoing ring root hn B]
  exact ⟨hdata.1.trans hrow.2, hdata.2.trans hrow.1⟩

/-- Selecting the predecessor of a non-top outward front preserves
the empty predecessor and the RR front. -/
theorem bankTrialLocalOutwardPredecessorPair {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hn : 2 ≤ n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Nat)
    (hfront : BankTrialLocalFrontOut q B j)
    (hj : 1 < j)
    (hjlt : j < (compileAdvice q).b)
    (he : e = Counter.site ring root (j - 1)) :
    (((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨j - 1, by rcases hfront with ⟨hjb, _⟩; omega⟩).2.1 = false ∧
     ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields
        ⟨j - 1, by rcases hfront with ⟨hjb, _⟩; omega⟩).2.2.1 = .E) ∧
    (((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨j, by rcases hfront with ⟨hjb, _⟩; omega⟩).2.1 = false ∧
     ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields
        ⟨j, by rcases hfront with ⟨hjb, _⟩; omega⟩).2.2.1 = .RR) := by
  obtain ⟨hjb, _, hbit, htok, hprefix⟩ := hfront
  have hprevBound : j - 1 < (compileAdvice q).b := by omega
  have hprevData :
      (B.fields ⟨j - 1, by omega⟩).2.1 = false ∧
      (B.fields ⟨j - 1, by omega⟩).2.2.1 = .E :=
    hprefix (j - 1) (by omega) (by omega) (by omega)
  have hs : Counter.Support q ring root e :=
    Or.inr ⟨j - 1, by omega, he⟩
  have hstep : j - 1 + 1 = j := by omega
  have hfrontBit :
      (B.fields ⟨j - 1 + 1, by omega⟩).2.1 = false := by
    simpa only [hstep] using hbit
  have hfrontTok :
      (B.fields ⟨j - 1 + 1, by omega⟩).2.2.1 = .RR := by
    simpa only [hstep] using htok
  have hrow := bankTrialLocalRawPredecessorHold
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j - 1, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j - 1 + 1, by omega⟩)
    (by change 1 ≤ j - 1; omega)
    (by change j - 1 < (compileAdvice q).b; exact hprevBound)
    rfl
    (by change j - 1 + 1 < (compileAdvice q).b; omega)
    hprevData.2 hfrontTok hprevData.1 hfrontBit
  have hleftData := bankTrialLocalClampedData q
    ((GrantBankReference.bankLocalReferenceInternalPair q B
      ⟨j - 1, hprevBound⟩).1)
  have hrightData := bankTrialLocalClampedData q
    ((GrantBankReference.bankLocalReferenceInternalPair q B
      ⟨j - 1, hprevBound⟩).2)
  have hsource :
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨j - 1, by omega⟩ =
        GrantBankReference.bankLocalReferenceClampedQuad q
          ((GrantBankReference.bankLocalReferenceInternalPair q B
            ⟨j - 1, hprevBound⟩).1) := by
    rw [bankTrialLocalStepField ring root e B hs hf]
    exact bankTrialLocalSelectedSource ring root e B
      ⟨j - 1, by omega⟩ ⟨hprevBound, he⟩
  have hnotSource :
      ¬ (j < (compileAdvice q).b ∧
          e = Counter.site ring root j) := by
    intro hx
    have hne := bankTrialLocalAdjacentSitesDistinct
      ring root hn (j - 1)
    apply hne
    rw [hstep]
    exact he.symm.trans hx.2
  have htarget :
      0 < j ∧ e = Counter.site ring root (j - 1) :=
    ⟨by omega, he⟩
  have hresponder :
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨j, by omega⟩ =
        GrantBankReference.bankLocalReferenceClampedQuad q
          ((GrantBankReference.bankLocalReferenceInternalPair q B
            ⟨j - 1, hprevBound⟩).2) := by
    rw [bankTrialLocalStepField ring root e B hs hf]
    exact bankTrialLocalSelectedResponder ring root e B
      ⟨j, by omega⟩ hnotSource htarget
  rw [hsource, hresponder]
  exact ⟨⟨hleftData.1.trans hrow.2.1,
        hleftData.2.trans hrow.1⟩,
    ⟨hrightData.1.trans hrow.2.2.2,
      hrightData.2.trans hrow.2.2.1⟩⟩

/-- Selecting the predecessor of the top RR turns the outward
front into an RL at the predecessor and empties the top. -/
theorem bankTrialLocalOutwardTopTurnPair {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hn : 2 ≤ n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Nat)
    (hfront : BankTrialLocalFrontOut q B j)
    (hj : 1 < j)
    (hjtop : j = (compileAdvice q).b)
    (he : e = Counter.site ring root (j - 1)) :
    (((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨j - 1, by rcases hfront with ⟨hjb, _⟩; omega⟩).2.1 = false ∧
     ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields
        ⟨j - 1, by rcases hfront with ⟨hjb, _⟩; omega⟩).2.2.1 = .RL) ∧
    (((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨j, by rcases hfront with ⟨hjb, _⟩; omega⟩).2.1 = false ∧
     ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields
        ⟨j, by rcases hfront with ⟨hjb, _⟩; omega⟩).2.2.1 = .E) := by
  obtain ⟨hjb, _, hbit, htok, hprefix⟩ := hfront
  have hprevBound : j - 1 < (compileAdvice q).b := by omega
  have hprevData :
      (B.fields ⟨j - 1, by omega⟩).2.1 = false ∧
      (B.fields ⟨j - 1, by omega⟩).2.2.1 = .E :=
    hprefix (j - 1) (by omega) (by omega) (by omega)
  have hs : Counter.Support q ring root e :=
    Or.inr ⟨j - 1, by omega, he⟩
  have hstep : j - 1 + 1 = j := by omega
  have hfrontBit :
      (B.fields ⟨j - 1 + 1, by omega⟩).2.1 = false := by
    simpa only [hstep] using hbit
  have hfrontTok :
      (B.fields ⟨j - 1 + 1, by omega⟩).2.2.1 = .RR := by
    simpa only [hstep] using htok
  have hrow := bankTrialLocalRawTopTurn
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j - 1, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j - 1 + 1, by omega⟩)
    (by change 1 ≤ j - 1; omega)
    (by change j - 1 < (compileAdvice q).b; exact hprevBound)
    rfl
    (by change j - 1 + 1 = (compileAdvice q).b; omega)
    hprevData.2 hfrontTok hfrontBit
  have hleftData := bankTrialLocalClampedData q
    ((GrantBankReference.bankLocalReferenceInternalPair q B
      ⟨j - 1, hprevBound⟩).1)
  have hrightData := bankTrialLocalClampedData q
    ((GrantBankReference.bankLocalReferenceInternalPair q B
      ⟨j - 1, hprevBound⟩).2)
  have hsource :
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨j - 1, by omega⟩ =
        GrantBankReference.bankLocalReferenceClampedQuad q
          ((GrantBankReference.bankLocalReferenceInternalPair q B
            ⟨j - 1, hprevBound⟩).1) := by
    rw [bankTrialLocalStepField ring root e B hs hf]
    exact bankTrialLocalSelectedSource ring root e B
      ⟨j - 1, by omega⟩ ⟨hprevBound, he⟩
  have hnotSource :
      ¬ (j < (compileAdvice q).b ∧
          e = Counter.site ring root j) := by
    intro hx
    omega
  have htarget :
      0 < j ∧ e = Counter.site ring root (j - 1) :=
    ⟨by omega, he⟩
  have hresponder :
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨j, by omega⟩ =
        GrantBankReference.bankLocalReferenceClampedQuad q
          ((GrantBankReference.bankLocalReferenceInternalPair q B
            ⟨j - 1, hprevBound⟩).2) := by
    rw [bankTrialLocalStepField ring root e B hs hf]
    exact bankTrialLocalSelectedResponder ring root e B
      ⟨j, by omega⟩ hnotSource htarget
  rw [hsource, hresponder]
  exact ⟨⟨hleftData.1.trans hrow.2.1,
        hleftData.2.trans hrow.1⟩,
    ⟨hrightData.1.trans hrow.2.2.2,
      hrightData.2.trans hrow.2.2.1⟩⟩

/-- An outward front keeps its zero/RR data unless its forward
edge advances it or the predecessor of a top front turns it. -/
theorem bankTrialLocalOutwardFrontSafe {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n) (hn : 2 ≤ n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RWAIT)
    (j : Nat) (hfront : BankTrialLocalFrontOut q B j)
    (hsource : j < (compileAdvice q).b →
      e ≠ Counter.site ring root j)
    (hturn : j = (compileAdvice q).b →
      e ≠ Counter.site ring root (j - 1)) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨j, by rcases hfront with ⟨hjb, _⟩; omega⟩).2.1 = false ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨j, by rcases hfront with ⟨hjb, _⟩; omega⟩).2.2.1 = .RR := by
  have hcopy := hfront
  obtain ⟨hjb, hjpos, hbit, htok, _⟩ := hcopy
  by_cases hone : j = 1
  · subst j
    by_cases he : e = root
    · subst e
      exact bankTrialLocalOutwardRootFirst ring root hn
        B hf hm hbit htok
    · have hnotSource : e ≠ Counter.site ring root 1 :=
        hsource (bankTrialLocalWidthLarge q)
      have hnotResponder :
          e ≠ Counter.site ring root (1 - 1) := by
        simpa only [Nat.sub_self, Counter.site] using he
      have hframe := bankTrialLocalReturnDigitFrame
        ring root e B hf 1 (by omega) hjb
        hnotSource hnotResponder (by intro htop; have hwidth := bankTrialLocalWidthLarge q; omega)
      rw [hframe]
      exact ⟨hbit, htok⟩
  · have hjlarge : 1 < j := by omega
    by_cases hin : e = Counter.site ring root (j - 1)
    · have hjlt : j < (compileAdvice q).b := by
        by_cases hlt : j < (compileAdvice q).b
        · exact hlt
        · have hjtop : j = (compileAdvice q).b := by omega
          exact False.elim (hturn hjtop hin)
      exact (bankTrialLocalOutwardPredecessorPair
        ring root e hn B hf j hfront hjlarge hjlt hin).2
    · by_cases hout : e = Counter.site ring root j
      · have hjtop : j = (compileAdvice q).b := by
          by_cases hlt : j < (compileAdvice q).b
          · exact False.elim (hsource hlt hout)
          · omega
        have hs : Counter.Support q ring root e :=
          Or.inr ⟨j, hjb, hout⟩
        have hx :
            ¬ (j < (compileAdvice q).b ∧
              e = Counter.site ring root j) := by
          intro h
          omega
        have hy :
            ¬ (0 < j ∧
              e = Counter.site ring root (j - 1)) := by
          intro h
          exact hin h.2
        have ht :
            j = (compileAdvice q).b ∧
              e = Counter.site ring root (compileAdvice q).b := by
          refine ⟨hjtop, ?_⟩
          rw [← hjtop]
          exact hout
        rw [bankTrialLocalStepField ring root e B hs hf,
          bankTrialLocalSelectedTop ring root e B
            ⟨j, by omega⟩ hx hy ht]
        have hnotIR :
            (GrantBankReference.bankLocalReferenceCell B
              ⟨j, by omega⟩).tok ≠ .IR := by
          intro h
          have hbad :
              (B.fields ⟨j, by omega⟩).2.2.1 = .IR := h
          rw [htok] at hbad
          cases hbad
        have hrow := bankTrialLocalTopDataRow q
          (GrantBankReference.bankLocalReferenceCell B
            ⟨j, by omega⟩) hnotIR
        exact ⟨hrow.1.trans hbit, hrow.2.trans htok⟩
      · have hframe := bankTrialLocalReturnDigitFrame
          ring root e B hf j hjpos hjb hout hin (by intro hh; rw [hh] at hout; exact hout)
        rw [hframe]
        exact ⟨hbit, htok⟩

/-- The first digit of an outward front beyond one stays zero/empty.
The case j=2 uses the non-top predecessor row explicitly. -/
theorem bankTrialLocalOutwardFirstSafe {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n) (hn : 2 ≤ n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RWAIT)
    (j : Nat) (hfront : BankTrialLocalFrontOut q B j)
    (hj : 1 < j) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.1 = false ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.2.1 = .E := by
  have hcopy := hfront
  obtain ⟨hjb, _, _, _, hprefix⟩ := hcopy
  have hfirst :
      (B.fields ⟨1, by omega⟩).2.1 = false ∧
      (B.fields ⟨1, by omega⟩).2.2.1 = .E :=
    hprefix 1 (by omega) hj (by omega)
  by_cases he : e = root
  · subst e
    exact bankTrialLocalReturnRootFirstEmpty
      ring root hn B hf hm hfirst.1 hfirst.2
  · by_cases htwo : j = 2
    · subst j
      by_cases hselected : e = Counter.site ring root 1
      · have hpair := bankTrialLocalOutwardPredecessorPair
          ring root e hn B hf 2 hfront (by omega)
          (by change 2 < (compileAdvice q).s + 11; omega)
          hselected
        exact hpair.1
      · have hframe := bankTrialLocalReturnDigitFrame
          ring root e B hf 1 (by omega) (by omega)
          hselected
          (by simpa only [Nat.sub_self, Counter.site] using he)
          (by intro hb; have hw := bankTrialLocalWidthLarge q; omega)
        rw [hframe]
        exact hfirst
    · have hsecond :
          (B.fields ⟨2, by omega⟩).2.1 = false ∧
          (B.fields ⟨2, by omega⟩).2.2.1 = .E :=
        hprefix 2 (by omega) (by omega) (by omega)
      exact bankTrialLocalEmptyDigitNoResponder
        ring root e B hf 1 (by omega) (by omega)
        hfirst (fun _ => hsecond)
        (by simpa only [Nat.sub_self, Counter.site] using he)

/-- The empty predecessor of an outward front remains empty unless
this is the selected top-turn row. -/
theorem bankTrialLocalOutwardPredecessorSafe {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n) (hn : 2 ≤ n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Nat) (hfront : BankTrialLocalFrontOut q B j)
    (hj : 2 < j)
    (hsafe : j < (compileAdvice q).b ∨
      e ≠ Counter.site ring root (j - 1)) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨j - 1, by rcases hfront with ⟨hjb, _⟩; omega⟩).2.1 = false ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨j - 1, by rcases hfront with ⟨hjb, _⟩; omega⟩).2.2.1 = .E := by
  have hcopy := hfront
  obtain ⟨hjb, _, _, _, hprefix⟩ := hcopy
  by_cases he : e = Counter.site ring root (j - 1)
  · have hjlt : j < (compileAdvice q).b := by
      rcases hsafe with hlt | hne
      · exact hlt
      · exact False.elim (hne he)
    exact (bankTrialLocalOutwardPredecessorPair
      ring root e hn B hf j hfront (by omega) hjlt he).1
  · have hbefore :
        (B.fields ⟨j - 2, by omega⟩).2.1 = false ∧
        (B.fields ⟨j - 2, by omega⟩).2.2.1 = .E :=
      hprefix (j - 2) (by omega) (by omega) (by omega)
    have hhere :
        (B.fields ⟨j - 1, by omega⟩).2.1 = false ∧
        (B.fields ⟨j - 1, by omega⟩).2.2.1 = .E :=
      hprefix (j - 1) (by omega) (by omega) (by omega)
    by_cases hprev : e = Counter.site ring root (j - 2)
    · have hbound : j - 2 < (compileAdvice q).b := by omega
      have hindex : j - 2 + 1 = j - 1 := by omega
      have hhere' :
          (B.fields ⟨j - 2 + 1, by omega⟩).2.1 = false ∧
          (B.fields ⟨j - 2 + 1, by omega⟩).2.2.1 = .E := by
        simpa only [hindex] using hhere
      have hrow := bankTrialLocalInternalEmptyData B
        ⟨j - 2, hbound⟩ (by change 1 ≤ j - 2; omega)
        hbefore hhere'
      have hs : Counter.Support q ring root e :=
        Or.inr ⟨j - 2, by omega, hprev⟩
      have hx :
          ¬ (j - 1 < (compileAdvice q).b ∧
            e = Counter.site ring root (j - 1)) := by
        intro h
        exact he h.2
      have hy :
          0 < j - 1 ∧
            e = Counter.site ring root (j - 1 - 1) := by
        refine ⟨by omega, ?_⟩
        have hsub : j - 1 - 1 = j - 2 := by omega
        rw [hsub]
        exact hprev
      rw [bankTrialLocalStepField ring root e B hs hf,
        bankTrialLocalSelectedResponder ring root e B
          ⟨j - 1, by omega⟩ hx hy]
      have hfin :
          (⟨j - 1 - 1, by omega⟩ :
            Fin (compileAdvice q).b) =
            ⟨j - 2, hbound⟩ :=
        Fin.ext (by show j - 1 - 1 = j - 2; omega)
      rw [hfin]
      exact hrow.2
    · have hnotResponder :
          e ≠ Counter.site ring root (j - 1 - 1) := by
        intro h
        have hsub : j - 1 - 1 = j - 2 := by omega
        rw [hsub] at h
        exact hprev h
      have hframe := bankTrialLocalReturnDigitFrame
        ring root e B hf (j - 1) (by omega) (by omega)
        he hnotResponder (by intro hh; omega)
      rw [hframe]
      exact hhere

/-- Every cleared outward prefix slot stays cleared when the top
turn is excluded; the first and immediate-predecessor slots are
handled separately from the deep prefix. -/
theorem bankTrialLocalOutwardPrefixSafe {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n) (hn : 2 ≤ n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RWAIT)
    (j i : Nat) (hfront : BankTrialLocalFrontOut q B j)
    (hi : 1 ≤ i) (hij : i < j)
    (hib : i ≤ (compileAdvice q).b)
    (hsafe : j < (compileAdvice q).b ∨
      e ≠ Counter.site ring root (j - 1)) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨i, Nat.lt_succ_of_le hib⟩).2.1 = false ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨i, Nat.lt_succ_of_le hib⟩).2.2.1 = .E := by
  have hcopy := hfront
  obtain ⟨hjb, _, _, _, _⟩ := hcopy
  by_cases hone : i = 1
  · subst i
    exact bankTrialLocalOutwardFirstSafe
      ring root e hn B hf hm j hfront (by omega)
  · by_cases hpred : i + 1 = j
    · have hdata := bankTrialLocalOutwardPredecessorSafe
        ring root e hn B hf j hfront (by omega) hsafe
      have hfin :
          (⟨j - 1, by omega⟩ :
            Fin ((compileAdvice q).b + 1)) =
            ⟨i, Nat.lt_succ_of_le hib⟩ :=
        Fin.ext (by show j - 1 = i; omega)
      rw [← hfin]
      exact hdata
    · exact bankTrialLocalFrontOutDeepPrefix ring root e
        B hf j i hfront (by omega) (by omega) hib

/-- Complete outward F_j array transition. The forward edge advances
a non-top RR; the incoming top edge turns RR into a returning RL;
every other edge preserves an outward front. Physical aliases of
nonadjacent logical sites are allowed throughout. -/
theorem bankTrialLocalOutwardArrayStep {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n) (hn : 2 ≤ n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RWAIT)
    (j : Nat) (hfront : BankTrialLocalFrontOut q B j) :
    (∃ k : Nat, BankTrialLocalFrontOut q
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) k) ∨
    (∃ k : Nat, BankTrialLocalFrontBack q
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) k) := by
  have hcopy := hfront
  obtain ⟨hjb, hjpos, hbit, htok, hprefix⟩ := hcopy
  by_cases hjlt : j < (compileAdvice q).b
  · by_cases he : e = Counter.site ring root j
    · have hpair := bankTrialLocalOutwardAdvancePair
        ring root e hn B hf j hfront hjlt he
      apply Or.inl
      refine ⟨j + 1, ⟨(by omega), (by omega),
        hpair.2.1, hpair.2.2, ?_⟩⟩
      intro i hi hij hib
      by_cases hsame : i = j
      · subst i
        exact hpair.1
      · exact bankTrialLocalOutwardPrefixSafe
          ring root e hn B hf hm j i hfront hi
          (by omega) hib (Or.inl hjlt)
    · have hfront' := bankTrialLocalOutwardFrontSafe
        ring root e hn B hf hm j hfront
        (fun _ => he) (by intro htop; omega)
      apply Or.inl
      refine ⟨j, ⟨hjb, hjpos, hfront'.1, hfront'.2, ?_⟩⟩
      intro i hi hij hib
      exact bankTrialLocalOutwardPrefixSafe
        ring root e hn B hf hm j i hfront hi hij hib
        (Or.inl hjlt)
  · have hjtop : j = (compileAdvice q).b := by omega
    have hjlarge : 1 < j := by
      have hw := bankTrialLocalWidthLarge q
      omega
    by_cases he : e = Counter.site ring root (j - 1)
    · have hpair := bankTrialLocalOutwardTopTurnPair
        ring root e hn B hf j hfront hjlarge hjtop he
      apply Or.inr
      refine ⟨j - 1, ⟨(by omega), (by omega),
        hpair.1.1, hpair.1.2, ?_⟩⟩
      intro i hi hib hneq
      by_cases hsame : i = j
      · subst i
        exact hpair.2
      · by_cases hone : i = 1
        · subst i
          exact bankTrialLocalOutwardFirstSafe
            ring root e hn B hf hm j hfront hjlarge
        · exact bankTrialLocalFrontOutDeepPrefix
            ring root e B hf j i hfront
            (by omega) (by omega) hib
    · have hfront' := bankTrialLocalOutwardFrontSafe
        ring root e hn B hf hm j hfront
        (by intro hlt; exact False.elim (hjlt hlt))
        (fun _ => he)
      apply Or.inl
      refine ⟨j, ⟨hjb, hjpos, hfront'.1, hfront'.2, ?_⟩⟩
      intro i hi hij hib
      exact bankTrialLocalOutwardPrefixSafe
        ring root e hn B hf hm j i hfront hi hij hib
        (Or.inr he)

/-- The exact hout binder type of
bankTrialLocalRecoveryCertStepPremiseOfMainCases. -/
theorem bankTrialLocalRecoveryCertStepOutward {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) (hn : 2 ≤ n) :
    ∀ (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (e : Fin n) (j : Nat),
      BankTrialLocalRecoveryCert q B →
      (B.fields ⟨0, by omega⟩).1 = .RWAIT →
      BankTrialLocalFrontOut q B j →
      (BankTrialLocalRecoveryCert q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e) ∨
       BankTrialLocalClean q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e)) := by
  intro B e j hc hm hfront
  have harray := bankTrialLocalOutwardArrayStep
    ring root e hn B hc.2.1 hm j hfront
  exact Or.inl (bankTrialLocalRecoveryCertStepOutwardOfArray
    ring root e B hc hm j hfront harray)

/-- The full original-clock recovery certificate-step premise,
using the outward family and the existing returning family. -/
theorem bankTrialLocalRecoveryCertStepPremise {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) (hn : 2 ≤ n) :
    BankTrialLocalRecoveryCertStepPremise (q := q) ring root := by
  exact bankTrialLocalRecoveryCertStepPremiseOfMainCases
    (q := q) ring root hn
    (bankTrialLocalRecoveryCertStepOutward (q := q) ring root hn)
    (bankTrialLocalRecoveryCertStepReturn (q := q) ring root hn)

end L3

namespace L3

/-- No recovery success on the local trial observer, unconditionally:
the closure premise is `bankTrialLocalRecoveryCertStepPremise`. -/
theorem bankTrialLocalRecoveryNoWin {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) (hn : 2 ≤ n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (w : List (Fin n))
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hrun : bankTrialLocalRun ring root w
      (bankTrialLocalStart S) = ⟨B, .recovery⟩)
    (e : Fin n) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).success = false :=
  bankTrialLocalRecoveryNoWinOfStepPremise ring root
    (bankTrialLocalRecoveryCertStepPremise (q := q) ring root hn)
    S hclean w B hrun e

end L3

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
Physical-to-local clamped BANK coupling at every safe
prefix and root-nominated success transfer at the next letter.
No existing declarations change.

The whole safe word excludes nominated-root success by definition.
Consequently a success-producing last letter is treated separately:
only its proper prefix is required to satisfy SafeWord.
-/

/-- Every prefix of a full safe word retains the physical/reference
four-field agreement, PACK completeness and the false local success
latch. This is an induction over actual scheduler letters, not an
assumption of injectivity of the logical site map. The one-step
bridge contains internal, top, incoming and frame selectors. -/
theorem bankTrialLocalSafePrefixCoupling {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false) :
    ∀ (u v : List (Fin n))
      (C : Counter.Config q n)
      (S : GrantBankReference.BankLocalReference
        (compileAdvice q).b),
      Counter.Complete ring C root →
      GrantBankReference.bankLocalReferenceFieldsAgree
        ring C root S →
      S.success = false →
      GrantBankReference.bankLocalReferenceSafeWord
        ring root C (u ++ v) →
      GrantBankReference.bankLocalReferenceFieldsAgree ring
        (Counter.Word ring u C) root
        (GrantBankReference.bankLocalReferenceWordClamped
          ring root u S) ∧
      Counter.Complete ring (Counter.Word ring u C) root ∧
      (GrantBankReference.bankLocalReferenceWordClamped
        ring root u S).success = false := by
  intro u
  induction u with
  | nil =>
      intro v C S hc hfields hfalse hsafe
      exact ⟨hfields, hc, hfalse⟩
  | cons e es ih =>
      intro v C S hc hfields hfalse hsafe
      have hg : Counter.GrantFree C root := hsafe.1.1
      have hd :
          ¬ Counter.ResetClockBankDefectEntry ring C root e :=
        hsafe.2.1.1
      have hn :
          GrantBankReference.bankLocalReferenceRealSuccessEvent
            ring root C e = false := hsafe.2.2.1
      have hs := GrantBankReference.bankLocalReferenceSupportStep
        ring C root e S hsp hc hg hfields hfalse hd
      have hf :
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root S e).success = false := hs.2.2.trans hn
      exact ih v ((protocol q).step ring C e)
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root S e)
        hs.2.1 hs.1 hf
        ⟨hsafe.1.2, hsafe.2.1.2, hsafe.2.2.2⟩

/-- The quantified all-prefix form, retaining the ORIGINAL physical
scheduler word. The prefix may be empty or the entire safe word. -/
theorem bankTrialLocalSafeWordAllPrefixes {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (C : Counter.Config q n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : Counter.Complete ring C root)
    (hfields : GrantBankReference.bankLocalReferenceFieldsAgree
      ring C root S)
    (hfalse : S.success = false)
    (w : List (Fin n))
    (hsafe : GrantBankReference.bankLocalReferenceSafeWord
      ring root C w) :
    ∀ (u v : List (Fin n)), w = u ++ v →
      GrantBankReference.bankLocalReferenceFieldsAgree ring
        (Counter.Word ring u C) root
        (GrantBankReference.bankLocalReferenceWordClamped
          ring root u S) ∧
      Counter.Complete ring (Counter.Word ring u C) root ∧
      (GrantBankReference.bankLocalReferenceWordClamped
        ring root u S).success = false := by
  intro u v hw
  rw [hw] at hsafe
  exact bankTrialLocalSafePrefixCoupling
    ring root hsp u v C S hc hfields hfalse hsafe

/-- The same physical prefix is coupled to the reference driven
only by its boundary-inclusive support subword. The deleted letters
are only deleted in the reference, never in the physical run. -/
theorem bankTrialLocalSafePrefixSupportFieldsAgree {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (C : Counter.Config q n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : Counter.Complete ring C root)
    (hfields : GrantBankReference.bankLocalReferenceFieldsAgree
      ring C root S)
    (hfalse : S.success = false)
    (u v : List (Fin n))
    (hsafe : GrantBankReference.bankLocalReferenceSafeWord
      ring root C (u ++ v)) :
    GrantBankReference.bankLocalReferenceFieldsAgree ring
      (Counter.Word ring u C) root
      (GrantBankReference.bankLocalReferenceWordClamped
        ring root
        (GrantBankReference.bankLocalReferenceSupportSubword
          (q := q) ring root u) S) := by
  have hp := bankTrialLocalSafePrefixCoupling
    ring root hsp u v C S hc hfields hfalse hsafe
  rw [GrantBankReference.bankLocalReferenceWordLocalityClamped
    ring root u S]
  exact hp.1

/-- GrantFreeWord includes the final physical cut, even for the
empty scheduler word. -/
theorem bankTrialLocalGrantFreeAtWordEnd {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (w : List (Fin n)) (C : Counter.Config q n),
      Counter.GrantFreeWord ring root C w →
      Counter.GrantFree (Counter.Word ring w C) root := by
  intro w
  induction w with
  | nil =>
      intro C hg
      exact hg
  | cons e es ih =>
      intro C hg
      exact ih ((protocol q).step ring C e) hg.2

/-- A nominated-root BANK success immediately AFTER a safe proper
prefix sets the local clamped latch on that same next letter.
The successful letter need not belong to SafeWord; including it in
SafeWord would contradict the definition of that event. -/
theorem bankTrialLocalPhysicalRootSuccessReflected {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (C : Counter.Config q n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : Counter.Complete ring C root)
    (hfields : GrantBankReference.bankLocalReferenceFieldsAgree
      ring C root S)
    (hfalse : S.success = false)
    (pre : List (Fin n)) (e : Fin n)
    (hsafe : GrantBankReference.bankLocalReferenceSafeWord
      ring root C pre)
    (hwin :
      GrantBankReference.bankLocalReferenceRealSuccessEvent
        ring root (Counter.Word ring pre C) e = true) :
    (GrantBankReference.bankLocalReferenceWordClamped ring root
      (pre ++ [e]) S).success = true := by
  have hp := GrantBankReference.bankLocalReferenceNoSuccessWordCouplingClamped
    ring root hsp pre C S hc
    hsafe.1 hsafe.2.1 hfields hfalse hsafe.2.2
  have hg := bankTrialLocalGrantFreeAtWordEnd
    ring root pre C hsafe.1
  have heq := GrantBankReference.bankLocalReferenceLatchStepMatchesRealClamped
    ring (Counter.Word ring pre C) root e
    (GrantBankReference.bankLocalReferenceWordClamped
      ring root pre S)
    hp.2.1 hg hp.1 hp.2.2
  rw [GrantBankReference.bankLocalReferenceWordAppendClamped
    ring root pre [e] S]
  change (GrantBankReference.bankLocalReferenceStepClamped
    ring root
      (GrantBankReference.bankLocalReferenceWordClamped
        ring root pre S) e).success = true
  exact heq.trans hwin

/-- An active observer phase (LIVE or RECOVERY) always writes the
same clamped BANK successor as the standalone local reference. -/
theorem bankTrialLocalActiveStepBank {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialLocalState q)
    (hz : (∃ begun : Bool, z.phase = .live begun) ∨
      z.phase = .recovery) :
    (bankTrialLocalNext ring root z e).bank =
      GrantBankReference.bankLocalReferenceStepClamped
        ring root z.bank e := by
  cases z with
  | mk bank phase =>
      cases phase with
      | live begun =>
          exact bankTrialLocalNextLiveBank ring root e bank begun
      | recovery =>
          exact bankTrialLocalNextRecoveryBank ring root e bank
      | won =>
          rcases hz with ⟨begun, hh⟩ | hh
          · cases hh
          · cases hh
      | lost =>
          rcases hz with ⟨begun, hh⟩ | hh
          · cases hh
          · cases hh

/-- An absorbing WON or LOST observer cannot end a later word in
RECOVERY. This excludes a false bank/reference synchronization
argument across a terminated observer. -/
theorem bankTrialLocalTerminalNotRecovery {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (w : List (Fin n)) (z : BankTrialLocalState q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hz : bankTrialLocalTerminal z)
    (hrun : bankTrialLocalRun ring root w z =
      ⟨B, .recovery⟩) : False := by
  have hfixed :=
    bankTrialLocalRunTerminalAbsorbs ring root w z hz
  rw [hfixed] at hrun
  have hphase := congrArg BankTrialLocalState.phase hrun
  rcases hz with hw | hl
  · rw [hw] at hphase
    cases hphase
  · rw [hl] at hphase
    cases hphase

/-- On any observer word ending in RECOVERY, the observer bank is
exactly the standalone clamped-reference bank of that word. The
initial observer must be active. In particular, terminal LOST
cannot silently desynchronize the two runs and later re-enter
RECOVERY. -/
theorem bankTrialLocalRecoveryBankSync {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (w : List (Fin n)) (z : BankTrialLocalState q)
      (B : GrantBankReference.BankLocalReference
        (compileAdvice q).b),
      ((∃ begun : Bool, z.phase = .live begun) ∨
        z.phase = .recovery) →
      bankTrialLocalRun ring root w z = ⟨B, .recovery⟩ →
      GrantBankReference.bankLocalReferenceWordClamped
        ring root w z.bank = B := by
  intro w
  induction w with
  | nil =>
      intro z B hactive hrun
      have hbank := congrArg BankTrialLocalState.bank hrun
      exact hbank
  | cons e es ih =>
      intro z B hactive hrun
      have hnextRun :
          bankTrialLocalRun ring root es
            (bankTrialLocalNext ring root z e) =
              ⟨B, .recovery⟩ := hrun
      have hnextActive :
          (∃ begun : Bool,
            (bankTrialLocalNext ring root z e).phase =
              .live begun) ∨
          (bankTrialLocalNext ring root z e).phase =
            .recovery := by
        cases hp : (bankTrialLocalNext ring root z e).phase with
        | live begun =>
            exact Or.inl ⟨begun, rfl⟩
        | recovery =>
            exact Or.inr rfl
        | won =>
            have ht : bankTrialLocalTerminal
                (bankTrialLocalNext ring root z e) :=
              Or.inl hp
            exact False.elim
              (bankTrialLocalTerminalNotRecovery
                ring root es (bankTrialLocalNext ring root z e)
                B ht hnextRun)
        | lost =>
            have ht : bankTrialLocalTerminal
                (bankTrialLocalNext ring root z e) :=
              Or.inr hp
            exact False.elim
              (bankTrialLocalTerminalNotRecovery
                ring root es (bankTrialLocalNext ring root z e)
                B ht hnextRun)
      have hbank := bankTrialLocalActiveStepBank
        ring root e z hactive
      have htail := ih
        (bankTrialLocalNext ring root z e) B
        hnextActive hnextRun
      change GrantBankReference.bankLocalReferenceWordClamped
        ring root es
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root z.bank e) = B
      rw [← hbank]
      exact htail

/-- Physical no-win at the next nominated-root service of an
authenticated RECOVERY cut reached through a safe physical prefix.
No safety hypothesis on this *next* letter is necessary: the event
tests OLD data, and the prefix provides the old grant and field
agreement. This is the nonvacuous transfer of local RecoveryNoWin. -/
theorem bankTrialLocalPhysicalRecoveryNoWin {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (hsp : (compileAdvice q).useSmall = false)
    (C : Counter.Config q n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : Counter.Complete ring C root)
    (hfields : GrantBankReference.bankLocalReferenceFieldsAgree
      ring C root S)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n))
    (hsafe : GrantBankReference.bankLocalReferenceSafeWord
      ring root C pre)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hrun : bankTrialLocalRun ring root pre
      (bankTrialLocalStart S) = ⟨B, .recovery⟩)
    (e : Fin n) :
    GrantBankReference.bankLocalReferenceRealSuccessEvent
      ring root (Counter.Word ring pre C) e = false := by
  have hp := GrantBankReference.bankLocalReferenceNoSuccessWordCouplingClamped
    ring root hsp pre C S hc
    hsafe.1 hsafe.2.1 hfields hclean.1 hsafe.2.2
  have hg := bankTrialLocalGrantFreeAtWordEnd
    ring root pre C hsafe.1
  have heq := GrantBankReference.bankLocalReferenceLatchStepMatchesRealClamped
    ring (Counter.Word ring pre C) root e
    (GrantBankReference.bankLocalReferenceWordClamped
      ring root pre S)
    hp.2.1 hg hp.1 hp.2.2
  have hsync := bankTrialLocalRecoveryBankSync
    ring root pre (bankTrialLocalStart S) B
    (Or.inl ⟨false, rfl⟩) hrun
  change GrantBankReference.bankLocalReferenceWordClamped
    ring root pre S = B at hsync
  rw [hsync] at heq
  have hno := bankTrialLocalRecoveryNoWin
    ring root hn S hclean pre B hrun e
  exact heq.symm.trans hno

end L3
