import Leader.Wu.PartialProtocol.MinimalLockRepair

/-!
# Why an arbitrary-initialized lock cannot authenticate its own origin

The one-bit minimal-lock repair proves a real birth route and a closed safe
kernel, but its extra bit is ordinary protocol state.  Under arbitrary
initialization, an adversary may initialize an endpoint -- or a whole local
pair -- to the exact current state produced by a genuine birth.  The two cases
differ only in external history, which is not an input to a population-protocol
transition.

This file records that narrow indistinguishability theorem.  It quantifies over
every deterministic local rule on the complete one-bit carrier, not merely the
accepted minimal-lock transition.  Hence no such rule can retain an authentic
lock and clear a byte-for-byte stale copy on the same local observation.

The result is deliberately not a general impossibility theorem for eventual
self-stabilization.  Different surrounding states and asynchronous evolution
can later create different observations.  Nor does adding a fixed second bit
authenticate history: arbitrary initialization can copy the complete extended
state too.  A successful resettable design therefore needs a state-based,
dynamically verifiable global certificate.  The existing `slot : Fin n`
protected epoch is one such construction at factor `n`; no smaller factor is
claimed here.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialResettableLockSol

open PPLL PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPartialMinimalLockRepairSol

set_option autoImplicit false

variable {n psi kappa tau : Nat}

/-! ## History tags are proof-side data, not protocol state -/

/-- External provenance used only to state the observation boundary. -/
inductive LockOrigin where
  | arbitraryInitialization
  | pPsiBirth
  deriving DecidableEq, Repr

/-- A current protocol value paired with proof-side provenance. -/
structure ProvenanceTagged (Q : Type) where
  current : Q
  origin : LockOrigin

/-- The local protocol can inspect only the current value. -/
def ProvenanceTagged.erase {Q : Type} (u : ProvenanceTagged Q) : Q :=
  u.current

/-- The same complete current value, regarded as genuinely produced. -/
def authenticCopy {Q : Type} (q : Q) : ProvenanceTagged Q :=
  ⟨q, .pPsiBirth⟩

/-- Arbitrary initialization may install that exact complete current value. -/
def staleCopy {Q : Type} (q : Q) : ProvenanceTagged Q :=
  ⟨q, .arbitraryInitialization⟩

/-- Erasing provenance makes the authentic and stale cases identical. -/
theorem authentic_stale_erase_eq {Q : Type} (q : Q) :
    (authenticCopy q).erase = (staleCopy q).erase := by
  rfl

/-- No deterministic classifier of current state can accept the authentic
copy and reject the stale copy.  This is polymorphic in `Q`, so adding any
fixed finite handshake component does not change the provenance argument. -/
theorem no_current_state_origin_classifier
    {Q : Type} (q : Q) (classify : Q → Bool) :
    ¬(classify (authenticCopy q).erase = true ∧
      classify (staleCopy q).erase = false) := by
  rintro ⟨hauth, hstale⟩
  have hsame : classify (authenticCopy q).erase =
      classify (staleCopy q).erase :=
    congrArg classify (authentic_stale_erase_eq q)
  have hbad : true = false :=
    hauth.symm.trans (hsame.trans hstale)
  exact Bool.noConfusion hbad

/-! ## Specialization to the accepted concrete first-birth pair -/

abbrev ResettableAuditPsi : Nat := 2

private theorem resettableAuditHPsi : ResettableAuditPsi > 0 := by
  decide

/-- The literal current pair returned by the accepted atomic P'_psi birth
branch on its explicit rank-zero witness. -/
def concretePostBirthPair (kappa tau : Nat) :
    MinimalLockState ResettableAuditPsi kappa tau ×
      MinimalLockState ResettableAuditPsi kappa tau :=
  P_partialMinimalLock resettableAuditHPsi kappa tau
    (minimalLockBirthLeft kappa tau)
    (minimalLockBirthRight kappa tau)

/-- Proof-side authentic interpretation of the concrete post-birth pair. -/
def concreteAuthenticPair (kappa tau : Nat) :
    ProvenanceTagged
      (MinimalLockState ResettableAuditPsi kappa tau ×
        MinimalLockState ResettableAuditPsi kappa tau) :=
  authenticCopy (concretePostBirthPair kappa tau)

/-- The byte-for-byte same pair installed directly by arbitrary
initialization. -/
def concreteStalePair (kappa tau : Nat) :
    ProvenanceTagged
      (MinimalLockState ResettableAuditPsi kappa tau ×
        MinimalLockState ResettableAuditPsi kappa tau) :=
  staleCopy (concretePostBirthPair kappa tau)

/-- The accepted birth theorem makes this a locked pair with a real responder
leader. -/
theorem concretePostBirthPair_locked_leader (kappa tau : Nat) :
    (concretePostBirthPair kappa tau).1.2 = true ∧
      (concretePostBirthPair kappa tau).2.2 = true ∧
      minimalLockLeader (concretePostBirthPair kappa tau).2 = true := by
  simpa [concretePostBirthPair] using
    (minimalLock_concrete_first_birth kappa tau).2.2

/-- Authentic and stale interpretations expose exactly the same complete
one-bit local pair. -/
theorem concrete_authentic_stale_erase_eq (kappa tau : Nat) :
    (concreteAuthenticPair kappa tau).erase =
      (concreteStalePair kappa tau).erase := by
  rfl

/-- Every deterministic local rule, even one returning an arbitrary result
type, acts identically on the authentic pair and its stale initialized copy. -/
theorem local_rule_indistinguishable
    (kappa tau : Nat) {R : Type}
    (rule : MinimalLockState ResettableAuditPsi kappa tau →
      MinimalLockState ResettableAuditPsi kappa tau → R) :
    rule (concreteAuthenticPair kappa tau).erase.1
        (concreteAuthenticPair kappa tau).erase.2 =
      rule (concreteStalePair kappa tau).erase.1
        (concreteStalePair kappa tau).erase.2 := by
  have hpair := concrete_authentic_stale_erase_eq kappa tau
  exact congrArg (fun q => rule q.1 q.2) hpair

/-! ## The local reset/retention conflict -/

/-- Both output locks of a local result are retained. -/
def PairLocksTrue
    (q : MinimalLockState psi kappa tau ×
      MinimalLockState psi kappa tau) : Prop :=
  q.1.2 = true ∧ q.2.2 = true

/-- Both output locks of a local result are cleared. -/
def PairLocksFalse
    (q : MinimalLockState psi kappa tau ×
      MinimalLockState psi kappa tau) : Prop :=
  q.1.2 = false ∧ q.2.2 = false

/-- On identical current inputs, no deterministic one-bit rule can both keep
the authentic protection and clear its stale copy.  The theorem is local and
does not rule out a later reset after the two executions acquire genuinely
different current neighborhoods. -/
theorem no_local_rule_retains_authentic_and_clears_stale
    (kappa tau : Nat)
    (rule : MinimalLockState ResettableAuditPsi kappa tau →
      MinimalLockState ResettableAuditPsi kappa tau →
        MinimalLockState ResettableAuditPsi kappa tau ×
          MinimalLockState ResettableAuditPsi kappa tau) :
    ¬(PairLocksTrue
        (rule (concreteAuthenticPair kappa tau).erase.1
          (concreteAuthenticPair kappa tau).erase.2) ∧
      PairLocksFalse
        (rule (concreteStalePair kappa tau).erase.1
          (concreteStalePair kappa tau).erase.2)) := by
  rintro ⟨hkeep, hclear⟩
  have hsame := local_rule_indistinguishable kappa tau rule
  have hleft := congrArg
    (fun q : MinimalLockState ResettableAuditPsi kappa tau ×
      MinimalLockState ResettableAuditPsi kappa tau => q.1.2) hsame
  have hbad : true = false :=
    hkeep.1.symm.trans (hleft.trans hclear.1)
  exact Bool.noConfusion hbad

/-! ## Noncircular obligations for any future resettable candidate -/

/-- A future resettable candidate must expose a state predicate strictly
weaker than semantic safety from which stale protection is guaranteed to be
removed along a concrete schedule.  This definition names only the reset
obligation; it does not assume convergence to a legitimate state. -/
def StaleResetProducer
    {Q : Type} (ring : DirectedRing n)
    (T : Q → Q → Q × Q) (Stale : (Fin n → Q) → Prop)
    (Cleared : (Fin n → Q) → Prop) (bound : Nat) : Prop :=
  ∀ C : Fin n → Q, Stale C →
    ∃ word : DetSchedule n,
      word.length ≤ bound ∧
        Cleared (runLocalSchedule ring T C word)

/-- Separately, a legitimate kernel must be closed and preserve pointwise
outputs.  Keeping this obligation separate from `StaleResetProducer` prevents
a reset premise equivalent to the desired safety conclusion. -/
def ResettableLocalSafety
    (P : PopulationProtocol) (ring : DirectedRing n)
    (Legit : P.Configuration n → Prop) : Prop :=
  PopulationProtocol.ClosedPred P ring Legit ∧
    StepOutputPreservingOn P ring Legit

end PPartialResettableLockSol
end PPLLCompleteMultiLeaderCleanup
