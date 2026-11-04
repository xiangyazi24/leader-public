import Leader.Wu.Birth.GenericRenewal
import Leader.Wu.Birth.ShortDoneTerminalCheckInputProducer
import Leader.Wu.Birth.ShortDoneTerminalBirthPhysical
import Leader.Wu.Birth.ShortDoneTerminalNoHitCount
import Leader.Wu.Birth.ShortDoneTerminalOpenMatchedHandoffCounterexample

namespace BirthPhaseCapToFirstBirth

open PPLLLeaderCreationCleanupRepair
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open BirthSigMoveDisposalRepair

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {n psi kappa tau : Nat}

abbrev FC (n psi kappa tau : Nat) :=
  Fin n → ExpiringAgentState psi kappa tau

/-- The literal current width-two terminal consumer. -/
def currentStep
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) (e : Fin n) :
    FC n psi kappa tau :=
  BirthShortDoneTerminalConsumer.step
    hpsi (by decide : 0 < 2) h2 ring C e

/-- Strong temporary writer-scope premise.  This is exactly the raw
`rightPrepared.core.path3 = none` condition, before deletion normalization.
It blocks both the flag-zero increment witness and the flag-one
overwrite witness. -/
def WriterBlockedRaw
    (hpsi : 0 < psi) (u : ExpiringAgentState psi kappa tau) : Prop :=
  (prepareExpiringDisposal hpsi u).core.erase.core.path3 = none

/-- Live, non-cleared branch of the corrected matched handoff. -/
def LiveMatchedHandoffAt
    (hpsi : 0 < psi) (bit : Nat)
    (u : ExpiringAgentState psi kappa tau) : Prop :=
  u.core.erase.core.path = .some (psi - 1) bit ∧
  deletionActive u.core.erase = false ∧
  BirthShortDoneTerminalOpenMatchedHandoffCounterexample.CheckOpenState
    u.core.erase.core.state ∧
  u.core.erase.core.label = ⟨psi - 1, by omega⟩ ∧
  checkBit u.core.erase.core.bit bit = .equal ∧
  u.stall = freshStall tau

/-- Post-handoff witness attached to the responder of edge `e`. -/
def CorrectedHandoffAt
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (e : Fin n) : Prop :=
  ∃ bit : Nat,
    LiveMatchedHandoffAt hpsi bit (C (ring.rightNeighbor e)) ∧
    WriterBlockedRaw hpsi (C (ring.rightNeighbor e))

/-- The exact current-host source premise consumed by the proved CHECK birth
producer on edge `e`. -/
def BirthReadyAt
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (e : Fin n) : Prop :=
  BirthShortDoneTerminalCheckInputProducer.PreparedCapturedMatchBirthSource
    hpsi (by decide : 0 < 2) h2
    (C e) (C (ring.rightNeighbor e))

/-- B6 state after the first cap and corrected live handoff, before the first
birth: literally leaderless, with one protected current-host birth-ready edge. -/
def B6Carrier
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) : Prop :=
  BirthShortDoneTerminalFirstHit.Leaderless C ∧
  ∃ e : Fin n,
    CorrectedHandoffAt hpsi ring C e ∧
    BirthReadyAt hpsi h2 ring C e

/-- Broader side carrier allowed after a target-free touching-edge step. -/
def B6ReacquireCarrier
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) : Prop :=
  BirthShortDoneTerminalFirstHit.Leaderless C ∧
  ∃ e : Fin n,
    WriterBlockedRaw hpsi (C (ring.rightNeighbor e)) ∧
    BirthReadyAt hpsi h2 ring C e

/-- One raw scheduler edge is one B6 charged block. -/
def L6 (n psi kappa tau : Nat) : Nat := 1

/-- One distinguished good edge among `n` literal one-edge words. -/
def Q6 (n psi kappa tau : Nat) : Nat := n

/-- Public B7-facing name for the raw B6 block horizon. -/
def chargedHorizon (n psi kappa tau : Nat) : Nat :=
  L6 n psi kappa tau

/-- Public B7-facing B6 mass denominator. -/
def massConstant (n psi kappa tau : Nat) : Nat :=
  Q6 n psi kappa tau

/-- Target/good bit on the literal current consumer. -/
def firstBirthGoodBit
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) :
    FC n psi kappa tau → List (Fin n) → Bool
  | _, [] => false
  | C, e :: es =>
      if BirthShortDoneTerminalObserver.birthEvent
          hpsi (by decide : 0 < 2) h2
          (C e) (C (ring.rightNeighbor e)) = true then
        true
      else
        firstBirthGoodBit hpsi h2 ring
          (currentStep hpsi h2 ring C e) es

/-- Exact closure hypothesis expected by `BirthPhaseGenericRenewal`. -/
def hclosed6
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) : Prop :=
  ∀ C : FC n psi kappa tau,
    BirthPhaseGenericRenewal.RenewalAllowed
      (B6Carrier hpsi h2 ring)
      (B6ReacquireCarrier hpsi h2 ring) C →
    ∀ w : List (Fin n),
      w.length = L6 n psi kappa tau →
      firstBirthGoodBit hpsi h2 ring C w = false →
      BirthPhaseGenericRenewal.RenewalAllowed
        (B6Carrier hpsi h2 ring)
        (B6ReacquireCarrier hpsi h2 ring)
        (BirthPhaseGenericRenewal.rawEndpoint
          (currentStep hpsi h2 ring) C w)

/-- Exact good-word mass hypothesis expected by `BirthPhaseGenericRenewal`. -/
def hmass6
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) : Prop :=
  ∀ C : FC n psi kappa tau,
    BirthPhaseGenericRenewal.RenewalAllowed
      (B6Carrier hpsi h2 ring)
      (B6ReacquireCarrier hpsi h2 ring) C →
    n ^ L6 n psi kappa tau ≤
      Q6 n psi kappa tau *
        FixedSpanRenewalPayload.wordSum n
          (L6 n psi kappa tau)
          (BirthPhaseGenericRenewal.goodWeight
            (firstBirthGoodBit hpsi h2 ring) C)

/-- Constant rank used when feeding B6 to the generic renewal theorem. -/
def rank6 (_ : FC n psi kappa tau) : Nat := 1

/-- B6 has a one-level rank budget. -/
def R6 : Nat := 1

/-- One extra Bellman half-life gives the `1/(2n)` allocation used for B5 and
B6 composition. -/
def halfBudgetK (n Q : Nat) : Nat :=
  BirthPhaseGenericRenewal.renewalK Q (Nat.log2 n + 2)

/-- Amplified B6 suffix horizon for the half-budget tail. -/
def halfBudgetHorizon
    (n psi kappa tau : Nat) : Nat :=
  halfBudgetK n (Q6 n psi kappa tau) *
    L6 n psi kappa tau * R6

theorem B6Carrier_to_reacquire
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (hC : B6Carrier hpsi h2 ring C) :
    B6ReacquireCarrier hpsi h2 ring C := by
  rcases hC with ⟨hzero, e, hhandoff, hready⟩
  rcases hhandoff with ⟨bit, hlive, hwriter⟩
  exact ⟨hzero, e, hwriter, hready⟩

theorem chargedHorizon_eq_one (n psi kappa tau : Nat) :
    chargedHorizon n psi kappa tau = 1 := by
  rfl

theorem massConstant_eq_n (n psi kappa tau : Nat) :
    massConstant n psi kappa tau = n := by
  rfl

theorem Q6_pos
    (ring : DirectedRing n) (psi kappa tau : Nat) :
    0 < Q6 n psi kappa tau := by
  simpa [Q6] using ring.hn

theorem rank6_pos (C : FC n psi kappa tau) :
    1 ≤ rank6 C := by
  simp [rank6]

theorem rank6_bound (C : FC n psi kappa tau) :
    rank6 C ≤ R6 := by
  simp [rank6, R6]

theorem rank6_mono
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (w : List (Fin n)) :
    rank6
        (BirthPhaseGenericRenewal.rawEndpoint
          (currentStep hpsi h2 ring) C w) ≤
      rank6 C := by
  simp [rank6]

theorem rank6_good
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (w : List (Fin n))
    (hg : firstBirthGoodBit hpsi h2 ring C w = true) :
    firstBirthGoodBit hpsi h2 ring C w = true ∨
      rank6
          (BirthPhaseGenericRenewal.rawEndpoint
            (currentStep hpsi h2 ring) C w) <
        rank6 C := by
  exact Or.inl hg

end BirthPhaseCapToFirstBirth

#print axioms BirthPhaseCapToFirstBirth.B6Carrier_to_reacquire
#print axioms BirthPhaseCapToFirstBirth.chargedHorizon_eq_one
#print axioms BirthPhaseCapToFirstBirth.massConstant_eq_n
#print axioms BirthPhaseCapToFirstBirth.Q6_pos
#print axioms BirthPhaseCapToFirstBirth.rank6_pos
#print axioms BirthPhaseCapToFirstBirth.rank6_bound
#print axioms BirthPhaseCapToFirstBirth.rank6_mono
#print axioms BirthPhaseCapToFirstBirth.rank6_good
