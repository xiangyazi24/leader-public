import Leader.Wu.Birth.ResetFreeControlled


namespace BirthB1ResetFreeEntranceMass


open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open BirthB1ResetFreeControlled
open BirthB1ReacquireReentryMass
open PPLLLeaderCreationCleanupRepair


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


variable {n psi kappa tau : Nat}


abbrev FC (n psi kappa tau : Nat) :=
  BirthPhaseWait2BlockProgress.FC n psi kappa tau


/-- No physical leader is presently stored anywhere. -/
def Leaderless (C : FC n psi kappa tau) : Prop :=
  forall i, (rawAt C i).leader = false


/-- The priority premise needed by the checked reset-drain cone. -/
def NoActiveDeletionAt (C : FC n psi kappa tau) : Prop :=
  forall i, deletionActive (C i).core.erase = false


/-- A physical leader has been reached; B1 may stop successfully here. -/
def HasPhysicalLeader (C : FC n psi kappa tau) : Prop :=
  exists i, (rawAt C i).leader = true


/-- One unit for each live physical reset command. -/
def resetMassAt (C : FC n psi kappa tau) (i : Fin n) : Nat :=
  if (rawAt C i).reset_cmd = true then 1 else 0


/-- Global stale-reset rank used by the drain composition. -/
def resetCount (C : FC n psi kappa tau) : Nat :=
  (List.ofFn (fun i : Fin n => resetMassAt C i)).sum


/-- Along a drain word no interaction may increase the global reset rank.
Movement is allowed: the Boolean may move to a new site, but not multiply. -/
def ResetCountNonincreaseAlong
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n) :
    FC n psi kappa tau -> List (Fin n) -> Prop
  | _, [] => True
  | C, e :: es =>
      let D := BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e
      resetCount D <= resetCount C /\
        ResetCountNonincreaseAlong hpsi h2 ring D es


/-- Exact missing item-1 contract for the literal B1 consumer.
`hpsiLe` is the bound used by the checked clockwise construction. -/
def OneResetDrainCurrentStep2
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 1 < n)
    (hpsiLe : psi <= n) (kappa : Nat)
    (ring : DirectedRing n) : Prop :=
  forall (C : FC n psi kappa tau),
    Leaderless C ->
    NoActiveDeletionAt C ->
    forall root : Fin n, (rawAt C root).reset_cmd = true ->
      exists word : List (Fin n),
        word.length <= 2 * n /\
        let D := prefixEndpoint hpsi h2 ring C word
        HasPhysicalLeader D \/
          (Leaderless D /\
            resetCount D < resetCount C /\
            ResetCountNonincreaseAlong hpsi h2 ring C word)


/-- Exact item-2 composition target.  A leader hit stops the word; otherwise
all stale reset commands have drained. -/
def AllResetDrainCurrentStep2
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 1 < n)
    (hpsiLe : psi <= n) (kappa : Nat)
    (ring : DirectedRing n) : Prop :=
  forall (C : FC n psi kappa tau),
    Leaderless C ->
    NoActiveDeletionAt C ->
      exists word : List (Fin n),
        word.length <= 2 * n * n /\
        let D := prefixEndpoint hpsi h2 ring C word
        HasPhysicalLeader D \/
          (Leaderless D /\ resetCount D = 0 /\
            ResetCountNonincreaseAlong hpsi h2 ring C word)


/-- Length consumed by the prescribed all-reset drain. -/
abbrev resetFreeDrainBudget (n : Nat) : Nat := 2 * n * n


/-- Reciprocal mass supplied by one prescribed drain prefix. -/
def resetFreeEntranceDrainQ (n : Nat) : Nat :=
  n ^ resetFreeDrainBudget n


/-- Indicator for the strengthened entrance event. -/
noncomputable def ResetFreeControlledEntranceSuccessBit
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (Controlled : FC n psi kappa tau -> Prop)
    (C : FC n psi kappa tau) (u : List (Fin n)) : Nat :=
  @ite Nat
    (ResetFreeControlledEntranceSuccess
      hpsi h2 hn kappa tau ring anchor Controlled C u)
    (Classical.propDecidable _) 1 0


/-- Exact strengthened entrance-mass target with the denominator actually
provided by the single-prescribed-word drain argument. -/
def ResetFreeControlledEntranceSuccessMass
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (Controlled : FC n psi kappa tau -> Prop) : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
      n ^ resetFreeControlledEntranceL n <=
        resetFreeEntranceDrainQ n *
          FixedSpanRenewalPayload.wordSum n
            (resetFreeControlledEntranceL n)
            (ResetFreeControlledEntranceSuccessBit
              hpsi h2 hn kappa tau ring anchor Controlled C)


/-- Conservative two-phase constants after composing the drain entrance with
one existing `1/8` controlled-exit block. -/
abbrev resetFreeControlledReacquireL (n : Nat) : Nat := 32 * n * n


def resetFreeControlledReacquireQ (n : Nat) : Nat :=
  8 * resetFreeEntranceDrainQ n


theorem drainBudget_fits_entrance (n : Nat) :
    resetFreeDrainBudget n <= resetFreeControlledEntranceL n := by
  unfold resetFreeDrainBudget resetFreeControlledEntranceL
  exact Nat.mul_le_mul_right n (by omega)


theorem resetFreeControlledReacquire_constants (n : Nat) :
    resetFreeControlledReacquireL n = 32 * n * n /\
      resetFreeControlledReacquireQ n = 8 * n ^ (2 * n * n) := by
  unfold resetFreeControlledReacquireL resetFreeControlledReacquireQ resetFreeEntranceDrainQ
  exact ⟨by simp [resetFreeControlledEntranceL], rfl⟩


end BirthB1ResetFreeEntranceMass


#print axioms BirthB1ResetFreeEntranceMass.drainBudget_fits_entrance
#print axioms BirthB1ResetFreeEntranceMass.resetFreeControlledReacquire_constants
