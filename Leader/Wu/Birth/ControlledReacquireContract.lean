import Leader.Wu.Birth.ReacquirePhaseMass


/-!
# Controlled B4 Reacquire contract


This file is the fixture-free half of the B4 Mono decision.  It contains only
the adopted controlled Reacquire interface and its repaired quantitative
constants.  In particular it performs no closed configuration or scheduler-run
computation.
-/


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace BirthB4ReacquireMonoDecision


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLExpiringComparisonRepair
open BirthB1ReacquireReentryMass


variable {n psi kappa tau : Nat}


abbrev FC (n psi kappa tau : Nat) :=
  BirthPhaseWait2BlockProgress.FC n psi kappa tau


/-- Entrance block: the original `16*n*n` Reacquire block. -/
abbrev controlledEntranceL (n : Nat) : Nat := fallbackReacquireL n


/-- Repaired total controlled block: definitionally `32*n*n`. -/
abbrev controlledReacquireL (n : Nat) : Nat :=
  controlledEntranceL n + fallbackReacquireL n


/-- Two `1/8` stages: repaired denominator `64`. -/
abbrev controlledReacquireQ : Nat :=
  fallbackReacquireQ * fallbackReacquireQ


/-- Proof-side controlled subclass; no protocol state is added. -/
def ControlledReacquire
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (Controlled : FC n psi kappa tau -> Prop)
    (C : FC n psi kappa tau) : Prop :=
  BirthPhaseWait2BlockProgress.Reacquire
      hpsi h2 hn kappa tau ring anchor C /\ Controlled C


/-- Once the entrance has reached the controlled subclass, the original
fallback block is rank-monotone on target-free words. -/
def ControlledReacquireMono
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (Controlled : FC n psi kappa tau -> Prop) : Prop :=
  forall C : FC n psi kappa tau,
    ControlledReacquire
        hpsi h2 hn kappa tau ring anchor Controlled C ->
    forall u : List (Fin n),
      u.length = fallbackReacquireL n ->
      BirthPhaseWait2BlockProgress.target
          hpsi h2 kappa ring C u = false ->
        BirthPhaseWait2BlockProgress.rank kappa ring anchor
            (prefixEndpoint hpsi h2 ring C u) <=
          BirthPhaseWait2BlockProgress.rank kappa ring anchor C


/-- Entrance success either hits the target or reaches the controlled subclass
without increasing the fixed B4 rank (`rank D <= rank C`). -/
def ControlledEntranceSuccess
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (Controlled : FC n psi kappa tau -> Prop)
    (C : FC n psi kappa tau) (u : List (Fin n)) : Prop :=
  BirthPhaseWait2BlockProgress.target
      hpsi h2 kappa ring C u = true \/
    let D := prefixEndpoint hpsi h2 ring C u
    ControlledReacquire
        hpsi h2 hn kappa tau ring anchor Controlled D /\
      BirthPhaseWait2BlockProgress.rank kappa ring anchor D <=
        BirthPhaseWait2BlockProgress.rank kappa ring anchor C


noncomputable def ControlledEntranceBit
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (Controlled : FC n psi kappa tau -> Prop)
    (C : FC n psi kappa tau) (u : List (Fin n)) : Nat :=
  @ite Nat
    (ControlledEntranceSuccess
      hpsi h2 hn kappa tau ring anchor Controlled C u)
    (Classical.propDecidable _) 1 0


/-- `1/8` entrance mass into target or controlled Reacquire. -/
def ControlledReacquireEntranceMass
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (Controlled : FC n psi kappa tau -> Prop) : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
      n ^ controlledEntranceL n <=
        fallbackReacquireQ *
          FixedSpanRenewalPayload.wordSum n (controlledEntranceL n)
            (ControlledEntranceBit
              hpsi h2 hn kappa tau ring anchor Controlled C)


/-- At `n = 4`, `L_R = 256`, hence `L_R' = 512`, and `Q_R' = 64`. -/
theorem controlled_cost_four :
    controlledEntranceL 4 = 256 /\
      controlledReacquireL 4 = 512 /\
      controlledReacquireQ = 64 := by
  change fallbackReacquireL 4 = 256 /\
    fallbackReacquireL 4 + fallbackReacquireL 4 = 512 /\
    fallbackReacquireQ * fallbackReacquireQ = 64
  rw [BirthB1ReacquirePhaseMass.fallbackReacquireL_four]
  decide


end BirthB4ReacquireMonoDecision


#print axioms BirthB4ReacquireMonoDecision.ControlledReacquireMono
#print axioms BirthB4ReacquireMonoDecision.ControlledEntranceSuccess
#print axioms BirthB4ReacquireMonoDecision.ControlledReacquireEntranceMass
#print axioms BirthB4ReacquireMonoDecision.controlled_cost_four
