import Leader.PPL.Transition
import Leader.PPL.Probability.EncounterProjection
import Leader.PPL.Probability.LotteryCounts
import Init.Omega

namespace PPL.Modes.SignalLineage

set_option autoImplicit false

structure SignalTag (n : Nat) where
  origin : Fin n
  arm : Nat
  deriving DecidableEq, Repr

structure GhostConfig (n psi kappa : Nat) where
  physical : Fin n → PPL.State psi kappa
  owner : Fin n → Option (SignalTag n)
  nextArm : Fin n → Nat

def erase {n psi kappa : Nat}
    (g : GhostConfig n psi kappa) :
    Fin n → PPL.State psi kappa :=
  g.physical

def step {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Fin n → PPL.State psi kappa)
    (e : Fin n) :
    Fin n → PPL.State psi kappa :=
  PopulationProtocol.step (PPL.protocol psi kappa) ring C e

private def writePair {n : Nat} {α : Type}
    (f : Fin n → α)
    (i : Fin n) (xi : α)
    (j : Fin n) (xj : α) :
    Fin n → α :=
  fun k =>
    if k = i then xi
    else if k = j then xj
    else f k

private def bumpAt {n : Nat}
    (f : Fin n → Nat) (i : Fin n) :
    Fin n → Nat :=
  fun k => if k = i then f k + 1 else f k

def freshTag {n psi kappa : Nat}
    (g : GhostConfig n psi kappa) (i : Fin n) :
    SignalTag n :=
  { origin := i, arm := g.nextArm i }

def armedTTL {n psi kappa : Nat}
    (g : GhostConfig n psi kappa) (i : Fin n) : Nat :=
  if (g.physical i).leader = true then
    kappa
  else
    (g.physical i).signalR.val

def armedOwner {n psi kappa : Nat}
    (g : GhostConfig n psi kappa) (i : Fin n) :
    Option (SignalTag n) :=
  if (g.physical i).leader = true then
    some (freshTag g i)
  else
    g.owner i

/--
Ownership of the physical signal that can remain at the responder after
DetermineMode. This is Algorithm-4 line 40: maximum TTL wins, with the
left/post-arm signal winning ties.
-/
def winnerOwner {n psi kappa : Nat}
    (g : GhostConfig n psi kappa)
    (i j : Fin n) : Option (SignalTag n) :=
  if (g.physical j).signalR.val ≤ armedTTL g i then
    armedOwner g i
  else
    g.owner j

/--
The physical component is the literal P_PL step. Ghost ownership is updated
only for the two interacted sites because signalR is written only by
DetermineMode. The final responder signal gates whether the winner tag remains:
TTL decrement to zero therefore terminates the tag automatically.
-/
def ghostStep {n psi kappa : Nat}
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e : Fin n) :
    GhostConfig n psi kappa :=
  let j := ring.rightNeighbor e
  let C' := step ring g.physical e
  let win := winnerOwner g e j
  let rOwner :=
    if 0 < (C' j).signalR.val then win else none
  {
    physical := C'
    owner := writePair g.owner e none j rOwner
    nextArm :=
      if (g.physical e).leader = true then
        bumpAt g.nextArm e
      else
        g.nextArm
  }

def OwnerMatches {n psi kappa : Nat}
    (g : GhostConfig n psi kappa) : Prop :=
  ∀ i : Fin n,
    g.owner i = none ↔ (g.physical i).signalR.val = 0

def NoCloning {n psi kappa : Nat}
    (g : GhostConfig n psi kappa) : Prop :=
  ∀ i j : Fin n, ∀ t : SignalTag n,
    g.owner i = some t →
    g.owner j = some t →
    i = j

def Issued {n psi kappa : Nat}
    (g : GhostConfig n psi kappa) : Prop :=
  ∀ i : Fin n, ∀ t : SignalTag n,
    g.owner i = some t →
    t.arm < g.nextArm t.origin

def LineageWellFormed {n psi kappa : Nat}
    (g : GhostConfig n psi kappa) : Prop :=
  OwnerMatches g ∧ NoCloning g ∧ Issued g

/--
Canonical epoch-start lift. Arm 0 is reserved for an arbitrary positive
initial signal; later genuine line-35 arms start at 1.
-/
def initialGhost {n psi kappa : Nat}
    (C : Fin n → PPL.State psi kappa) :
    GhostConfig n psi kappa :=
  {
    physical := C
    owner := fun i =>
      if 0 < (C i).signalR.val then
        some { origin := i, arm := 0 }
      else
        none
    nextArm := fun _ => 1
  }

def OwnersFrom {n psi kappa : Nat}
    (start current : GhostConfig n psi kappa) : Prop :=
  ∀ i : Fin n, ∀ t : SignalTag n,
    current.owner i = some t →
    ∃ j : Fin n, start.owner j = some t

def StartTagsGone {n psi kappa : Nat}
    (start current : GhostConfig n psi kappa) : Prop :=
  ∀ i : Fin n, ∀ t : SignalTag n,
    start.owner i = some t →
    ∀ j : Fin n, current.owner j ≠ some t

def Leaderless {n psi kappa : Nat}
    (g : GhostConfig n psi kappa) : Prop :=
  ∀ i : Fin n, (g.physical i).leader = false

def MaxTTLMergerOwnership {n psi kappa : Nat}
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e : Fin n) : Prop :=
  let j := ring.rightNeighbor e
  0 < ((ghostStep ring g e).physical j).signalR.val →
    (ghostStep ring g e).owner j =
      winnerOwner g e j

/-
The following named Props are the remaining kernel obligations. They are
definitions, not axioms. A downstream theorem may assume
SignalLineageOwnership only explicitly; there is no hidden theorem here.
-/

def OwnerMatchesPreserved {n psi kappa : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ g : GhostConfig n psi kappa, ∀ e : Fin n,
    2 ≤ psi →
    ring.rightNeighbor e ≠ e →
    LineageWellFormed g →
    OwnerMatches (ghostStep ring g e)

def NoCloningPreserved {n psi kappa : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ g : GhostConfig n psi kappa, ∀ e : Fin n,
    2 ≤ psi →
    ring.rightNeighbor e ≠ e →
    LineageWellFormed g →
    NoCloning (ghostStep ring g e)

def IssuedPreserved {n psi kappa : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ g : GhostConfig n psi kappa, ∀ e : Fin n,
    2 ≤ psi →
    ring.rightNeighbor e ≠ e →
    LineageWellFormed g →
    Issued (ghostStep ring g e)

def MaxTTLClause {n psi kappa : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ g : GhostConfig n psi kappa, ∀ e : Fin n,
    2 ≤ psi →
    ring.rightNeighbor e ≠ e →
    MaxTTLMergerOwnership ring g e

def RearmTerminatesPreserved {n psi kappa : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ g : GhostConfig n psi kappa, ∀ e : Fin n,
    2 ≤ psi →
    ring.rightNeighbor e ≠ e →
    LineageWellFormed g →
    (g.physical e).leader = true →
    ∀ t : SignalTag n,
      g.owner e = some t →
      ∀ k : Fin n,
        (ghostStep ring g e).owner k ≠ some t

def TagTTLNonincreasePreserved {n psi kappa : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ g : GhostConfig n psi kappa, ∀ e : Fin n,
    2 ≤ psi →
    ring.rightNeighbor e ≠ e →
    LineageWellFormed g →
    ∀ i j : Fin n, ∀ t : SignalTag n,
      g.owner i = some t →
      (ghostStep ring g e).owner j = some t →
      ((ghostStep ring g e).physical j).signalR.val ≤
        (g.physical i).signalR.val

def MovedWinnerHitsResetPreserved {n psi kappa : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ g : GhostConfig n psi kappa, ∀ e : Fin n,
    2 ≤ psi →
    ring.rightNeighbor e ≠ e →
    LineageWellFormed g →
    (g.physical e).leader = false →
    ∀ t : SignalTag n,
      g.owner e = some t →
      (ghostStep ring g e).owner (ring.rightNeighbor e) = some t →
      ((ghostStep ring g e).physical
        (ring.rightNeighbor e)).hits.val = 0

def LeaderlessCoveragePreserved {n psi kappa : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ start g : GhostConfig n psi kappa, ∀ e : Fin n,
    2 ≤ psi →
    ring.rightNeighbor e ≠ e →
    LineageWellFormed g →
    OwnersFrom start g →
    Leaderless g →
    OwnersFrom start (ghostStep ring g e)

/--
The exact Wave-2 ownership interface consumed by the mode proofs.
The final "all start tags gone => no physical signal" step is a theorem below,
not an additional assumption.
-/
def SignalLineageOwnership {n psi kappa : Nat}
    (ring : DirectedRing n) : Prop :=
  OwnerMatchesPreserved (psi := psi) (kappa := kappa) ring ∧
    NoCloningPreserved (psi := psi) (kappa := kappa) ring ∧
    IssuedPreserved (psi := psi) (kappa := kappa) ring ∧
    MaxTTLClause (psi := psi) (kappa := kappa) ring ∧
    RearmTerminatesPreserved (psi := psi) (kappa := kappa) ring ∧
    TagTTLNonincreasePreserved (psi := psi) (kappa := kappa) ring ∧
    MovedWinnerHitsResetPreserved (psi := psi) (kappa := kappa) ring ∧
    LeaderlessCoveragePreserved (psi := psi) (kappa := kappa) ring

@[simp] theorem ghostStep_erase
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e : Fin n) :
    erase (ghostStep ring g e) =
      step ring (erase g) e := by
  rfl

theorem initialGhost_ownerMatches
    {n psi kappa : Nat}
    (C : Fin n → PPL.State psi kappa) :
    OwnerMatches (initialGhost C) := by
  intro i
  by_cases h : 0 < (C i).signalR.val
  · have hz : (C i).signalR.val ≠ 0 := by omega
    simp [initialGhost, h, hz]
  · have hz : (C i).signalR.val = 0 := by omega
    simp [initialGhost, h, hz]

theorem initialGhost_noCloning
    {n psi kappa : Nat}
    (C : Fin n → PPL.State psi kappa) :
    NoCloning (initialGhost C) := by
  intro i j t hi hj
  by_cases hip : 0 < (C i).signalR.val
  · have hti : SignalTag.mk i 0 = t := by
      simpa [initialGhost, hip] using hi
    by_cases hjp : 0 < (C j).signalR.val
    · have htj : SignalTag.mk j 0 = t := by
        simpa [initialGhost, hjp] using hj
      have htag :
          SignalTag.mk i 0 = SignalTag.mk j 0 :=
        hti.trans htj.symm
      simpa using congrArg SignalTag.origin htag
    · simp [initialGhost, hjp] at hj
  · simp [initialGhost, hip] at hi

theorem initialGhost_issued
    {n psi kappa : Nat}
    (C : Fin n → PPL.State psi kappa) :
    Issued (initialGhost C) := by
  intro i t hi
  by_cases hip : 0 < (C i).signalR.val
  · have hti : SignalTag.mk i 0 = t := by
      simpa [initialGhost, hip] using hi
    rw [← hti]
    simp [initialGhost]
  · simp [initialGhost, hip] at hi

theorem initialGhost_wellFormed
    {n psi kappa : Nat}
    (C : Fin n → PPL.State psi kappa) :
    LineageWellFormed (initialGhost C) :=
  ⟨initialGhost_ownerMatches C,
    initialGhost_noCloning C,
    initialGhost_issued C⟩

theorem ghostStep_initiator_owner_none
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e : Fin n) :
    (ghostStep ring g e).owner e = none := by
  simp [ghostStep, writePair]

theorem ghostStep_responder_owner
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e : Fin n)
    (hself : ring.rightNeighbor e ≠ e) :
    (ghostStep ring g e).owner (ring.rightNeighbor e) =
      if 0 <
          (step ring g.physical e
            (ring.rightNeighbor e)).signalR.val then
        winnerOwner g e (ring.rightNeighbor e)
      else
        none := by
  simp [ghostStep, writePair, hself]

theorem ghostStep_maxTTL_merger_owner
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e : Fin n)
    (hself : ring.rightNeighbor e ≠ e) :
    MaxTTLMergerOwnership ring g e := by
  intro hpos
  have hp :
      0 <
        (step ring g.physical e
          (ring.rightNeighbor e)).signalR.val := by
    simpa [ghostStep] using hpos
  rw [ghostStep_responder_owner ring g e hself]
  simp [hp]

theorem maxTTLClause_holds
    {n psi kappa : Nat}
    (ring : DirectedRing n) :
    MaxTTLClause (psi := psi) (kappa := kappa) ring := by
  intro g e _ hself
  exact ghostStep_maxTTL_merger_owner ring g e hself

theorem ghostStep_nextArm_of_arm
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e : Fin n)
    (h : (g.physical e).leader = true) :
    (ghostStep ring g e).nextArm e =
      g.nextArm e + 1 := by
  simp [ghostStep, h, bumpAt]

theorem ghostStep_nextArm_of_no_arm
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e : Fin n)
    (h : (g.physical e).leader = false) :
    (ghostStep ring g e).nextArm =
      g.nextArm := by
  simp [ghostStep, h]

theorem freshTag_not_preowned
    {n psi kappa : Nat}
    (g : GhostConfig n psi kappa)
    (e : Fin n)
    (hissued : Issued g) :
    ∀ k : Fin n,
      g.owner k ≠ some (freshTag g e) := by
  intro k hk
  have hlt :=
    hissued k (freshTag g e) hk
  dsimp [freshTag] at hlt
  omega

theorem signal_free_of_start_tags_gone
    {n psi kappa : Nat}
    (start current : GhostConfig n psi kappa)
    (hmatch : OwnerMatches current)
    (hfrom : OwnersFrom start current)
    (hgone : StartTagsGone start current) :
    ∀ i : Fin n,
      (current.physical i).signalR.val = 0 := by
  intro i
  cases howner : current.owner i with
  | none =>
      exact (hmatch i).1 howner
  | some t =>
      obtain ⟨j, hj⟩ :=
        hfrom i t howner
      exact False.elim ((hgone j t hj i) howner)

end PPL.Modes.SignalLineage

#print axioms PPL.Modes.SignalLineage.ghostStep_erase
#print axioms PPL.Modes.SignalLineage.initialGhost_ownerMatches
#print axioms PPL.Modes.SignalLineage.initialGhost_noCloning
#print axioms PPL.Modes.SignalLineage.initialGhost_issued
#print axioms PPL.Modes.SignalLineage.initialGhost_wellFormed
#print axioms PPL.Modes.SignalLineage.ghostStep_initiator_owner_none
#print axioms PPL.Modes.SignalLineage.ghostStep_responder_owner
#print axioms PPL.Modes.SignalLineage.ghostStep_maxTTL_merger_owner
#print axioms PPL.Modes.SignalLineage.maxTTLClause_holds
#print axioms PPL.Modes.SignalLineage.ghostStep_nextArm_of_arm
#print axioms PPL.Modes.SignalLineage.ghostStep_nextArm_of_no_arm
#print axioms PPL.Modes.SignalLineage.freshTag_not_preowned
#print axioms PPL.Modes.SignalLineage.signal_free_of_start_tags_gone
