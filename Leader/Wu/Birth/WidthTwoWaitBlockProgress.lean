import Leader.Wu.Birth.WidthTwoWaitTransfer
import Leader.Wu.Birth.WaitClockMassDirtyMass
import Leader.Wu.Birth.GenericRenewal
import Leader.Wu.Birth.ShortDoneTerminalConsumer
import Leader.Wu.Scheduler.FixedSpanRenewalPayload




set_option autoImplicit false
set_option pp.structureInstances false




namespace BirthPhaseWait2BlockProgress




open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair




variable {n psi kappa tau : Nat}




/-- Canonical full configuration: use B2's alias instead of introducing a
second `FC` whose elaboration can drift from the current R4 configuration. -/
abbrev FC (n psi kappa tau : Nat) :=
  BirthPhaseWait2Transfer.FC n psi kappa tau




/-- Literal current consumer, with the physical short-WAIT width fixed to two. -/
def currentStep2
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n)
    (C : FC n psi kappa tau) (e : Fin n) :
    FC n psi kappa tau :=
  BirthShortDoneTerminalConsumer.step
    hpsi (by decide : 0 < 2) h2 ring C e




/-- Repair of the adapter equality.  The missing Consumer import and
Expiring namespace are now explicit, and the configuration type is B2's
canonical `FC`. -/
theorem hostStep_eq_currentStep2
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n)
    (C : FC n psi kappa tau) (e : Fin n) :
    BirthPhaseWait2Transfer.hostStep hpsi h2 ring C e =
      currentStep2 hpsi h2 ring C e := by
  simpa [BirthPhaseWait2Transfer.hostStep,
    BirthShortDoneTerminalPassiveR4.hostStep,
    currentStep2,
    BirthShortDoneTerminalConsumer.step,
    BirthShortDoneTerminalConsumer.protocol] using
    (PPLLResearchFormulation.localStep_eq_protocol_step
      (BirthShortDoneTerminalConsumer.protocol
        hpsi (by decide : 0 < 2) h2 kappa tau) ring C e)




/-- Physical width-two terminal count at the tracked Local3 anchor. -/
def shortCountAt
    (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) : Nat :=
  (C (ring.rightNeighbor anchor)).core.core.count.val




/-- B4/B5 fixed raw-word horizon.  At width two this is `6*n`. -/
abbrev L (n : Nat) : Nat :=
  BirthWaitClockMass.DirtyMass.horizon n 2




/-- Reciprocal dirty-success mass at width two. -/
def Q : Nat := 128




/-- Uniform rank ceiling. -/
def R (kappa : Nat) : Nat := kappa + 1




theorem Q_pos : 0 < Q := by
  decide




/-- `requestedLength 2 = 6`, so the dirty theorem's factor is exactly 128. -/
theorem dirty_factor_eq_Q :
    2 ^ (BirthWaitClockMass.DirtyMass.requestedLength 2 + 1) = Q := by
  decide




/-- Bare B2 Local3 state, before adding the sub-cap condition required by the
raw dirty-mass theorem. -/
def LocalCarrier
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) : Prop :=
  BirthPhaseWait2Transfer.LocalWait2Carrier
    hpsi h2 hn ring anchor C




/-- Active renewal carrier.  Capped states are not active starts. -/
def Carrier
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) : Prop :=
  LocalCarrier hpsi h2 hn ring anchor C /\
    shortCountAt ring anchor C < kappa




/-- A cap occurs somewhere in this literal original scheduler word.  Since the
predicate is prefix-existential, it is the appropriate block Boolean for the
first-cap target. -/
def FirstCapWithin
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n)
    (C : FC n psi kappa tau) (u : List (Fin n)) : Prop :=
  exists pre : List (Fin n), exists e : Fin n, exists post : List (Fin n),
    u = pre ++ (e :: post) /\
      BirthShortDoneTerminalPassiveR4.RowCap2
        hpsi h2 kappa ring
        (pre.foldl (currentStep2 hpsi h2 ring) C) e




/-- Certified-renewal target: first cap somewhere in the block. -/
noncomputable def target
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n)
    (C : FC n psi kappa tau) (u : List (Fin n)) : Bool := by
  classical
  exact if FirstCapWithin hpsi h2 kappa ring C u then true else false




/-- Physical B4 outcome, retained as a compile-clean proposition. -/
def CapOrEndpointProgress
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (u : List (Fin n)) : Prop :=
  FirstCapWithin hpsi h2 kappa ring C u \/
    shortCountAt ring anchor C <
      shortCountAt ring anchor
        (u.foldl (currentStep2 hpsi h2 ring) C)




noncomputable def capOrEndpointProgressBit
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (u : List (Fin n)) : Nat := by
  classical
  exact if CapOrEndpointProgress
    hpsi h2 kappa ring anchor C u then 1 else 0




noncomputable def capOrEndpointProgressNumerator
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) : Nat :=
  FixedSpanRenewalPayload.wordSum n (L n)
    (capOrEndpointProgressBit hpsi h2 kappa ring anchor C)




/-- The old target, now named as a proposition rather than left as an
unfinished theorem.  Proving this is still B4. -/
def FullHostWait2BlockProgressMass
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) : Prop :=
  n ^ L n <= Q *
    capOrEndpointProgressNumerator hpsi h2 kappa ring anchor C




/-- Proof-side recovery cone after executing a pre-cap B2 boundary row.  The
suffix is still the literal current consumer; no forged scheduler transition
is introduced. -/
def BoundaryRecoveryReachable
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (D : FC n psi kappa tau) : Prop :=
  exists C : FC n psi kappa tau, exists e : Fin n,
    exists tail : List (Fin n),
      Carrier hpsi h2 hn ring anchor C /\
      BirthShortDoneTerminalPassiveR4.RowPreCap2
        hpsi h2 kappa ring C e /\
      BirthPhaseWait2Transfer.LocalWait2BoundaryNow
        hn ring anchor e /\
      D = tail.foldl (currentStep2 hpsi h2 ring)
        (currentStep2 hpsi h2 ring C e)




/-- Explicit B1 side state: post-boundary, still sub-cap, and not currently a
Local3 carrier at this anchor.  B1's missing contract is the productive return
from this side state to `Carrier` (or a stronger target). -/
def Reacquire
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (D : FC n psi kappa tau) : Prop :=
  BoundaryRecoveryReachable
      hpsi h2 hn kappa tau ring anchor D /\
    Not (LocalCarrier hpsi h2 hn ring anchor D) /\
    shortCountAt ring anchor D < kappa




/-- Exactly the active union consumed by `BirthPhaseGenericRenewal`. -/
abbrev Allowed
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (D : FC n psi kappa tau) : Prop :=
  BirthPhaseGenericRenewal.RenewalAllowed
    (fun C : FC n psi kappa tau =>
      Carrier hpsi h2 hn ring anchor C)
    (fun C : FC n psi kappa tau =>
      Reacquire hpsi h2 hn kappa tau ring anchor C) D




/-- The one unresolved concrete adapter datum.  On Carrier states this is
intended to be the pullback of `DirtyMass.DirtyIncreaseWithin`; on Reacquire
states it includes the B1 re-acquisition part before applying the same dirty
certificate. -/
abbrev DirtySuccessRel (n psi kappa tau : Nat) :=
  FC n psi kappa tau -> List (Fin n) -> Prop




/-- B4 source event.  Keeping the relation explicit avoids inventing the
schematic `projectWait2` that is not present on current main. -/
noncomputable def good
    (DirtySuccess : DirtySuccessRel n psi kappa tau)
    (C : FC n psi kappa tau) (u : List (Fin n)) : Bool := by
  classical
  exact if DirtySuccess C u then true else false




/-- Natural first-cap deficit rank. -/
def rank
    (kappa : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) : Nat :=
  kappa + 1 - shortCountAt ring anchor C




/-- Exact `hclosed` proposition of `BirthPhaseGenericRenewal`. -/
def HClosed
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  forall x : FC n psi kappa tau,
    Allowed hpsi h2 hn kappa tau ring anchor x ->
    forall u : List (Fin n), u.length = L n ->
      target hpsi h2 kappa ring x u = false ->
      Allowed hpsi h2 hn kappa tau ring anchor
        (BirthPhaseGenericRenewal.rawEndpoint
          (currentStep2 hpsi h2 ring) x u)




/-- Exact `hpos` proposition. -/
def HPos
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  forall x : FC n psi kappa tau,
    Allowed hpsi h2 hn kappa tau ring anchor x ->
      1 <= rank kappa ring anchor x




/-- Exact `hbound` proposition. -/
def HBound
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  forall x : FC n psi kappa tau,
    Allowed hpsi h2 hn kappa tau ring anchor x ->
      rank kappa ring anchor x <= R kappa




/-- Exact `hmono` proposition. -/
def HMono
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  forall x : FC n psi kappa tau,
    Allowed hpsi h2 hn kappa tau ring anchor x ->
    forall u : List (Fin n), u.length = L n ->
      target hpsi h2 kappa ring x u = false ->
      rank kappa ring anchor
          (BirthPhaseGenericRenewal.rawEndpoint
            (currentStep2 hpsi h2 ring) x u) <=
        rank kappa ring anchor x




/-- Exact `hgood` proposition. -/
def HGood
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (DirtySuccess : DirtySuccessRel n psi kappa tau) : Prop :=
  forall x : FC n psi kappa tau,
    Allowed hpsi h2 hn kappa tau ring anchor x ->
    forall u : List (Fin n), u.length = L n ->
      good DirtySuccess x u = true ->
      target hpsi h2 kappa ring x u = true \/
        rank kappa ring anchor
            (BirthPhaseGenericRenewal.rawEndpoint
              (currentStep2 hpsi h2 ring) x u) <
          rank kappa ring anchor x




/-- Exact `hmass` proposition. -/
def HMass
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (DirtySuccess : DirtySuccessRel n psi kappa tau) : Prop :=
  forall x : FC n psi kappa tau,
    Allowed hpsi h2 hn kappa tau ring anchor x ->
      n ^ L n <= Q *
        FixedSpanRenewalPayload.wordSum n (L n)
          (BirthPhaseGenericRenewal.goodWeight
            (good DirtySuccess) x)




/-! Immediate adapter/rank facts. -/




theorem shortCountAt_lt_succ
    (kappa : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) :
    shortCountAt ring anchor C < kappa + 1 := by
  simpa [shortCountAt] using
    (C (ring.rightNeighbor anchor)).core.core.count.isLt




theorem rank_pos
    (kappa : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) :
    1 <= rank kappa ring anchor C := by
  have hc := shortCountAt_lt_succ kappa ring anchor C
  unfold rank
  omega




theorem rank_le_R
    (kappa : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) :
    rank kappa ring anchor C <= R kappa := by
  unfold rank R
  omega




/-- Rank nonincrease is exactly tracked-count nondecrease. -/
theorem rank_le_iff_shortCount_le
    (kappa : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C D : FC n psi kappa tau) :
    rank kappa ring anchor D <= rank kappa ring anchor C <->
      shortCountAt ring anchor C <= shortCountAt ring anchor D := by
  have hC := shortCountAt_lt_succ kappa ring anchor C
  have hD := shortCountAt_lt_succ kappa ring anchor D
  unfold rank
  omega




/-- Strict rank drop is exactly strict endpoint count increase. -/
theorem rank_lt_iff_shortCount_lt
    (kappa : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C D : FC n psi kappa tau) :
    rank kappa ring anchor D < rank kappa ring anchor C <->
      shortCountAt ring anchor C < shortCountAt ring anchor D := by
  have hC := shortCountAt_lt_succ kappa ring anchor C
  have hD := shortCountAt_lt_succ kappa ring anchor D
  unfold rank
  omega




theorem target_true_iff
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n)
    (C : FC n psi kappa tau) (u : List (Fin n)) :
    target hpsi h2 kappa ring C u = true <->
      FirstCapWithin hpsi h2 kappa ring C u := by
  classical
  simp [target]




theorem good_true_iff
    (DirtySuccess : DirtySuccessRel n psi kappa tau)
    (C : FC n psi kappa tau) (u : List (Fin n)) :
    good DirtySuccess C u = true <-> DirtySuccess C u := by
  classical
  simp [good]




/-- The post-boundary side-state definition really contains the immediate
executed boundary successor whenever that successor has left Local3 and is
still sub-cap. -/
theorem boundary_step_is_reacquire
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor e : Fin n)
    (C : FC n psi kappa tau)
    (hC : Carrier hpsi h2 hn ring anchor C)
    (hpre : BirthShortDoneTerminalPassiveR4.RowPreCap2
      hpsi h2 kappa ring C e)
    (hboundary : BirthPhaseWait2Transfer.LocalWait2BoundaryNow
      hn ring anchor e)
    (hbreak : Not (LocalCarrier hpsi h2 hn ring anchor
      (currentStep2 hpsi h2 ring C e)))
    (hsub : shortCountAt ring anchor
      (currentStep2 hpsi h2 ring C e) < kappa) :
    Reacquire hpsi h2 hn kappa tau ring anchor
      (currentStep2 hpsi h2 ring C e) := by
  refine ⟨?_, hbreak, hsub⟩
  exact ⟨C, e, [], hC, hpre, hboundary, rfl⟩




/-- The two arithmetic renewal hypotheses are unconditional for this rank. -/
theorem hpos_proved
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) :
    HPos hpsi h2 hn kappa tau ring anchor := by
  intro x _hx
  exact rank_pos kappa ring anchor x




theorem hbound_proved
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) :
    HBound hpsi h2 hn kappa tau ring anchor := by
  intro x _hx
  exact rank_le_R kappa ring anchor x




/-- Exact reduction of `hmono` to the missing target-free physical count
nondecrease statement. -/
theorem hmono_of_shortCount_mono
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (hcount : forall x : FC n psi kappa tau,
      Allowed hpsi h2 hn kappa tau ring anchor x ->
      forall u : List (Fin n), u.length = L n ->
        target hpsi h2 kappa ring x u = false ->
        shortCountAt ring anchor x <=
          shortCountAt ring anchor
            (BirthPhaseGenericRenewal.rawEndpoint
              (currentStep2 hpsi h2 ring) x u)) :
    HMono hpsi h2 hn kappa tau ring anchor := by
  intro x hx u hlen ht
  apply (rank_le_iff_shortCount_le kappa ring anchor x
    (BirthPhaseGenericRenewal.rawEndpoint
      (currentStep2 hpsi h2 ring) x u)).2
  exact hcount x hx u hlen ht




/-- Exact reduction of `hgood` to B3's pointwise dirty-success bridge. -/
theorem hgood_of_dirty_bridge
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (DirtySuccess : DirtySuccessRel n psi kappa tau)
    (hbridge : forall x : FC n psi kappa tau,
      Allowed hpsi h2 hn kappa tau ring anchor x ->
      forall u : List (Fin n), u.length = L n ->
        DirtySuccess x u ->
        target hpsi h2 kappa ring x u = true \/
          shortCountAt ring anchor x <
            shortCountAt ring anchor
              (BirthPhaseGenericRenewal.rawEndpoint
                (currentStep2 hpsi h2 ring) x u)) :
    HGood hpsi h2 hn kappa tau ring anchor DirtySuccess := by
  intro x hx u hlen hg
  have hd : DirtySuccess x u :=
    (good_true_iff DirtySuccess x u).1 hg
  rcases hbridge x hx u hlen hd with ht | hp
  · exact Or.inl ht
  · exact Or.inr
      ((rank_lt_iff_shortCount_lt kappa ring anchor x
        (BirthPhaseGenericRenewal.rawEndpoint
          (currentStep2 hpsi h2 ring) x u)).2 hp)




theorem hmass_of_source
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (DirtySuccess : DirtySuccessRel n psi kappa tau)
    [hdec : forall x u, Decidable (DirtySuccess x u)]
    (hsource : forall x : FC n psi kappa tau,
      Allowed hpsi h2 hn kappa tau ring anchor x ->
        n ^ L n <= Q *
          FixedSpanRenewalPayload.wordSum n (L n)
            (fun u => if DirtySuccess x u then 1 else 0)) :
    HMass hpsi h2 hn kappa tau ring anchor DirtySuccess := by
  intro x hx
  have hweight :
      BirthPhaseGenericRenewal.goodWeight (good DirtySuccess) x =
        (fun u => if DirtySuccess x u then 1 else 0) := by
    funext u
    by_cases h : DirtySuccess x u
    · simp only [BirthPhaseGenericRenewal.goodWeight, good, h, if_pos]
    · simp [BirthPhaseGenericRenewal.goodWeight, good, h]
  rw [hweight]
  exact hsource x hx




#print axioms BirthPhaseWait2BlockProgress.hostStep_eq_currentStep2
#print axioms BirthPhaseWait2BlockProgress.dirty_factor_eq_Q
#print axioms BirthPhaseWait2BlockProgress.rank_pos
#print axioms BirthPhaseWait2BlockProgress.rank_le_R
#print axioms BirthPhaseWait2BlockProgress.rank_le_iff_shortCount_le
#print axioms BirthPhaseWait2BlockProgress.rank_lt_iff_shortCount_lt
#print axioms BirthPhaseWait2BlockProgress.target_true_iff
#print axioms BirthPhaseWait2BlockProgress.good_true_iff
#print axioms BirthPhaseWait2BlockProgress.boundary_step_is_reacquire
#print axioms BirthPhaseWait2BlockProgress.hpos_proved
#print axioms BirthPhaseWait2BlockProgress.hbound_proved
#print axioms BirthPhaseWait2BlockProgress.hmono_of_shortCount_mono
#print axioms BirthPhaseWait2BlockProgress.hgood_of_dirty_bridge
#print axioms BirthPhaseWait2BlockProgress.hmass_of_source




end BirthPhaseWait2BlockProgress
