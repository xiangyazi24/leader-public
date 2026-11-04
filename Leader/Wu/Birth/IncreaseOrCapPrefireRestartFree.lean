import Leader.Wu.Birth.IncreaseOrCapFourWayCoverage
import Leader.Core.ThreePortSerialCount

namespace BirthPhaseB3PrefireRestartFree

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLExpiringComparisonRepair
open BirthShortDoneTerminalPassiveR4
open BirthShortDoneTerminalPassiveLocal3
open BirthPhaseB3CoverageFour
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {n psi kappa tau : Nat}

abbrev FC (n psi kappa tau : Nat) :=
  BirthPhaseWait2BlockProgress.FC n psi kappa tau

/-- B4 success stopped at an earlier prefix.  Padding after that prefix is
irrelevant to this predicate. -/
def StoppedB4Progress
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (u : List (Fin n)) : Prop :=
  exists pre post,
    u = pre ++ post /\
      (BirthPhaseWait2BlockProgress.target
          hpsi h2 kappa ring C pre = true \/
        BirthPhaseWait2BlockProgress.rank kappa ring anchor
            (BirthPhaseGenericRenewal.rawEndpoint
              (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring)
              C pre) <
          BirthPhaseWait2BlockProgress.rank kappa ring anchor C)

/-- Physical form of the first dirty fire.  The raw-to-physical synchronization
missing from current main should produce exactly this certificate. -/
def PhysicalPrefire
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (pre : List (Fin n)) : Prop :=
  let Cpre := BirthPhaseGenericRenewal.rawEndpoint
    (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring) C pre
  BirthPhaseWait2BlockProgress.Carrier
      hpsi h2 hn ring anchor Cpre /\
    RowPreCap2 hpsi h2 kappa ring Cpre anchor /\
    BirthPhaseWait2BlockProgress.shortCountAt ring anchor C <=
      BirthPhaseWait2BlockProgress.shortCountAt ring anchor Cpre /\
    BirthPhaseWait2BlockProgress.shortCountAt ring anchor Cpre <
      BirthPhaseWait2BlockProgress.shortCountAt ring anchor
        (BirthPhaseWait2BlockProgress.currentStep2
          hpsi h2 ring Cpre anchor)

/-- Dirty success with the restart filter stopped at the physical fire.
Nothing is required of `post`. -/
def PrefireRestartFreeDirtySuccess
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (x : BirthPhaseB3DirtySuccess.CarrierState
      (kappa := kappa) (tau := tau) hpsi h2 hn ring anchor)
    (u : List (Fin n)) : Prop :=
  BirthPhaseB3DirtySuccess.DirtySuccess
      hpsi h2 hn ring anchor x u /\
    exists pre post,
      u = pre ++ (anchor :: post) /\
      (¬ SurvivingCrossingWithin
        hpsi h2 hn kappa tau ring anchor x.1 pre) /\
      PhysicalPrefire hpsi h2 hn kappa tau ring anchor x.1 pre

noncomputable def prefireRestartFreeDirtyBit
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (x : BirthPhaseB3DirtySuccess.CarrierState
      (kappa := kappa) (tau := tau) hpsi h2 hn ring anchor)
    (u : List (Fin n)) : Nat := by
  classical
  exact if PrefireRestartFreeDirtySuccess
    hpsi h2 hn kappa tau ring anchor x u then 1 else 0

theorem prefireRestartFreeDirtyBit_eq_one_iff
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (x : BirthPhaseB3DirtySuccess.CarrierState
      (kappa := kappa) (tau := tau) hpsi h2 hn ring anchor)
    (u : List (Fin n)) :
    prefireRestartFreeDirtyBit
        hpsi h2 hn kappa tau ring anchor x u = 1 <->
      PrefireRestartFreeDirtySuccess
        hpsi h2 hn kappa tau ring anchor x u := by
  classical
  unfold prefireRestartFreeDirtyBit
  by_cases h : PrefireRestartFreeDirtySuccess
      hpsi h2 hn kappa tau ring anchor x u <;> simp [h]

/-- The pre-fire event is already a stopped strict B4 rank drop. -/
theorem prefire_success_stopped_progress
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (x : BirthPhaseB3DirtySuccess.CarrierState
      (kappa := kappa) (tau := tau) hpsi h2 hn ring anchor)
    (u : List (Fin n))
    (h : PrefireRestartFreeDirtySuccess
      hpsi h2 hn kappa tau ring anchor x u) :
    StoppedB4Progress hpsi h2 kappa ring anchor x.1 u := by
  rcases h.2 with ⟨pre, post, hword, _hnorestart, hfire⟩
  let step := BirthPhaseWait2BlockProgress.currentStep2 (kappa := kappa) (tau := tau) hpsi h2 ring
  let Cpre := BirthPhaseGenericRenewal.rawEndpoint step x.1 pre
  change BirthPhaseWait2BlockProgress.Carrier
      hpsi h2 hn ring anchor Cpre /\
    RowPreCap2 hpsi h2 kappa ring Cpre anchor /\
    BirthPhaseWait2BlockProgress.shortCountAt ring anchor x.1 <=
      BirthPhaseWait2BlockProgress.shortCountAt ring anchor Cpre /\
    BirthPhaseWait2BlockProgress.shortCountAt ring anchor Cpre <
      BirthPhaseWait2BlockProgress.shortCountAt ring anchor
        (step Cpre anchor) at hfire
  have hinc : BirthPhaseWait2BlockProgress.shortCountAt ring anchor x.1 <
      BirthPhaseWait2BlockProgress.shortCountAt ring anchor
        (step Cpre anchor) :=
    Nat.lt_of_le_of_lt hfire.2.2.1 hfire.2.2.2
  have hdrop : BirthPhaseWait2BlockProgress.rank kappa ring anchor
        (step Cpre anchor) <
      BirthPhaseWait2BlockProgress.rank kappa ring anchor x.1 :=
    (BirthPhaseWait2BlockProgress.rank_lt_iff_shortCount_lt
      kappa ring anchor x.1 (step Cpre anchor)).2 hinc
  refine ⟨pre ++ [anchor], post, ?_, Or.inr ?_⟩
  · calc
      u = pre ++ (anchor :: post) := hword
      _ = (pre ++ [anchor]) ++ post := by simp [List.append_assoc]
  · simpa [step, Cpre, BirthPhaseGenericRenewal.rawEndpoint,
      List.foldl_append] using hdrop

/-- Existing four-way suffix classifier, now explicitly started after the
physical fire.  A surviving crossing in this suffix is the restart arm and
carries exact rank equality at that crossing. -/
theorem suffix_four_way_after_fire
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (pre post : List (Fin n))
    (htri : SuffixStopTrichotomy hpsi h2 hn kappa tau ring anchor
      (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring
        (BirthPhaseGenericRenewal.rawEndpoint
          (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring) C pre)
        anchor) post) :
    SuffixFourWay hpsi h2 hn kappa tau ring anchor
      (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring
        (BirthPhaseGenericRenewal.rawEndpoint
          (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring) C pre)
        anchor) post := by
  exact suffix_trichotomy_to_four_way
    hpsi h2 hn kappa tau ring anchor _ post htri

/-- Extra semantic premise needed only if B4 keeps its present endpoint HGood
rather than changing to stopped/restart success. -/
def PrefireEndpointPersistence
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  forall x : BirthPhaseB3DirtySuccess.CarrierState
      (kappa := kappa) (tau := tau) hpsi h2 hn ring anchor,
    forall u : List (Fin n),
      u.length = BirthPhaseWait2BlockProgress.L n ->
      PrefireRestartFreeDirtySuccess
        hpsi h2 hn kappa tau ring anchor x u ->
      BirthPhaseWait2BlockProgress.target
          hpsi h2 kappa ring x.1 u = true \/
        BirthPhaseWait2BlockProgress.rank kappa ring anchor
            (BirthPhaseGenericRenewal.rawEndpoint
              (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring)
              x.1 u) <
          BirthPhaseWait2BlockProgress.rank kappa ring anchor x.1

/-! Quantitative boundary. -/

def prefireRestartFreeQ : Nat := 2 * 3 ^ 6

theorem prefireRestartFreeQ_eq : prefireRestartFreeQ = 1458 := by
  decide

/-- Exact six-hit mass theorem still to be connected to the physical pre-fire
certificate.  The word horizon remains the original `6*n`. -/
def PrefireRestartFreeDirtyMass1458
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  forall x : BirthPhaseB3DirtySuccess.CarrierState
      (kappa := kappa) (tau := tau) hpsi h2 hn ring anchor,
    n ^ BirthPhaseWait2BlockProgress.L n <=
      prefireRestartFreeQ *
        FixedSpanRenewalPayload.wordSum n
          (BirthPhaseWait2BlockProgress.L n)
          (prefireRestartFreeDirtyBit
            hpsi h2 hn kappa tau ring anchor x)

private def ports
    (hn : 4 <= n) (a : Fin n)
    (ha2 : a != p2 hn) (haL : a != leftCross hn) :
    ThreePortSerialCount.Ports n where
  a := a
  b := p2 hn
  c := leftCross hn
  ab := by simpa only [bne_iff_ne] using ha2
  ac := by simpa only [bne_iff_ne] using haL
  bc := by
    intro h
    have hv := congrArg Fin.val h
    change 2 = n - 1 at hv
    omega

/-- Checked one-stage geometry: one requested port beats the two crossings
with at least quarter mass in `2*n` scheduler letters. -/
theorem one_stage_three_port_quarter
    (hn : 4 <= n) (a : Fin n)
    (ha2 : a != p2 hn) (haL : a != leftCross hn) :
    n ^ (2 * n) <=
      4 * successCount
        (ThreePortSerialCount.stageStep (ports hn a ha2 haL))
        (.active ()) (2 * n) := by
  exact ThreePortSerialCount.single_stage_quarter
    (ports hn a ha2 haL) (by omega)

end BirthPhaseB3PrefireRestartFree

#print axioms BirthPhaseB3PrefireRestartFree.prefireRestartFreeDirtyBit_eq_one_iff
#print axioms BirthPhaseB3PrefireRestartFree.prefire_success_stopped_progress
#print axioms BirthPhaseB3PrefireRestartFree.suffix_four_way_after_fire
#print axioms BirthPhaseB3PrefireRestartFree.prefireRestartFreeQ_eq
#print axioms BirthPhaseB3PrefireRestartFree.one_stage_three_port_quarter
