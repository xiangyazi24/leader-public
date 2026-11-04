import Leader.Wu.Coherence.OpenNoHazardUnframedCarriers


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2CoherenceV31MainClearTruth


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches R2CoherenceV31PhaseMainClear R2CoherenceV31ReachablePlus4 R2CoherenceV31ReachableReleaseOwner2 R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePlus2
open R2CoherenceV31OpenNoHazard
open R2CoherenceV31ReachablePlus2 R2CoherenceV31ReachablePlus3
open R2CoherenceV31ReachableAdjacentRoot
open R2CoherenceV31OpenNoHazardMainClear


variable {n ψ κ τ : Nat}


/-- Exactly the information freshness consumers need from `MainClearV3`. -/
def FreshnessClearV31 (u : Cell ψ κ τ) : Prop :=
  (raw u).path = .bot


theorem freshnessClear_of_mainClear
    (u : Cell ψ κ τ) (h : MainClearV3 u) : FreshnessClearV31 u := by
  unfold MainClearV3 R2CoherenceBranches.MainClear at h
  unfold FreshnessClearV31
  change u.phys.base.core.core.path = .bot
  exact h.2.1


theorem freshComponent_false_of_freshnessClear
    (u : Cell ψ κ τ) (k : Nat)
    (hm : FreshnessClearV31 u)
    (hf : R2Coherence.freshComponent (eraseCellV3 u) k) : False := by
  unfold FreshnessClearV31 at hm
  unfold R2Coherence.freshComponent at hf
  change
    (raw u).label.val = k ∧
      (match (raw u).path with
       | .bot => False
       | .some lab b =>
           lab.val = k ∧ b.val = (if (raw u).bit then 1 else 0)) at hf
  rw [hm] at hf
  exact hf.2


/-- Pair-local absence of every auxiliary carrier that can be imported. -/
def AuxImportEmptyV31 (l r : Cell ψ κ τ) : Prop :=
  (raw l).path2 = none ∧ (raw r).path2 = none ∧
  (raw l).path4 = none ∧ (raw r).path4 = none ∧
  (raw l).path5 = none ∧ (raw r).path5 = none ∧
  (raw l).p = false ∧ (raw r).p = false ∧
  (raw l).p_carry = false ∧ (raw r).p_carry = false


theorem auxImportEmpty_of_mainClearPair
    (l r : Cell ψ κ τ) (hl : MainClearV3 l) (hr : MainClearV3 r) :
    AuxImportEmptyV31 l r := by
  unfold MainClearV3 R2CoherenceBranches.MainClear at hl hr
  change
    (raw l).state = .none ∧ (raw l).path = .bot ∧
      (raw l).path2 = none ∧ (raw l).path4 = none ∧
      (raw l).path5 = none ∧ (raw l).p = false ∧
      (raw l).p_carry = false at hl
  change
    (raw r).state = .none ∧ (raw r).path = .bot ∧
      (raw r).path2 = none ∧ (raw r).path4 = none ∧
      (raw r).path5 = none ∧ (raw r).p = false ∧
      (raw r).p_carry = false at hr
  rcases hl with ⟨_, _, hl2, hl4, hl5, hlp, hlpc⟩
  rcases hr with ⟨_, _, hr2, hr4, hr5, hrp, hrpc⟩
  exact ⟨hl2, hr2, hl4, hr4, hl5, hr5, hlp, hrp, hlpc, hrpc⟩


private theorem h3 : 0 < 3 := by decide
private theorem h23 : 2 ≤ 3 := by decide


private def badRaw (lab : Fin 3) (w : Bool) : R2.Cell 3 3 48 :=
  let s := WriterProducerRegression.clean h3 (fun _ => false) lab
  let b := s.base.core.core
  let b' : BoundedAgentState 3 3 := {
    b with
    leader := false
    shield := false
    gen_ws := false
    label := lab
    wait := w
    state := .none
    path := .bot
    path2 := none
    path3 := none
    path4 := none
    path5 := none
    p := false
    p_carry := false
    reset_cmd := false
    echo := false
    write_state := .none
    write := .none
    b_carry := false
  }
  ⟨⟨⟨b', false⟩, 48⟩, 0⟩


private def openCell3 (p : R2.Cell 3 3 48) : Cell 3 3 48 :=
  ⟨p, ⟨.open, .none⟩⟩
private def badL : Cell 3 3 48 := openCell3 (badRaw 0 false)
private def badR : Cell 3 3 48 := openCell3 (badRaw 1 true)
private def badQ := proposalV3 h3 (by decide : 0 < 2) h23 badL badR


theorem q14010_bad_right_mainClear : MainClearV3 badR := by
  unfold MainClearV3 R2CoherenceBranches.MainClear
  change
    (raw badR).state = .none ∧ (raw badR).path = .bot ∧
      (raw badR).path2 = none ∧ (raw badR).path4 = none ∧
      (raw badR).path5 = none ∧ (raw badR).p = false ∧
      (raw badR).p_carry = false
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem q14010_bad_noHazard :
    pairHazardV3 badL.phys badR.phys badQ.1 badQ.2 = false := by
  decide +kernel
theorem q14010_bad_branch :
    branchAtV3 h3 h23 badL badR = .openNoHazard := by decide +kernel
theorem q14010_bad_right_produce :
    badQ.2.base.core.core.state = .produce := by decide +kernel


set_option maxHeartbeats 32000000 in
set_option maxRecDepth 65536 in
theorem openNoHazardMainClearUnframedCarrierGuard_false :
    ¬ OpenNoHazardMainClearUnframedCarrierGuardV31
      (κ := 3) (τ := 48) h3 h23 := by
  intro h
  have hc := (h badL badR q14010_bad_noHazard).2 q14010_bad_right_mainClear
  have hn : badQ.2.base.core.core.state = .none := hc.1
  have hf : MainState.produce = MainState.none :=
    q14010_bad_right_produce.symm.trans hn
  cases hf



namespace WeakFreshnessLayer


/-- P8's direct safety side, without overclaiming full sanitation. -/
def SweepOpenRSafeFreshV31
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (owner p : Fin n) : Prop :=
  FreshnessClearV31 (C p) ∨
    ¬ InOpenRFreshFootprintV31 ring C owner p


theorem sweepOpenRSafeFresh_of_old
    (ring : DirectedRing n) (C : FC n ψ κ τ) (owner p : Fin n)
    (h : SweepOpenRSafeAtV31 ring C owner p) :
    SweepOpenRSafeFreshV31 ring C owner p := by
  rcases h with hm | hout
  · exact Or.inl (freshnessClear_of_mainClear _ hm)
  · exact Or.inr hout


/-- Existing full group sanitation remains strong enough for weak P8 safety. -/
theorem groupOwnedClear_freshnessClear
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n)
    (h : GroupOwnedClearV31 ring C i) (k : Fin ψ) :
    FreshnessClearV31
      (C (R2Coherence.groupPos ring (eraseCfgV3 C) i k.val)) := by
  unfold GroupOwnedClearV31 at h
  exact freshnessClear_of_mainClear _ (h k).1


/-- Direct-side cover with the exact predicate used by freshness. -/
def PendingOpenRFootprintCoveredFreshV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∀ (owner p : Fin n),
    PendingOpenROwnerV31 ring C owner →
    InOpenRFreshFootprintV31 ring C owner p →
      FreshnessClearV31 (C p) ∨
      InGroupOwnedFootprintV31 ring C (ring.rightNeighbor owner) p


theorem pendingCoveredFresh_of_old
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (h : PendingOpenRFootprintCoveredV31 ring C) :
    PendingOpenRFootprintCoveredFreshV31 ring C := by
  intro owner p hp hf
  rcases h owner p hp hf with hm | hg
  · exact Or.inl (freshnessClear_of_mainClear _ hm)
  · exact Or.inr hg


/-- Open-no-hazard preserves exactly the weak freshness-clear predicate. -/
theorem freshnessClear_openNoHazard_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) =
      .openNoHazard)
    (hp : FreshnessClearV31 (C p)) :
    FreshnessClearV31 (stepV3 hψ h2 ring C e p) := by
  have hF := openNoHazard_step_frame hψ h2 ring C e hb
  unfold FreshnessClearV31 at hp ⊢
  exact (hF p).2.2.1.trans hp


/-- ψ=2 adjacent-root fact at the strength actually needed by freshness. -/
def AdjacentRootPredecessorFreshnessClearPsi2V31
    (ring : DirectedRing n) (C : FC n 2 κ τ) : Prop :=
  ∀ p : Fin n,
    atRootB (C p) = true →
    atRootB (C (ring.rightNeighbor p)) = true →
      FreshnessClearV31 (C p)


theorem adjacentRootFreshnessClear_of_mainClear
    (ring : DirectedRing n) (C : FC n 2 κ τ)
    (h : AdjacentRootPredecessorMainClearPsi2V31 ring C) :
    AdjacentRootPredecessorFreshnessClearPsi2V31 ring C := by
  intro p hp hq
  exact freshnessClear_of_mainClear _ (h p hp hq)


theorem adjacentRootFreshnessClear_openNoHazard_step
    (ring : DirectedRing n) (C : FC n 2 κ τ) (e : Fin n)
    (hAdj : AdjacentRootPredecessorFreshnessClearPsi2V31 ring C)
    (hb : branchAtV3 (by decide : 0 < 2) (by decide : 2 ≤ 2)
      (C e) (C (ring.rightNeighbor e)) = .openNoHazard) :
    AdjacentRootPredecessorFreshnessClearPsi2V31 ring
      (stepV3 (by decide : 0 < 2) (by decide : 2 ≤ 2) ring C e) := by
  let D := stepV3 (by decide : 0 < 2) (by decide : 2 ≤ 2) ring C e
  have hF : OpenNoHazardFrameV31 C D :=
    openNoHazard_step_frame
      (by decide : 0 < 2) (by decide : 2 ≤ 2) ring C e hb
  intro p hpD hqD
  have hpC : atRootB (C p) = true := by
    unfold atRootB at hpD ⊢
    rw [(hF p).1] at hpD
    exact hpD
  have hqC : atRootB (C (ring.rightNeighbor p)) = true := by
    unfold atRootB at hqD ⊢
    rw [(hF (ring.rightNeighbor p)).1] at hqD
    exact hqD
  have hOld := hAdj p hpC hqC
  unfold FreshnessClearV31 at hOld ⊢
  exact (hF p).2.2.1.trans hOld


end WeakFreshnessLayer
end R2CoherenceV31MainClearTruth
