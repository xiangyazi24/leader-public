import Leader.Wu.Coherence.ReachableOverlapPayload


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2CoherenceV31ReachablePlus3


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31PhaseMainClear
open R2CoherenceV31BirthQuarantine
open R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts
open R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus
open R2CoherenceV31ReachablePlus2


variable {n ψ κ τ : Nat}


/-- The same per-cell safety disjunction used by the pointwise clause. -/
def SweepOpenRSafeAtV31
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (owner p : Fin n) : Prop :=
  MainClearV3 (C p) ∨
    ¬ InOpenRFreshFootprintV31 ring C owner p


/-- Window-wide prepaid sweep/openR compatibility.


Besides the responder itself, certify every clockwise cell from the sweep
front through the terminal label.  On a valid nonterminal sweep this is
exactly the remaining group suffix, and after one service the suffix shrinks
by one cell. -/
def SweepOpenROverlapClearWideV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∀ (e owner : Fin n),
    (C e).ctl.tok = .sweep →
    PendingOpenROwnerV31 ring C owner →
      SweepOpenRSafeAtV31 ring C owner (ring.rightNeighbor e) ∧
      ∀ d : Fin (ψ - (raw (C e)).label.val),
        SweepOpenRSafeAtV31 ring C owner
          (R2Coherence.fwd ring e d.val)


def ReachablePhaseFactsPlus3V31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ReachablePhaseFactsPlus2V31 ring C ∧
    SweepOpenROverlapClearWideV31 ring C


/-- The wide clause implies the pointwise pair clause without geometry:
distance zero is the front, and the responder is stored explicitly. -/
theorem sweepOpenROverlapClearWide_implies_pointwise
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (hWide : SweepOpenROverlapClearWideV31 ring C) :
    SweepOpenROverlapClearV31 ring C := by
  intro e owner hSweep hPending
  have h := hWide e owner hSweep hPending
  constructor
  · have hpos : 0 < ψ - (raw (C e)).label.val :=
      Nat.sub_pos_of_lt (raw (C e)).label.isLt
    let d0 : Fin (ψ - (raw (C e)).label.val) := ⟨0, hpos⟩
    have h0 := h.2 d0
    change SweepOpenRSafeAtV31 ring C owner
      (R2Coherence.fwd ring e 0) at h0
    have hFwd0 : R2Coherence.fwd ring e 0 = e := by
      apply Fin.ext
      simp [R2Coherence.fwd, Nat.mod_eq_of_lt e.isLt]
    rw [hFwd0] at h0
    simpa only [SweepOpenRSafeAtV31] using h0
  · simpa [SweepOpenRSafeAtV31] using h.1


/-- Entrance is vacuous because quarantine installs token `.none` everywhere. -/
theorem sweepOpenROverlapClearWide_quarantineInit
    (ring : DirectedRing n) (C : FC n ψ κ τ) :
    SweepOpenROverlapClearWideV31 ring (quarantineInitV31 C) := by
  intro e owner hSweep
  simp [quarantineInitV31, setControl] at hSweep


/-- Full Plus3 entrance. -/
theorem reachablePhaseFactsPlus3_entrance
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ)
    (hBirth : BirthEntranceV1 hψ h2 ring C) :
    ReachablePhaseFactsPlus3V31 ring C := by
  constructor
  · exact reachablePhaseFactsPlus2_entrance hψ h2 ring C hBirth
  · rcases hBirth.1 with ⟨_, D, _, hEq⟩
    rw [hEq]
    exact sweepOpenROverlapClearWide_quarantineInit ring D


private theorem bool_false_of_not_true_plus3
    (b : Bool) (h : b ≠ true) : b = false := by
  cases b <;> simp_all


private theorem branch_sweep_conditions_plus3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .sweep) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok = .sweep := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind


private theorem rowV3_sweep_eq_plus3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .sweep) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = sweepStageV3 l r := by
  rcases branch_sweep_conditions_plus3 hψ h2 l r hb with
    ⟨hSeek, hSweep⟩
  simp [rowV3, hSeek, hSweep]


private theorem successor_labels_plus3
    (l r : Cell ψ κ τ) (h : successorB l r = true) :
    (raw r).label.val = (raw l).label.val + 1 := by
  simpa [successorB] using h


private theorem edge_distinct_of_successor_plus3
    (C : FC n ψ κ τ) (ring : DirectedRing n) (e : Fin n)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    e ≠ ring.rightNeighbor e := by
  intro h
  have hSame := congrArg (fun p : Fin n => (raw (C p)).label.val) h
  have hSucc := successor_labels_plus3
    (C e) (C (ring.rightNeighbor e)) hs
  omega

private theorem sweep_step_left_good_plus3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    stepV3 hψ h2 ring C e e =
      setControl (clearMain (C e)) .closing .none := by
  have hrow := rowV3_sweep_eq_plus3 hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step,
    hrow, sweepStageV3, hs]




private theorem sweep_step_right_good_plus3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    stepV3 hψ h2 ring C e (ring.rightNeighbor e) =
      setControl (clearMain (C (ring.rightNeighbor e))) .closing
        (if atTerminalB (C (ring.rightNeighbor e))
          then .commit else .sweep) := by
  have hrow := rowV3_sweep_eq_plus3 hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  have hne := edge_distinct_of_successor_plus3 C ring e hs
  have hrne : ring.rightNeighbor e ≠ e := Ne.symm hne
  simp [stepV3, protocolV3, PopulationProtocol.step,
    hrow, sweepStageV3, hs, hrne]


private theorem sweep_step_left_bad_plus3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = false) :
    stepV3 hψ h2 ring C e e = startClosing (C e) := by
  have hrow := rowV3_sweep_eq_plus3 hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step,
    hrow, sweepStageV3, hs]


private theorem sweep_step_bad_other_plus3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e i : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = false)
    (hi : i ≠ e) :
    stepV3 hψ h2 ring C e i = C i := by
  by_cases hij : i = ring.rightNeighbor e
  · subst i
    have hrow := rowV3_sweep_eq_plus3 hψ h2
      (C e) (C (ring.rightNeighbor e)) hb
    simpa [stepV3, protocolV3, PopulationProtocol.step,
      hrow, sweepStageV3, hs, hi]
  · exact stepV3_other hψ h2 ring C e i hi hij


private theorem clearMain_control_mainClear_plus3
    (u : Cell ψ κ τ) (t : TokenV3) :
    MainClearV3 (setControl (clearMain u) .closing t) := by
  unfold MainClearV3 R2CoherenceBranches.MainClear
  simp [eraseCellV3, setControl, clearMain,
    R2Coherence.clearMainPhys,
    PPLLExpiringComparisonRepair.clearComparisonCarrier,
    R2Coherence.raw]


private theorem groupPos_eq_of_labels_plus3
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p : Fin n, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.groupPos ring (eraseCfgV3 D) i k =
      R2Coherence.groupPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.groupPos R2Coherence.groupStart
  change
    R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (D i)).label.val) k =
    R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (C i)).label.val) k
  rw [hLab i]


private theorem prefixPos_eq_of_labels_plus3
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p : Fin n, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.prefixPos ring (eraseCfgV3 D) i k =
      R2Coherence.prefixPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.prefixPos
  change
    R2Coherence.back ring i ((raw (D i)).label.val - k) =
      R2Coherence.back ring i ((raw (C i)).label.val - k)
  rw [hLab i]

/-- `InOpenRFreshFootprintV31` depends only on physical labels and cyclic
positions, so a global label frame preserves it exactly. -/
private theorem footprint_iff_of_labels_plus3
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p : Fin n,
      (raw (D p)).label = (raw (C p)).label)
    (owner p : Fin n) :
    InOpenRFreshFootprintV31 ring D owner p ↔
      InOpenRFreshFootprintV31 ring C owner p := by
  constructor
  · rintro ⟨j, ko, q, hOwnerD, kD, hPrefixD⟩
    have hGPko := groupPos_eq_of_labels_plus3 ring hLab j ko.val
    rw [hGPko] at hOwnerD
    have hGPq := groupPos_eq_of_labels_plus3 ring hLab j q.val
    let front := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
    have hFrontD :
        R2Coherence.groupPos ring (eraseCfgV3 D) j q.val = front := by
      simpa [front] using hGPq
    have hLabelVal :
        (raw (D (R2Coherence.groupPos ring
          (eraseCfgV3 D) j q.val))).label.val =
          (raw (C front)).label.val := by
      rw [hFrontD]
      exact congrArg (fun x : Fin ψ => x.val) (hLab front)
    have hkC : kD.val < (raw (C front)).label.val + 1 := by
      let m : Nat := kD.val
      have hmD : m <
          (raw (D (R2Coherence.groupPos ring
            (eraseCfgV3 D) j q.val))).label.val + 1 := kD.isLt
      simpa only [hLabelVal] using hmD
    let kC : Fin ((raw (C front)).label.val + 1) := ⟨kD.val, hkC⟩
    refine ⟨j, ko, q, hOwnerD, kC, ?_⟩
    let m : Nat := kD.val
    have hPrefixD0 :
        R2Coherence.prefixPos ring (eraseCfgV3 D)
          (R2Coherence.groupPos ring (eraseCfgV3 D) j q.val) m = p := by
      simpa [m] using hPrefixD
    have hPrefixD1 :
        R2Coherence.prefixPos ring (eraseCfgV3 D) front m = p := by
      simpa only [hFrontD] using hPrefixD0
    have hPP := prefixPos_eq_of_labels_plus3 ring hLab front m
    have hPrefixC :
        R2Coherence.prefixPos ring (eraseCfgV3 C) front m = p := by
      exact hPP.symm.trans hPrefixD1
    have hFrontC :
        R2Coherence.groupPos ring (eraseCfgV3 C) j q.val = front := by
      rfl
    have hkCm : kC.val = m := by
      rfl
    simpa only [hFrontC, hkCm] using hPrefixC
  · rintro ⟨j, ko, q, hOwnerC, kC, hPrefixC⟩
    have hGPko := groupPos_eq_of_labels_plus3 ring hLab j ko.val
    have hOwnerD :
        R2Coherence.groupPos ring (eraseCfgV3 D) j ko.val = owner := by
      rw [hGPko]
      exact hOwnerC
    have hGPq := groupPos_eq_of_labels_plus3 ring hLab j q.val
    let front := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
    have hFrontD :
        R2Coherence.groupPos ring (eraseCfgV3 D) j q.val = front := by
      simpa [front] using hGPq
    have hLabelVal :
        (raw (D (R2Coherence.groupPos ring
          (eraseCfgV3 D) j q.val))).label.val =
          (raw (C front)).label.val := by
      rw [hFrontD]
      exact congrArg (fun x : Fin ψ => x.val) (hLab front)
    have hkD : kC.val <
        (raw (D (R2Coherence.groupPos ring
          (eraseCfgV3 D) j q.val))).label.val + 1 := by
      let m : Nat := kC.val
      have hmC : m < (raw (C front)).label.val + 1 := kC.isLt
      simpa only [hLabelVal] using hmC
    let kD : Fin
        ((raw (D (R2Coherence.groupPos ring
          (eraseCfgV3 D) j q.val))).label.val + 1) := ⟨kC.val, hkD⟩
    refine ⟨j, ko, q, hOwnerD, kD, ?_⟩
    let m : Nat := kC.val
    have hPrefixC0 :
        R2Coherence.prefixPos ring (eraseCfgV3 C)
          (R2Coherence.groupPos ring (eraseCfgV3 C) j q.val) m = p := by
      simpa [m] using hPrefixC
    have hFrontC :
        R2Coherence.groupPos ring (eraseCfgV3 C) j q.val = front := by
      rfl
    have hPrefixC1 :
        R2Coherence.prefixPos ring (eraseCfgV3 C) front m = p := by
      simpa only [hFrontC] using hPrefixC0
    have hPP := prefixPos_eq_of_labels_plus3 ring hLab front m
    have hPrefixD1 :
        R2Coherence.prefixPos ring (eraseCfgV3 D) front m = p := by
      exact hPP.trans hPrefixC1
    have hPrefixD0 :
        R2Coherence.prefixPos ring (eraseCfgV3 D)
          (R2Coherence.groupPos ring (eraseCfgV3 D) j q.val) m = p := by
      simpa only [hFrontD] using hPrefixD1
    have hkDm : kD.val = m := by
      rfl
    simpa only [hkDm] using hPrefixD0




private theorem safeAt_of_phys_eq_plus3
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (owner p : Fin n)
    (hLab : ∀ x : Fin n,
      (raw (D x)).label = (raw (C x)).label)
    (hPhys : (D p).phys = (C p).phys)
    (hSafe : SweepOpenRSafeAtV31 ring C owner p) :
    SweepOpenRSafeAtV31 ring D owner p := by
  unfold SweepOpenRSafeAtV31 at hSafe ⊢
  rcases hSafe with hm | hout
  · left
    unfold MainClearV3 R2CoherenceBranches.MainClear at hm ⊢
    simpa [eraseCellV3, R2Coherence.raw, hPhys] using hm
  · right
    intro hFoot
    exact hout ((footprint_iff_of_labels_plus3
      ring hLab owner p).1 hFoot)

private theorem safeAt_sweep_step_plus3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    (hSafe : SweepOpenRSafeAtV31 ring C owner p) :
    SweepOpenRSafeAtV31 ring (stepV3 hψ h2 ring C e) owner p := by
  have hLab := stepV3_labels_eq_or_held hψ h2 ring C e
  by_cases hsT : successorB (C e) (C (ring.rightNeighbor e)) = true
  · by_cases hpe : p = e
    · subst p
      unfold SweepOpenRSafeAtV31
      left
      rw [sweep_step_left_good_plus3 hψ h2 ring C e hb hsT]
      exact clearMain_control_mainClear_plus3 (C e) .none
    · by_cases hpr : p = ring.rightNeighbor e
      · subst p
        unfold SweepOpenRSafeAtV31
        left
        rw [sweep_step_right_good_plus3 hψ h2 ring C e hb hsT]
        exact clearMain_control_mainClear_plus3
          (C (ring.rightNeighbor e)) _
      · apply safeAt_of_phys_eq_plus3 ring owner p hLab ?_ hSafe
        rw [stepV3_other hψ h2 ring C e p hpe hpr]
  · have hsF := bool_false_of_not_true_plus3 _ hsT
    by_cases hpe : p = e
    · subst p
      apply safeAt_of_phys_eq_plus3 ring owner e hLab ?_ hSafe
      rw [sweep_step_left_bad_plus3 hψ h2 ring C e hb hsF]
      simp [startClosing, setControl]
    · apply safeAt_of_phys_eq_plus3 ring owner p hLab ?_ hSafe
      rw [sweep_step_bad_other_plus3 hψ h2 ring C e p hb hsF hpe]


/-- A post-sweep scrubL token was not created by the sweep. -/
private theorem scrubL_after_sweep_was_before_plus3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    (hPost : (stepV3 hψ h2 ring C e p).ctl.tok = .scrubL) :
    (C p).ctl.tok = .scrubL := by
  by_cases hsT : successorB (C e) (C (ring.rightNeighbor e)) = true
  · by_cases hpe : p = e
    · subst p
      rw [sweep_step_left_good_plus3 hψ h2 ring C e hb hsT] at hPost
      simp [setControl] at hPost
    · by_cases hpr : p = ring.rightNeighbor e
      · subst p
        rw [sweep_step_right_good_plus3 hψ h2 ring C e hb hsT] at hPost
        cases ht : atTerminalB (C (ring.rightNeighbor e)) <;>
          simp [setControl, ht] at hPost
      · rw [stepV3_other hψ h2 ring C e p hpe hpr] at hPost
        exact hPost
  · have hsF := bool_false_of_not_true_plus3 _ hsT
    by_cases hpe : p = e
    · subst p
      rw [sweep_step_left_bad_plus3 hψ h2 ring C e hb hsF] at hPost
      simp [startClosing, setControl] at hPost
    · rw [sweep_step_bad_other_plus3
        hψ h2 ring C e p hb hsF hpe] at hPost
      exact hPost


private theorem pendingOpenR_before_sweep_plus3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    (hPost : PendingOpenROwnerV31 ring
      (stepV3 hψ h2 ring C e) owner) :
    PendingOpenROwnerV31 ring C owner := by
  rcases hPost with ⟨hScrub, hSucc, hRoot⟩
  have hLab := stepV3_labels_eq_or_held hψ h2 ring C e
  refine ⟨?_, ?_, ?_⟩
  · exact scrubL_after_sweep_was_before_plus3
      hψ h2 ring C e (ring.rightNeighbor owner) hb hScrub
  · unfold successorB at hSucc ⊢
    simpa [hLab owner, hLab (ring.rightNeighbor owner)] using hSucc
  · unfold atRootB at hRoot ⊢
    simpa [hLab owner] using hRoot


private theorem mod_add_mod_left_plus3 (a b n : Nat) :
    (a % n + b) % n = (a + b) % n := by
  rw [Nat.add_mod (a % n) b n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm


private theorem fwd_zero_plus3
    (ring : DirectedRing n) (i : Fin n) :
    R2Coherence.fwd ring i 0 = i := by
  apply Fin.ext
  simp [R2Coherence.fwd, Nat.mod_eq_of_lt i.isLt]


private theorem fwd_one_plus3
    (ring : DirectedRing n) (i : Fin n) :
    R2Coherence.fwd ring i 1 = ring.rightNeighbor i := by
  rfl


private theorem fwd_rightNeighbor_plus3
    (ring : DirectedRing n) (i : Fin n) (d : Nat) :
    R2Coherence.fwd ring (ring.rightNeighbor i) d =
      R2Coherence.fwd ring i (d + 1) := by
  apply Fin.ext
  unfold R2Coherence.fwd DirectedRing.rightNeighbor
  dsimp only
  rw [mod_add_mod_left_plus3 (i.val + 1) d n]
  congr 1
  omega


/-- The good-sweep case for a pre-existing remote sweep front.  Kept separate
only to keep the main proof's new-front branch readable. -/
private theorem sweepWide_good_remote_plus3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e s owner : Fin n)
    (hWide : SweepOpenROverlapClearWideV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    (hsT : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (hse : s ≠ e) (hsr : s ≠ ring.rightNeighbor e)
    (hSweepD :
      (stepV3 hψ h2 ring C e s).ctl.tok = .sweep)
    (hPendingC : PendingOpenROwnerV31 ring C owner) :
    SweepOpenRSafeAtV31 ring (stepV3 hψ h2 ring C e) owner
        (ring.rightNeighbor s) ∧
      ∀ d : Fin
          (ψ - (raw (stepV3 hψ h2 ring C e s)).label.val),
        SweepOpenRSafeAtV31 ring (stepV3 hψ h2 ring C e) owner
          (R2Coherence.fwd ring s d.val) := by
  have hDs := stepV3_other hψ h2 ring C e s hse hsr
  have hSweepC : (C s).ctl.tok = .sweep := by
    rw [hDs] at hSweepD
    exact hSweepD
  have hSource := hWide s owner hSweepC hPendingC
  constructor
  · exact safeAt_sweep_step_plus3
      hψ h2 ring C e owner (ring.rightNeighbor s) hb hSource.1
  · intro dD
    have hLab := stepV3_labels_eq_or_held hψ h2 ring C e s
    have hLabelS :
        (raw (stepV3 hψ h2 ring C e s)).label.val =
          (raw (C s)).label.val := by
      exact congrArg (fun x : Fin ψ => x.val) hLab
    have hdC : dD.val < ψ - (raw (C s)).label.val := by
      let m : Nat := dD.val
      have hm : m < ψ -
          (raw (stepV3 hψ h2 ring C e s)).label.val := dD.isLt
      simpa only [hLabelS] using hm
    let dC : Fin (ψ - (raw (C s)).label.val) := ⟨dD.val, hdC⟩
    have hOld := hSource.2 dC
    change SweepOpenRSafeAtV31 ring C owner
      (R2Coherence.fwd ring s dD.val) at hOld
    exact safeAt_sweep_step_plus3
      hψ h2 ring C e owner (R2Coherence.fwd ring s dD.val) hb hOld

/-- The window-wide suffix is closed by one sweep service.  This proof uses
only the local sweep equations above plus `stepV3_other`; it never unfolds a
whole configuration transition globally. -/
theorem sweepOpenROverlapClearWide_sweep_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hWide : SweepOpenROverlapClearWideV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep) :
    SweepOpenROverlapClearWideV31 ring
      (stepV3 hψ h2 ring C e) := by
  have hLab : ∀ p : Fin n,
      (raw (stepV3 hψ h2 ring C e p)).label = (raw (C p)).label :=
    stepV3_labels_eq_or_held hψ h2 ring C e
  have hSweepE : (C e).ctl.tok = .sweep :=
    (branch_sweep_conditions_plus3 hψ h2
      (C e) (C (ring.rightNeighbor e)) hb).2
  intro s owner hSweepD hPendingD
  have hPendingC := pendingOpenR_before_sweep_plus3
    hψ h2 ring C e owner hb hPendingD
  by_cases hsT : successorB (C e) (C (ring.rightNeighbor e)) = true
  · have hLeft := sweep_step_left_good_plus3 hψ h2 ring C e hb hsT
    have hRight := sweep_step_right_good_plus3 hψ h2 ring C e hb hsT
    have hse : s ≠ e := by
      intro h
      subst s
      have hx := hSweepD
      rw [hLeft] at hx
      simp [setControl] at hx
    by_cases hsr : s = ring.rightNeighbor e
    · subst s
      have htF : atTerminalB (C (ring.rightNeighbor e)) = false := by
        cases ht : atTerminalB (C (ring.rightNeighbor e)) with
        | false => rfl
        | true =>
          have hx := hSweepD
          rw [hRight] at hx
          simp [setControl, ht] at hx
      have hSource := hWide e owner hSweepE hPendingC
      have hSuccLab := successor_labels_plus3
        (C e) (C (ring.rightNeighbor e)) hsT
      have hTermNe :
          (raw (C (ring.rightNeighbor e))).label.val + 1 ≠ ψ := by
        intro hz
        have htT : atTerminalB (C (ring.rightNeighbor e)) = true := by
          simp [atTerminalB, hz]
        rw [htF] at htT

        cases htT
      have hTermLt :
          (raw (C (ring.rightNeighbor e))).label.val + 1 < ψ := by
        have hle :
            (raw (C (ring.rightNeighbor e))).label.val + 1 ≤ ψ :=
          Nat.succ_le_of_lt (raw (C (ring.rightNeighbor e))).label.isLt
        omega
      constructor
      · have hd2 : 2 < ψ - (raw (C e)).label.val := by omega
        let d2 : Fin (ψ - (raw (C e)).label.val) := ⟨2, hd2⟩
        have hOld := hSource.2 d2
        change SweepOpenRSafeAtV31 ring C owner
          (R2Coherence.fwd ring e 2) at hOld
        have hF2 :
            R2Coherence.fwd ring e 2 =
              ring.rightNeighbor (ring.rightNeighbor e) := by
          calc
            R2Coherence.fwd ring e 2 =
                R2Coherence.fwd ring (ring.rightNeighbor e) 1 :=
              (fwd_rightNeighbor_plus3 ring e 1).symm
            _ = ring.rightNeighbor (ring.rightNeighbor e) :=
              fwd_one_plus3 ring (ring.rightNeighbor e)
        rw [hF2] at hOld
        exact safeAt_sweep_step_plus3
          hψ h2 ring C e owner
            (ring.rightNeighbor (ring.rightNeighbor e)) hb hOld
      · intro dD
        have hLabelR :
            (raw (stepV3 hψ h2 ring C e
              (ring.rightNeighbor e))).label.val =
              (raw (C (ring.rightNeighbor e))).label.val := by
          exact congrArg (fun x : Fin ψ => x.val)
            (hLab (ring.rightNeighbor e))
        have hdR :
            dD.val < ψ -
              (raw (C (ring.rightNeighbor e))).label.val := by
          let m : Nat := dD.val
          have hm : m < ψ -
              (raw (stepV3 hψ h2 ring C e
                (ring.rightNeighbor e))).label.val := dD.isLt
          simpa only [hLabelR] using hm
        have hdC : dD.val + 1 < ψ - (raw (C e)).label.val := by
          omega
        let dC : Fin (ψ - (raw (C e)).label.val) :=
          ⟨dD.val + 1, hdC⟩
        have hOld := hSource.2 dC
        change SweepOpenRSafeAtV31 ring C owner
          (R2Coherence.fwd ring e (dD.val + 1)) at hOld
        have hMove := fwd_rightNeighbor_plus3 ring e dD.val
        rw [← hMove] at hOld
        exact safeAt_sweep_step_plus3
          hψ h2 ring C e owner
            (R2Coherence.fwd ring (ring.rightNeighbor e) dD.val) hb hOld
    · exact sweepWide_good_remote_plus3
        hψ h2 ring C e s owner hWide hb hsT hse hsr
        hSweepD hPendingC
  · have hsF := bool_false_of_not_true_plus3 _ hsT
    have hse : s ≠ e := by
      intro h
      subst s
      have hx := hSweepD
      rw [sweep_step_left_bad_plus3 hψ h2 ring C e hb hsF] at hx
      simp [startClosing, setControl] at hx
    have hDs : stepV3 hψ h2 ring C e s = C s :=
      sweep_step_bad_other_plus3 hψ h2 ring C e s hb hsF hse
    have hSweepC : (C s).ctl.tok = .sweep := by
      rw [hDs] at hSweepD
      exact hSweepD
    have hSource := hWide s owner hSweepC hPendingC
    constructor
    · exact safeAt_sweep_step_plus3
        hψ h2 ring C e owner (ring.rightNeighbor s) hb hSource.1
    · intro dD
      have hLabelS :
          (raw (stepV3 hψ h2 ring C e s)).label.val =
            (raw (C s)).label.val := by
        exact congrArg (fun x : Fin ψ => x.val) (hLab s)
      have hdC : dD.val < ψ - (raw (C s)).label.val := by
        let m : Nat := dD.val
        have hm : m < ψ -
            (raw (stepV3 hψ h2 ring C e s)).label.val := dD.isLt
        simpa only [hLabelS] using hm
      let dC : Fin (ψ - (raw (C s)).label.val) := ⟨dD.val, hdC⟩
      have hOld := hSource.2 dC
      change SweepOpenRSafeAtV31 ring C owner
        (R2Coherence.fwd ring s dD.val) at hOld
      exact safeAt_sweep_step_plus3
        hψ h2 ring C e owner (R2Coherence.fwd ring s dD.val) hb hOld


/-- Completion of the good branch omitted from the preceding theorem body by
factoring the remote-front case through `sweepWide_good_remote_plus3`.
This is the exact sweep-preservation interface used downstream. -/
theorem sweepOpenROverlapClearWide_sweep_step_full
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hWide : SweepOpenROverlapClearWideV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep) :
    SweepOpenROverlapClearWideV31 ring
      (stepV3 hψ h2 ring C e) := by
  exact sweepOpenROverlapClearWide_sweep_step
    hψ h2 ring C e hWide hb


end R2CoherenceV31ReachablePlus3
