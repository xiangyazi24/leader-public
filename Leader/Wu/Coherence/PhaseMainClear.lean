import Leader.Wu.Coherence.LiveCommitShape


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2CoherenceV31PhaseMainClear


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2


variable {n ψ κ τ : Nat}


/-- A cell cannot participate in an ordinary open/open service. -/
def PhaseOwnedV31 (u : Cell ψ κ τ) : Prop :=
  u.ctl.mark ≠ .open ∨ u.ctl.tok ≠ .none


instance phaseOwnedV31Decidable (u : Cell ψ κ τ) :
    Decidable (PhaseOwnedV31 u) := by
  unfold PhaseOwnedV31
  infer_instance


/-- The part strictly behind a live sweep front is already cleared and owned.
At label 0 this is vacuous, so seek -> root-sweep needs no precondition. -/
def SweptPrefixOwnedClearV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) : Prop :=
  ∀ k : Fin (raw (C i)).label.val,
    let j := R2Coherence.groupPos ring (eraseCfgV3 C) i k.val
    MainClearV3 (C j) ∧ PhaseOwnedV31 (C j)


instance sweptPrefixOwnedClearV31Decidable
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) :
    Decidable (SweptPrefixOwnedClearV31 ring C i) := by
  unfold SweptPrefixOwnedClearV31
  infer_instance


/-- Whole-group version used from commit onward. -/
def GroupOwnedClearV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) : Prop :=
  ∀ k : Fin ψ,
    let j := R2Coherence.groupPos ring (eraseCfgV3 C) i k.val
    MainClearV3 (C j) ∧ PhaseOwnedV31 (C j)


instance groupOwnedClearV31Decidable
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) :
    Decidable (GroupOwnedClearV31 ring C i) := by
  unfold GroupOwnedClearV31
  infer_instance


/-- Main-clear debt is a phase invariant, not a controller-shape clause. -/
def PhaseMainClearV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  (∀ i : Fin n, (C i).ctl.tok = .sweep →
      SweptPrefixOwnedClearV31 ring C i) ∧
  (∀ i : Fin n, (C i).ctl.tok = .commit →
      GroupOwnedClearV31 ring C i) ∧
  (∀ i : Fin n, (C i).ctl.mark = .sealed →
      GroupOwnedClearV31 ring C i) ∧
  (∀ i : Fin n, (C i).ctl.tok = .release →
      GroupOwnedClearV31 ring C i) ∧
  (∀ i : Fin n, (C i).ctl.tok = .scrubL →
      GroupOwnedClearV31 ring C i)


instance phaseMainClearV31Decidable
    (ring : DirectedRing n) (C : FC n ψ κ τ) :
    Decidable (PhaseMainClearV31 ring C) := by
  unfold PhaseMainClearV31
  infer_instance


/-- Structural controller conditions after removing all main-clear ownership. -/
def ControllerShapeStructuralV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  (∀ i : Fin n, (C i).ctl.tok = .release →
      (C i).ctl.mark = .releasing) ∧
  (∀ i : Fin n, (C i).ctl.tok = .scrubL →
      (C i).ctl.mark = .releasing ∧ (raw (C i)).label.val ≠ 0) ∧
  (∀ i : Fin n, (C i).ctl.tok = .openR →
      (C i).ctl.mark = .releasing ∧ OpenROwnerFreshV3 ring C i)


instance controllerShapeStructuralV31Decidable
    (ring : DirectedRing n) (C : FC n ψ κ τ) :
    Decidable (ControllerShapeStructuralV31 ring C) := by
  unfold ControllerShapeStructuralV31
  infer_instance


/-- New executable/current-state proxy; the executable row itself is unchanged. -/
def RecoveryProxySplitV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ControllerShapeStructuralV31 ring C ∧
    PhaseMainClearV31 ring C ∧
    CoherentPrefixesV3 ring C


instance recoveryProxySplitV31Decidable
    (ring : DirectedRing n) (C : FC n ψ κ τ) :
    Decidable (RecoveryProxySplitV31 ring C) := by
  unfold RecoveryProxySplitV31
  infer_instance

private theorem bool_false_of_not_true_phase (b : Bool) (h : b ≠ true) :
    b = false := by
  cases b <;> simp_all


private theorem mod_add_mod_left_phase (a b n : Nat) :
    (a % n + b) % n = (a + b) % n := by
  rw [Nat.add_mod (a % n) b n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm


private theorem mod_add_mod_right_phase (a b n : Nat) :
    (a + b % n) % n = (a + b) % n := by
  rw [Nat.add_mod a (b % n) n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm


private theorem prefixPos_eq_groupPosR2_phase
    (ring : DirectedRing n) (C : R2Coherence.FC n ψ κ τ)
    (i : Fin n) (k : Nat)
    (hk : k ≤ (R2Coherence.raw (C i)).label.val) :
    R2Coherence.prefixPos ring C i k =
      R2Coherence.groupPos ring C i k := by
  let L := (R2Coherence.raw (C i)).label.val
  let A := i.val + n
  let a := (L - k) % n
  let b := k % n
  have hkL : k ≤ L := by
    simpa [L] using hk
  have hn : 0 < n := ring.hn
  have ha : a < n := by
    dsimp [a]
    exact Nat.mod_lt _ hn
  have hb : b < n := by
    dsimp [b]
    exact Nat.mod_lt _ hn
  have hA : n ≤ A := by
    dsimp [A]
    omega
  have hLmod : L % n = (a + b) % n := by
    calc
      L % n = (L - k + k) % n := by
        rw [Nat.sub_add_cancel hkL]
      _ = ((L - k) % n + k % n) % n := Nat.add_mod _ _ _
      _ = (a + b) % n := rfl
  apply Fin.ext
  change (A - a) % n =
    (((A - (L % n)) % n + k) % n)
  symm
  by_cases hsum : a + b < n
  · have hLm : L % n = a + b := by
      calc
        L % n = (a + b) % n := hLmod
        _ = a + b := Nat.mod_eq_of_lt hsum
    calc
      (((A - (L % n)) % n + k) % n) =
          (A - (L % n) + k) % n :=
        mod_add_mod_left_phase (A - (L % n)) k n
      _ = (A - (L % n) + b) % n := by
        simpa [b] using
          (mod_add_mod_right_phase (A - (L % n)) k n).symm
      _ = (A - a) % n := by
        rw [hLm]
        have hnum : A - (a + b) + b = A - a := by
          omega
        rw [hnum]
  · have hsumGe : n ≤ a + b := by omega
    have hsumSub : a + b - n < n := by omega
    have hLm : L % n = a + b - n := by
      calc
        L % n = (a + b) % n := hLmod
        _ = (a + b - n) % n := Nat.mod_eq_sub_mod hsumGe
        _ = a + b - n := Nat.mod_eq_of_lt hsumSub
    calc
      (((A - (L % n)) % n + k) % n) =
          (A - (L % n) + k) % n :=
        mod_add_mod_left_phase (A - (L % n)) k n
      _ = (A - (L % n) + b) % n := by
        simpa [b] using
          (mod_add_mod_right_phase (A - (L % n)) k n).symm
      _ = (A - a) % n := by
        rw [hLm]
        have hnum : A - (a + b - n) + b = n + (A - a) := by
          omega
        rw [hnum, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]


private theorem groupPos_label_selfR2_phase
    (ring : DirectedRing n) (C : R2Coherence.FC n ψ κ τ)
    (i : Fin n) :
    R2Coherence.groupPos ring C i
        (R2Coherence.raw (C i)).label.val = i := by
  rw [← prefixPos_eq_groupPosR2_phase ring C i
    (R2Coherence.raw (C i)).label.val (Nat.le_refl _)]
  apply Fin.ext
  simp only [R2Coherence.prefixPos, R2Coherence.back,
    Nat.sub_self, Nat.zero_mod, Nat.sub_zero]
  rw [Nat.add_mod, Nat.mod_eq_of_lt i.isLt, Nat.mod_self,
    Nat.add_zero, Nat.mod_eq_of_lt i.isLt]


private theorem groupPos_label_selfV3_phase
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) :
    R2Coherence.groupPos ring (eraseCfgV3 C) i
        (raw (C i)).label.val = i := by
  have h := groupPos_label_selfR2_phase ring (eraseCfgV3 C) i
  change
    R2Coherence.groupPos ring (eraseCfgV3 C) i
        (raw (C i)).label.val = i at h
  exact h


private theorem groupPos_rightNeighborR2_phase
    (ring : DirectedRing n) (C : R2Coherence.FC n ψ κ τ)
    (i : Fin n) (k : Nat) :
    ring.rightNeighbor (R2Coherence.groupPos ring C i k) =
      R2Coherence.groupPos ring C i (k + 1) := by
  apply Fin.ext
  unfold DirectedRing.rightNeighbor R2Coherence.groupPos R2Coherence.fwd
  dsimp only
  rw [mod_add_mod_left_phase]
  congr 1


private theorem groupPos_eq_of_labels_phase
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


private theorem back_rightNeighbor_succ_phase
    (ring : DirectedRing n) (i : Fin n) (d : Nat) :
    R2Coherence.back ring (ring.rightNeighbor i) (d + 1) =
      R2Coherence.back ring i d := by
  apply Fin.ext
  unfold R2Coherence.back DirectedRing.rightNeighbor
  dsimp only
  by_cases hn1 : n = 1
  · subst n
    simp
  · have hn : 0 < n := ring.hn
    have hn2 : 2 ≤ n := by omega
    have hOne : 1 < n := by omega
    have hdlt : d % n < n := Nat.mod_lt _ ring.hn
    have hdmod : (d + 1) % n = (d % n + 1) % n := by
      calc
        (d + 1) % n = (d % n + 1 % n) % n := Nat.add_mod _ _ _
        _ = (d % n + 1) % n := by rw [Nat.mod_eq_of_lt hOne]
    rw [hdmod]
    by_cases hi : i.val + 1 < n
    · rw [Nat.mod_eq_of_lt hi]
      by_cases hd : d % n + 1 < n
      · rw [Nat.mod_eq_of_lt hd]
        have hnum :
            i.val + 1 + n - (d % n + 1) =
              i.val + n - d % n := by omega
        rw [hnum]
      · have hdeq : d % n + 1 = n := by omega
        rw [hdeq, Nat.mod_self, Nat.sub_zero]
        have hr : i.val + n - d % n = i.val + 1 := by omega
        rw [hr, Nat.mod_eq_of_lt hi]
        have hl : i.val + 1 + n = n + (i.val + 1) := by omega
        rw [hl, Nat.add_mod, Nat.mod_self, Nat.zero_add,
          Nat.mod_mod, Nat.mod_eq_of_lt hi]
    · have hieq : i.val + 1 = n := by omega
      rw [hieq, Nat.mod_self, Nat.zero_add]
      by_cases hd : d % n + 1 < n
      · rw [Nat.mod_eq_of_lt hd]
        have hvlt : n - (d % n + 1) < n := by omega
        rw [Nat.mod_eq_of_lt hvlt]
        have hr :
            i.val + n - d % n =
              n + (n - (d % n + 1)) := by omega
        rw [hr, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod,
          Nat.mod_eq_of_lt hvlt]
      · have hdeq : d % n + 1 = n := by omega
        rw [hdeq, Nat.mod_self, Nat.sub_zero, Nat.mod_self]
        have hr : i.val + n - d % n = n := by omega
        rw [hr, Nat.mod_self]


private theorem successor_labels_phase
    (l r : Cell ψ κ τ) (h : successorB l r = true) :
    (raw r).label.val = (raw l).label.val + 1 := by
  simpa [successorB] using h


private theorem terminal_label_phase
    (u : Cell ψ κ τ) (h : atTerminalB u = true) :
    (raw u).label.val + 1 = ψ := by
  simpa [atTerminalB] using h


private theorem groupStart_successor_phase
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    R2Coherence.groupStart ring (eraseCfgV3 C) (ring.rightNeighbor e) =
      R2Coherence.groupStart ring (eraseCfgV3 C) e := by
  unfold R2Coherence.groupStart
  change
    R2Coherence.back ring (ring.rightNeighbor e)
        (raw (C (ring.rightNeighbor e))).label.val =
      R2Coherence.back ring e (raw (C e)).label.val
  rw [successor_labels_phase (C e) (C (ring.rightNeighbor e)) hs]
  exact back_rightNeighbor_succ_phase ring e (raw (C e)).label.val


private theorem groupPos_same_successor_phase
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (k : Nat) :
    R2Coherence.groupPos ring (eraseCfgV3 C)
        (ring.rightNeighbor e) k =
      R2Coherence.groupPos ring (eraseCfgV3 C) e k := by
  unfold R2Coherence.groupPos
  rw [groupStart_successor_phase ring C e hs]


private theorem branch_sweep_conditions_phase
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .sweep) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok = .sweep := by
  unfold branchAtV3 at hb
  by_cases hSeek : r.ctl.tok = .seek
  · rw [if_pos hSeek] at hb
    cases hb
  · rw [if_neg hSeek] at hb
    by_cases hSweep : l.ctl.tok = .sweep
    · exact ⟨hSeek, hSweep⟩
    · rw [if_neg hSweep] at hb
      by_cases hCommit : r.ctl.tok = .commit
      · rw [if_pos hCommit] at hb
        cases hb
      · rw [if_neg hCommit] at hb
        by_cases hRelease : l.ctl.tok = .release
        · rw [if_pos hRelease] at hb
          cases hb
        · rw [if_neg hRelease] at hb
          by_cases hScrub : r.ctl.tok = .scrubL
          · rw [if_pos hScrub] at hb
            cases hb
          · rw [if_neg hScrub] at hb
            by_cases hOpenR : l.ctl.tok = .openR
            · rw [if_pos hOpenR] at hb
              cases hb
            · rw [if_neg hOpenR] at hb
              by_cases hNone :
                  l.ctl.tok = .none ∧ r.ctl.tok = .none
              · rw [if_pos hNone] at hb
                by_cases hSealed :
                    l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed
                · rw [if_pos hSealed] at hb
                  cases hb
                · rw [if_neg hSealed] at hb
                  by_cases hOpen :
                      l.ctl.mark = .open ∧ r.ctl.mark = .open
                  · rw [if_pos hOpen] at hb
                    by_cases hHaz :
                        pairHazardV3 l.phys r.phys
                            (proposalV3 hψ (by decide : 0 < 2) h2 l r).1
                            (proposalV3 hψ (by decide : 0 < 2) h2 l r).2 = true
                    · simp [hHaz] at hb
                    · simp [hHaz] at hb
                  · rw [if_neg hOpen] at hb
                    cases hb
              · rw [if_neg hNone] at hb
                cases hb


private theorem rowV3_sweep_eq_phase
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .sweep) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = sweepStageV3 l r := by
  rcases branch_sweep_conditions_phase hψ h2 l r hb with
    ⟨hSeek, hSweep⟩
  simp [rowV3, hSeek, hSweep]


private theorem edge_distinct_of_successor_phase
    (C : FC n ψ κ τ) (ring : DirectedRing n) (e : Fin n)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    e ≠ ring.rightNeighbor e := by
  intro h
  have hSame := congrArg (fun p : Fin n => (raw (C p)).label.val) h
  have hSucc := successor_labels_phase
    (C e) (C (ring.rightNeighbor e)) hs
  omega


private theorem clearMain_mainClearV3_phase (u : Cell ψ κ τ) :
    MainClearV3 (clearMain u) := by
  unfold MainClearV3 R2CoherenceBranches.MainClear
  simp [eraseCellV3, clearMain, R2Coherence.clearMainPhys,
    PPLLExpiringComparisonRepair.clearComparisonCarrier,
    R2Coherence.raw]


private theorem mainClearV3_setControl_iff_phase
    (u : Cell ψ κ τ) (m : R2Coherence.Mark) (t : TokenV3) :
    MainClearV3 (setControl u m t) ↔ MainClearV3 u := by
  simp [MainClearV3, R2CoherenceBranches.MainClear,
    eraseCellV3, setControl, R2Coherence.raw]


private theorem closing_phaseOwnedV31
    (u : Cell ψ κ τ) (t : TokenV3) :
    PhaseOwnedV31 (setControl u .closing t) := by
  simp [PhaseOwnedV31, setControl]


private theorem clearMain_closing_owned_phase
    (u : Cell ψ κ τ) (t : TokenV3) :
    MainClearV3 (setControl (clearMain u) .closing t) ∧
      PhaseOwnedV31 (setControl (clearMain u) .closing t) := by
  constructor
  · exact (mainClearV3_setControl_iff_phase
      (clearMain u) .closing t).2 (clearMain_mainClearV3_phase u)
  · exact closing_phaseOwnedV31 (clearMain u) t


private theorem startClosing_owned_of_clear_phase
    (u : Cell ψ κ τ) (hMain : MainClearV3 u) :
    MainClearV3 (startClosing u) ∧ PhaseOwnedV31 (startClosing u) := by
  constructor
  · have h := (mainClearV3_setControl_iff_phase u .closing .seek).2 hMain
    simpa [startClosing] using h
  · simpa [startClosing] using closing_phaseOwnedV31 u .seek


private theorem sweep_step_left_good_phase
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    stepV3 hψ h2 ring C e e =
      setControl (clearMain (C e)) .closing .none := by
  have hrow := rowV3_sweep_eq_phase hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step,
    hrow, sweepStageV3, hs]


private theorem sweep_step_right_good_phase
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    stepV3 hψ h2 ring C e (ring.rightNeighbor e) =
      setControl (clearMain (C (ring.rightNeighbor e))) .closing
        (if atTerminalB (C (ring.rightNeighbor e)) then .commit else .sweep) := by
  have hrow := rowV3_sweep_eq_phase hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  have hne := edge_distinct_of_successor_phase C ring e hs
  have hrne : ring.rightNeighbor e ≠ e := Ne.symm hne
  simp [stepV3, protocolV3, PopulationProtocol.step,
    hrow, sweepStageV3, hs, hrne]


private theorem sweep_step_left_bad_phase
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = false) :
    stepV3 hψ h2 ring C e e = startClosing (C e) := by
  have hrow := rowV3_sweep_eq_phase hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step,
    hrow, sweepStageV3, hs]


private theorem sweep_step_bad_other_phase
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e i : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = false)
    (hi : i ≠ e) :
    stepV3 hψ h2 ring C e i = C i := by
  by_cases hij : i = ring.rightNeighbor e
  · subst i
    have hrow := rowV3_sweep_eq_phase hψ h2
      (C e) (C (ring.rightNeighbor e)) hb
    simpa [stepV3, protocolV3, PopulationProtocol.step,
      hrow, sweepStageV3, hs, hi]
  · exact stepV3_other hψ h2 ring C e i hi hij


private theorem ownedClear_mono_sweep_phase
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep) :
    ∀ p : Fin n,
      (MainClearV3 (C p) ∧ PhaseOwnedV31 (C p)) →
      (MainClearV3 (stepV3 hψ h2 ring C e p) ∧
        PhaseOwnedV31 (stepV3 hψ h2 ring C e p)) := by
  intro p hp
  by_cases hs : successorB (C e) (C (ring.rightNeighbor e)) = true
  · by_cases hpe : p = e
    · subst p
      rw [sweep_step_left_good_phase hψ h2 ring C e hb hs]
      exact clearMain_closing_owned_phase (C e) .none
    · by_cases hpj : p = ring.rightNeighbor e
      · subst p
        rw [sweep_step_right_good_phase hψ h2 ring C e hb hs]
        exact clearMain_closing_owned_phase
          (C (ring.rightNeighbor e))
          (if atTerminalB (C (ring.rightNeighbor e)) then .commit else .sweep)
      · rw [stepV3_other hψ h2 ring C e p hpe hpj]
        exact hp
  · have hsF := bool_false_of_not_true_phase _ hs
    by_cases hpe : p = e
    · subst p
      rw [sweep_step_left_bad_phase hψ h2 ring C e hb hsF]
      exact startClosing_owned_of_clear_phase (C e) hp.1
    · rw [sweep_step_bad_other_phase hψ h2 ring C e p hb hsF hpe]
      exact hp


private theorem sweptPrefix_frame_sweep_phase
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e i : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    (hOld : SweptPrefixOwnedClearV31 ring C i) :
    SweptPrefixOwnedClearV31 ring (stepV3 hψ h2 ring C e) i := by
  have hLab : ∀ p : Fin n,
      (raw (stepV3 hψ h2 ring C e p)).label = (raw (C p)).label :=
    stepV3_labels_eq_or_held hψ h2 ring C e
  have hMono := ownedClear_mono_sweep_phase hψ h2 ring C e hb
  unfold SweptPrefixOwnedClearV31 at hOld ⊢
  intro k
  dsimp only
  have hVal := congrArg Fin.val (hLab i)
  have hkC : k.val < (raw (C i)).label.val := by
    rw [← hVal]
    exact k.isLt
  let kC : Fin (raw (C i)).label.val := ⟨k.val, hkC⟩
  have hPrev := hOld kC
  dsimp only at hPrev
  rw [groupPos_eq_of_labels_phase ring hLab i k.val]
  exact hMono _ hPrev


private theorem group_frame_sweep_phase
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e i : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    (hOld : GroupOwnedClearV31 ring C i) :
    GroupOwnedClearV31 ring (stepV3 hψ h2 ring C e) i := by
  have hLab : ∀ p : Fin n,
      (raw (stepV3 hψ h2 ring C e p)).label = (raw (C p)).label :=
    stepV3_labels_eq_or_held hψ h2 ring C e
  have hMono := ownedClear_mono_sweep_phase hψ h2 ring C e hb
  unfold GroupOwnedClearV31 at hOld ⊢
  intro k
  dsimp only
  have hPrev := hOld k
  dsimp only at hPrev
  rw [groupPos_eq_of_labels_phase ring hLab i k.val]
  exact hMono _ hPrev


private theorem groupPos_front_step_eq_phase
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (k : Nat) :
    R2Coherence.groupPos ring
        (eraseCfgV3 (stepV3 hψ h2 ring C e))
        (ring.rightNeighbor e) k =
      R2Coherence.groupPos ring (eraseCfgV3 C) e k := by
  have hLab : ∀ p : Fin n,
      (raw (stepV3 hψ h2 ring C e p)).label = (raw (C p)).label :=
    stepV3_labels_eq_or_held hψ h2 ring C e
  calc
    R2Coherence.groupPos ring
        (eraseCfgV3 (stepV3 hψ h2 ring C e))
        (ring.rightNeighbor e) k =
      R2Coherence.groupPos ring (eraseCfgV3 C)
        (ring.rightNeighbor e) k :=
      groupPos_eq_of_labels_phase ring hLab (ring.rightNeighbor e) k
    _ = R2Coherence.groupPos ring (eraseCfgV3 C) e k :=
      groupPos_same_successor_phase ring C e hs k


private theorem sweep_new_front_prefix_phase
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hSweepOld : ∀ i : Fin n, (C i).ctl.tok = .sweep →
      SweptPrefixOwnedClearV31 ring C i)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    SweptPrefixOwnedClearV31 ring
      (stepV3 hψ h2 ring C e) (ring.rightNeighbor e) := by
  have hSweepTok := (branch_sweep_conditions_phase hψ h2
    (C e) (C (ring.rightNeighbor e)) hb).2
  have hOld := hSweepOld e hSweepTok
  have hMono := ownedClear_mono_sweep_phase hψ h2 ring C e hb
  have hSucc := successor_labels_phase
    (C e) (C (ring.rightNeighbor e)) hs
  have hDVal :
      (raw (stepV3 hψ h2 ring C e (ring.rightNeighbor e))).label.val =
        (raw (C (ring.rightNeighbor e))).label.val := by
    exact congrArg Fin.val
      (stepV3_labels_eq_or_held hψ h2 ring C e (ring.rightNeighbor e))
  unfold SweptPrefixOwnedClearV31
  intro k
  dsimp only
  have hk : k.val < (raw (C e)).label.val + 1 := by
    calc
      k.val <
          (raw (stepV3 hψ h2 ring C e (ring.rightNeighbor e))).label.val :=
        k.isLt
      _ = (raw (C (ring.rightNeighbor e))).label.val := hDVal
      _ = (raw (C e)).label.val + 1 := hSucc
  by_cases hlt : k.val < (raw (C e)).label.val
  · let kC : Fin (raw (C e)).label.val := ⟨k.val, hlt⟩
    have hPrev := hOld kC
    dsimp only at hPrev
    have hPrevD := hMono _ hPrev
    rw [groupPos_front_step_eq_phase hψ h2 ring C e hs k.val]
    exact hPrevD
  · have hkEq : k.val = (raw (C e)).label.val := by omega
    rw [groupPos_front_step_eq_phase hψ h2 ring C e hs k.val,
      hkEq, groupPos_label_selfV3_phase ring C e,
      sweep_step_left_good_phase hψ h2 ring C e hb hs]
    exact clearMain_closing_owned_phase (C e) .none


private theorem sweep_new_terminal_group_phase
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hSweepOld : ∀ i : Fin n, (C i).ctl.tok = .sweep →
      SweptPrefixOwnedClearV31 ring C i)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (ht : atTerminalB (C (ring.rightNeighbor e)) = true) :
    GroupOwnedClearV31 ring
      (stepV3 hψ h2 ring C e) (ring.rightNeighbor e) := by
  have hSweepTok := (branch_sweep_conditions_phase hψ h2
    (C e) (C (ring.rightNeighbor e)) hb).2
  have hOld := hSweepOld e hSweepTok
  have hMono := ownedClear_mono_sweep_phase hψ h2 ring C e hb
  have hSucc := successor_labels_phase
    (C e) (C (ring.rightNeighbor e)) hs
  have hTerm := terminal_label_phase (C (ring.rightNeighbor e)) ht
  have hPsi : (raw (C e)).label.val + 2 = ψ := by omega
  have hLeft := sweep_step_left_good_phase hψ h2 ring C e hb hs
  have hRight0 := sweep_step_right_good_phase hψ h2 ring C e hb hs
  have hRight :
      stepV3 hψ h2 ring C e (ring.rightNeighbor e) =
        setControl (clearMain (C (ring.rightNeighbor e))) .closing .commit := by
    simpa [ht] using hRight0
  unfold GroupOwnedClearV31
  intro k
  dsimp only
  have hkBound : k.val < (raw (C e)).label.val + 2 := by
    rw [hPsi]
    exact k.isLt
  by_cases hlt : k.val < (raw (C e)).label.val
  · let kC : Fin (raw (C e)).label.val := ⟨k.val, hlt⟩
    have hPrev := hOld kC
    dsimp only at hPrev
    have hPrevD := hMono _ hPrev
    rw [groupPos_front_step_eq_phase hψ h2 ring C e hs k.val]
    exact hPrevD
  · by_cases hEq : k.val = (raw (C e)).label.val
    · rw [groupPos_front_step_eq_phase hψ h2 ring C e hs k.val,
        hEq, groupPos_label_selfV3_phase ring C e, hLeft]
      exact clearMain_closing_owned_phase (C e) .none
    · have hNext : k.val = (raw (C e)).label.val + 1 := by omega
      have hMove := groupPos_rightNeighborR2_phase
        ring (eraseCfgV3 C) e (raw (C e)).label.val
      have hSelf := groupPos_label_selfV3_phase ring C e
      rw [hSelf] at hMove
      rw [groupPos_front_step_eq_phase hψ h2 ring C e hs k.val,
        hNext, ← hMove, hRight]
      exact clearMain_closing_owned_phase
        (C (ring.rightNeighbor e)) .commit


theorem phaseMainClear_sweep_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (_hElection : ElectionGeometryV31 ring C)
    (hPhase : PhaseMainClearV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep) :
    PhaseMainClearV31 ring (stepV3 hψ h2 ring C e) := by
  unfold PhaseMainClearV31 at hPhase ⊢
  rcases hPhase with ⟨hSweep, hCommit, hSealed, hRelease, hScrub⟩
  have hMono := ownedClear_mono_sweep_phase hψ h2 ring C e hb
  by_cases hs : successorB (C e) (C (ring.rightNeighbor e)) = true
  · have hLeft := sweep_step_left_good_phase hψ h2 ring C e hb hs
    have hRight := sweep_step_right_good_phase hψ h2 ring C e hb hs
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      by_cases hie : i = e
      · subst i
        rw [hLeft] at hi
        simp [setControl] at hi
      · by_cases hij : i = ring.rightNeighbor e
        · subst i
          exact sweep_new_front_prefix_phase
            hψ h2 ring C e hSweep hb hs
        · have hEq := stepV3_other hψ h2 ring C e i hie hij
          rw [hEq] at hi
          exact sweptPrefix_frame_sweep_phase
            hψ h2 ring C e i hb (hSweep i hi)
    · intro i hi
      by_cases hie : i = e
      · subst i
        rw [hLeft] at hi
        simp [setControl] at hi
      · by_cases hij : i = ring.rightNeighbor e
        · subst i
          by_cases ht : atTerminalB (C (ring.rightNeighbor e)) = true
          · exact sweep_new_terminal_group_phase
              hψ h2 ring C e hSweep hb hs ht
          · have htF := bool_false_of_not_true_phase _ ht
            rw [hRight] at hi
            simp [htF, setControl] at hi
        · have hEq := stepV3_other hψ h2 ring C e i hie hij
          rw [hEq] at hi
          exact group_frame_sweep_phase
            hψ h2 ring C e i hb (hCommit i hi)
    · intro i hi
      by_cases hie : i = e
      · subst i
        rw [hLeft] at hi
        simp [setControl] at hi
      · by_cases hij : i = ring.rightNeighbor e
        · subst i
          rw [hRight] at hi
          simp [setControl] at hi
        · have hEq := stepV3_other hψ h2 ring C e i hie hij
          rw [hEq] at hi
          exact group_frame_sweep_phase
            hψ h2 ring C e i hb (hSealed i hi)
    · intro i hi
      by_cases hie : i = e
      · subst i
        rw [hLeft] at hi
        simp [setControl] at hi
      · by_cases hij : i = ring.rightNeighbor e
        · subst i
          rw [hRight] at hi
          cases ht : atTerminalB (C (ring.rightNeighbor e))
          · rw [ht] at hi
            have hbad :
                (setControl (clearMain (C (ring.rightNeighbor e)))
                  R2Coherence.Mark.closing TokenV3.sweep).ctl.tok =
                  TokenV3.release := by
              exact hi
            change TokenV3.sweep = TokenV3.release at hbad
            cases hbad
          · rw [ht] at hi
            have hbad :
                (setControl (clearMain (C (ring.rightNeighbor e)))
                  R2Coherence.Mark.closing TokenV3.commit).ctl.tok =
                  TokenV3.release := by
              exact hi
            change TokenV3.commit = TokenV3.release at hbad
            cases hbad
        · have hEq := stepV3_other hψ h2 ring C e i hie hij
          rw [hEq] at hi
          exact group_frame_sweep_phase
            hψ h2 ring C e i hb (hRelease i hi)
    · intro i hi
      by_cases hie : i = e
      · subst i
        rw [hLeft] at hi
        simp [setControl] at hi
      · by_cases hij : i = ring.rightNeighbor e
        · subst i
          rw [hRight] at hi
          cases ht : atTerminalB (C (ring.rightNeighbor e))
          · rw [ht] at hi
            have hbad :
                (setControl (clearMain (C (ring.rightNeighbor e)))
                  R2Coherence.Mark.closing TokenV3.sweep).ctl.tok =
                  TokenV3.scrubL := by
              exact hi
            change TokenV3.sweep = TokenV3.scrubL at hbad
            cases hbad
          · rw [ht] at hi
            have hbad :
                (setControl (clearMain (C (ring.rightNeighbor e)))
                  R2Coherence.Mark.closing TokenV3.commit).ctl.tok =
                  TokenV3.scrubL := by
              exact hi
            change TokenV3.commit = TokenV3.scrubL at hbad
            cases hbad
        · have hEq := stepV3_other hψ h2 ring C e i hie hij
          rw [hEq] at hi
          exact group_frame_sweep_phase
            hψ h2 ring C e i hb (hScrub i hi)
  · have hsF := bool_false_of_not_true_phase _ hs
    have hLeft := sweep_step_left_bad_phase hψ h2 ring C e hb hsF
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      by_cases hie : i = e
      · subst i
        rw [hLeft] at hi
        simp [startClosing, setControl] at hi
      · have hEq := sweep_step_bad_other_phase hψ h2 ring C e i hb hsF hie
        rw [hEq] at hi
        exact sweptPrefix_frame_sweep_phase
          hψ h2 ring C e i hb (hSweep i hi)
    · intro i hi
      by_cases hie : i = e
      · subst i
        rw [hLeft] at hi
        simp [startClosing, setControl] at hi
      · have hEq := sweep_step_bad_other_phase hψ h2 ring C e i hb hsF hie
        rw [hEq] at hi
        exact group_frame_sweep_phase
          hψ h2 ring C e i hb (hCommit i hi)
    · intro i hi
      by_cases hie : i = e
      · subst i
        rw [hLeft] at hi
        simp [startClosing, setControl] at hi
      · have hEq := sweep_step_bad_other_phase hψ h2 ring C e i hb hsF hie
        rw [hEq] at hi
        exact group_frame_sweep_phase
          hψ h2 ring C e i hb (hSealed i hi)
    · intro i hi
      by_cases hie : i = e
      · subst i
        rw [hLeft] at hi
        simp [startClosing, setControl] at hi
      · have hEq := sweep_step_bad_other_phase hψ h2 ring C e i hb hsF hie
        rw [hEq] at hi
        exact group_frame_sweep_phase
          hψ h2 ring C e i hb (hRelease i hi)
    · intro i hi
      by_cases hie : i = e
      · subst i
        rw [hLeft] at hi
        simp [startClosing, setControl] at hi
      · have hEq := sweep_step_bad_other_phase hψ h2 ring C e i hb hsF hie
        rw [hEq] at hi
        exact group_frame_sweep_phase
          hψ h2 ring C e i hb (hScrub i hi)


/-- Admitted geometry supplies the ambient ElectionGeometryV31 premise. -/
theorem phaseMainClear_sweep_step_of_admitted
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hGeom : AdmittedPostBirthGeometryV3 hψ ring C)
    (hPhase : PhaseMainClearV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep) :
    PhaseMainClearV31 ring (stepV3 hψ h2 ring C e) := by
  exact phaseMainClear_sweep_step hψ h2 ring C e
    (admitted_implies_electionGeometryV31 hψ ring C hGeom)
    hPhase hb

private theorem h3 : 0 < 3 := by decide
private theorem h23 : 2 ≤ 3 := by decide
private def ring3 : DirectedRing 3 := ⟨by decide⟩


private def literalPhase
    (lab : Fin 3) (state : MainState := .none) : R2.Cell 3 3 48 :=
  let seed := WriterProducerRegression.clean h3 (fun _ => false) lab
  let b := seed.base.core.core
  let b' : BoundedAgentState 3 3 := {
    b with
    leader := false
    shield := false
    gen_ws := false
    label := lab
    state := state
    path := .bot
    bit := false
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


private def cellPhase
    (p : R2.Cell 3 3 48)
    (m : R2Coherence.Mark) (t : TokenV3) : Cell 3 3 48 :=
  ⟨p, ⟨m, t⟩⟩


/-- Restatement of the private forged-commit fixture. -/
private def commitProxyPhase : FC 3 3 3 48 := fun i =>
  match i.val with
  | 0 => cellPhase (literalPhase 0) .open .commit
  | 1 => cellPhase (literalPhase 1 .compare1) .open .none
  | _ => cellPhase (literalPhase 2) .open .none


/-- Restatement of the private forged-sweep fixture. -/
private def sweepProxyPhase : FC 3 3 3 48 := fun i =>
  match i.val with
  | 0 => cellPhase (literalPhase 0 .compare1) .open .none
  | 1 => cellPhase (literalPhase 1) .closing .sweep
  | _ => cellPhase (literalPhase 2) .closing .none


theorem commitProxyPhase_geometry :
    AdmittedPostBirthGeometryV3 h3 ring3 commitProxyPhase := by
  decide +kernel


theorem commitProxyPhase_branch :
    branchAtV3 h3 h23
      (commitProxyPhase 2)
      (commitProxyPhase (ring3.rightNeighbor 2)) = .commit := by
  decide +kernel


/-- The forged-commit fixture is excluded by the separate phase invariant. -/
theorem commitProxyPhase_not_phaseMainClear :
    ¬ PhaseMainClearV31 ring3 commitProxyPhase := by
  decide +kernel


theorem sweepProxyPhase_geometry :
    AdmittedPostBirthGeometryV3 h3 ring3 sweepProxyPhase := by
  decide +kernel


theorem sweepProxyPhase_branch :
    branchAtV3 h3 h23
      (sweepProxyPhase 1)
      (sweepProxyPhase (ring3.rightNeighbor 1)) = .sweep := by
  decide +kernel


/-- The forged-sweep fixture is excluded already at the strict prefix behind the live sweep. -/
theorem sweepProxyPhase_not_phaseMainClear :
    ¬ PhaseMainClearV31 ring3 sweepProxyPhase := by
  decide +kernel


end R2CoherenceV31PhaseMainClear


