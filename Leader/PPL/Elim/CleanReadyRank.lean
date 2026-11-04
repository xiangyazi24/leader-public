import Leader.PPL.Elim.PBClosure

/-!
# LD(736): corrected clean-ready rank and finite cost

CRRankStepSpec from LDLocalSector is false because its current
configuration is not required to have a follower-only strict sector interior.
This file states the corrected current-sector invariant, proves the exact
initial classifier, isolates one literal row-E obligation per CR stage, and
completes the Bellman/accounting layer from those four obligations.
-/

namespace PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Current consecutiveness of the fixed sector endpoints. This is the
File-2 spelling of the same current-state condition used by the corrected
File-3 sealed-sector checker. -/
def CRInteriorFollowers
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n) : Prop :=
  ∀ q, 0 < q → q < A.gap →
    (C (advance ring A.left q)).leader = false

/-- A false interior leader bit can never be recreated by literal row E. -/
theorem crInteriorFollowers_step
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n) (e : Fin n)
    (h : CRInteriorFollowers A C) :
    CRInteriorFollowers A (stepE ring C e) := by
  intro q hq0 hq
  exact
    stepE_leader_false_of_false ring C e
      (advance ring A.left q) (h q hq0 hq)

/-! ## Initial CR classifier -/

private theorem boundedLeast
    (P : Nat → Prop) (d : Nat)
    (h : ∃ q, q < d ∧ P q) :
    ∃ p, p < d ∧ P p ∧ ∀ q, q < p → ¬ P q := by
  classical
  obtain ⟨q, hqd, hq⟩ := h
  revert hqd hq
  induction q using Nat.strongRecOn with
  | ind q ih =>
      intro hqd hq
      by_cases he : ∃ r, r < q ∧ P r
      · obtain ⟨r, hrq, hr⟩ := he
        exact ih r hrq (Nat.lt_trans hrq hqd) hr
      · exact ⟨q, hqd, hq, by
          intro r hrq hr
          exact he ⟨r, hrq, hr⟩⟩

private theorem leastBulletOffset_exists
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (h : SectorHasBullet A C) :
    ∃ p, LeastBulletOffset A C p := by
  obtain ⟨p, hp, hbullet, hmin⟩ :=
    boundedLeast
      (fun q =>
        (C (advance ring A.left q)).bullet ≠ (0 : Fin 3))
      A.gap h
  refine ⟨p, hp, hbullet, ?_⟩
  intro q hq
  by_cases hz :
      (C (advance ring A.left q)).bullet = (0 : Fin 3)
  · exact hz
  · exact False.elim ((hmin q hq) hz)

private theorem sectorBulletFree_of_not_hasBullet
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (h : ¬ SectorHasBullet A C) :
    SectorBulletFree A C := by
  intro q hq
  by_cases hz :
      (C (advance ring A.left q)).bullet = (0 : Fin 3)
  · exact hz
  · exact False.elim (h ⟨q, hq, hz⟩)

private theorem returnFront_exists
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n)
    (hs0 : (C A.left).signalB = false) :
    ∃ q, ReturnFront A C q := by
  classical
  by_cases hsig :
      ∃ q, q < A.gap ∧
        (C (advance ring A.left q)).signalB = true
  · obtain ⟨q, hq, htrue, hmin⟩ :=
      boundedLeast
        (fun r =>
          (C (advance ring A.left r)).signalB = true)
        A.gap hsig
    have hq0 : 0 < q := by
      rcases Nat.eq_zero_or_pos q with hqz | hpos
      · exfalso
        subst q
        have ht0 : (C (advance ring A.left 0)).signalB = true := htrue
        simp [advance_zero] at ht0
        rw [hs0] at ht0
        contradiction
      · exact hpos
    refine ⟨q, hq0, Nat.le_of_lt hq, ?_, ?_⟩
    · intro r hr
      cases hrs : (C (advance ring A.left r)).signalB with
      | false =>
          rfl
      | true =>
          exact False.elim ((hmin r hr) hrs)
    · intro _
      exact htrue
  · refine ⟨A.gap, A.gap_pos, Nat.le_refl _, ?_, ?_⟩
    · intro r hr
      cases hrs : (C (advance ring A.left r)).signalB with
      | false =>
          rfl
      | true =>
          exact False.elim (hsig ⟨r, hr, hrs⟩)
    · intro hlt
      omega

theorem crRankInit : CRRankInitSpec := by
  classical
  intro n ring C0 A C _hPB hnotDone
  have hnotDeleted : ¬ EndpointDeleted A C := by
    intro h
    exact hnotDone (Or.inl h)
  by_cases hbullet : SectorHasBullet A C
  · cases hs : (C A.left).signalB with
    | false =>
        obtain ⟨p, hp⟩ :=
          leastBulletOffset_exists ring A C hbullet
        let mode : CRMode := .drain p
        have hholds : CRModeHolds A C mode := by
          exact ⟨hnotDeleted, hs, hp⟩
        exact
          ⟨mode, hholds,
            crRank_le_three_gap A mode
              (crModeHolds_valid A C mode hholds)⟩
    | true =>
        let mode : CRMode := .repair
        have hholds : CRModeHolds A C mode := by
          exact ⟨hnotDeleted, hs, hbullet⟩
        exact
          ⟨mode, hholds,
            crRank_le_three_gap A mode
              (crModeHolds_valid A C mode hholds)⟩
  · have hfree : SectorBulletFree A C :=
      sectorBulletFree_of_not_hasBullet A C hbullet
    cases hs : (C A.left).signalB with
    | false =>
        obtain ⟨q, hfront⟩ :=
          returnFront_exists ring A C hs
        let mode : CRMode := .ret q
        have hholds : CRModeHolds A C mode := by
          exact ⟨hnotDeleted, hfree, hs, hfront⟩
        exact
          ⟨mode, hholds,
            crRank_le_three_gap A mode
              (crModeHolds_valid A C mode hholds)⟩
    | true =>
        exact False.elim
          (hnotDone (Or.inr ⟨hs, hfree⟩))

/-! ## Corrected one-step interface -/

/-- The conclusion of the old CRRankStepSpec, factored out so that the
four literal row-E stages can be isolated independently. -/
def CRStepConclusion
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (mode : CRMode) : Prop :=
  (∀ e : Fin n,
    CRDone A (stepE ring C e) ∨
      ∃ mode',
        CRModeHolds A (stepE ring C e) mode' ∧
        crRank A mode' ≤ crRank A mode) ∧
  (CRDone A (stepE ring C (crRequiredEdge A mode)) ∨
    ∃ mode',
      CRModeHolds
        A (stepE ring C (crRequiredEdge A mode)) mode' ∧
      crRank A mode' < crRank A mode)

/-- Corrected form of CRRankStepSpec: the fixed endpoints must still be
consecutive in the current configuration. -/
def CRRankStepSpecCorrected : Prop :=
  ∀ {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (mode : CRMode),
    PPL.Elim.PB ring C →
    CRInteriorFollowers A C →
    CRModeHolds A C mode →
      CRStepConclusion ring A C mode

/-- Remaining physical row-E obligation for the arbitrary initial drain
stage. -/
def CRDrainStepSpec : Prop :=
  ∀ {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (p : Nat),
    PPL.Elim.PB ring C →
    CRInteriorFollowers A C →
    CRModeHolds A C (.drain p) →
      CRStepConclusion ring A C (.drain p)

/-- Remaining physical row-E obligation for the one-source-firing repair
stage. -/
def CRRepairStepSpec : Prop :=
  ∀ {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n),
    PPL.Elim.PB ring C →
    CRInteriorFollowers A C →
    CRModeHolds A C .repair →
      CRStepConclusion ring A C .repair

/-- Remaining physical row-E obligation for the fresh-front sweep stage. -/
def CRSweepStepSpec : Prop :=
  ∀ {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (p : Nat),
    PPL.Elim.PB ring C →
    CRInteriorFollowers A C →
    CRModeHolds A C (.sweep p) →
      CRStepConclusion ring A C (.sweep p)

/-- Remaining physical row-E obligation for nearest-return propagation. -/
def CRReturnStepSpec : Prop :=
  ∀ {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (q : Nat),
    PPL.Elim.PB ring C →
    CRInteriorFollowers A C →
    CRModeHolds A C (.ret q) →
      CRStepConclusion ring A C (.ret q)

theorem crRankStep_corrected
    (hDrain : CRDrainStepSpec)
    (hRepair : CRRepairStepSpec)
    (hSweep : CRSweepStepSpec)
    (hReturn : CRReturnStepSpec) :
    CRRankStepSpecCorrected := by
  intro n ring C0 A C mode hPB hInterior hmode
  cases mode with
  | drain p =>
      exact hDrain ring A C p hPB hInterior hmode
  | repair =>
      exact hRepair ring A C hPB hInterior hmode
  | sweep p =>
      exact hSweep ring A C p hPB hInterior hmode
  | ret q =>
      exact hReturn ring A C q hPB hInterior hmode

/-! ## Stopped ghost monitor and raw-cost domination -/

private structure CRState
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0) where
  config : Config n
  mode : CRMode
  pb : PPL.Elim.PB ring config
  interior : CRInteriorFollowers A config
  holds : CRModeHolds A config mode

private theorem crNext_exists
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (hstep : CRRankStepSpecCorrected)
    (s : CRState ring A) (e : Fin n)
    (hdone : ¬ CRDone A (stepE ring s.config e)) :
    ∃ mode',
      CRModeHolds A (stepE ring s.config e) mode' ∧
      crRank A mode' ≤ crRank A s.mode ∧
      (e = crRequiredEdge A s.mode →
        crRank A mode' < crRank A s.mode) := by
  have hs :=
    hstep ring A s.config s.mode
      s.pb s.interior s.holds
  by_cases he : e = crRequiredEdge A s.mode
  · subst e
    rcases hs.2 with hdone' | ⟨mode', hmode', hrank'⟩
    · exact False.elim (hdone hdone')
    · exact
        ⟨mode', hmode', Nat.le_of_lt hrank',
          fun _ => hrank'⟩
  · rcases hs.1 e with hdone' | ⟨mode', hmode', hrank'⟩
    · exact False.elim (hdone hdone')
    · exact
        ⟨mode', hmode', hrank',
          fun h => False.elim (he h)⟩

private noncomputable def crNextMode
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (hstep : CRRankStepSpecCorrected)
    (s : CRState ring A) (e : Fin n)
    (hdone : ¬ CRDone A (stepE ring s.config e)) :
    CRMode :=
  Classical.choose
    (crNext_exists ring A hstep s e hdone)

private theorem crNextMode_spec
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (hstep : CRRankStepSpecCorrected)
    (s : CRState ring A) (e : Fin n)
    (hdone : ¬ CRDone A (stepE ring s.config e)) :
    CRModeHolds A (stepE ring s.config e)
        (crNextMode ring A hstep s e hdone) ∧
      crRank A (crNextMode ring A hstep s e hdone) ≤
        crRank A s.mode ∧
      (e = crRequiredEdge A s.mode →
        crRank A (crNextMode ring A hstep s e hdone) <
          crRank A s.mode) := by
  exact
    Classical.choose_spec
      (crNext_exists ring A hstep s e hdone)

private noncomputable def crGhostStep
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (hstep : CRRankStepSpecCorrected) :
    CRState ring A → Fin n → StopNode (CRState ring A) :=
  fun s e => by
    classical
    if hdone : CRDone A (stepE ring s.config e) then
      exact .success
    else
      exact .active {
        config := stepE ring s.config e
        mode := crNextMode ring A hstep s e hdone
        pb := pbStepClosure ring s.config e s.pb
        interior :=
          crInteriorFollowers_step A s.config e s.interior
        holds :=
          (crNextMode_spec ring A hstep s e hdone).1
      }

private def crGhostRank
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (s : CRState ring A) : Nat :=
  crRank A s.mode

private def crGhostRequired
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (s : CRState ring A) : Fin n :=
  crRequiredEdge A s.mode

private theorem crGhostLaws
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (hstep : CRRankStepSpecCorrected) :
    PredictableRankLaws
      (crGhostStep ring A hstep)
      (crGhostRank ring A)
      (crGhostRequired ring A) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro s
    exact
      crRank_pos A s.mode
        (crModeHolds_valid A s.config s.mode s.holds)
  · intro s
    by_cases hdone :
        CRDone A
          (stepE ring s.config (crGhostRequired ring A s))
    · simp [crGhostStep, hdone]
    · have hs :=
        crNextMode_spec ring A hstep s
          (crGhostRequired ring A s) hdone
      have hlt := hs.2.2 (by
        rfl)
      unfold crGhostStep crGhostRank crGhostRequired at *
      rw [dif_neg hdone]
      exact hlt
  · intro s e he
    by_cases hdone : CRDone A (stepE ring s.config e)
    · simp [crGhostStep, hdone]
    · have hs :=
        crNextMode_spec ring A hstep s e hdone
      simpa [crGhostStep, hdone, crGhostRank]
        using hs.2.1

private theorem crGhost_active_config
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (hstep : CRRankStepSpecCorrected)
    (s : CRState ring A) (e : Fin n) (t : CRState ring A)
    (h :
      crGhostStep ring A hstep s e = .active t) :
    t.config = stepE ring s.config e := by
  classical
  by_cases hdone : CRDone A (stepE ring s.config e)
  · have hf : False := by
      simpa [crGhostStep, hdone] using h
    exact hf.elim
  · simp [crGhostStep, hdone] at h
    cases h
    rfl

private theorem crGhost_success_done
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (hstep : CRRankStepSpecCorrected)
    (s : CRState ring A) (e : Fin n)
    (h : crGhostStep ring A hstep s e = .success) :
    CRDone A (stepE ring s.config e) := by
  classical
  by_cases hdone : CRDone A (stepE ring s.config e)
  · exact hdone
  · have hf : False := by
      simpa [crGhostStep, hdone] using h
    exact hf.elim

private theorem crGhost_ne_failure
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (hstep : CRRankStepSpecCorrected)
    (s : CRState ring A) (e : Fin n) :
    crGhostStep ring A hstep s e ≠ .failure := by
  classical
  by_cases hdone : CRDone A (stepE ring s.config e) <;>
    simp [crGhostStep, hdone]

/-- A sound never-failing stopped strategy upper-bounds the repository's
raw first-done cost numerator. -/
private theorem costNumerator_le_soundStrategy
    {P G : Type} {n : Nat}
    (physicalStep : P → Fin n → P)
    (done : P → Prop)
    (strategyStep : G → Fin n → StopNode G)
    (physical : G → P)
    (hactive : ∀ state edge child,
      strategyStep state edge = .active child →
        physical child =
          physicalStep (physical state) edge)
    (hsuccess : ∀ state edge,
      strategyStep state edge = .success →
        done (physicalStep (physical state) edge))
    (hfailure : ∀ state edge,
      strategyStep state edge ≠ .failure) :
    ∀ state T,
      costNumerator physicalStep done
          (physical state) T ≤
        truncatedActiveCostNumerator strategyStep
          (.active state) T := by
  intro state T
  induction T generalizing state with
  | zero =>
      simp [truncatedActiveCostNumerator]
  | succ T ih =>
      by_cases hdone : done (physical state)
      · rw [costNumerator_terminal
          physicalStep done (physical state) hdone]
        exact Nat.zero_le _
      · rw [costNumerator_succ
          physicalStep done (physical state) hdone]
        simp only [truncatedActiveCostNumerator]
        apply Nat.add_le_add_left
        apply ofFn_sum_le
        intro edge
        generalize hnode :
          strategyStep state edge = node
        cases node with
        | success =>
            have hchildDone :=
              hsuccess state edge hnode
            rw [costNumerator_terminal
              physicalStep done
              (physicalStep (physical state) edge)
              hchildDone]
            exact Nat.zero_le _
        | failure =>
            exact False.elim
              (hfailure state edge hnode)
        | active child =>
            have hphysical :=
              hactive state edge child hnode
            simpa [hphysical] using ih child

/-! ## File-2 cost endpoint -/

/-- Once the four corrected literal row-E stage obligations are discharged,
the exact File-2 raw cost bound follows with no further physical assumptions. -/
theorem cleanReady_cost
    (hDrain : CRDrainStepSpec)
    (hRepair : CRRepairStepSpec)
    (hSweep : CRSweepStepSpec)
    (hReturn : CRReturnStepSpec) :
    CleanReadyCostObligation := by
  classical
  intro n ring C hPB A T
  by_cases hdone : CRDone A C
  · rw [costNumerator_terminal
      (stepE ring) (CRDone A) C hdone]
    exact Nat.zero_le _
  · obtain ⟨mode, hmode, hrank⟩ :=
      crRankInit ring A C hPB hdone
    have hInterior : CRInteriorFollowers A C := by
      exact A.interior_follower
    have hstep : CRRankStepSpecCorrected :=
      crRankStep_corrected
        hDrain hRepair hSweep hReturn
    let start : CRState ring A := {
      config := C
      mode := mode
      pb := hPB
      interior := hInterior
      holds := hmode
    }
    have hdom0 :=
      costNumerator_le_soundStrategy
        (stepE ring) (CRDone A)
        (crGhostStep ring A hstep)
        (fun s : CRState ring A => s.config)
        (crGhost_active_config ring A hstep)
        (crGhost_success_done ring A hstep)
        (crGhost_ne_failure ring A hstep)
        start T
    have hdom :
        costNumerator (stepE ring) (CRDone A) C T ≤
          truncatedActiveCostNumerator
            (crGhostStep ring A hstep)
            (.active start) T := by
      simpa [start] using hdom0
    have hsuper :=
      predictableRank_cost
        (crGhostStep ring A hstep)
        (crGhostRank ring A)
        (crGhostRequired ring A)
        (crGhostLaws ring A hstep)
    have hbell :=
      truncatedActiveCostNumerator_mul_le_of_natSuperSolution
        (crGhostStep ring A hstep) 1
        (predictableRankPotential n (crGhostRank ring A))
        hsuper (.active start) T
    have htree :
        truncatedActiveCostNumerator
            (crGhostStep ring A hstep)
            (.active start) T ≤
          n ^ T * (n * crRank A mode) := by
      simpa
        [predictableRankPotential, crGhostRank, start]
        using hbell
    have hm :
        n * crRank A mode ≤
          3 * n * A.gap := by
      have h := Nat.mul_le_mul_left n hrank
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        using h
    calc
      costNumerator (stepE ring) (CRDone A) C T
          ≤ truncatedActiveCostNumerator
              (crGhostStep ring A hstep)
              (.active start) T := hdom
      _ ≤ n ^ T * (n * crRank A mode) := htree
      _ ≤ n ^ T * (3 * n * A.gap) :=
        Nat.mul_le_mul_left (n ^ T) hm

end PPL.Convergence.LDLocal

#print axioms PPL.Convergence.LDLocal.crInteriorFollowers_step
#print axioms PPL.Convergence.LDLocal.crRankInit
#print axioms PPL.Convergence.LDLocal.crRankStep_corrected
#print axioms PPL.Convergence.LDLocal.cleanReady_cost
