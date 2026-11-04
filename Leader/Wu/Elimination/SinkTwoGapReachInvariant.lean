import Leader.Wu.Elimination.SinkTwoGapDeletionWired
import Leader.Wu.Elimination.SinkTwoGapEpochSuccessor

open FiniteUniformStoppingTree PPLLRepair
open LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption
open LDSinkGapDoneInvariant LDSinkGapBlockedPreStep LDSinkGapServiceRank
open LDSinkGapCleanupBound LDTwoGapFrame
open LDSinkTwoGapEpochKernel LDSinkTwoGapEpochSuccessor
open LDSinkTwoGapNoResetKernel LDSinkTwoGapAttemptCells
open LDSinkTwoGapEntrance LDSinkTwoGapDeletionWired

namespace LDSinkTwoGapReachInvariant

set_option autoImplicit false

noncomputable section

variable {n ψ : Nat}

/-! ## Exact obstructions to preserving the old tag -/

/-- Failure fixes the old phase at parked, even after reactivation. -/
theorem absorption_post_parked
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : AState n ψ) (e : Fin n)
    (hf : attemptStepRaw hψ F x e = .failure) :
    (postState hψ F x e).phase = .parked := by
  have hp : x.phase = .parked :=
    ((attemptStepRaw_failure_iff hψ F x e).mp hf).2.1
  simp [postState, advanceAState, advanceAPhase, hp]

/-- The precise failed TagDomain field when the parked bullet is gone.
The clearing fact is a hypothesis, not an asserted kernel fact. -/
theorem absorption_parked_iff_fails
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : AState n ψ) (e : Fin n)
    (hf : attemptStepRaw hψ F x e = .failure)
    (hb : (attemptStepConf hψ F x e (F.attack.pos 1)).bullet ≠ (2 : Fin 3)) :
    ¬ ((postState hψ F x e).phase = .parked ↔
      ((postState hψ F x e).conf (F.attack.pos 1)).bullet = (2 : Fin 3)) := by
  intro h
  exact hb (h.mp (absorption_post_parked hψ F x e hf))

theorem absorption_post_not_tag
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : AState n ψ) (e : Fin n)
    (hf : attemptStepRaw hψ F x e = .failure)
    (hb : (attemptStepConf hψ F x e (F.attack.pos 1)).bullet ≠ (2 : Fin 3)) :
    ¬ TagDomain F (postState hψ F x e) := by
  intro ht
  exact absorption_parked_iff_fails hψ F x e hf hb ht.parked_iff

/-- With no live bullet anywhere in the attack sector, the shot field fails. -/
theorem no_live_not_uniqueLiveShot
    (F : TwoGapFrame n) (C : Fin n → AgentState ψ)
    (hclear : ∀ t : Nat, 0 < t → t ≤ F.attack.d →
      (C (F.attack.pos t)).bullet ≠ (2 : Fin 3)) :
    ¬ UniqueLiveShot F C := by
  intro hs
  rcases hs with ⟨t, ht, htd, hb, _⟩
  exact hclear t ht htd hb

/-- Done attack states also contradict the explicit non-done tag field. -/
theorem done_not_tag (F : TwoGapFrame n) (x : AState n ψ)
    (hd : GapDoneC F.attack x.conf) : ¬ TagDomain F x := by
  intro ht
  exact ht.not_done hd

/-- A cleared raw absorption is an active entrance successor, not RaceReady. -/
theorem cleared_absorption_is_entrance_active
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : AState n ψ) (e : Fin n)
    (hf : attemptStepRaw hψ F x e = .failure)
    (hb : (attemptStepConf hψ F x e (F.attack.pos 1)).bullet ≠ (2 : Fin 3)) :
    entranceStep hψ F x e = .active (postState hψ F x e) := by
  classical
  have hs := ((attemptStepRaw_failure_iff hψ F x e).mp hf).1
  have hE : ¬ EntranceSuccess F (attemptStepConf hψ F x e) := by
    intro hh
    rcases hh with hr | hd
    · exact hb hr.1
    · exact hs hd
  rw [entrance_normal_form, if_neg hE]

/-- A witnessed cleared absorption from a valid seed refutes old closure.
This theorem does not assert that such a witness has been constructed here. -/
theorem no_old_closure_of_cleared_absorption
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : AState n ψ) (e : Fin n)
    (hi : AInvariant hψ F x)
    (hf : attemptStepRaw hψ F x e = .failure)
    (hb : (attemptStepConf hψ F x e (F.attack.pos 1)).bullet ≠ (2 : Fin 3)) :
    ¬ (∀ y : AState n ψ, EntranceReach hψ F y → AInvariant hψ F y) := by
  intro hclosed
  have hr : EntranceReach hψ F (postState hψ F x e) :=
    ActiveReach.next e (ActiveReach.base hi)
      (cleared_absorption_is_entrance_active hψ F x e hf hb)
  exact absorption_post_not_tag hψ F x e hf hb
    (hclosed (postState hψ F x e) hr).tag

/-! ## Gap preservation: isolate only the clean-boundary signal seam -/

structure GapPair (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AState n ψ) : Prop where
  recovery : GapInvariant hψ F.recovery x.conf
  attack : GapInvariant hψ F.attack x.conf

private theorem invariant_not_deleted
    (hψ : ψ > 0) (G : GapFrame n) (C : Fin n → AgentState ψ)
    (hi : GapInvariant hψ G C) : ¬ EndpointDeleted G C := by
  intro hd
  rcases hd with h0 | hd
  · have hh : true = false := hi.1.1.symm.trans h0
    cases hh
  · have hh : true = false := hi.1.2.symm.trans hd
    cases hh

private theorem follower_after_step
    (hψ : ψ > 0) (G : GapFrame n) (C : Fin n → AgentState ψ)
    (e v : Fin n) (hv : (C v).leader = false) :
    (sinkStepC hψ G C e v).leader = false := by
  by_cases hL : v = e
  · subst v
    have hh := (LDSinkTwoGapEpochSuccessor.kernelC_no_leader_creation
      hψ (C e) (C (G.ring.rightNeighbor e))).1 hv
    simpa [sinkStepC, updatePair] using hh
  · by_cases hR : v = G.ring.rightNeighbor e
    · subst v
      have hh := (LDSinkTwoGapEpochSuccessor.kernelC_no_leader_creation
        hψ (C e) (C (G.ring.rightNeighbor e))).2 hv
      simpa [sinkStepC, updatePair, hL] using hh
    · rw [sinkStepC_other hψ G C e v hL hR]
      exact hv

/-- These three shape components need no non-done precondition. -/
private theorem shape_after_step
    (hψ : ψ > 0) (G : GapFrame n) (C : Fin n → AgentState ψ)
    (e : Fin n) (hi : GapInvariant hψ G C)
    (hdel : ¬ EndpointDeleted G (sinkStepC hψ G C e)) :
    GapEndpointsPresent G (sinkStepC hψ G C e) ∧
    GapInteriorFollowers G (sinkStepC hψ G C e) ∧
    GapLabelAligned hψ G (sinkStepC hψ G C e) := by
  refine ⟨?_, ?_, ?_⟩
  · change
      (sinkStepC hψ G C e (G.pos 0)).leader = true ∧
      (sinkStepC hψ G C e (G.pos G.d)).leader = true
    constructor
    · cases he : (sinkStepC hψ G C e (G.pos 0)).leader with
      | false => exact (hdel (Or.inl he)).elim
      | true => rfl
    · cases he : (sinkStepC hψ G C e (G.pos G.d)).leader with
      | false => exact (hdel (Or.inr he)).elim
      | true => rfl
  · intro k hk hkd
    exact follower_after_step hψ G C e (G.pos k) (hi.2.1 k hk hkd)
  · intro k hk
    simpa only [nextLabel, LDSinkTwoGapEpochSuccessor.sinkStepC_label_eq]
      using hi.2.2.1 k hk

/-- The non-done branch is Kernel2. At a done pre-state, endpoint presence
makes it CleanReady. A clean post-state supplies signal coherence for free;
only the clean-pre/nonclean-post signal fact is needed from the caller. -/
private theorem gap_step_of_clean_boundary_signal
    (hψ : ψ > 0) (G : GapFrame n) (C : Fin n → AgentState ψ)
    (e : Fin n) (hi : GapInvariant hψ G C)
    (hdel : ¬ EndpointDeleted G (sinkStepC hψ G C e))
    (hboundary : CleanReady G C →
      ¬ CleanReady G (sinkStepC hψ G C e) →
      GapSignalBelowBullets G (sinkStepC hψ G C e)) :
    GapInvariant hψ G (sinkStepC hψ G C e) := by
  classical
  by_cases hd : GapDoneC G C
  · have hc : CleanReady G C := by
      rcases hd with hc | hdelPre
      · exact hc
      · exact (invariant_not_deleted hψ G C hi hdelPre).elim
    have hshape := shape_after_step hψ G C e hi hdel
    have hsignal : GapSignalBelowBullets G (sinkStepC hψ G C e) := by
      by_cases hpost : CleanReady G (sinkStepC hψ G C e)
      · exact gapSignalBelowBullets_of_cleanReady G _ hpost
      · exact hboundary hc hpost
    exact ⟨hshape.1, hshape.2.1, hshape.2.2, hsignal⟩
  · exact LDSinkTwoGapEpochSuccessor.gapInvariant_step_of_not_endpointDeleted
      hψ G C e hi hd hdel

/-- THE SINGLE UNPROVED CLOSURE FIELD.
Prove signal-below-bullets coherence when a reachable active entrance edge
leaves a clean gap and its post-gap is nonclean. The field is needed only when
the old invariant continuation theorem does not already apply: the pre-state
is outside AInvariant, or this edge is a reactivated raw failure.
This field asks for neither TagDomain, reachability closure, a rank law,
a success probability, nor an expected-cost inequality. -/
structure CleanBoundarySignalResidual
    (hψ : ψ > 0) (F : TwoGapFrame n) : Prop where
  signal : ∀ (x : AState n ψ) (e : Fin n) (y : AState n ψ) (G : GapFrame n),
    (G = F.recovery ∨ G = F.attack) →
    EntranceReach hψ F x → GapPair hψ F x →
    (¬ AInvariant hψ F x ∨ attemptStepRaw hψ F x e = .failure) →
    entranceStep hψ F x e = .active y →
    CleanReady G x.conf → ¬ CleanReady G y.conf →
    GapSignalBelowBullets G y.conf

/-- Complete gap-pair closure conditional only on the clean-boundary field. -/
theorem gapPair_step
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (hBoundary : CleanBoundarySignalResidual hψ F)
    (x : AState n ψ) (e : Fin n) (y : AState n ψ)
    (hx : EntranceReach hψ F x) (hi : GapPair hψ F x)
    (hy : entranceStep hψ F x e = .active y) : GapPair hψ F y := by
  classical
  have hd := entrance_active_data_wired hψ F x y e hy
  have hc : y.conf = attemptStepConf hψ F x e :=
    congrArg (fun z : AState n ψ => z.conf) hd.2
  have hatt : y.conf = sinkStepC hψ F.attack x.conf e :=
    hc.trans (attemptStepConf_eq_sinkStepC hψ F x e)
  have hrec : y.conf = sinkStepC hψ F.recovery x.conf e :=
    hatt.trans (twoGap_sinkStepC_eq hψ F x.conf e).symm
  have hn : ¬ NoResetSuccess F y.conf := by
    intro hs
    apply hd.1
    exact Or.inr (by simpa only [hc] using hs)
  have remaining :
      (¬ AInvariant hψ F x ∨ attemptStepRaw hψ F x e = .failure) →
      GapPair hψ F y := by
    intro hcase
    have one : ∀ G : GapFrame n,
        (G = F.recovery ∨ G = F.attack) →
        GapInvariant hψ G x.conf →
        y.conf = sinkStepC hψ G x.conf e →
        ¬ EndpointDeleted G y.conf → GapInvariant hψ G y.conf := by
      intro G hG hiG heq hdel
      rw [heq]
      apply gap_step_of_clean_boundary_signal hψ G x.conf e hiG
      · simpa only [heq] using hdel
      · intro hpre hpost
        have hpost' : ¬ CleanReady G y.conf := by
          simpa only [heq] using hpost
        have hs := hBoundary.signal x e y G hG hx hi hcase hy hpre hpost'
        simpa only [heq] using hs
    exact ⟨one F.recovery (Or.inl rfl) hi.recovery hrec
        (fun h => hn (Or.inr h)),
      one F.attack (Or.inr rfl) hi.attack hatt
        (fun h => hn (Or.inl h))⟩
  by_cases hiA : AInvariant hψ F x
  · rcases entrance_active_source_cases hψ F x y e hy with ha | hf
    · have hiY := (attemptLaws_K2 hψ F).continuation ⟨x, hiA⟩ e y ha
      exact ⟨hiY.recovery, hiY.attack⟩
    · exact remaining (Or.inr hf.1)
  · exact remaining (Or.inl hiA)

/-- The two physical gap invariants hold along the original entrance runs. -/
theorem entranceReach_gapPair
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (hBoundary : CleanBoundarySignalResidual hψ F)
    (x : AState n ψ) (hx : EntranceReach hψ F x) : GapPair hψ F x := by
  induction hx with
  | base hi => exact ⟨hi.recovery, hi.attack⟩
  | next e hprev he ih =>
      exact gapPair_step hψ F hBoundary _ e _ hprev ih he

/-! ## A proof-only phase-indexed tag, with exact erasure -/

/-- Seeking means that no live-shot certificate is currently owned. It does
not assert that every physical bullet is absent. There is no automatic rearm. -/
inductive TagMode where
  | tracking
  | seeking
  deriving DecidableEq

structure TaggedState (n ψ : Nat) where
  raw : AState n ψ
  mode : TagMode

/-- Only an actual raw failure retires a tracked certificate; seeking is sticky. -/
def modeAfter {S : Type} : TagMode → StopNode S → TagMode
  | .seeking, _ => .seeking
  | .tracking, .failure => .seeking
  | .tracking, _ => .tracking

private theorem modeAfter_tracking_iff {S : Type}
    (m : TagMode) (q : StopNode S) :
    modeAfter m q = .tracking ↔ m = .tracking ∧ q ≠ .failure := by
  cases m <;> cases q <;> simp [modeAfter]

private def pack (m : TagMode) : StopNode (AState n ψ) → StopNode (TaggedState n ψ)
  | .active x => .active ⟨x, m⟩
  | .success => .success
  | .failure => .failure

def eraseNode : StopNode (TaggedState n ψ) → StopNode (AState n ψ)
  | .active z => .active z.raw
  | .success => .success
  | .failure => .failure

private theorem erase_pack (m : TagMode) (q : StopNode (AState n ψ)) :
    eraseNode (pack m q) = q := by
  cases q <;> rfl

/-- A ghost lift of the existing entrance step, not a replacement protocol. -/
def taggedEntranceStep (hψ : ψ > 0) (F : TwoGapFrame n)
    (z : TaggedState n ψ) (e : Fin n) : StopNode (TaggedState n ψ) :=
  pack (modeAfter z.mode (attemptStepRaw hψ F z.raw e))
    (entranceStep hψ F z.raw e)

theorem erase_taggedEntranceStep
    (hψ : ψ > 0) (F : TwoGapFrame n) (z : TaggedState n ψ) (e : Fin n) :
    eraseNode (taggedEntranceStep hψ F z e) = entranceStep hψ F z.raw e := by
  exact erase_pack _ _

private theorem tagged_active_data
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (z : TaggedState n ψ) (e : Fin n) (w : TaggedState n ψ)
    (hw : taggedEntranceStep hψ F z e = .active w) :
    entranceStep hψ F z.raw e = .active w.raw ∧
      w.mode = modeAfter z.mode (attemptStepRaw hψ F z.raw e) := by
  have hr : entranceStep hψ F z.raw e = .active w.raw :=
    (erase_taggedEntranceStep hψ F z e).symm.trans (congrArg eraseNode hw)
  have hh := hw
  change pack (modeAfter z.mode (attemptStepRaw hψ F z.raw e))
    (entranceStep hψ F z.raw e) = .active w at hh
  rw [hr] at hh
  have heq : (⟨w.raw, modeAfter z.mode (attemptStepRaw hψ F z.raw e)⟩ :
      TaggedState n ψ) = w := StopNode.active.inj hh
  exact ⟨hr, (congrArg (fun t : TaggedState n ψ => t.mode) heq).symm⟩

/-- A reactivated absorption actually selects seeking in the lifted process. -/
theorem tagged_absorption_seeking
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (z : TaggedState n ψ) (e : Fin n) (w : TaggedState n ψ)
    (hw : taggedEntranceStep hψ F z e = .active w)
    (hf : attemptStepRaw hψ F z.raw e = .failure) : w.mode = .seeking := by
  have hm := (tagged_active_data hψ F z e w hw).2
  rw [hm, hf]
  cases z.mode <;> rfl

private theorem erase_stepNode
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (q : StopNode (TaggedState n ψ)) (e : Fin n) :
    eraseNode (stepNode (taggedEntranceStep hψ F) q e) =
      stepNode (entranceStep hψ F) (eraseNode q) e := by
  cases q with
  | active z => exact erase_taggedEntranceStep hψ F z e
  | success => rfl
  | failure => rfl

/-- No raw interaction, success leaf, or scheduler word is added or removed. -/
theorem tagged_successCount_eq
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (q : StopNode (TaggedState n ψ)) (T : Nat) :
    successCount (taggedEntranceStep hψ F) q T =
      successCount (entranceStep hψ F) (eraseNode q) T := by
  induction T generalizing q with
  | zero => cases q <;> rfl
  | succ T ih =>
      change
        (List.ofFn (fun e : Fin n =>
          successCount (taggedEntranceStep hψ F)
            (stepNode (taggedEntranceStep hψ F) q e) T)).sum =
        (List.ofFn (fun e : Fin n =>
          successCount (entranceStep hψ F)
            (stepNode (entranceStep hψ F) (eraseNode q) e) T)).sum
      apply ofFn_sum_eq
      intro e
      rw [ih (stepNode (taggedEntranceStep hψ F) q e), erase_stepNode]

/-! ## Tracking safety is unconditional -/

def TrackingInvariant (hψ : ψ > 0) (F : TwoGapFrame n)
    (z : TaggedState n ψ) : Prop :=
  z.mode = .tracking → AInvariant hψ F z.raw

/-- The full old invariant survives while the certificate remains tracked.
The only new entrance branch, raw failure, cannot leave tracking enabled. -/
theorem trackingInvariant_step
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (z : TaggedState n ψ) (e : Fin n) (w : TaggedState n ψ)
    (hi : TrackingInvariant hψ F z)
    (hw : taggedEntranceStep hψ F z e = .active w) :
    TrackingInvariant hψ F w := by
  intro hm
  have hd := tagged_active_data hψ F z e w hw
  have hmode : modeAfter z.mode (attemptStepRaw hψ F z.raw e) = .tracking :=
    hd.2.symm.trans hm
  have hc := (modeAfter_tracking_iff z.mode (attemptStepRaw hψ F z.raw e)).mp hmode
  have hiZ := hi hc.1
  rcases entrance_active_source_cases hψ F z.raw w.raw e hd.1 with ha | hf
  · exact (attemptLaws_K2 hψ F).continuation ⟨z.raw, hiZ⟩ e w.raw ha
  · exact (hc.2 hf.1).elim

def TaggedSeed (hψ : ψ > 0) (F : TwoGapFrame n)
    (z : TaggedState n ψ) : Prop :=
  z.mode = .tracking ∧ AInvariant hψ F z.raw

abbrev TaggedReach (hψ : ψ > 0) (F : TwoGapFrame n) :=
  ActiveReach (taggedEntranceStep hψ F) (TaggedSeed hψ F)

theorem taggedReach_trackingInvariant
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (z : TaggedState n ψ) (hz : TaggedReach hψ F z) :
    TrackingInvariant hψ F z := by
  exact ActiveReach.invariant
    (taggedEntranceStep hψ F) (TaggedSeed hψ F) (TrackingInvariant hψ F)
    (fun _ hs _ => hs.2)
    (fun u e v hi he => trackingInvariant_step hψ F u e v hi he) z hz

theorem taggedReach_erase
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (z : TaggedState n ψ) (hz : TaggedReach hψ F z) :
    EntranceReach hψ F z.raw := by
  induction hz with
  | base hs => exact ActiveReach.base hs.2
  | next e _ he ih =>
      exact ActiveReach.next e ih (tagged_active_data hψ F _ e _ he).1

/-- Every original active entrance run has a lift, starting in tracking mode.
Thus the new carrier does not discard inconvenient post-absorption runs. -/
theorem entranceReach_lift
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AState n ψ) (hx : EntranceReach hψ F x) :
    ∃ z : TaggedState n ψ, z.raw = x ∧ TaggedReach hψ F z := by
  induction hx with
  | @base x hi =>
      exact ⟨⟨x, .tracking⟩, rfl, ActiveReach.base ⟨rfl, hi⟩⟩
  | @next x y e _ he ih =>
      obtain ⟨z, hz, hzr⟩ := ih
      let w : TaggedState n ψ :=
        ⟨y, modeAfter z.mode (attemptStepRaw hψ F z.raw e)⟩
      have hr : entranceStep hψ F z.raw e = .active y := by
        simpa only [hz] using he
      have hw : taggedEntranceStep hψ F z e = .active w := by
        simp only [taggedEntranceStep, hr, pack, w]
      exact ⟨w, rfl, ActiveReach.next e hzr hw⟩

/-! ## Corrected phase-indexed invariant and its reachable closure -/

/-- Both physical gaps are always invariant. The live-shot certificate is
required only in tracking mode. Seeking is a proof mode, not a claim that the
original two-valued APhase acquired a new constructor or a new phase debt. -/
structure AInvariant' (hψ : ψ > 0) (F : TwoGapFrame n)
    (z : TaggedState n ψ) : Prop where
  recovery : GapInvariant hψ F.recovery z.raw.conf
  attack : GapInvariant hψ F.attack z.raw.conf
  tag : z.mode = .tracking → TagDomain F z.raw

/-- On tracking states the corrected invariant is exactly the original one. -/
theorem corrected_tracking_iff
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : AState n ψ) :
    AInvariant' hψ F ⟨x, .tracking⟩ ↔ AInvariant hψ F x := by
  constructor
  · intro hi
    exact ⟨hi.recovery, hi.attack, hi.tag rfl⟩
  · intro hi
    exact ⟨hi.recovery, hi.attack, fun _ => hi.tag⟩

/-- On seeking states no live tag or non-done attack premise is invented. -/
theorem corrected_seeking_iff
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : AState n ψ) :
    AInvariant' hψ F ⟨x, .seeking⟩ ↔ GapPair hψ F x := by
  constructor
  · intro hi
    exact ⟨hi.recovery, hi.attack⟩
  · intro hi
    refine ⟨hi.recovery, hi.attack, ?_⟩
    intro hm
    cases hm

/-- One-step closure on the actual reachable domain. -/
theorem correctedInvariant_step
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (hBoundary : CleanBoundarySignalResidual hψ F)
    (z : TaggedState n ψ) (e : Fin n) (w : TaggedState n ψ)
    (hz : EntranceReach hψ F z.raw)
    (hi : AInvariant' hψ F z)
    (hw : taggedEntranceStep hψ F z e = .active w) : AInvariant' hψ F w := by
  have hd := tagged_active_data hψ F z e w hw
  have hg := gapPair_step hψ F hBoundary z.raw e w.raw hz
    ⟨hi.recovery, hi.attack⟩ hd.1
  have ht : TrackingInvariant hψ F z := by
    intro hm
    exact ⟨hi.recovery, hi.attack, hi.tag hm⟩
  refine ⟨hg.recovery, hg.attack, ?_⟩
  intro hm
  exact (trackingInvariant_step hψ F z e w ht hw hm).tag

theorem taggedReach_invariant'
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (hBoundary : CleanBoundarySignalResidual hψ F)
    (z : TaggedState n ψ) (hz : TaggedReach hψ F z) : AInvariant' hψ F z := by
  have hg := entranceReach_gapPair hψ F hBoundary z.raw
    (taggedReach_erase hψ F z hz)
  have ht := taggedReach_trackingInvariant hψ F z hz
  exact ⟨hg.recovery, hg.attack, fun hm => (ht hm).tag⟩

/-- Corrected closure for every original entrance run, including absorptions.
The prime is intentional: this does not assert the false old tag obligation. -/
theorem entranceReach_invariant'
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (hBoundary : CleanBoundarySignalResidual hψ F)
    (x : AState n ψ) (hx : EntranceReach hψ F x) :
    ∃ z : TaggedState n ψ,
      z.raw = x ∧ TaggedReach hψ F z ∧ AInvariant' hψ F z := by
  obtain ⟨z, hz, hzr⟩ := entranceReach_lift hψ F x hx
  exact ⟨z, hz, hzr, taggedReach_invariant' hψ F hBoundary z hzr⟩

/-- The old numerical upper bound uses only the two gap invariants.
This proves boundedness, not nonincrease or strict decrease in seeking mode. -/
theorem corrected_rank_le
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (z : TaggedState n ψ) (hi : AInvariant' hψ F z) :
    LDSinkTwoGapNoResetKernel.R F z.raw ≤
      16 * (F.recovery.d + F.attack.d) := by
  exact R_le hψ F z.raw hi.recovery hi.attack

#print axioms absorption_post_parked
#print axioms absorption_parked_iff_fails
#print axioms absorption_post_not_tag
#print axioms no_live_not_uniqueLiveShot
#print axioms done_not_tag
#print axioms cleared_absorption_is_entrance_active
#print axioms no_old_closure_of_cleared_absorption
#print axioms gapPair_step
#print axioms entranceReach_gapPair
#print axioms erase_taggedEntranceStep
#print axioms tagged_absorption_seeking
#print axioms tagged_successCount_eq
#print axioms trackingInvariant_step
#print axioms taggedReach_trackingInvariant
#print axioms taggedReach_erase
#print axioms entranceReach_lift
#print axioms corrected_tracking_iff
#print axioms corrected_seeking_iff
#print axioms correctedInvariant_step
#print axioms taggedReach_invariant'
#print axioms entranceReach_invariant'
#print axioms corrected_rank_le

end

end LDSinkTwoGapReachInvariant
