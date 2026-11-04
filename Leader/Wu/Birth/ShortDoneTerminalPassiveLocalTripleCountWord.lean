import Leader.Wu.Birth.ShortDoneTerminalPassiveLocalTripleCount
import Leader.Core.ControlledSchedulerMass

namespace BirthShortDoneTerminalPassiveLocal3CountWord

open FiniteUniformStoppingTree
open ControlledSchedulerMass
open BirthShortDoneTerminalPassiveLocal3
open BirthShortDoneTerminalPassiveLocal3Count

set_option autoImplicit false

variable {n : Nat}

/-- While still waiting for the first successful port, `p1` and every
non-designated outside scheduler letter are neutral.  The only forbidden
letters are the phase-changing `p0` itself and the two crossing/failure ports. -/
def Phase0Neutral (hn : 4 <= n) (e : Fin n) : Prop :=
  e ≠ p0 hn ∧ e ≠ p2 hn ∧ e ≠ leftCross hn

/-- After `p0`, repeated `p0` and all outside scheduler letters are neutral.
The first `p1` succeeds, while either crossing port fails. -/
def Phase1Neutral (hn : 4 <= n) (e : Fin n) : Prop :=
  e ≠ p1 hn ∧ e ≠ p2 hn ∧ e ≠ leftCross hn

/-- Exact successful-prefix shape.  The displayed `p1` is the first success:
all preceding symbols keep the matcher active in the indicated phase.  The
suffix is intentionally unrestricted because stopped-tree success absorbs it. -/
def EarliestTwoCrossSuccess (hn : 4 <= n) (w : List (Fin n)) : Prop :=
  ∃ pre mid suffix,
    w = pre ++ (p0 hn :: (mid ++ (p1 hn :: suffix))) ∧
      (∀ e, e ∈ pre → Phase0Neutral hn e) ∧
      (∀ e, e ∈ mid → Phase1Neutral hn e)

/-! Only the public matcher is unfolded below.  No private `ports0`/`ports1`
counting helper is referenced. -/

private theorem step0_hit (hn : 4 <= n) :
    twoCrossStep hn false (p0 hn) = StopNode.active true := by
  change (if p0 hn = p0 hn then StopNode.active true
    else if p0 hn = p2 hn then (StopNode.failure : StopNode Bool)
    else if p0 hn = leftCross hn then (StopNode.failure : StopNode Bool)
    else StopNode.active false) = StopNode.active true
  simp

private theorem step1_hit (hn : 4 <= n) :
    twoCrossStep hn true (p1 hn) = (StopNode.success : StopNode Bool) := by
  change (if p1 hn = p1 hn then (StopNode.success : StopNode Bool)
    else if p1 hn = p2 hn then (StopNode.failure : StopNode Bool)
    else if p1 hn = leftCross hn then (StopNode.failure : StopNode Bool)
    else StopNode.active true) = (StopNode.success : StopNode Bool)
  simp

private theorem step0_neutral (hn : 4 <= n) {e : Fin n}
    (h0 : e ≠ p0 hn) (h2 : e ≠ p2 hn) (hc : e ≠ leftCross hn) :
    twoCrossStep hn false e = StopNode.active false := by
  change (if e = p0 hn then StopNode.active true
    else if e = p2 hn then (StopNode.failure : StopNode Bool)
    else if e = leftCross hn then (StopNode.failure : StopNode Bool)
    else StopNode.active false) = StopNode.active false
  rw [if_neg h0, if_neg h2, if_neg hc]

private theorem step1_neutral (hn : 4 <= n) {e : Fin n}
    (h1 : e ≠ p1 hn) (h2 : e ≠ p2 hn) (hc : e ≠ leftCross hn) :
    twoCrossStep hn true e = StopNode.active true := by
  change (if e = p1 hn then (StopNode.success : StopNode Bool)
    else if e = p2 hn then (StopNode.failure : StopNode Bool)
    else if e = leftCross hn then (StopNode.failure : StopNode Bool)
    else StopNode.active true) = StopNode.active true
  rw [if_neg h1, if_neg h2, if_neg hc]

private theorem runWord_append_stopped {S : Type} {m : Nat}
    (step : S → Fin m → StopNode S) (x : StopNode S)
    (pre suffix : List (Fin m)) :
    ControlledSchedulerMass.runWord step x (pre ++ suffix) =
      ControlledSchedulerMass.runWord step
        (ControlledSchedulerMass.runWord step x pre) suffix := by
  induction pre generalizing x with
  | nil => rfl
  | cons e pre ih =>
      simp only [List.cons_append, ControlledSchedulerMass.runWord]
      exact ih (stepNode step x e)

private theorem run_phase0_neutral (hn : 4 <= n) (pre : List (Fin n))
    (hpre : ∀ e, e ∈ pre → Phase0Neutral hn e) :
    ControlledSchedulerMass.runWord (twoCrossStep hn) (StopNode.active false) pre =
      StopNode.active false := by
  induction pre with
  | nil => rfl
  | cons e es ih =>
      have he := hpre e (by simp)
      have htail : ∀ x, x ∈ es → Phase0Neutral hn x := by
        intro x hx
        exact hpre x (by simp [hx])
      simp only [ControlledSchedulerMass.runWord, stepNode]
      rw [step0_neutral hn he.1 he.2.1 he.2.2]
      exact ih htail

private theorem run_phase1_neutral (hn : 4 <= n) (mid : List (Fin n))
    (hmid : ∀ e, e ∈ mid → Phase1Neutral hn e) :
    ControlledSchedulerMass.runWord (twoCrossStep hn) (StopNode.active true) mid =
      StopNode.active true := by
  induction mid with
  | nil => rfl
  | cons e es ih =>
      have he := hmid e (by simp)
      have htail : ∀ x, x ∈ es → Phase1Neutral hn x := by
        intro x hx
        exact hmid x (by simp [hx])
      simp only [ControlledSchedulerMass.runWord, stepNode]
      rw [step1_neutral hn he.1 he.2.1 he.2.2]
      exact ih htail

/-- If phase one eventually succeeds, there is a first `p1` before either
crossing port.  Everything after that `p1` is unrestricted terminal padding. -/
private theorem phase1_success_prefix (hn : 4 <= n) (es : List (Fin n))
    (hs : ControlledSchedulerMass.runWord (twoCrossStep hn)
      (StopNode.active true) es = (StopNode.success : StopNode Bool)) :
    ∃ mid suffix,
      es = mid ++ (p1 hn :: suffix) ∧
        ∀ e, e ∈ mid → Phase1Neutral hn e := by
  induction es with
  | nil =>
      have hf : False := by
        simpa [ControlledSchedulerMass.runWord] using hs
      exact hf.elim
  | cons e es ih =>
      simp only [ControlledSchedulerMass.runWord, stepNode] at hs
      by_cases h1 : e = p1 hn
      · subst e
        exact ⟨[], es, by simp, by simp⟩
      · by_cases h2 : e = p2 hn
        · have hstep : twoCrossStep hn true e = (StopNode.failure : StopNode Bool) := by
            change (if e = p1 hn then (StopNode.success : StopNode Bool)
              else if e = p2 hn then (StopNode.failure : StopNode Bool)
              else if e = leftCross hn then (StopNode.failure : StopNode Bool)
              else StopNode.active true) = (StopNode.failure : StopNode Bool)
            rw [if_neg h1, if_pos h2]
          rw [hstep] at hs
          have hf : False := by simpa using hs
          exact hf.elim
        · by_cases hc : e = leftCross hn
          · have hstep : twoCrossStep hn true e = (StopNode.failure : StopNode Bool) := by
              change (if e = p1 hn then (StopNode.success : StopNode Bool)
                else if e = p2 hn then (StopNode.failure : StopNode Bool)
                else if e = leftCross hn then (StopNode.failure : StopNode Bool)
                else StopNode.active true) = (StopNode.failure : StopNode Bool)
              rw [if_neg h1, if_neg h2, if_pos hc]
            rw [hstep] at hs
            have hf : False := by simpa using hs
            exact hf.elim
          · rw [step1_neutral hn h1 h2 hc] at hs
            obtain ⟨mid, suffix, heq, hmid⟩ := ih hs
            refine ⟨e :: mid, suffix, ?_, ?_⟩
            · simp [heq]
            · intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · exact ⟨h1, h2, hc⟩
              · exact hmid x hx

/-- Success from phase zero has an exact earliest successful prefix:
first `p0`, then first `p1`, with neither crossing port appearing before that
success.  Repeats of the phase-neutral designated port are allowed. -/
private theorem phase0_success_prefix (hn : 4 <= n) (es : List (Fin n))
    (hs : ControlledSchedulerMass.runWord (twoCrossStep hn)
      (StopNode.active false) es = (StopNode.success : StopNode Bool)) :
    EarliestTwoCrossSuccess hn es := by
  unfold EarliestTwoCrossSuccess
  induction es with
  | nil =>
      have hf : False := by
        simpa [ControlledSchedulerMass.runWord] using hs
      exact hf.elim
  | cons e es ih =>
      simp only [ControlledSchedulerMass.runWord, stepNode] at hs
      by_cases h0 : e = p0 hn
      · subst e
        rw [step0_hit hn] at hs
        obtain ⟨mid, suffix, heq, hmid⟩ :=
          phase1_success_prefix hn es hs
        refine ⟨[], mid, suffix, ?_, ?_, hmid⟩
        · simp [heq]
        · simp
      · by_cases h2 : e = p2 hn
        · have hstep : twoCrossStep hn false e = (StopNode.failure : StopNode Bool) := by
            change (if e = p0 hn then StopNode.active true
              else if e = p2 hn then (StopNode.failure : StopNode Bool)
              else if e = leftCross hn then (StopNode.failure : StopNode Bool)
              else StopNode.active false) = (StopNode.failure : StopNode Bool)
            rw [if_neg h0, if_pos h2]
          rw [hstep] at hs
          have hf : False := by simpa using hs
          exact hf.elim
        · by_cases hc : e = leftCross hn
          · have hstep : twoCrossStep hn false e = (StopNode.failure : StopNode Bool) := by
              change (if e = p0 hn then StopNode.active true
                else if e = p2 hn then (StopNode.failure : StopNode Bool)
                else if e = leftCross hn then (StopNode.failure : StopNode Bool)
                else StopNode.active false) = (StopNode.failure : StopNode Bool)
              rw [if_neg h0, if_neg h2, if_pos hc]
            rw [hstep] at hs
            have hf : False := by simpa using hs
            exact hf.elim
          · rw [step0_neutral hn h0 h2 hc] at hs
            obtain ⟨pre, mid, suffix, heq, hpre, hmid⟩ := ih hs
            refine ⟨e :: pre, mid, suffix, ?_, ?_, hmid⟩
            · simp [heq]
            · intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · exact ⟨h0, h2, hc⟩
              · exact hpre x hx

private theorem success_of_earliest_prefix (hn : 4 <= n)
    {w : List (Fin n)} (h : EarliestTwoCrossSuccess hn w) :
    ControlledSchedulerMass.runWord (twoCrossStep hn)
      (StopNode.active false) w = (StopNode.success : StopNode Bool) := by
  unfold EarliestTwoCrossSuccess at h
  rcases h with ⟨pre, mid, suffix, rfl, hpre, hmid⟩
  rw [runWord_append_stopped]
  rw [run_phase0_neutral hn pre hpre]
  simp only [ControlledSchedulerMass.runWord, stepNode]
  rw [step0_hit hn]
  rw [runWord_append_stopped]
  rw [run_phase1_neutral hn mid hmid]
  simp only [ControlledSchedulerMass.runWord, stepNode]
  rw [step1_hit hn]
  exact ControlledSchedulerMass.runWord_success _ suffix

/-- Exact semantic audit of the public two-cross matcher.  This is an iff,
not merely a sufficient pattern.  Success means that some earliest prefix has
seen `p0` and then `p1` before either crossing edge; the remaining raw suffix
is arbitrary. -/
theorem runWord_success_iff_earliest_two_cross
    (hn : 4 <= n) (w : List (Fin n)) :
    ControlledSchedulerMass.runWord (twoCrossStep hn)
        (StopNode.active false) w = (StopNode.success : StopNode Bool) ↔
      EarliestTwoCrossSuccess hn w := by
  constructor
  · exact phase0_success_prefix hn w
  · exact success_of_earliest_prefix hn

/-- The prefix immediately before its final `p1` is still active, and adding
that `p1` makes it successful.  Since success/failure are absorbing, this also
certifies that the displayed prefix is genuinely the earliest successful one. -/
theorem earliest_two_cross_cut
    (hn : 4 <= n) (pre mid : List (Fin n))
    (hpre : ∀ e, e ∈ pre → Phase0Neutral hn e)
    (hmid : ∀ e, e ∈ mid → Phase1Neutral hn e) :
    ControlledSchedulerMass.runWord (twoCrossStep hn) (StopNode.active false)
        (pre ++ (p0 hn :: mid)) = StopNode.active true ∧
      ControlledSchedulerMass.runWord (twoCrossStep hn) (StopNode.active false)
        (pre ++ (p0 hn :: (mid ++ [p1 hn]))) = (StopNode.success : StopNode Bool) := by
  constructor
  · rw [runWord_append_stopped]
    rw [run_phase0_neutral hn pre hpre]
    simp only [ControlledSchedulerMass.runWord, stepNode]
    rw [step0_hit hn]
    exact run_phase1_neutral hn mid hmid
  · apply success_of_earliest_prefix hn
    unfold EarliestTwoCrossSuccess
    exact ⟨pre, mid, [], by simp, hpre, hmid⟩

/-! ## Closed `n = 4` witnesses -/

def n4Bound : 4 <= 4 := by decide

/-- Both crossing letters occur only after success. -/
def n4PostSuccessCrossWord : List (Fin 4) :=
  [p0 n4Bound, p1 n4Bound, p2 n4Bound, leftCross n4Bound]

theorem n4_post_success_cross_shape :
    EarliestTwoCrossSuccess n4Bound n4PostSuccessCrossWord := by
  unfold EarliestTwoCrossSuccess n4PostSuccessCrossWord
  refine ⟨[], [], [p2 n4Bound, leftCross n4Bound], ?_, ?_, ?_⟩
  · rfl
  · simp
  · simp

/-- The post-success `p2,leftCross` suffix is absorbed: this word succeeds. -/
theorem n4_post_success_cross_success :
    ControlledSchedulerMass.runWord (twoCrossStep n4Bound)
      (StopNode.active false) n4PostSuccessCrossWord = (StopNode.success : StopNode Bool) :=
  (runWord_success_iff_earliest_two_cross n4Bound n4PostSuccessCrossWord).2
    n4_post_success_cross_shape

/-- A crossing before the required `p1` is terminal failure. -/
def n4PreSuccessCrossWord : List (Fin 4) :=
  [p0 n4Bound, p2 n4Bound, p1 n4Bound]

private theorem n4_p2_ne_p1 : p2 n4Bound ≠ p1 n4Bound := by
  apply Fin.ne_of_val_ne
  simp [p1, p2]

private theorem n4_step1_p2 :
    twoCrossStep n4Bound true (p2 n4Bound) = (StopNode.failure : StopNode Bool) := by
  change (if p2 n4Bound = p1 n4Bound then (StopNode.success : StopNode Bool)
    else if p2 n4Bound = p2 n4Bound then (StopNode.failure : StopNode Bool)
    else if p2 n4Bound = leftCross n4Bound then (StopNode.failure : StopNode Bool)
    else StopNode.active true) = (StopNode.failure : StopNode Bool)
  simp [n4_p2_ne_p1]

theorem n4_cross_before_success_failure :
    ControlledSchedulerMass.runWord (twoCrossStep n4Bound)
      (StopNode.active false) n4PreSuccessCrossWord = (StopNode.failure : StopNode Bool) := by
  unfold n4PreSuccessCrossWord
  change ControlledSchedulerMass.runWord (twoCrossStep n4Bound)
      (twoCrossStep n4Bound false (p0 n4Bound))
      [p2 n4Bound, p1 n4Bound] = (StopNode.failure : StopNode Bool)
  rw [step0_hit n4Bound]
  change ControlledSchedulerMass.runWord (twoCrossStep n4Bound)
      (twoCrossStep n4Bound true (p2 n4Bound))
      [p1 n4Bound] = (StopNode.failure : StopNode Bool)
  rw [n4_step1_p2]
  exact ControlledSchedulerMass.runWord_failure _ _

#print axioms BirthShortDoneTerminalPassiveLocal3CountWord.runWord_success_iff_earliest_two_cross
#print axioms BirthShortDoneTerminalPassiveLocal3CountWord.earliest_two_cross_cut
#print axioms BirthShortDoneTerminalPassiveLocal3CountWord.n4_post_success_cross_success
#print axioms BirthShortDoneTerminalPassiveLocal3CountWord.n4_cross_before_success_failure

end BirthShortDoneTerminalPassiveLocal3CountWord
