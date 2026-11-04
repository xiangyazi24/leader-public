import Leader.AAFJ.MultiBarrier.SixHitContactBlock
import Leader.AAFJ.MultiBarrier.GappedThreeHit
import Leader.AAFJ.MultiBarrier.GappedSixHit
import Leader.AAFJ.MultiBarrier.NonbarrierInterleaving

set_option autoImplicit false

namespace AAFJPK.OriginalStagePhysicalPrefix

open BarrierAlgebra
open OriginalNonbarrierWord

abbrev Configuration (n k : Nat) := Fin n → State k

/-- Terminal/nonterminal result of scanning a raw physical scheduler word.

* `completed`: the requested number of good charged stages has been reached;
  no further raw edge is consumed.
* `exhausted`: the physical word ended before completion and without a
  terminal drop/failure.
* `dropped`: this physical interaction strictly lowered barrier count.
* `failed`: this physical interaction was charged but was not the prescribed
  good edge for the current stage.

The protocol-specific theorem must later rule out `completed` for the
six-stage AAFJ payload by proving that a strict drop occurs by the sixth good
service. -/
inductive StageOutcome (n k : Nat) where
  | completed (stage : Nat) (C : Configuration n k)
  | exhausted (stage : Nat) (C : Configuration n k)
  | dropped (stage : Nat)
      (pre post : Configuration n k) (hit : Fin n)
  | failed (stage : Nat)
      (pre post : Configuration n k) (hit : Fin n)

/-- Scan a raw physical word.

Priority at each active stage:
1. if all requested good stages are already complete, stop;
2. if the current edge is nonbarrier, execute it and stay at the same stage;
3. if it is charged and the physical step strictly drops support, succeed;
4. if it is charged, does not drop, and equals the prescribed good edge,
   execute it and advance the stage;
5. otherwise the charged non-good edge is a failure.

Thus a nonbarrier occurrence of the numerical edge `good stage` does *not*
advance the service counter. Stage advancement means an actual charged good
hit. -/
def stageClassify
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (stages : Nat) (good : Nat → Fin n) :
    Nat → Configuration n k → List (Fin n) → StageOutcome n k
  | stage, C, [] =>
      if stages ≤ stage then
        .completed stage C
      else
        .exhausted stage C
  | stage, C, hit :: rest =>
      if stages ≤ stage then
        .completed stage C
      else
        let D := (protocol k hk).step ring C hit
        if hbar : IsBarrier hk (C hit) (C (ring.rightNeighbor hit)) then
          if hdrop :
              barrierCount hk ring (labelsOf D) <
                barrierCount hk ring (labelsOf C) then
            .dropped stage C D hit
          else if hit = good stage then
            stageClassify hk ring stages good (stage + 1) D rest
          else
            .failed stage C D hit
        else
          stageClassify hk ring stages good stage D rest

/-- Proof relation exposing exactly why the executable classifier took each
branch. In particular, every `nonbarrier` constructor is an actual
current-prestate nonbarrier interaction, and terminal constructors do not
recurse into the remaining physical suffix. -/
inductive StageClassified
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (stages : Nat) (good : Nat → Fin n) :
    Nat → Configuration n k → List (Fin n) → StageOutcome n k → Prop
  | completed
      {stage : Nat} {C : Configuration n k} {word : List (Fin n)}
      (hdone : stages ≤ stage) :
      StageClassified hk ring stages good stage C word
        (.completed stage C)
  | exhausted
      {stage : Nat} {C : Configuration n k}
      (hactive : ¬ stages ≤ stage) :
      StageClassified hk ring stages good stage C []
        (.exhausted stage C)
  | dropped
      {stage : Nat} {C : Configuration n k}
      {hit : Fin n} {rest : List (Fin n)}
      (hactive : ¬ stages ≤ stage)
      (hbar : IsBarrier hk (C hit) (C (ring.rightNeighbor hit)))
      (hdrop :
        barrierCount hk ring
            (labelsOf ((protocol k hk).step ring C hit)) <
          barrierCount hk ring (labelsOf C)) :
      StageClassified hk ring stages good stage C (hit :: rest)
        (.dropped stage C ((protocol k hk).step ring C hit) hit)
  | advanced
      {stage : Nat} {C : Configuration n k}
      {hit : Fin n} {rest : List (Fin n)} {out : StageOutcome n k}
      (hactive : ¬ stages ≤ stage)
      (hbar : IsBarrier hk (C hit) (C (ring.rightNeighbor hit)))
      (hnodrop :
        ¬ barrierCount hk ring
              (labelsOf ((protocol k hk).step ring C hit)) <
            barrierCount hk ring (labelsOf C))
      (hgood : hit = good stage)
      (htail :
        StageClassified hk ring stages good (stage + 1)
          ((protocol k hk).step ring C hit) rest out) :
      StageClassified hk ring stages good stage C (hit :: rest) out
  | failed
      {stage : Nat} {C : Configuration n k}
      {hit : Fin n} {rest : List (Fin n)}
      (hactive : ¬ stages ≤ stage)
      (hbar : IsBarrier hk (C hit) (C (ring.rightNeighbor hit)))
      (hnodrop :
        ¬ barrierCount hk ring
              (labelsOf ((protocol k hk).step ring C hit)) <
            barrierCount hk ring (labelsOf C))
      (hbad : hit ≠ good stage) :
      StageClassified hk ring stages good stage C (hit :: rest)
        (.failed stage C ((protocol k hk).step ring C hit) hit)
  | nonbarrier
      {stage : Nat} {C : Configuration n k}
      {hit : Fin n} {rest : List (Fin n)} {out : StageOutcome n k}
      (hactive : ¬ stages ≤ stage)
      (hnb : ¬ IsBarrier hk (C hit) (C (ring.rightNeighbor hit)))
      (htail :
        StageClassified hk ring stages good stage
          ((protocol k hk).step ring C hit) rest out) :
      StageClassified hk ring stages good stage C (hit :: rest) out

/-- The executable classifier is completely justified by the structural
relation. No stage payload invariant or six-hit semantic theorem is assumed. -/
theorem stageClassify_sound
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (stages : Nat) (good : Nat → Fin n)
    (stage : Nat) (C : Configuration n k) (word : List (Fin n)) :
    StageClassified hk ring stages good stage C word
      (stageClassify hk ring stages good stage C word) := by
  induction word generalizing stage C with
  | nil =>
      by_cases hdone : stages ≤ stage
      · simpa [stageClassify, hdone] using
          (StageClassified.completed
            (hk := hk) (ring := ring) (stages := stages) (good := good)
            (stage := stage) (C := C) (word := []) hdone)
      · simpa [stageClassify, hdone] using
          (StageClassified.exhausted
            (hk := hk) (ring := ring) (stages := stages) (good := good)
            (stage := stage) (C := C) hdone)
  | cons hit rest ih =>
      by_cases hdone : stages ≤ stage
      · simpa [stageClassify, hdone] using
          (StageClassified.completed
            (hk := hk) (ring := ring) (stages := stages) (good := good)
            (stage := stage) (C := C) (word := hit :: rest) hdone)
      · let D : Configuration n k := (protocol k hk).step ring C hit
        by_cases hbar :
            IsBarrier hk (C hit) (C (ring.rightNeighbor hit))
        · by_cases hdrop :
            barrierCount hk ring (labelsOf D) <
              barrierCount hk ring (labelsOf C)
          · have hdrop' :
                barrierCount hk ring
                    (labelsOf ((protocol k hk).step ring C hit)) <
                  barrierCount hk ring (labelsOf C) := by
              simpa [D] using hdrop
            simpa [stageClassify, hdone, D, hbar, hdrop] using
              (StageClassified.dropped
                (hk := hk) (ring := ring) (stages := stages) (good := good)
                (stage := stage) (C := C) (hit := hit) (rest := rest)
                hdone hbar hdrop')
          · by_cases hgood : hit = good stage
            · have htail :=
                ih (stage := stage + 1) (C := D)
              have hnodrop' :
                  ¬ barrierCount hk ring
                        (labelsOf ((protocol k hk).step ring C hit)) <
                      barrierCount hk ring (labelsOf C) := by
                simpa [D] using hdrop
              have htail' :
                  StageClassified hk ring stages good (stage + 1)
                    ((protocol k hk).step ring C hit) rest
                    (stageClassify hk ring stages good (stage + 1)
                      D rest) := by
                simpa [D] using htail
              subst hit
              simpa [stageClassify, hdone, D, hbar, hdrop] using
                (StageClassified.advanced
                  (hk := hk) (ring := ring) (stages := stages)
                  (good := good) (stage := stage) (C := C)
                  (hit := good stage) (rest := rest)
                  hdone hbar hnodrop' rfl htail')
            · have hnodrop' :
                  ¬ barrierCount hk ring
                        (labelsOf ((protocol k hk).step ring C hit)) <
                      barrierCount hk ring (labelsOf C) := by
                simpa [D] using hdrop
              simpa [stageClassify, hdone, D, hbar, hdrop, hgood] using
                (StageClassified.failed
                  (hk := hk) (ring := ring) (stages := stages)
                  (good := good) (stage := stage) (C := C)
                  (hit := hit) (rest := rest)
                  hdone hbar hnodrop' hgood)
        · have htail :=
            ih (stage := stage) (C := D)
          have htail' :
              StageClassified hk ring stages good stage
                ((protocol k hk).step ring C hit) rest
                (stageClassify hk ring stages good stage D rest) := by
            simpa [D] using htail
          simpa [stageClassify, hdone, D, hbar] using
            (StageClassified.nonbarrier
              (hk := hk) (ring := ring) (stages := stages) (good := good)
              (stage := stage) (C := C) (hit := hit) (rest := rest)
              hdone hbar htail')

/-- One raw current-nonbarrier physical interaction has exactly the basic
frames needed by stage payload proofs: labels and barrier count are unchanged,
and every phase bit is unchanged. -/
theorem current_nonbarrier_step_frame
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Configuration n k) (hit : Fin n)
    (hnb : ¬ IsBarrier hk (C hit) (C (ring.rightNeighbor hit))) :
    let D := (protocol k hk).step ring C hit
    labelsOf D = labelsOf C ∧
      barrierCount hk ring (labelsOf D) =
        barrierCount hk ring (labelsOf C) ∧
      ∀ i : Fin n, (D i).phase = (C i).phase := by
  dsimp
  have hnot : ¬ AdvanceReady hk ring C hit :=
    not_advanceReady_of_nonbarrier hk ring C hit hnb
  have hlabels :
      labelsOf ((protocol k hk).step ring C hit) = labelsOf C :=
    labelsOf_step_eq_self_of_not_ready hk ring C hit hnot
  refine ⟨hlabels, ?_, ?_⟩
  · rw [hlabels]
  · exact
      AAFJPK.OriginalNonbarrierFrame.nonbarrier_step_preserves_phase
        hk ring C hit hnb

/-- Under exact support {good, other}, every raw edge outside those two tagged
edges is a current nonbarrier. This is the key correction to the old generic
Prefix classifier. -/
theorem outside_exact_two_is_current_nonbarrier
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Configuration n k) (good other hit : Fin n)
    (hsupport : ExactTwoBarrierSupport hk ring C good other)
    (hgood : hit ≠ good) (hother : hit ≠ other) :
    ¬ IsBarrier hk (C hit) (C (ring.rightNeighbor hit)) := by
  intro hbar
  have hb : BarrierAt hk ring (labelsOf C) hit :=
    (barrierAt_labelsOf_iff hk ring C hit).2 hbar
  rcases (hsupport.2 hit).1 hb with hg | ho
  · exact hgood hg
  · exact hother ho

/-- Under exact support {good, other}, a charged non-good edge is exactly the
unique competitor. The generic classifier itself does not assume this support
invariant; protocol stage payload producers supply it. -/
theorem charged_non_good_eq_other_of_exact_two
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Configuration n k) (good other hit : Fin n)
    (hsupport : ExactTwoBarrierSupport hk ring C good other)
    (hbar : IsBarrier hk (C hit) (C (ring.rightNeighbor hit)))
    (hbad : hit ≠ good) :
    hit = other := by
  have hb : BarrierAt hk ring (labelsOf C) hit :=
    (barrierAt_labelsOf_iff hk ring C hit).2 hbar
  rcases (hsupport.2 hit).1 hb with hg | ho
  · exact (hbad hg).elim
  · exact ho

/-- The six prescribed good service edges [a,b,a,b,c,b].
Values beyond stage 5 are irrelevant because the six-stage classifier stops
before consuming another physical edge. -/
def goodSixEdge {n : Nat} (a b c : Fin n) : Nat → Fin n
  | 0 => a
  | 1 => b
  | 2 => a
  | 3 => b
  | 4 => c
  | 5 => b
  | _ => b

def classifyGoodSix
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Configuration n k) (a b c : Fin n)
    (word : List (Fin n)) : StageOutcome n k :=
  stageClassify hk ring 6 (goodSixEdge a b c) 0 C word

/-- Typed failure event for the physical six-stage scanner.
Its terminal constructor certifies a current charged hit unequal to the
current stage's prescribed good edge. With the separate exact-two stage
payload invariant, `charged_non_good_eq_other_of_exact_two` identifies it
with the unique competitor. -/
def NoGoodPrefixFailure
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Configuration n k) (a b c : Fin n)
    (word : List (Fin n)) : Prop :=
  ∃ stage pre post hit,
    StageClassified hk ring 6 (goodSixEdge a b c)
      0 C word (.failed stage pre post hit)

/-- Soundness of the concrete [a,b,a,b,c,b] physical-word classifier.
This proves only the generic scheduler-word classification layer. -/
theorem classifyGoodSix_sound
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Configuration n k) (a b c : Fin n)
    (word : List (Fin n)) :
    StageClassified hk ring 6 (goodSixEdge a b c)
      0 C word (classifyGoodSix hk ring C a b c word) := by
  simpa [classifyGoodSix] using
    stageClassify_sound hk ring 6 (goodSixEdge a b c) 0 C word

#check stageClassify_sound
#check current_nonbarrier_step_frame
#check outside_exact_two_is_current_nonbarrier
#check charged_non_good_eq_other_of_exact_two
#check classifyGoodSix_sound

#print axioms stageClassify_sound
#print axioms current_nonbarrier_step_frame
#print axioms outside_exact_two_is_current_nonbarrier
#print axioms charged_non_good_eq_other_of_exact_two
#print axioms classifyGoodSix_sound

end AAFJPK.OriginalStagePhysicalPrefix

namespace AAFJPK.OriginalPhysicalTraceAdapter

open BarrierAlgebra
open OriginalNonbarrierWord

abbrev Configuration (n k : Nat) := Fin n → State k

/-- A raw word split into a gap followed by a suffix executes the suffix from
    the exact endpoint of the gap. -/
theorem rawRun_append_trace
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Configuration n k) (u v : List (Fin n)) :
    rawRun hk ring C (u ++ v) =
      rawRun hk ring (rawRun hk ring C u) v := by
  induction u generalizing C with
  | nil => rfl
  | cons e es ih =>
      change rawRun hk ring
          ((protocol k hk).step ring C e) (es ++ v) =
        rawRun hk ring
          (rawRun hk ring ((protocol k hk).step ring C e) es) v
      exact ih ((protocol k hk).step ring C e)

/-- The same split at the proof level.  The suffix starts at the actual
    post-gap configuration, so this is the invariant used by the physical
    trace adapter. -/
theorem currentNonbarrierWord_append_iff_trace
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Configuration n k) (u v : List (Fin n)) :
    CurrentNonbarrierWord hk ring C (u ++ v) ↔
      CurrentNonbarrierWord hk ring C u ∧
        CurrentNonbarrierWord hk ring (rawRun hk ring C u) v := by
  induction u generalizing C with
  | nil => simp [CurrentNonbarrierWord, rawRun]
  | cons e es ih =>
      change
        (¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) ∧
          CurrentNonbarrierWord hk ring
            ((protocol k hk).step ring C e) (es ++ v)) ↔
        (¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) ∧
          CurrentNonbarrierWord hk ring
            ((protocol k hk).step ring C e) es) ∧
          CurrentNonbarrierWord hk ring
            (rawRun hk ring
              ((protocol k hk).step ring C e) es) v
      constructor
      · rintro ⟨he, htail⟩
        have hsplit :=
          (ih ((protocol k hk).step ring C e)).1 htail
        exact ⟨⟨he, hsplit.1⟩, hsplit.2⟩
      · rintro ⟨⟨he, hu⟩, hv⟩
        exact ⟨he, (ih ((protocol k hk).step ring C e)).2 ⟨hu, hv⟩⟩

/-- One newly checked outside-support draw can be appended to a gap. -/
theorem currentNonbarrierWord_append_singleton_trace
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Configuration n k) (u : List (Fin n)) (e : Fin n)
    (hu : CurrentNonbarrierWord hk ring C u)
    (he : ¬ IsBarrier hk
      ((rawRun hk ring C u) e)
      ((rawRun hk ring C u) (ring.rightNeighbor e))) :
    CurrentNonbarrierWord hk ring C (u ++ [e]) := by
  exact (currentNonbarrierWord_append_iff_trace hk ring C u [e]).2
    ⟨hu, ⟨he, trivial⟩⟩

/-- The support-driven physical classification of one draw.  A draw outside
    the two charged edges is a one-step current-nonbarrier gap, never a
    failure and never a counted good hit. -/
inductive DrawClass
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Configuration n k) (good competitor e : Fin n) : Prop
  | good (h : e = good) : DrawClass hk ring C good competitor e
  | competitor (h : e = competitor) : DrawClass hk ring C good competitor e
  | nonbarrier
      (h : CurrentNonbarrierWord hk ring C [e]) :
      DrawClass hk ring C good competitor e

/-- Exact two-edge support partitions every physical draw into the desired
    edge, the current competitor, or a real current-prestate nonbarrier. -/
theorem exactTwo_draw_classify
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Configuration n k) (good competitor e : Fin n)
    (hs : ExactTwoBarrierSupport hk ring C good competitor) :
    DrawClass hk ring C good competitor e := by
  by_cases hg : e = good
  · exact DrawClass.good hg
  by_cases hc : e = competitor
  · exact DrawClass.competitor hc
  · apply DrawClass.nonbarrier
    refine ⟨?_, trivial⟩
    intro hbar
    have he : BarrierAt hk ring (labelsOf C) e :=
      (barrierAt_labelsOf_iff hk ring C e).2 hbar
    rcases (hs.2 e).1 he with h | h
    · exact hg h
    · exact hc h

/-- The literal six good edges.  The word is kept as a value so an adapter
    can bind it to a recorded raw scheduler trace without adding a suffix. -/
def gappedWord {n : Nat} (a b c : Fin n)
    (w0 w1 w2 w3 w4 w5 : List (Fin n)) : List (Fin n) :=
  w0 ++ [a] ++ w1 ++ [b] ++ w2 ++ [a] ++ w3 ++ [b] ++ w4 ++ [c] ++ w5 ++ [b]

/-- A proof-carrying physical trace: the stored word is exactly six desired
    charged hits separated by current-prestate nonbarrier gaps.  There is no
    padding after a terminal drop and no dummy hit in this object. -/
structure GappedSixTrace
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Configuration n k) (a b c : Fin n)
    (w0 w1 w2 w3 w4 w5 : List (Fin n))
    (word : List (Fin n)) : Prop where
  word_eq : word = gappedWord a b c w0 w1 w2 w3 w4 w5
  hab : ring.rightNeighbor a = b
  hbc : ring.rightNeighbor b = c
  hsupport : ∀ e, BarrierAt hk ring (labelsOf C) e ↔ e = a ∨ e = b
  hw0 : CurrentNonbarrierWord hk ring C w0
  hw1 : CurrentNonbarrierWord hk ring
    (AAFJPK.OriginalGappedThree.gapHit hk ring C w0 a) w1
  hw2 : CurrentNonbarrierWord hk ring
    (AAFJPK.OriginalGappedThree.gapHit hk ring
      (AAFJPK.OriginalGappedThree.gapHit hk ring C w0 a) w1 b) w2
  hw3 : CurrentNonbarrierWord hk ring
    (AAFJPK.OriginalGappedThree.gapHit hk ring
      (AAFJPK.OriginalGappedThree.gapHit hk ring
        (AAFJPK.OriginalGappedThree.gapHit hk ring C w0 a) w1 b) w2 a) w3
  hw4 : CurrentNonbarrierWord hk ring
    (AAFJPK.OriginalGappedThree.gapHit hk ring
      (AAFJPK.OriginalGappedThree.gapHit hk ring
        (AAFJPK.OriginalGappedThree.gapHit hk ring
          (AAFJPK.OriginalGappedThree.gapHit hk ring C w0 a) w1 b) w2 a)
        w3 b) w4
  hw5 : CurrentNonbarrierWord hk ring
    (AAFJPK.OriginalGappedThree.gapHit hk ring
      (AAFJPK.OriginalGappedThree.gapHit hk ring
        (AAFJPK.OriginalGappedThree.gapHit hk ring
          (AAFJPK.OriginalGappedThree.gapHit hk ring
            (AAFJPK.OriginalGappedThree.gapHit hk ring C w0 a) w1 b) w2 a)
          w3 b) w4 c) w5

/-- The raw execution of the recorded six-stage word is the endpoint named by
    the already verified deterministic GappedSix consumer. -/
theorem rawRun_gappedWord_eq_gappedService6
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Configuration n k) (a b c : Fin n)
    (w0 w1 w2 w3 w4 w5 : List (Fin n)) :
    rawRun hk ring C (gappedWord a b c w0 w1 w2 w3 w4 w5) =
      AAFJPK.OriginalGappedSix.gappedService6 hk ring C a b c w0 w1 w2 w3 w4 w5 := by
  unfold gappedWord
  rw [rawRun_append_trace, rawRun_append_trace, rawRun_append_trace,
    rawRun_append_trace, rawRun_append_trace, rawRun_append_trace,
    rawRun_append_trace, rawRun_append_trace, rawRun_append_trace,
    rawRun_append_trace, rawRun_append_trace]
  rfl

/-- Deterministic consumer for a successful physical trace.  Early strict
    drops are preserved by the six-stage theorem; the adapter only supplies
    the exact raw-word decomposition and never turns a failure into a dummy
    completion. -/
theorem gappedSixTrace_strict_drop
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (C : Configuration n k) (a b c : Fin n)
    (w0 w1 w2 w3 w4 w5 : List (Fin n)) (word : List (Fin n))
    (tr : GappedSixTrace hk ring C a b c w0 w1 w2 w3 w4 w5 word) :
    barrierCount hk ring (labelsOf (rawRun hk ring C word)) <
      barrierCount hk ring (labelsOf C) := by
  rw [tr.word_eq, rawRun_gappedWord_eq_gappedService6]
  exact AAFJPK.OriginalGappedSix.gapped_six_hit_drops_of_exact_adjacent
    hk ring hn3 C a b c w0 w1 w2 w3 w4 w5
    tr.hab tr.hbc tr.hsupport tr.hw0 tr.hw1 tr.hw2 tr.hw3 tr.hw4 tr.hw5

#check exactTwo_draw_classify
#check rawRun_gappedWord_eq_gappedService6
#check gappedSixTrace_strict_drop
#print axioms exactTwo_draw_classify
#print axioms rawRun_gappedWord_eq_gappedService6
#print axioms gappedSixTrace_strict_drop

end AAFJPK.OriginalPhysicalTraceAdapter
namespace AAFJPK.OriginalSuccessRefinesStages04

open AAFJPK.BarrierAlgebra
open AAFJPK.OriginalNonbarrierWord
open AAFJPK.OriginalGappedThree

abbrev Cfg (n k : Nat) := Fin n → AAFJPK.State k

theorem stage0_to_stage1_of_nodrop
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Cfg n k) (a b : Fin n) (w : List (Fin n))
    (hab : ring.rightNeighbor a = b)
    (hs : ExactTwoBarrierSupport hk ring C a b)
    (hw : CurrentNonbarrierWord hk ring C w)
    (hno : ¬ barrierCount hk ring
        (labelsOf (AAFJPK.OriginalGappedThree.gapHit hk ring C w a)) <
      barrierCount hk ring (labelsOf (rawRun hk ring C w))) :
    let E := AAFJPK.OriginalGappedThree.gapHit hk ring C w a
    ExactTwoBarrierSupport hk ring E a b ∧
      (E a).phase = true ∧ (E a).probe = false ∧
      (E b).phase = (C b).phase := by
  have h := AAFJPK.OriginalContactPrefix.first_gapped_a_stage
    hk ring hn2 C a b w hab hs hw
  dsimp only at h
  rcases h.2.2.2 with hd | hkeep
  · have hc := barrierCount_rawRun_eq hk ring hw
    exfalso
    apply hno
    rw [hc]
    simpa [AAFJPK.OriginalGappedThree.gapHit] using hd
  · simpa [AAFJPK.OriginalGappedThree.gapHit] using hkeep

theorem stage1_to_stage2
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (D : Cfg n k) (a b : Fin n) (w : List (Fin n))
    (hab : ring.rightNeighbor a = b)
    (hs : ExactTwoBarrierSupport hk ring D a b)
    (ha : (D a).phase = true)
    (hw : CurrentNonbarrierWord hk ring D w) :
    let c := ring.rightNeighbor b
    let E := AAFJPK.OriginalGappedThree.gapHit hk ring D w b
    AdvanceReady hk ring E a ∧
      (ExactTwoBarrierSupport hk ring E a b ∨
        (ExactTwoBarrierSupport hk ring E a c ∧
          (E c).phase = false ∧ (E c).probe = false)) := by
  simpa [AAFJPK.OriginalGappedThree.gapHit] using
    AAFJPK.OriginalAnchoredSecond.second_hit_stage2
      hk ring hn3 D a b w hab hs ha hw

theorem stage2_to_stage3_of_nodrop
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (D : Cfg n k) (a b c : Fin n) (w : List (Fin n))
    (hab : ring.rightNeighbor a = b)
    (hbc : ring.rightNeighbor b = c)
    (hr : AdvanceReady hk ring D a)
    (hshape :
      ExactTwoBarrierSupport hk ring D a b ∨
        (ExactTwoBarrierSupport hk ring D a c ∧
          (D c).phase = false ∧ (D c).probe = false))
    (hw : CurrentNonbarrierWord hk ring D w)
    (hno : ¬ barrierCount hk ring
        (labelsOf (AAFJPK.OriginalGappedThree.gapHit hk ring D w a)) <
      barrierCount hk ring (labelsOf (rawRun hk ring D w))) :
    let E := AAFJPK.OriginalGappedThree.gapHit hk ring D w a
    NormalizedAdjacentRestart hk ring E b c ∧
      (E b).probe = false ∧ (E c).probe = false := by
  have hn2 : 1 < n := by omega
  rcases hshape with hsab | hsac
  · have hrW := AAFJPK.OriginalAnchoredSecond.ready_through_next_nb
      hk ring a hr hw
    have hsW : ExactTwoBarrierSupport hk ring
        (rawRun hk ring D w) a b :=
      exactTwoBarrierSupport_rawRun hk ring hw hsab
    have hb : BarrierAt hk ring (labelsOf (rawRun hk ring D w)) b :=
      (hsW.2 b).2 (Or.inr rfl)
    have hd := original_ready_collision_drops hk ring hn2
      (rawRun hk ring D w) a hrW (by simpa [hab] using hb)
    exact (hno (by
      simpa [AAFJPK.OriginalGappedThree.gapHit] using hd)).elim
  · rcases hsac with ⟨hsac, hc0, hcp⟩
    have hb : (D b).probe = false := by
      simpa [hab] using hr.2.2
    have h := AAFJPK.OriginalGappedFirstTriple.third_hit_restart_or_drop
      hk ring hn3 D a b c hab hbc hsac.2 hr.2.1 hb hc0 hcp w hw
    rcases h with hd | hkeep
    · exact (hno (by
        simpa [AAFJPK.OriginalGappedThree.gapHit] using hd)).elim
    · simpa [AAFJPK.OriginalGappedThree.gapHit] using hkeep

theorem stage3_to_stage4_of_nodrop
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (D : Cfg n k) (b c : Fin n) (w : List (Fin n))
    (hr : NormalizedAdjacentRestart hk ring D b c)
    (hw : CurrentNonbarrierWord hk ring D w)
    (hno : ¬ barrierCount hk ring
        (labelsOf (AAFJPK.OriginalGappedThree.gapHit hk ring D w b)) <
      barrierCount hk ring (labelsOf (rawRun hk ring D w))) :
    let E := AAFJPK.OriginalGappedThree.gapHit hk ring D w b
    ExactTwoBarrierSupport hk ring E b c ∧
      (E b).phase = true ∧ (E b).probe = false ∧
      (E c).phase = false := by
  have hne : b ≠ c := by
    rw [← hr.1.1]
    exact (rightNeighbor_ne_self ring hn2 b).symm
  have hs : ExactTwoBarrierSupport hk ring D b c := ⟨hne, hr.1.2⟩
  have h := stage0_to_stage1_of_nodrop
    hk ring hn2 D b c w hr.1.1 hs hw hno
  dsimp only at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans hr.2.2⟩

theorem stage4_to_stage5
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (D : Cfg n k) (b c : Fin n) (w : List (Fin n))
    (hbc : ring.rightNeighbor b = c)
    (hs : ExactTwoBarrierSupport hk ring D b c)
    (hb : (D b).phase = true) (hc : (D c).phase = false)
    (hw : CurrentNonbarrierWord hk ring D w) :
    let E := AAFJPK.OriginalGappedThree.gapHit hk ring D w c
    AdvanceReady hk ring E b ∧
      ExactTwoBarrierSupport hk ring E b c := by
  let W := rawRun hk ring D w
  let E := AAFJPK.OriginalGappedThree.gapHit hk ring D w c
  have hsecond := AAFJPK.OriginalAnchoredSecond.second_hit_stage2
    hk ring hn3 D b c w hbc hs hb hw
  have hready : AdvanceReady hk ring E b := by
    simpa [E, AAFJPK.OriginalGappedThree.gapHit] using hsecond.1
  have hsW : ExactTwoBarrierSupport hk ring W b c := by
    simpa [W] using exactTwoBarrierSupport_rawRun hk ring hw hs
  have hphase : (W c).phase = false := by
    simpa [W] using (rawRun_phases_eq hk ring hw c).trans hc
  have hnot : ¬ AdvanceReady hk ring W c := by
    intro h
    exact Bool.noConfusion (hphase.symm.trans h.2.1)
  have hlabels : labelsOf E = labelsOf W := by
    simpa [E, W, AAFJPK.OriginalGappedThree.gapHit] using
      labelsOf_step_eq_self_of_not_ready hk ring W c hnot
  refine ⟨hready, hsW.1, ?_⟩
  intro e
  rw [hlabels]
  exact hsW.2 e

#print axioms stage0_to_stage1_of_nodrop
#print axioms stage1_to_stage2
#print axioms stage2_to_stage3_of_nodrop
#print axioms stage3_to_stage4_of_nodrop
#print axioms stage4_to_stage5

end AAFJPK.OriginalSuccessRefinesStages04

namespace AAFJPK.OriginalRawSixTraceSupport


open AAFJPK.BarrierAlgebra
open AAFJPK.OriginalNonbarrierWord
open AAFJPK.OriginalGappedThree


abbrev Cfg (n k : Nat) := Fin n → AAFJPK.State k


/-- Exact-two support is symmetric in its two named endpoints. -/
theorem exactTwoBarrierSupport_swap
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Cfg n k) (x y : Fin n)
    (hs : ExactTwoBarrierSupport hk ring C x y) :
    ExactTwoBarrierSupport hk ring C y x := by
  refine ⟨hs.1.symm, ?_⟩
  intro e
  simpa [or_comm] using hs.2 e


/-- The exact premise carried by Decomp.supportFailure is impossible as soon
as the related live state carries one concrete current mate. -/
theorem supportFailure_absurd_of_exact_two
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Cfg n k) (good mate : Fin n)
    (hs : ExactTwoBarrierSupport hk ring C good mate)
    (hmissing :
      ¬ ∃ m, ExactTwoBarrierSupport hk ring C good m) :
    False := by
  exact hmissing ⟨mate, hs⟩


/-- On a valid exact-two live state, every non-mate scheduler edge is either
the charged good edge or is genuinely nonbarrier in its current prestate. -/
theorem nonmate_good_or_current_nonbarrier
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Cfg n k) (good mate e : Fin n)
    (hs : ExactTwoBarrierSupport hk ring C good mate)
    (hneMate : e ≠ mate) :
    (e = good ∧
      IsBarrier hk (C e) (C (ring.rightNeighbor e))) ∨
    (e ≠ good ∧ CurrentNonbarrierWord hk ring C [e]) := by
  by_cases hgood : e = good
  · subst e
    left
    refine ⟨rfl, ?_⟩
    exact
      (barrierAt_labelsOf_iff hk ring C good).1
        ((hs.2 good).2 (Or.inl rfl))
  · right
    refine ⟨hgood, ?_⟩
    have hnb :
        ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
      intro hbar
      have hb : BarrierAt hk ring (labelsOf C) e :=
        (barrierAt_labelsOf_iff hk ring C e).2 hbar
      rcases (hs.2 e).1 hb with he | he
      · exact hgood he
      · exact hneMate he
    simpa [CurrentNonbarrierWord] using hnb


/-- Consequently an off-support non-mate/non-good literal step preserves the
same exact current support.  This is the one-step induction needed while the
parser grows the current NB gap without advancing the stage. -/
theorem nonmate_nongood_step_preserves_exact_two
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Cfg n k) (good mate e : Fin n)
    (hs : ExactTwoBarrierSupport hk ring C good mate)
    (hneMate : e ≠ mate) (hneGood : e ≠ good) :
    ExactTwoBarrierSupport hk ring
      ((AAFJPK.protocol k hk).step ring C e) good mate := by
  have hclass :=
    nonmate_good_or_current_nonbarrier
      hk ring C good mate e hs hneMate
  rcases hclass with hgood | hnb
  · exact (hneGood hgood.1).elim
  · have ht :=
      exactTwoBarrierSupport_rawRun hk ring hnb.2 hs
    simpa [rawRun] using ht

private theorem exactTwo_of_normalized_restart
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn : 1 < n) (D : Cfg n k) (x y : Fin n)
    (hr : NormalizedAdjacentRestart hk ring D x y) :
    ExactTwoBarrierSupport hk ring D x y := by
  rcases hr with ⟨⟨hxy, hs⟩, _, _⟩
  refine ⟨?_, hs⟩
  intro h
  exact (rightNeighbor_ne_self ring hn x) (hxy.trans h.symm)

theorem barrierCount_eq_base_of_nodrop
    {n k B : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn : 1 < n) (C : Cfg n k) (w : List (Fin n)) (e : Fin n)
    (hw : CurrentNonbarrierWord hk ring C w)
    (hbase : barrierCount hk ring (labelsOf C) = B)
    (hnodrop : ¬ barrierCount hk ring
      (labelsOf (gapHit hk ring C w e)) < B) :
    barrierCount hk ring (labelsOf (gapHit hk ring C w e)) = B := by
  have hle : barrierCount hk ring
        (labelsOf (gapHit hk ring C w e)) ≤
      barrierCount hk ring (labelsOf C) := by
    calc
      _ ≤ barrierCount hk ring (labelsOf (rawRun hk ring C w)) := by
        simpa [gapHit] using
          protocol_step_barrierCount_le hk ring hn (rawRun hk ring C w) e
      _ = _ := barrierCount_rawRun_eq hk ring hw
  rw [hbase] at hle
  omega

theorem nodrop_against_rawRun
    {n k B : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Cfg n k) (w : List (Fin n)) (e : Fin n)
    (hw : CurrentNonbarrierWord hk ring C w)
    (hbase : barrierCount hk ring (labelsOf C) = B)
    (hnodrop : ¬ barrierCount hk ring
      (labelsOf (gapHit hk ring C w e)) < B) :
    ¬ barrierCount hk ring
      (labelsOf (gapHit hk ring C w e)) <
      barrierCount hk ring (labelsOf (rawRun hk ring C w)) := by
  intro hlt
  apply hnodrop
  rw [barrierCount_rawRun_eq hk ring hw] at hlt
  rw [hbase] at hlt
  exact hlt

/-- The five desired service boundaries retain an oriented exact-two support
    whenever the first four literal services have not dropped below the
    initial count.  This is the concrete producer used to rule out parser
    `supportFailure`; it does not classify a competitor or add a suffix. -/
theorem supports_before_six
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (C : Cfg n k) (a b : Fin n)
    (w0 w1 w2 w3 w4 : List (Fin n))
    (hab : ring.rightNeighbor a = b)
    (hs0 : ExactTwoBarrierSupport hk ring C a b)
    (hw0 : CurrentNonbarrierWord hk ring C w0)
    (hw1 : CurrentNonbarrierWord hk ring
      (gapHit hk ring C w0 a) w1)
    (hw2 : CurrentNonbarrierWord hk ring
      (gapHit hk ring (gapHit hk ring C w0 a) w1 b) w2)
    (hw3 : CurrentNonbarrierWord hk ring
      (gapHit hk ring (gapHit hk ring
        (gapHit hk ring C w0 a) w1 b) w2 a) w3)
    (hw4 : CurrentNonbarrierWord hk ring
      (gapHit hk ring (gapHit hk ring
        (gapHit hk ring (gapHit hk ring C w0 a) w1 b) w2 a) w3 b) w4) :
    let c := ring.rightNeighbor b
    let C1 := gapHit hk ring C w0 a
    let C2 := gapHit hk ring C1 w1 b
    let C3 := gapHit hk ring C2 w2 a
    let C4 := gapHit hk ring C3 w3 b
    let C5 := gapHit hk ring C4 w4 c
    (¬ barrierCount hk ring (labelsOf C1) < barrierCount hk ring (labelsOf C)) →
    (¬ barrierCount hk ring (labelsOf C2) < barrierCount hk ring (labelsOf C)) →
    (¬ barrierCount hk ring (labelsOf C3) < barrierCount hk ring (labelsOf C)) →
    (¬ barrierCount hk ring (labelsOf C4) < barrierCount hk ring (labelsOf C)) →
    (∃ m, ExactTwoBarrierSupport hk ring C1 b m) ∧
    (∃ m, ExactTwoBarrierSupport hk ring C2 a m) ∧
    (∃ m, ExactTwoBarrierSupport hk ring C3 b m) ∧
    (∃ m, ExactTwoBarrierSupport hk ring C4 c m) ∧
    (∃ m, ExactTwoBarrierSupport hk ring C5 b m) := by
  let c := ring.rightNeighbor b
  let C1 := gapHit hk ring C w0 a
  let C2 := gapHit hk ring C1 w1 b
  let C3 := gapHit hk ring C2 w2 a
  let C4 := gapHit hk ring C3 w3 b
  let C5 := gapHit hk ring C4 w4 c
  change (¬ barrierCount hk ring (labelsOf C1) <
      barrierCount hk ring (labelsOf C)) →
    (¬ barrierCount hk ring (labelsOf C2) <
      barrierCount hk ring (labelsOf C)) →
    (¬ barrierCount hk ring (labelsOf C3) <
      barrierCount hk ring (labelsOf C)) →
    (¬ barrierCount hk ring (labelsOf C4) <
      barrierCount hk ring (labelsOf C)) →
    (∃ m, ExactTwoBarrierSupport hk ring C1 b m) ∧
    (∃ m, ExactTwoBarrierSupport hk ring C2 a m) ∧
    (∃ m, ExactTwoBarrierSupport hk ring C3 b m) ∧
    (∃ m, ExactTwoBarrierSupport hk ring C4 c m) ∧
    (∃ m, ExactTwoBarrierSupport hk ring C5 b m)
  intro h0 h1 h2 h3
  have hn : 1 < n := by omega
  have hbc : ring.rightNeighbor b = c := rfl
  have q1 := AAFJPK.OriginalContactPrefix.first_gapped_a_stage
    hk ring hn C a b w0 hab hs0 hw0
  dsimp only at q1
  rcases q1 with ⟨_, _, _, q1⟩
  have k1 : ExactTwoBarrierSupport hk ring C1 a b ∧
      (C1 a).phase = true ∧ (C1 a).probe = false ∧
      (C1 b).phase = (C b).phase := by
    rcases q1 with hd | h
    · exact False.elim (h0 (by simpa [C1, gapHit] using hd))
    · simpa [C1, gapHit] using h
  have hs1 : ExactTwoBarrierSupport hk ring C1 a b := by
    exact k1.1
  have hp1 : (C1 a).phase = true := by
    exact k1.2.1
  have hc1 := barrierCount_eq_base_of_nodrop hk ring hn C w0 a hw0
    (B := barrierCount hk ring (labelsOf C)) rfl h0
  have q2 := AAFJPK.OriginalAnchoredSecond.second_hit_stage2
    hk ring hn3 C1 a b w1 hab hs1 hp1 hw1
  dsimp only at q2
  have sh2 : ExactTwoBarrierSupport hk ring C2 a b ∨
      (ExactTwoBarrierSupport hk ring C2 a c ∧
        (C2 c).phase = false ∧ (C2 c).probe = false) := by
    simpa [C2, gapHit, c] using q2.2
  have ex2 : ∃ m, ExactTwoBarrierSupport hk ring C2 a m := by
    rcases sh2 with h | h
    · exact ⟨b, h⟩
    · exact ⟨c, h.1⟩
  have hc2 := barrierCount_eq_base_of_nodrop hk ring hn C1 w1 b hw1
    hc1 h1
  have hs3 : ExactTwoBarrierSupport hk ring C3 b c := by
    rcases sh2 with hsab | hsac
    · have hr := AAFJPK.OriginalAnchoredSecond.ready_through_next_nb
        hk ring a q2.1 hw2
      have hsD := exactTwoBarrierSupport_rawRun hk ring hw2 hsab
      have hb : BarrierAt hk ring
          (labelsOf (rawRun hk ring C2 w2)) b :=
        (hsD.2 b).2 (Or.inr rfl)
      have hd := original_ready_collision_drops hk ring hn
        (rawRun hk ring C2 w2) a hr (by simpa [hab] using hb)
      apply False.elim
      apply h2
      calc
        barrierCount hk ring (labelsOf C3) <
            barrierCount hk ring (labelsOf (rawRun hk ring C2 w2)) := by
          simpa [C3, gapHit] using hd
        _ = barrierCount hk ring (labelsOf C2) :=
          barrierCount_rawRun_eq hk ring hw2
        _ = barrierCount hk ring (labelsOf C) := hc2
    · rcases hsac with ⟨hsac, hp, hq⟩
      have hbp : (C2 b).probe = false := by
        simpa [C2, gapHit, hab] using q2.1.2.2
      have qt := AAFJPK.OriginalGappedFirstTriple.third_hit_restart_or_drop
        hk ring hn3 C2 a b c hab hbc hsac.2 q2.1.2.1 hbp hp hq w2 hw2
      rcases qt with hd | hr
      · apply False.elim
        apply h2
        calc
          barrierCount hk ring (labelsOf C3) <
              barrierCount hk ring (labelsOf (rawRun hk ring C2 w2)) := by
            simpa [C3, gapHit] using hd
          _ = barrierCount hk ring (labelsOf C2) :=
            barrierCount_rawRun_eq hk ring hw2
          _ = barrierCount hk ring (labelsOf C) := hc2
      · simpa [C3, gapHit] using
          (by
            have hn' : 1 < n := by omega
            exact exactTwo_of_normalized_restart hk ring hn' _ b c hr.1)
  have hc3 := barrierCount_eq_base_of_nodrop hk ring hn C2 w2 a hw2
    hc2 h2
  have q4 := AAFJPK.OriginalContactPrefix.first_gapped_a_stage
    hk ring hn C3 b c w3 hbc hs3 hw3
  dsimp only at q4
  rcases q4 with ⟨_, _, _, q4⟩
  have k4 : ExactTwoBarrierSupport hk ring C4 b c ∧
      (C4 b).phase = true ∧ (C4 b).probe = false ∧
      (C4 c).phase = (C3 c).phase := by
    rcases q4 with hd | h
    · apply False.elim
      have hd' : barrierCount hk ring (labelsOf C4) <
          barrierCount hk ring (labelsOf C3) := by
        simpa [C4, gapHit] using hd
      rw [hc3] at hd'
      exact h3 hd'
    · simpa [C4, gapHit] using h
  have hs4 : ExactTwoBarrierSupport hk ring C4 b c := by
    simpa [C4, gapHit] using k4.1
  have hp4 : (C4 b).phase = true := by
    simpa [C4, gapHit] using k4.2.1
  have q5 := AAFJPK.OriginalAnchoredSecond.second_hit_stage2
    hk ring hn3 C4 b c w4 hbc hs4 hp4 hw4
  have ex5 : ∃ m, ExactTwoBarrierSupport hk ring C5 b m := by
    rcases q5.2 with h | h
    · exact ⟨c, by simpa [C5, gapHit] using h⟩
    · exact ⟨ring.rightNeighbor c, by simpa [C5, gapHit] using h.1⟩
  exact ⟨⟨a, exactTwoBarrierSupport_swap hk ring C1 a b hs1⟩,
    ex2, ⟨c, hs3⟩,
    ⟨b, exactTwoBarrierSupport_swap hk ring C4 b c hs4⟩, ex5⟩

#print axioms exactTwoBarrierSupport_swap
#print axioms supportFailure_absurd_of_exact_two
#print axioms nonmate_good_or_current_nonbarrier
#print axioms nonmate_nongood_step_preserves_exact_two


end AAFJPK.OriginalRawSixTraceSupport

namespace AAFJPK.OriginalRawSixTrace

open BarrierAlgebra
open OriginalNonbarrierWord
open OriginalGappedThree

inductive Stage | s0 | s1 | s2 | s3 | s4 | s5
  deriving DecidableEq

/-- Frozen literal service word [a,b,a,b,c,b], c = rightNeighbor b. -/
def desired {n : Nat} (ring : DirectedRing n) (a b : Fin n) :
    Stage → Fin n
  | .s0 => a | .s1 => b | .s2 => a
  | .s3 => b | .s4 => ring.rightNeighbor b | .s5 => b

def nextStage : Stage → Option Stage
  | .s0 => some .s1 | .s1 => some .s2 | .s2 => some .s3
  | .s3 => some .s4 | .s4 => some .s5 | .s5 => none

/-- Maximal current-NB prefix before the next charged event. -/
inductive GapCut {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (d mate : Fin n) (base : Nat) :
    List (Fin n) → Type
  | cutPrefix {xs} :
      CurrentNonbarrierWord hk ring C xs →
      GapCut hk ring C d mate base xs
  | cutDesired (w rest) :
      CurrentNonbarrierWord hk ring C w →
      GapCut hk ring C d mate base (w ++ d :: rest)
  | cutDrop (w rest) :
      CurrentNonbarrierWord hk ring C w →
      barrierCount hk ring
          (labelsOf (gapHit hk ring C w mate)) <
        base →
      GapCut hk ring C d mate base (w ++ mate :: rest)
  | cutCompetitor (w rest) :
      CurrentNonbarrierWord hk ring C w →
      ¬ barrierCount hk ring
          (labelsOf (gapHit hk ring C w mate)) <
        base →
      GapCut hk ring C d mate base (w ++ mate :: rest)

theorem mate_unique
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {C : Fin n → State k} {d m₁ m₂ : Fin n}
    (h₁ : ExactTwoBarrierSupport hk ring C d m₁)
    (h₂ : ExactTwoBarrierSupport hk ring C d m₂) : m₁ = m₂ := by
  have hm : BarrierAt hk ring (labelsOf C) m₁ :=
    (h₁.2 m₁).2 (Or.inr rfl)
  rcases (h₂.2 m₁).1 hm with h | h
  · exact (h₁.1 h.symm).elim
  · exact h

/-- One stage is cut directly from the raw physical trace.
Every gap cons is derived from exact current support plus being outside both
the fixed desired edge and its unique current mate. -/
noncomputable def splitGap
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    {d mate : Fin n} (base : Nat) :
    ∀ (C : Fin n → State k) (xs : List (Fin n)),
      ExactTwoBarrierSupport hk ring C d mate →
      GapCut hk ring C d mate base xs := by
  intro C xs hs
  induction xs generalizing C with
  | nil => exact .cutPrefix (by trivial)
  | cons e es ih =>
      by_cases hd : e = d
      · subst e
        simpa using
          (GapCut.cutDesired (hk := hk) (ring := ring)
            (C := C) (d := d) (mate := mate) [] es (by trivial))
      · by_cases hm : e = mate
        · subst e
          by_cases hdrop : barrierCount hk ring
              (labelsOf (gapHit hk ring C [] mate)) < base
          · simpa using
              (GapCut.cutDrop (hk := hk) (ring := ring)
                (C := C) (d := d) (mate := mate) [] es
                (by trivial) hdrop)
          · simpa using
              (GapCut.cutCompetitor (hk := hk) (ring := ring)
                (C := C) (d := d) (mate := mate) [] es
                (by trivial) hdrop)
        · have hnb :
              ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
            intro hb
            have he : BarrierAt hk ring (labelsOf C) e :=
              (barrierAt_labelsOf_iff hk ring C e).2 hb
            rcases (hs.2 e).1 he with h | h
            · exact hd h
            · exact hm h
          let C' := (AAFJPK.protocol k hk).step ring C e
          have hs' : ExactTwoBarrierSupport hk ring C' d mate := by
            have hword : CurrentNonbarrierWord hk ring C [e] :=
              ⟨hnb, by trivial⟩
            simpa [C', rawRun] using
              exactTwoBarrierSupport_rawRun hk ring hword hs
          cases ih C' hs' with
          | cutPrefix hw =>
              exact .cutPrefix ⟨hnb, by simpa [C'] using hw⟩
          | cutDesired w rest hw =>
              exact .cutDesired (e :: w) rest
                ⟨hnb, by simpa [C'] using hw⟩
          | cutDrop w rest hw hdrop =>
              exact .cutDrop (e :: w) rest
                ⟨hnb, by simpa [C'] using hw⟩ hdrop
          | cutCompetitor w rest hw hnodrop =>
              exact .cutCompetitor (e :: w) rest
                ⟨hnb, by simpa [C'] using hw⟩ hnodrop

/-- Nested next constructors are precisely the six derived NB gaps followed
by the frozen desired hits.  competitor is the actual current support mate.
supportFailure is explicit; it is never hidden in a stage-law field. -/
inductive Decomp {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (a b : Fin n) (base : Nat) :
    Stage → (Fin n → State k) → List (Fin n) → Prop
  | cutPrefix {s C xs} :
      CurrentNonbarrierWord hk ring C xs →
      Decomp hk ring a b base s C xs
  | supportFailure {s C xs} :
      (¬ ∃ mate,
        ExactTwoBarrierSupport hk ring C (desired ring a b s) mate) →
      Decomp hk ring a b base s C xs
  | cutCompetitor {s C mate w rest}
      (hs : ExactTwoBarrierSupport hk ring C (desired ring a b s) mate)
      (hw : CurrentNonbarrierWord hk ring C w)
      (hnodrop : ¬ barrierCount hk ring
        (labelsOf (gapHit hk ring C w mate)) < base) :
      Decomp hk ring a b base s C (w ++ mate :: rest)
  | drop {s C mate hit w rest}
      (hs : ExactTwoBarrierSupport hk ring C (desired ring a b s) mate)
      (hw : CurrentNonbarrierWord hk ring C w)
      (hdrop : barrierCount hk ring
        (labelsOf (gapHit hk ring C w hit)) < base) :
      Decomp hk ring a b base s C
        (w ++ hit :: rest)
  | next {s t C mate w rest}
      (hs : ExactTwoBarrierSupport hk ring C (desired ring a b s) mate)
      (hw : CurrentNonbarrierWord hk ring C w)
      (hst : nextStage s = some t)
      (hnodrop : ¬ barrierCount hk ring
        (labelsOf (gapHit hk ring C w (desired ring a b s))) < base)
      (tail : Decomp hk ring a b base t
        (gapHit hk ring C w (desired ring a b s)) rest) :
      Decomp hk ring a b base s C
        (w ++ desired ring a b s :: rest)
  | complete {C mate w rest}
      (hs : ExactTwoBarrierSupport hk ring C (desired ring a b .s5) mate)
      (hw : CurrentNonbarrierWord hk ring C w)
      (hnodrop : ¬ barrierCount hk ring
        (labelsOf (gapHit hk ring C w (desired ring a b .s5))) < base) :
      Decomp hk ring a b base .s5 C
        (w ++ desired ring a b .s5 :: rest)

private theorem parseLast
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (a b : Fin n) (base : Nat) :
    ∀ C xs, Decomp hk ring a b base .s5 C xs := by
  intro C xs
  classical
  by_cases hex :
      ∃ mate, ExactTwoBarrierSupport hk ring C (desired ring a b .s5) mate
  · rcases hex with ⟨mate, hs⟩
    cases splitGap hk ring base C xs hs with
    | cutPrefix hw => exact .cutPrefix hw
    | cutDrop w rest hw hdrop =>
        exact .drop (hit := mate) hs hw hdrop
    | cutCompetitor w rest hw hnodrop => exact .cutCompetitor hs hw hnodrop
    | cutDesired w rest hw =>
        by_cases hd : barrierCount hk ring
            (labelsOf (gapHit hk ring C w (desired ring a b .s5))) < base
        · exact .drop (hit := desired ring a b .s5) hs hw hd
        · exact .complete hs hw hd
  · exact .supportFailure hex

private theorem parseStep
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (a b : Fin n) (base : Nat) (s t : Stage)
    (hst : nextStage s = some t)
    (tail : ∀ C xs, Decomp hk ring a b base t C xs) :
    ∀ C xs, Decomp hk ring a b base s C xs := by
  intro C xs
  classical
  by_cases hex :
      ∃ mate, ExactTwoBarrierSupport hk ring C (desired ring a b s) mate
  · rcases hex with ⟨mate, hs⟩
    cases splitGap hk ring base C xs hs with
    | cutPrefix hw => exact .cutPrefix hw
    | cutDrop w rest hw hdrop =>
        exact .drop (hit := mate) hs hw hdrop
    | cutCompetitor w rest hw hnodrop => exact .cutCompetitor hs hw hnodrop
    | cutDesired w rest hw =>
        by_cases hd : barrierCount hk ring
            (labelsOf (gapHit hk ring C w (desired ring a b s))) < base
        · exact .drop (hit := desired ring a b s) hs hw hd
        · exact .next hs hw hst hd
            (tail (gapHit hk ring C w (desired ring a b s)) rest)
  · exact .supportFailure hex

/-- Total raw-trace decomposition.  Use base = the initial barrierCount. -/
theorem rawTrace_decompose
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (a b : Fin n) (C : Fin n → State k) (xs : List (Fin n)) :
    Decomp hk ring a b (barrierCount hk ring (labelsOf C)) .s0 C xs := by
  let B := barrierCount hk ring (labelsOf C)
  let p5 := parseLast hk ring a b B
  let p4 := parseStep hk ring a b B .s4 .s5 rfl p5
  let p3 := parseStep hk ring a b B .s3 .s4 rfl p4
  let p2 := parseStep hk ring a b B .s2 .s3 rfl p3
  let p1 := parseStep hk ring a b B .s1 .s2 rfl p2
  let p0 := parseStep hk ring a b B .s0 .s1 rfl p1
  simpa [B] using p0 C xs

#check AAFJPK.OriginalContactPrefix.first_gapped_a_stage
#check AAFJPK.OriginalGappedThree.normalized_adjacent_gapped_service3_drops
#check splitGap
#check rawTrace_decompose
#print axioms rawTrace_decompose

/-- The final parser `complete` leaf is consumed only through the actual
    six-gap endpoint theorem.  It records no extra no-drop assumption: the
    resulting strict drop is obtained from the literal six-word witness. -/
theorem sixCompleteEndpoint_drops
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (C : Fin n → State k) (a b : Fin n)
    (w0 w1 w2 w3 w4 w5 : List (Fin n))
    (hab : ring.rightNeighbor a = b)
    (hs : ExactTwoBarrierSupport hk ring C a b)
    (hw0 : CurrentNonbarrierWord hk ring C w0)
    (hw1 : CurrentNonbarrierWord hk ring
      (AAFJPK.OriginalGappedThree.gapHit hk ring C w0 a) w1)
    (hw2 : CurrentNonbarrierWord hk ring
      (AAFJPK.OriginalGappedThree.gapHit hk ring
        (AAFJPK.OriginalGappedThree.gapHit hk ring C w0 a) w1 b) w2)
    (hw3 : CurrentNonbarrierWord hk ring
      (AAFJPK.OriginalGappedThree.gapHit hk ring
        (AAFJPK.OriginalGappedThree.gapHit hk ring
          (AAFJPK.OriginalGappedThree.gapHit hk ring C w0 a) w1 b) w2 a) w3)
    (hw4 : CurrentNonbarrierWord hk ring
      (AAFJPK.OriginalGappedThree.gapHit hk ring
        (AAFJPK.OriginalGappedThree.gapHit hk ring
          (AAFJPK.OriginalGappedThree.gapHit hk ring
            (AAFJPK.OriginalGappedThree.gapHit hk ring C w0 a) w1 b) w2 a)
          w3 b) w4)
    (hw5 : CurrentNonbarrierWord hk ring
      (AAFJPK.OriginalGappedThree.gapHit hk ring
        (AAFJPK.OriginalGappedThree.gapHit hk ring
          (AAFJPK.OriginalGappedThree.gapHit hk ring
            (AAFJPK.OriginalGappedThree.gapHit hk ring
              (AAFJPK.OriginalGappedThree.gapHit hk ring C w0 a) w1 b) w2 a)
            w3 b) w4 (ring.rightNeighbor b)) w5) :
    barrierCount hk ring
        (labelsOf
          (AAFJPK.OriginalGappedSix.gappedService6
            hk ring C a b (ring.rightNeighbor b)
            w0 w1 w2 w3 w4 w5)) <
      barrierCount hk ring (labelsOf C) := by
  exact
    AAFJPK.OriginalGappedSix.gapped_six_hit_drops_of_exact_adjacent
      hk ring hn3 C a b (ring.rightNeighbor b)
      w0 w1 w2 w3 w4 w5
      hab rfl hs.2 hw0 hw1 hw2 hw3 hw4 hw5

#check sixCompleteEndpoint_drops
#print axioms sixCompleteEndpoint_drops

/-- A parser branch with the five literal `next` stages and the final
    `complete` constructor is impossible under the genuine initial adjacent
    exact-two hypotheses.  The branch consumer is kept separate from the
    total `Decomp` relation so no large elimination from that `Prop` is used. -/
theorem complete_chain_impossible
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (C : Fin n → State k) (a b : Fin n)
    (w0 w1 w2 w3 w4 w5 : List (Fin n))
    (hw0 : CurrentNonbarrierWord hk ring C w0)
    (hw1 : CurrentNonbarrierWord hk ring
      (gapHit hk ring C w0 a) w1)
    (hw2 : CurrentNonbarrierWord hk ring
      (gapHit hk ring (gapHit hk ring C w0 a) w1 b) w2)
    (hw3 : CurrentNonbarrierWord hk ring
      (gapHit hk ring
        (gapHit hk ring (gapHit hk ring C w0 a) w1 b) w2 a) w3)
    (hw4 : CurrentNonbarrierWord hk ring
      (gapHit hk ring
        (gapHit hk ring
          (gapHit hk ring (gapHit hk ring C w0 a) w1 b) w2 a)
        w3 b) w4)
    (hw5 : CurrentNonbarrierWord hk ring
      (gapHit hk ring
        (gapHit hk ring
          (gapHit hk ring
            (gapHit hk ring (gapHit hk ring C w0 a) w1 b) w2 a)
          w3 b) w4 (ring.rightNeighbor b)) w5)
    (hab : ring.rightNeighbor a = b)
    (hs0 : ExactTwoBarrierSupport hk ring C a b)
    (hnodrop : ¬ barrierCount hk ring
      (labelsOf
        (gapHit hk ring
          (gapHit hk ring
            (gapHit hk ring
              (gapHit hk ring
                (gapHit hk ring
                  (gapHit hk ring C w0 a) w1 b) w2 a)
                w3 b) w4 (ring.rightNeighbor b)) w5 b)) <
      barrierCount hk ring (labelsOf C)) : False := by
  apply hnodrop
  exact sixCompleteEndpoint_drops
    hk ring hn3 C a b w0 w1 w2 w3 w4 w5 hab hs0 hw0 hw1 hw2 hw3 hw4 hw5

#check complete_chain_impossible
#print axioms complete_chain_impossible

/-- The actual parser has four physical early outcomes.  A favorable
    five-next/final-complete branch is eliminated below, so this result does
    not manufacture a sixth success or a dummy suffix. -/
inductive EarlyStop : Prop where
  | cutPrefix
  | supportFailure
  | cutCompetitor
  | drop

inductive SafeEarlyStop : Prop where
  | cutPrefix
  | cutCompetitor
  | drop

private theorem decomp_s0_safe
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (initial : Fin n → State k) (a b : Fin n) (xs : List (Fin n))
    (hab : ring.rightNeighbor a = b)
    (hs0 : ExactTwoBarrierSupport hk ring initial a b)
    (h : Decomp hk ring a b
      (barrierCount hk ring (labelsOf initial)) .s0 initial xs) :
    SafeEarlyStop := by
  have hn : 1 < n := by omega
  cases h with
  | cutPrefix _ => exact .cutPrefix
  | supportFailure hmissing =>
      exact (hmissing ⟨b, hs0⟩).elim
  | cutCompetitor _ _ _ => exact .cutCompetitor
  | drop _ _ _ => exact .drop
  | next hsTop hw0 h01 hno0 h1 =>
      rename_i t0 mate0 w0 rest0
      simp [nextStage] at h01
      cases h01
      have hno0' :=
        AAFJPK.OriginalRawSixTraceSupport.nodrop_against_rawRun
          hk ring initial w0 a hw0 rfl hno0
      have q1 :=
        AAFJPK.OriginalSuccessRefinesStages04.stage0_to_stage1_of_nodrop
          hk ring hn initial a b w0 hab hs0 hw0 hno0'
      dsimp only at q1
      have hs1ab : ExactTwoBarrierSupport hk ring
          (gapHit hk ring initial w0 a) a b := by
        simpa [gapHit] using q1.1
      have hs1ba : ExactTwoBarrierSupport hk ring
          (gapHit hk ring initial w0 a) b a :=
        AAFJPK.OriginalRawSixTraceSupport.exactTwoBarrierSupport_swap
          hk ring _ a b hs1ab
      have hc1 :=
        AAFJPK.OriginalRawSixTraceSupport.barrierCount_eq_base_of_nodrop
          hk ring hn initial w0 a hw0 rfl hno0
      cases h1 with
      | cutPrefix _ => exact .cutPrefix
      | supportFailure hmissing =>
          exact (hmissing ⟨a, hs1ba⟩).elim
      | cutCompetitor _ _ _ => exact .cutCompetitor
      | drop _ _ _ => exact .drop
      | next hsNext1 hw1 h12 hno1 h2 =>
          rename_i t1 mate1 w1 rest1
          simp [nextStage] at h12
          cases h12
          have q2 :=
            AAFJPK.OriginalSuccessRefinesStages04.stage1_to_stage2
              hk ring hn3 (gapHit hk ring initial w0 a) a b w1 hab
              hs1ab q1.2.1 hw1
          dsimp only at q2
          have hshape2 := q2.2
          have hs2 : ∃ m, ExactTwoBarrierSupport hk ring
              (gapHit hk ring (gapHit hk ring initial w0 a) w1 b) a m := by
            rcases hshape2 with hs | hs
            · exact ⟨b, by simpa [gapHit] using hs⟩
            · exact ⟨ring.rightNeighbor b, by simpa [gapHit] using hs.1⟩
          have hc2 :=
            AAFJPK.OriginalRawSixTraceSupport.barrierCount_eq_base_of_nodrop
              hk ring hn (gapHit hk ring initial w0 a) w1 b hw1 hc1 hno1
          cases h2 with
          | cutPrefix _ => exact .cutPrefix
          | supportFailure hmissing =>
              exact (hmissing hs2).elim
          | cutCompetitor _ _ _ => exact .cutCompetitor
          | drop _ _ _ => exact .drop
          | next hsNext2 hw2 h23 hno2 h3 =>
              rename_i t2 mate2 w2 rest2
              simp [nextStage] at h23
              cases h23
              have hno2' :=
                AAFJPK.OriginalRawSixTraceSupport.nodrop_against_rawRun
                  hk ring
                  (gapHit hk ring (gapHit hk ring initial w0 a) w1 b)
                  w2 a hw2 hc2 hno2
              have q3 :=
                AAFJPK.OriginalSuccessRefinesStages04.stage2_to_stage3_of_nodrop
                  hk ring hn3
                  (gapHit hk ring (gapHit hk ring initial w0 a) w1 b)
                  a b (ring.rightNeighbor b) w2 hab rfl q2.1 hshape2 hw2 hno2'
              dsimp only at q3
              have hs3 :=
                AAFJPK.OriginalRawSixTraceSupport.exactTwo_of_normalized_restart
                  hk ring hn
                  (gapHit hk ring
                    (gapHit hk ring (gapHit hk ring initial w0 a) w1 b) w2 a)
                  b (ring.rightNeighbor b) q3.1
              have hc3 :=
                AAFJPK.OriginalRawSixTraceSupport.barrierCount_eq_base_of_nodrop
                  hk ring hn
                  (gapHit hk ring (gapHit hk ring initial w0 a) w1 b)
                  w2 a hw2 hc2 hno2
              cases h3 with
              | cutPrefix _ => exact .cutPrefix
              | supportFailure hmissing =>
                  exact (hmissing ⟨ring.rightNeighbor b, hs3⟩).elim
              | cutCompetitor _ _ _ => exact .cutCompetitor
              | drop _ _ _ => exact .drop
              | next hsNext3 hw3 h34 hno3 h4 =>
                  rename_i t3 mate3 w3 rest3
                  simp [nextStage] at h34
                  cases h34
                  have hno3' :=
                    AAFJPK.OriginalRawSixTraceSupport.nodrop_against_rawRun
                      hk ring
                      (gapHit hk ring
                        (gapHit hk ring (gapHit hk ring initial w0 a) w1 b)
                        w2 a)
                      w3 b hw3 hc3 hno3
                  have q4 :=
                    AAFJPK.OriginalSuccessRefinesStages04.stage3_to_stage4_of_nodrop
                      hk ring hn
                      (gapHit hk ring
                        (gapHit hk ring (gapHit hk ring initial w0 a) w1 b)
                        w2 a)
                      b (ring.rightNeighbor b) w3 q3.1 hw3 hno3'
                  dsimp only at q4
                  have hs4 : ExactTwoBarrierSupport hk ring
                      (gapHit hk ring
                        (gapHit hk ring
                          (gapHit hk ring (gapHit hk ring initial w0 a) w1 b)
                          w2 a) w3 b)
                      b (ring.rightNeighbor b) := by
                    simpa [gapHit] using q4.1
                  cases h4 with
                  | cutPrefix _ => exact .cutPrefix
                  | supportFailure hmissing =>
                      have hs4' : ExactTwoBarrierSupport hk ring
                          (gapHit hk ring
                            (gapHit hk ring
                              (gapHit hk ring
                                (gapHit hk ring initial w0 a) w1 b) w2 a)
                            w3 b)
                          (desired ring a b .s4) b := by
                        have hswap := AAFJPK.OriginalRawSixTraceSupport.exactTwoBarrierSupport_swap
                          hk ring _ b (ring.rightNeighbor b) hs4
                        simpa [desired] using hswap
                      exact (hmissing ⟨b, hs4'⟩).elim
                  | cutCompetitor _ _ _ => exact .cutCompetitor
                  | drop _ _ _ => exact .drop
                  | next hsNext4 hw4 h45 hno4 h5 =>
                      rename_i t4 mate4 w4 rest4
                      simp [nextStage] at h45
                      cases h45
                      have q5 :=
                        AAFJPK.OriginalSuccessRefinesStages04.stage4_to_stage5
                          hk ring hn3
                          (gapHit hk ring
                            (gapHit hk ring
                              (gapHit hk ring
                                (gapHit hk ring initial w0 a) w1 b) w2 a)
                            w3 b)
                          b (ring.rightNeighbor b) w4 rfl hs4 q4.2.1
                          q4.2.2.2 hw4
                      dsimp only at q5
                      have hs5 : ExactTwoBarrierSupport hk ring
                          (gapHit hk ring
                            (gapHit hk ring
                              (gapHit hk ring
                                (gapHit hk ring
                                  (gapHit hk ring initial w0 a) w1 b) w2 a)
                                w3 b)
                            w4 (ring.rightNeighbor b))
                          b (ring.rightNeighbor b) := by
                        simpa [gapHit] using q5.2
                      cases h5 with
                      | cutPrefix _ => exact .cutPrefix
                      | supportFailure hmissing =>
                          exact (hmissing ⟨ring.rightNeighbor b, hs5⟩).elim
                      | cutCompetitor _ _ _ => exact .cutCompetitor
                      | drop _ _ _ => exact .drop
                      | next _ _ hbad _ _ =>
                          simp [nextStage] at hbad
                      | complete _ hw5 hnodrop5 =>
                          have hdrop :=
                            sixCompleteEndpoint_drops
                              hk ring hn3 initial a b
                              _ _ _ _ _ _ hab hs0 hw0 hw1 hw2 hw3 hw4 hw5
                          exact (hnodrop5 (by
                            simpa [desired,
                              AAFJPK.OriginalGappedSix.gappedService6]
                              using hdrop)).elim

private theorem decomp_s0_early
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (initial : Fin n → State k) (a b : Fin n) (xs : List (Fin n))
    (hab : ring.rightNeighbor a = b)
    (hs0 : ExactTwoBarrierSupport hk ring initial a b)
    (h : Decomp hk ring a b
      (barrierCount hk ring (labelsOf initial)) .s0 initial xs) :
    EarlyStop := by
  cases h with
  | cutPrefix _ => exact .cutPrefix
  | supportFailure _ => exact .supportFailure
  | cutCompetitor _ _ _ => exact .cutCompetitor
  | drop _ _ _ => exact .drop
  | next _ hw0 h01 _ h1 =>
      simp [nextStage] at h01
      cases h01
      cases h1 with
      | cutPrefix _ => exact .cutPrefix
      | supportFailure _ => exact .supportFailure
      | cutCompetitor _ _ _ => exact .cutCompetitor
      | drop _ _ _ => exact .drop
      | next _ hw1 h12 _ h2 =>
          simp [nextStage] at h12
          cases h12
          cases h2 with
          | cutPrefix _ => exact .cutPrefix
          | supportFailure _ => exact .supportFailure
          | cutCompetitor _ _ _ => exact .cutCompetitor
          | drop _ _ _ => exact .drop
          | next _ hw2 h23 _ h3 =>
              simp [nextStage] at h23
              cases h23
              cases h3 with
              | cutPrefix _ => exact .cutPrefix
              | supportFailure _ => exact .supportFailure
              | cutCompetitor _ _ _ => exact .cutCompetitor
              | drop _ _ _ => exact .drop
              | next _ hw3 h34 _ h4 =>
                  simp [nextStage] at h34
                  cases h34
                  cases h4 with
                  | cutPrefix _ => exact .cutPrefix
                  | supportFailure _ => exact .supportFailure
                  | cutCompetitor _ _ _ => exact .cutCompetitor
                  | drop _ _ _ => exact .drop
                  | next _ hw4 h45 _ h5 =>
                      simp [nextStage] at h45
                      cases h45
                      cases h5 with
                      | cutPrefix _ => exact .cutPrefix
                      | supportFailure _ => exact .supportFailure
                      | cutCompetitor _ _ _ => exact .cutCompetitor
                      | drop _ _ _ => exact .drop
                      | next _ _ hbad _ _ =>
                          simp [nextStage] at hbad
                      | complete _ hw5 hnodrop5 =>
                          have hdrop :=
                            sixCompleteEndpoint_drops
                              hk ring hn3 initial a b
                              _ _ _ _ _ _
                              hab hs0 hw0 hw1 hw2 hw3 hw4 hw5
                          exact
                            (hnodrop5 (by
                              simpa [desired,
                                AAFJPK.OriginalGappedSix.gappedService6]
                                using hdrop)).elim

/-- Consume the actual raw decomposition.  `supportFailure` remains explicit;
    only the syntactic six-good no-drop residual is ruled out by GappedSix. -/
theorem rawTrace_decompose_early
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (initial : Fin n → State k) (a b : Fin n) (xs : List (Fin n))
    (hab : ring.rightNeighbor a = b)
    (hs0 : ExactTwoBarrierSupport hk ring initial a b) :
    EarlyStop := by
  exact decomp_s0_early hk ring hn3 initial a b xs hab hs0
    (rawTrace_decompose hk ring a b initial xs)

theorem rawTrace_decompose_safe_early
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (initial : Fin n → State k) (a b : Fin n) (xs : List (Fin n))
    (hab : ring.rightNeighbor a = b)
    (hs0 : ExactTwoBarrierSupport hk ring initial a b) :
    SafeEarlyStop := by
  exact decomp_s0_safe hk ring hn3 initial a b xs hab hs0
    (rawTrace_decompose hk ring a b initial xs)

#check rawTrace_decompose_early
#check rawTrace_decompose_safe_early
#print axioms decomp_s0_early
#print axioms rawTrace_decompose_early
#print axioms rawTrace_decompose_safe_early

end AAFJPK.OriginalRawSixTrace

namespace AAFJPK.OriginalRawSixTraceSupport

open BarrierAlgebra
open OriginalNonbarrierWord

/-- A constructor-level view of parser support failure.  The equality keeps
    the branch explicit without eliminating the Prop-valued Decomp into data. -/
def IsSupportFailure
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {a b : Fin n} {base : Nat} {s : OriginalRawSixTrace.Stage}
    {C : Cfg n k} {xs : List (Fin n)}
    (d : OriginalRawSixTrace.Decomp hk ring a b base s C xs) : Prop :=
  ∃ hmissing,
    d = OriginalRawSixTrace.Decomp.supportFailure hmissing

theorem not_supportFailure_of_exact_two
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {a b : Fin n} {base : Nat} {s : OriginalRawSixTrace.Stage}
    {C : Cfg n k} {xs : List (Fin n)}
    (d : OriginalRawSixTrace.Decomp hk ring a b base s C xs)
    {good mate : Fin n}
    (hs : ExactTwoBarrierSupport hk ring C good mate)
    (hgood : good = OriginalRawSixTrace.desired ring a b s) :
    ¬ IsSupportFailure d := by
  intro hfail
  rcases hfail with ⟨hmissing, rfl⟩
  subst good
  exact supportFailure_absurd_of_exact_two hk ring C _ mate hs hmissing

#check not_supportFailure_of_exact_two
#print axioms not_supportFailure_of_exact_two

end AAFJPK.OriginalRawSixTraceSupport
