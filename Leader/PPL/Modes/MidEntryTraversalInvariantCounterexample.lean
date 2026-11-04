import Leader.PPL.Modes.MidEntryTraversalPaperEventsCorrected
import Init.Omega

namespace PPL.Modes.Lemma5

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9

private def q19857Ring : DirectedRing 3 :=
  ⟨by omega⟩

private def q19857State
    (i : Fin 3) : PPL.State 2 96 :=
  { leader := false
    id := false
    dist := 0
    last := true
    tokenB := none
    tokenW := none
    mode := false
    clock := 0
    signalR :=
      if i = (2 : Fin 3) then
        ⟨96, by omega⟩
      else
        0
    hits := 0
    bullet := 0
    shield := false
    signalB := false }

private def q19857D : Config 3 2 96 :=
  q19857State

private def q19857Pre : DetSchedule 3 :=
  List.replicate 192 (1 : Fin 3) ++
    List.replicate 191 (0 : Fin 3) ++
      [(2 : Fin 3), (0 : Fin 3)]

private def q19857E : Fin 3 :=
  (1 : Fin 3)

private def q19857Post : DetSchedule 3 :=
  q19857Pre ++ [q19857E]

private def q19857Start : Fin 3 :=
  q19765MaxSignalSite q19857Ring q19857D

private def q19857H : Nat :=
  (q19857D q19857Start).hits.val

private def q19857Host
    (word : DetSchedule 3) : Fin 3 :=
  q19765TraversalHost q19857Ring q19857D word

private def q19857StopB
    (word : DetSchedule 3) : Bool :=
  q19765TraversalStopB q19857Ring q19857D word

private def q19857ResetsB
    (word : DetSchedule 3) : Bool :=
  allClockResetsSeenB q19857Ring q19857D word

private def q19857SublistB
    (word : DetSchedule 3) : Bool :=
  decide
    ((PPL.seqR q19857Ring q19857Start 3).Sublist word)

private def q19857C1B
    (word : DetSchedule 3) : Bool :=
  decide
    (q19857StopB word = false →
      0 <
        (runPPL q19857Ring q19857D word
          (q19857Host word)).signalR.val)

private def q19857C2B
    (word : DetSchedule 3) : Bool :=
  decide
    ((PPL.seqR q19857Ring q19857Start 3).Sublist word →
      q19857ResetsB word = true ∨
        q19857StopB word = true)

private def q19857C3B
    (word : DetSchedule 3) : Bool :=
  let bits :=
    stoppedEncounterBits
      q19857Ring q19857Host q19857StopB word
  decide
    (96 ≤
      (lotteryRun 2
        (lotteryOffset q19857H) bits).wins +
        (runPPL q19857Ring q19857D word
          (q19857Host word)).signalR.val)

/-! Exact concrete checks. -/

private theorem q19857Start_is_two :
    q19857Start = (2 : Fin 3) := by
  decide +kernel

private theorem q19857H_is_zero :
    q19857H = 0 := by
  decide +kernel

private theorem q19857MaxReset_true :
    maxResetSignalB q19857D = true := by
  decide +kernel

private theorem q19857Pre_length :
    q19857Pre.length = 385 := by
  decide +kernel

private theorem q19857Post_length :
    q19857Post.length = 386 := by
  decide +kernel

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 1000000 in
private theorem q19857Stop_pre_true :
    q19857StopB q19857Pre = true := by
  decide +kernel

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 1000000 in
private theorem q19857Stop_post_false :
    q19857StopB q19857Post = false := by
  decide +kernel

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 1000000 in
private theorem q19857Resets_pre_false :
    q19857ResetsB q19857Pre = false := by
  decide +kernel

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 1000000 in
private theorem q19857Resets_post_false :
    q19857ResetsB q19857Post = false := by
  decide +kernel

private theorem q19857Sublist_pre_false :
    q19857SublistB q19857Pre = false := by
  decide +kernel

private theorem q19857Sublist_post_true :
    q19857SublistB q19857Post = true := by
  decide +kernel

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 1000000 in
private theorem q19857C1_pre_true :
    q19857C1B q19857Pre = true := by
  decide +kernel

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 1000000 in
private theorem q19857C1_post_true :
    q19857C1B q19857Post = true := by
  decide +kernel

private theorem q19857C2_pre_true :
    q19857C2B q19857Pre = true := by
  decide +kernel

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 1000000 in
private theorem q19857C2_post_false :
    q19857C2B q19857Post = false := by
  decide +kernel

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 1000000 in
private theorem q19857C3_pre_true :
    q19857C3B q19857Pre = true := by
  decide +kernel

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 1000000 in
private theorem q19857C3_post_true :
    q19857C3B q19857Post = true := by
  decide +kernel

/-! Bool-to-Prop bridges. -/

private theorem q19857Sublist_of_true
    (word : DetSchedule 3)
    (h : q19857SublistB word = true) :
    (PPL.seqR q19857Ring q19857Start 3).Sublist word := by
  unfold q19857SublistB at h
  exact of_decide_eq_true h

private theorem q19857Sublist_not_of_false
    (word : DetSchedule 3)
    (h : q19857SublistB word = false) :
    ¬ (PPL.seqR q19857Ring q19857Start 3).Sublist word := by
  unfold q19857SublistB at h
  exact of_decide_eq_false h

private theorem q19857C1_of_true
    (word : DetSchedule 3)
    (h : q19857C1B word = true) :
    q19857StopB word = false →
      0 <
        (runPPL q19857Ring q19857D word
          (q19857Host word)).signalR.val := by
  unfold q19857C1B at h
  exact of_decide_eq_true h

private theorem q19857C2_of_true
    (word : DetSchedule 3)
    (h : q19857C2B word = true) :
    (PPL.seqR q19857Ring q19857Start 3).Sublist word →
      q19857ResetsB word = true ∨
        q19857StopB word = true := by
  unfold q19857C2B at h
  exact of_decide_eq_true h

private theorem q19857C2_not_of_false
    (word : DetSchedule 3)
    (h : q19857C2B word = false) :
    ¬
      ((PPL.seqR q19857Ring q19857Start 3).Sublist word →
        q19857ResetsB word = true ∨
          q19857StopB word = true) := by
  unfold q19857C2B at h
  exact of_decide_eq_false h

private theorem q19857C3_of_true
    (word : DetSchedule 3)
    (h : q19857C3B word = true) :
    let bits :=
      stoppedEncounterBits
        q19857Ring q19857Host q19857StopB word
    96 ≤
      (lotteryRun 2
        (lotteryOffset q19857H) bits).wins +
        (runPPL q19857Ring q19857D word
          (q19857Host word)).signalR.val := by
  unfold q19857C3B at h
  exact of_decide_eq_true h

/-!
The raw post checks independently expose the C2 contradiction:
the rotated word has occurred, but neither all resets nor current stop holds.
-/
private theorem q19857Post_C2_contradiction :
    ¬
      ((PPL.seqR q19857Ring q19857Start 3).Sublist q19857Post →
        q19857ResetsB q19857Post = true ∨
          q19857StopB q19857Post = true) := by
  intro hfront
  have hsub :
      (PPL.seqR q19857Ring q19857Start 3).Sublist q19857Post :=
    q19857Sublist_of_true
      q19857Post q19857Sublist_post_true
  rcases hfront hsub with hreset | hstop
  · rw [q19857Resets_post_false] at hreset
    cases hreset
  · rw [q19857Stop_post_false] at hstop
    cases hstop

private theorem q19857Host_eq :
    q19857Host = q19765TraversalHost q19857Ring q19857D := rfl

private theorem q19857StopB_eq :
    q19857StopB = q19765TraversalStopB q19857Ring q19857D := rfl

private theorem q19857ResetsB_eq :
    q19857ResetsB = allClockResetsSeenB q19857Ring q19857D := rfl

private theorem q19857PreInvariant :
    q19792TraversalPrefixInvariant
      q19857Ring q19857D
      q19857Start q19857H q19857Pre := by
  have h1 := q19857C1_of_true q19857Pre q19857C1_pre_true
  have h2 := q19857C2_of_true q19857Pre q19857C2_pre_true
  have h3 := q19857C3_of_true q19857Pre q19857C3_pre_true
  dsimp only at h3
  rw [q19857Host_eq, q19857StopB_eq] at h1 h3
  rw [q19857ResetsB_eq, q19857StopB_eq] at h2
  unfold q19792TraversalPrefixInvariant
  dsimp only
  exact And.intro h1 (And.intro h2 h3)

private theorem q19857PostNotInvariant :
    ¬
      q19792TraversalPrefixInvariant
        q19857Ring q19857D
        q19857Start q19857H q19857Post := by
  intro hinv
  unfold q19792TraversalPrefixInvariant at hinv
  dsimp only at hinv
  have hC2 :
      (PPL.seqR q19857Ring q19857Start 3).Sublist q19857Post →
        q19857ResetsB q19857Post = true ∨
          q19857StopB q19857Post = true := by
    simpa [
      q19857ResetsB,
      q19857StopB
    ] using hinv.2.1
  exact q19857Post_C2_contradiction hC2

theorem lemma5iRetimedTraversalABCOneStepInvariant_false :
    ¬ Lemma5iRetimedTraversalABCOneStepInvariant := by
  intro hstep
  have hlocal :=
    hstep
      (n := 3) (psi := 2) (kappa := 96)
      (by omega)
      (by omega)
      (by omega)
      (by omega)
      q19857Ring q19857D
      (PPL.Modes.SignalLineage.signalLineageOwnership
        q19857Ring)
      q19857MaxReset_true
  dsimp only at hlocal
  have hpre :
      q19792TraversalPrefixInvariant
        q19857Ring q19857D
        (q19765MaxSignalSite q19857Ring q19857D)
        (q19857D
          (q19765MaxSignalSite
            q19857Ring q19857D)).hits.val
        q19857Pre := by
    simpa [q19857Start, q19857H] using
      q19857PreInvariant
  have hpost :=
    hlocal q19857Pre q19857E hpre
  have hpost' :
      q19792TraversalPrefixInvariant
        q19857Ring q19857D
        q19857Start q19857H q19857Post := by
    simpa [
      q19857Post,
      q19857Start,
      q19857H
    ] using hpost
  exact q19857PostNotInvariant hpost'

end PPL.Modes.Lemma5

#print axioms PPL.Modes.Lemma5.lemma5iRetimedTraversalABCOneStepInvariant_false
