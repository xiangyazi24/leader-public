import Leader.L4.WindowA0ApproachJoin

namespace L4.WindowA0ReleaseFailure
open WindowA0ApproachJoin WindowA0Leg WindowFiveStages RootedAssembly
open WindowA0ReleaseCredit WindowA0GapOneJoin FixedResidual

private theorem snoc_or_nil {α : Type} (u : List α) :
    u=[] ∨ ∃ v e, u=v++[e] := by
  cases he : u.reverse with
  | nil =>
    left
    have E := congrArg List.reverse he
    simpa using E
  | cons e v =>
    right
    have E := congrArg List.reverse he
    exact ⟨v.reverse,e,by simpa using E⟩

private theorem gap_failure {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (x : WindowA0ClosedEntry.State p c n) (i : Fin n) (u : Word n)
    (h : FirstExit (fun v => WindowA0GapOneWord.stopped
      (WindowA0GapOneWord.observe S i x.tag v)) u)
    (hb : WindowA0GapOneWord.failed (WindowA0GapOneWord.observe S i x.tag u)) :
    ¬ WindowA0Ledger.done (physicalAfter S x u).tag := by
  rcases snoc_or_nil u with rfl | ⟨v,e,rfl⟩
  · cases hb
  let old := WindowA0GapOneWord.observe S i x.tag v
  have hprev := ((clean_child _ v e).mp h.1).2
  change ¬WindowA0GapOneWord.stopped old at hprev
  have hs := WindowA0GapOneWord.observe_step S i x.tag v e
  change WindowA0GapOneWord.failed (WindowA0GapOneWord.observe S i x.tag (wordNext v e)) at hb
  rw [hs] at hb
  change WindowA0GapOneWord.failed (WindowA0GapOne.next S i old e) at hb
  have hp := WindowA0GapOneWord.observe_actual S i x (wordNext v e)
  rw [hs] at hp
  intro hd
  have hr : (WindowA0Ledger.next S old.1 e).reason.isSome=true := by
    change (WindowA0GapOne.next S i old e).1.reason.isSome=true
    rw [hp]
    exact hd
  cases hw : old.2 with
  | success | failed =>
    exact hprev (by simp [WindowA0GapOneWord.stopped,done,hw])
  | waiting k =>
    simp [WindowA0GapOneWord.failed,WindowA0GapOne.next,hw,hr] at hb

private theorem adjacent_failure {p c n : Nat} {initial : Config p c n}
    (hn : 5≤n) (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat)
    (x : WindowA0ClosedEntry.State p c n)
    (hx : WindowA0ClosedEntry.Admitted initial S J H x)
    (ha : ¬WindowA0Ledger.done x.tag)
    (u : Word n)
    (h : FirstExit (fun v => adjDone (WindowA0AdjacentEntry.routedState S x v)) u)
    (hb : (WindowA0AdjacentEntry.routedState S x u).2=.failed) :
    ¬ WindowA0Ledger.done (physicalAfter S x u).tag := by
  rcases snoc_or_nil u with rfl | ⟨v,e,rfl⟩
  · cases hb
  let old := WindowA0AdjacentEntry.routedState S x v
  have hprev := ((clean_child _ v e).mp h.1).2
  change ¬adjDone old at hprev
  change (WindowA0AdjacentEntry.routedState S x (wordNext v e)).2=.failed at hb
  have hstep : WindowA0AdjacentEntry.routedState S x (wordNext v e)=adjStep S x old e := by
    simp [old,WindowA0AdjacentEntry.routedState,adjStep,wordNext,GGTiming.runMarks_append,GGTiming.runMarks]
  rw [hstep] at hb
  cases hp : old.2 with
  | success | failed =>
    exact (hprev (by simp [adjDone,done,hp])).elim
  | waiting k =>
    have route : WindowA0Route.routeTwo S.group S.iTag S.jTag old.1 e=.keep := by
      apply Classical.byContradiction
      intro hne
      have E := WindowA0RoutedRelease.exit_priority S.group S.iTag S.jTag
        (WindowA0AdjacentEntry.guardBase (WindowA0ClosedEntry.cut x).top)
        (WindowA0AdjacentEntry.mode x) old e k hp hne
      change (adjStep S x old e).2=.success at E
      rw [E] at hb
      cases hb
    have hr := (WindowA0AdjacentMotion.waiting_donor_on_word hn S J H x hx ha v k hp).1
    have pr := WindowA0AdjacentEntry.project_word S x v
    change ¬WindowA0Ledger.done (physicalAfter S x (wordNext v e)).tag
    unfold physicalAfter wordNext
    rw [GGTiming.runMarks_append]
    change ¬WindowA0Ledger.done (WindowA0Ledger.next S (physicalAfter S x v).tag e)
    exact fun hd => (WindowA0Ledger.physical_exit_iff S _ e hr).mp hd (pr ▸ route)

/-- At the exact first release stop, a spoiled guard is not a scoped
exit. A true physical exit has priority on that same raw mark. -/
theorem first_release_bad_not_done {p c n : Nat} {initial : Config p c n}
    (hn : 5≤n) (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat)
    (q : Trip (2*c)) (z : AState p c n) (hz : ApproachGood initial S J H q z)
    (w : Word n) (h : FirstExit (releaseDone S z) w) (hb : releaseBad S z w) :
    ¬ WindowA0Ledger.done (physicalAfter S z.physical w).tag := by
  obtain ⟨a,u,rfl,ha,hu⟩ := splice_first (hit S z) (branchDone S z) w h
  have bad : branchBad S z a u := (splice_at (hit S z) _ a u ha).mp hb
  let x := (approachRead S z a).physical
  have hx : WindowA0ClosedEntry.Admitted initial S J H x :=
    (approachRead_good (by omega) S J H q z hz a ha.1).1
  have join : physicalAfter S z.physical (a++u)=physicalAfter S x u := by
    unfold physicalAfter
    rw [GGTiming.runMarks_append]
    exact congrArg (fun seed => GGTiming.runMarks (WindowA0ClosedEntry.next S) seed u)
      (approachRead_actual S z a).symm
  rw [join]
  by_cases hd : WindowA0Ledger.done x.tag
  · simp [branchBad,x,hd] at bad
  by_cases hw : (approachRead S z a).worker=0
  · let i := rightNeighbor x.tag.iSlot
    have D : branchDone S z a=fun v => WindowA0GapOneWord.stopped
        (WindowA0GapOneWord.observe S i x.tag v) := by funext; simp [branchDone,hd,hw,i,x]
    rw [D] at hu
    exact gap_failure S x i u hu (by simpa [branchBad,hd,hw,i,x] using bad)
  · have D : branchDone S z a=fun v => adjDone
        (WindowA0AdjacentEntry.routedState S x v) := by funext; simp [branchDone,hd,hw,x]
    rw [D] at hu
    exact adjacent_failure hn S J H x hx hd u hu (by simpa [branchBad,hd,hw,x] using bad)

end L4.WindowA0ReleaseFailure
