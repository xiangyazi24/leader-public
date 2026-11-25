import Leader.L4.WindowA0GapOneJoin
import Leader.L4.WindowA0AdjacentMotion
import Leader.L4.WindowA0ReturnStep

namespace L4.WindowA0Leg
open FixedResidual WindowFiveStages RootedAssembly TripleRenewal

abbrev AState := WindowA0ApproachOwned.State
noncomputable abbrev AStep := @WindowA0ApproachOwned.approachNext
abbrev AStop := @WindowA0ApproachOwned.done

noncomputable def approachRead {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (z : AState p c n) (w : Word n) : AState p c n :=
  GGTiming.runMarks (AStep S) z w

theorem approachRead_actual {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (z : AState p c n) (w : Word n) :
    (approachRead S z w).physical=WindowA0GapOneJoin.physicalAfter S z.physical w := by
  induction w generalizing z with
  | nil => rfl
  | cons e es ih => exact ih (AStep S z e)

/-- A common post-approach interface, using a closed physical cursor
and the current owned worker. Offset zero is reserved for true gap one. -/
def ApproachGood {p c n : Nat} (z0 : Config p c n) (S : WindowA0Ledger.Scope n)
    (J : Fin n) (H : Nat) (q : Trip (2*c)) (z : AState p c n) : Prop :=
  WindowA0ClosedEntry.Admitted z0 S J H z.physical ∧
    (WindowA0Ledger.done z.physical.tag ∨
      (WindowA0ApproachOwned.Physical J q z.physical z.worker ∧
        (z.worker=0 → z.physical.gap=1)))

theorem approach_step {p c n : Nat} {z0 : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (q : Trip (2*c))
    (z : AState p c n) (e : Fin n) (hz : ApproachGood z0 S J H q z)
    (hfar : ¬ AStop z) :
    ApproachGood z0 S J H q (AStep S z e) := by
  obtain ⟨hA,hP⟩ := hz
  have hA' := WindowA0ClosedEntry.close hn S J H z.physical e hA
  refine ⟨hA',?_⟩
  by_cases hs : WindowA0Ledger.done (AStep S z e).physical.tag
  · exact .inl hs
  have hw := (hP.resolve_left (fun h => hfar (.inl h))).1
  by_cases h : AStop (AStep S z e)
  · obtain ⟨h1,h2⟩ :=
      WindowA0ApproachOwned.first_adjacency hn S J H q z e hA hw hfar h hs
    exact .inr ⟨h1.symm ▸ h2,fun he => by rw [h1] at he; omega⟩
  · have hk : 2≤z.worker := by
      have K : ¬z.worker≤1 := fun hj => hfar (.inr hj)
      omega
    have K := WindowA0ApproachOwned.physical_step hn S J H q z.physical e z.worker hA hw hs hk
    have E : (AStep S z e).worker=
        z.worker-WindowA0XSweep.topShift z.physical e-
          WindowA0ApproachOwned.workerHit z.physical z.worker e := by
      simp only [WindowA0ApproachOwned.approachNext,if_neg hfar]
    refine .inr ⟨?_,fun he => (h (.inr (by omega))).elim⟩
    rw [E,WindowA0ApproachOwned.approach_project]
    exact K.2.2.2.2

private theorem snoc_ind {α : Type} (P : List α → Prop) (h0 : P [])
    (hs : ∀ u e, P u → P (u ++ [e])) (w : List α) : P w := by
  have aux : ∀ v : List α, P v.reverse := by
    intro v
    induction v with
    | nil => exact h0
    | cons e u ih => rw [List.reverse_cons]; exact hs _ _ ih
  simpa using aux w.reverse

theorem approachRead_child {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (z : AState p c n) (u : Word n) (e : Fin n) :
    approachRead S z (wordNext u e)=AStep S (approachRead S z u) e := by
  simp [approachRead,wordNext,GGTiming.runMarks_append,GGTiming.runMarks]

theorem approachRead_good {p c n : Nat} {z0 : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (q : Trip (2*c))
    (z : AState p c n) (hz : ApproachGood z0 S J H q z) (w : Word n)
    (hw : Clean (fun u => AStop (approachRead S z u)) w) :
    ApproachGood z0 S J H q (approachRead S z w) := by
  induction w using snoc_ind with
  | h0 => exact hz
  | hs u e ih =>
    change Clean _ (wordNext u e) at hw
    obtain ⟨hclean,hfar⟩ := (clean_child _ u e).mp hw
    change ApproachGood _ _ _ _ _ (approachRead _ _ (wordNext u e))
    rw [approachRead_child]
    exact approach_step hn S J H q _ e (ih hclean) hfar

#print axioms approach_step
#print axioms approachRead_good

def postApproach {p c n : Nat} (z0 : Config p c n) (S : WindowA0Ledger.Scope n)
    (J : Fin n) (H : Nat) (q : Trip (2*c)) (y : WindowA0ClosedEntry.State p c n) : Prop :=
  WindowA0ClosedEntry.Admitted z0 S J H y ∧
    (WindowA0Ledger.done y.tag ∨
      (∃ i : Fin n, J=rightNeighbor i ∧ WindowA0GapOneTrace.FrameAt z0 S i q 0 y.tag) ∨
      WindowA0ApproachOwned.Physical J q y 1)

theorem boundary_dispatch {p c n : Nat} {z0 : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (q : Trip (2*c))
    (z : AState p c n) (hz : ApproachGood z0 S J H q z) (w : Word n)
    (hw : FirstExit (fun u => AStop (approachRead S z u)) w) :
    postApproach z0 S J H q (WindowA0GapOneJoin.physicalAfter S z.physical w) := by
  let y := approachRead S z w
  rw [←approachRead_actual S z w]
  change postApproach z0 S J H q y.physical
  obtain ⟨hA,G⟩ := approachRead_good hn S J H q z hz w hw.1
  refine ⟨hA,?_⟩
  by_cases hd : WindowA0Ledger.done y.physical.tag
  · exact .inl hd
  obtain ⟨phys,hgap⟩ := G.resolve_left hd
  have hworker : y.worker≤1 := hw.2.resolve_left hd
  by_cases h0 : y.worker=0
  · let i := rightNeighbor y.physical.tag.iSlot
    have hi : J=rightNeighbor i := by
      have L := (hA.resolve_left hd).1.fixedRight
      simpa [WindowA0IH.target,WindowA0ClosedEntry.cut,hgap h0,
        liftedSite_succ,liftedSite_zero,i] using L.symm
    exact .inr (.inl ⟨i,hi,WindowA0GapOneTrace.approached_frame
      S J H y.physical q hA hd (hgap h0) (h0 ▸ phys)⟩)
  · have h1 : y.worker=1 := by omega
    exact .inr (.inr (h1 ▸ phys))

/-- Original raw word approach clock, on the exact same prefix alphabet
used by both admission cases. -/
theorem approach_word_mean {p c n : Nat} {z0 : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (q : Trip (2*c))
    (z : AState p c n) (hz : ApproachGood z0 S J H q z) :
    IIDExpectedHittingTimeAtMost wordNext (fun w => AStop (approachRead S z w))
      [] (n*z.worker) := by
  intro t
  have h := WindowA0Bridge.word_cost_le (AStep S) AStop
    (fun w => AStop (approachRead S z w)) (approachRead S z)
    (approachRead_child S z) (fun _ h => h) t []
  rcases hz.2 with hd | ⟨hw,_⟩
  · rw [iidHitCost_of_target wordNext _ _ (show AStop (approachRead S z []) from .inl hd)]
    exact Nat.zero_le _
  · exact Nat.le_trans h (WindowA0ApproachOwned.expected_approach hn S J H q z hz.1 hw t)

#print axioms boundary_dispatch
#print axioms approach_word_mean

open WindowA0ReleaseCredit WindowA0AdjacentEntry

def adjStep {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (z : WindowA0ClosedEntry.State p c n) :=
  WindowA0RoutedRelease.next (p:=p) (c:=c) S.group S.iTag S.jTag
    (guardBase (WindowA0ClosedEntry.cut z).top) (mode z)

def adjDone {p c n : Nat} (z : WindowA0RoutedRelease.State p c n) : Prop := done z.2

def adjReserve : Phase → Nat
  | .waiting k => 3-k.val
  | _ => 0

def adjNominate {p c n : Nat} (z : WindowA0ClosedEntry.State p c n)
    (v : WindowA0RoutedRelease.State p c n) : Fin n :=
  match v.2 with
  | .waiting k => WindowA0Release.asked (guardBase (WindowA0ClosedEntry.cut z).top) (mode z) k
  | _ => z.tag.iSlot

theorem adjDrop {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (z : WindowA0ClosedEntry.State p c n) (v : WindowA0RoutedRelease.State p c n)
    (e : Fin n) (h : ¬adjDone v) :
    adjReserve (adjStep S z v e).2+(if e=adjNominate z v then 1 else 0)≤adjReserve v.2 := by
  cases hp : v.2 with
  | success | failed => exact (h (by simp [adjDone,done,hp])).elim
  | waiting k =>
    simp only [adjStep,WindowA0RoutedRelease.next,WindowA0Release.monitorNext, hp,adjNominate,adjReserve]
    by_cases he : e=WindowA0Release.asked (guardBase (WindowA0ClosedEntry.cut z).top) (mode z) k
    · subst e
      by_cases ha : WindowA0RoutedRelease.early S.group S.iTag S.jTag v.1
          (WindowA0Release.asked (guardBase (WindowA0ClosedEntry.cut z).top) (mode z) k)=true <;>
        by_cases hk : k.val+1<3 <;> simp [ha,hk] <;> have := k.isLt <;> omega
    · simp only [if_neg he]
      split
      · rename_i k' h'
        split at h'
        · cases h'
        · split at h'
          · cases h'
          · have hk : k=k' := Phase.waiting.inj h'
            subst k'
            omega
      · omega

theorem adjacent_word_mean {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (z : WindowA0ClosedEntry.State p c n) :
    IIDExpectedHittingTimeAtMost wordNext (fun w => adjDone (routedState S z w))
      [] (n*3) := by
  have sticky : ∀ v e, adjDone v → adjDone (adjStep S z v e) := by
    intro v e h
    cases hp : v.2 <;> simp_all [adjDone,done,adjStep,WindowA0RoutedRelease.next,WindowA0Release.monitorNext]
  have C := WindowA0Machine.mean_of_reachable_budget (adjStep S z) adjDone
    (fun _ => True) (fun y => adjReserve y.2) (adjNominate z)
    (fun _ _ _ _ => trivial) (fun y e _ h => adjDrop S z y e h)
    (z.tag.ledger,.waiting 0) trivial sticky
  intro t
  apply Nat.le_trans (WindowA0Bridge.word_cost_le (adjStep S z) adjDone
    _ (routedState S z) ?_ (fun _ h => h) t [])
  · exact C t
  · intro w e
    simp [routedState,adjStep,wordNext,GGTiming.runMarks_append,GGTiming.runMarks]

theorem adjacent_word_failure {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (z : WindowA0ClosedEntry.State p c n) (t : Nat) :
    216*terminalMass wordNext (fun w => adjDone (routedState S z w))
      (fun w => (routedState S z w).2=.failed) t []≤215*n^t := by
  rw [WindowA0GapOneWord.terminalMass_map wordNext (adjStep S z) (routedState S z)
    (by intro w e; simp [routedState,adjStep,wordNext,GGTiming.runMarks_append,GGTiming.runMarks])
    adjDone (fun v => v.2=.failed) t []]
  exact WindowA0RoutedRelease.failure_mass S.group S.iTag S.jTag
    (guardBase (WindowA0ClosedEntry.cut z).top) (mode z) z.tag.ledger t

#print axioms adjacent_word_mean
#print axioms adjacent_word_failure
end L4.WindowA0Leg
