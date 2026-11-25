import Leader.L4.WindowCappedEntry
import Leader.L4.DistinctLiteralClock

namespace L4.WindowCappedAdvance
open WindowA0ClosedEntry SevenTagCharge TripleRenewal FixedResidual
open RootedAssembly WindowFourHeadTrace WindowA0Route WindowA0Bridge WindowFiveStages

variable {p c n : Nat}
abbrev St (p c n : Nat) := WindowA0ClosedEntry.State p c n

def goal (x : St p c n) : Prop := WindowA0Ledger.done x.tag

theorem fixed_at {z : Config p c n} {S : WindowA0Ledger.Scope n}
    {J : Fin n} {H : Nat} {x : St p c n} (A : Admitted z S J H x)
    (G : ¬goal x) :
    FixedLive x.tag.iSlot (rightNeighbor x.tag.iSlot) (x.gap-1) false
      x.tag.ledger.config := by
  have L := (A.resolve_left G).1
  have T : GGStage.incoming (rightNeighbor x.tag.iSlot) 0=x.tag.iSlot := by
    apply FreshSeparation.succ_inj
    rw [GGStage.incoming_right,liftedSite_zero]
  have g : 0<x.gap := L.gapPos
  refine ⟨?_,L.topGhost,⟨?_,L.markRight,?_⟩,?_⟩
  · simpa only [cut,T] using L.markTop
  · have := L.noWrap
    change x.gap<n at this
    omega
  · intro j hj
    have h := L.openBonds j (by change j+1<x.gap; omega)
    exact fun h' => Bool.false_ne_true (h.symm.trans h')
  · have E := L.fixedRight
    change liftedSite (rightNeighbor x.tag.iSlot) x.gap=J at E
    rw [show x.gap-1+1=x.gap by omega,E]
    exact L.rightGhost

theorem gap_mono (S : WindowA0Ledger.Scope n) (x : St p c n) (e : Fin n) :
    (next S x e).gap≤x.gap := by
  change (if (WindowA0Ledger.next S x.tag e).reason.isSome then x.gap else
    x.gap-(if moves x.tag.ledger e x.tag.iSlot then 1 else 0)) ≤ x.gap
  split
  · exact Nat.le_refl _
  · exact Nat.sub_le _ _

theorem sticky_step (S : WindowA0Ledger.Scope n) (x : St p c n) (e : Fin n) (h : goal x) :
    goal (next S x e) := by
  change (WindowA0Ledger.next S x.tag e).reason.isSome=true
  rw [WindowA0Ledger.terminal_sticky S x.tag e h]
  exact h

theorem no_move {z : Config p c n} {S : WindowA0Ledger.Scope n}
    {J : Fin n} {H : Nat} {x : St p c n} {e : Fin n} (A : Admitted z S J H x)
    (G : ¬goal (next S x e)) (E : (next S x e).gap=x.gap) :
    (next S x e).tag.iSlot=x.tag.iSlot := by
  have G0 : ¬goal x := fun h => G (sticky_step S x e h)
  have L := A.resolve_left G0
  have hStart := L.2.1.2.1
  have g : 0<x.gap := L.1.gapPos
  have noPay : ¬moves x.tag.ledger e x.tag.iSlot := by
    intro h
    change ¬ (WindowA0Ledger.next S x.tag e).reason.isSome=true at G
    simp only [next,if_neg G,if_pos h] at E
    omega
  have K : routeTwo S.group S.iTag S.jTag x.tag.ledger e=.keep := by
    exact Classical.byContradiction (fun h => G ((WindowA0Ledger.physical_exit_iff S x.tag e hStart).mpr h))
  simp [next,WindowA0Ledger.next,hStart,K,landing,noPay]

theorem gap_word_le (S : WindowA0Ledger.Scope n) (x : St p c n) (w : Word n) :
    (GGTiming.runMarks (next S) x w).gap≤x.gap := by
  induction w generalizing x with
  | nil => exact Nat.le_refl _
  | cons e w ih => exact Nat.le_trans (ih (next S x e)) (gap_mono S x e)

theorem sticky_word (S : WindowA0Ledger.Scope n) (x : St p c n) (w : Word n) (h : goal x) :
    goal (GGTiming.runMarks (next S) x w) := by
  induction w generalizing x with
  | nil => exact h
  | cons e w ih => exact ih (next S x e) (sticky_step S x e h)

theorem slot_word {z : Config p c n} {S : WindowA0Ledger.Scope n}
    {J : Fin n} {H : Nat} (hn : 4≤n) (x : St p c n) (w : Word n)
    (A : Admitted z S J H x)
    (G : ¬goal (GGTiming.runMarks (next S) x w))
    (E : (GGTiming.runMarks (next S) x w).gap=x.gap) :
    (GGTiming.runMarks (next S) x w).tag.iSlot=x.tag.iSlot := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    let y := next S x e
    have G0 : ¬goal y := fun h => G (sticky_word S y w h)
    have h₁ := gap_mono S x e
    have h₂ := gap_word_le S y w
    have d : y.gap=x.gap := by
      change y.gap≤x.gap at h₁
      change (GGTiming.runMarks (next S) y w).gap=x.gap at E
      omega
    exact (ih y (close hn S J H x e A) G (E.trans d.symm)).trans (no_move A G0 d)

theorem leg {z : Config p c n} (S : WindowA0Ledger.Scope n)
    (J : Fin n) (H : Nat) (hn : 4≤n) (hc : 0<c) (x : St p c n)
    (A : Admitted z S J H x) (G : ¬goal x) :
    IIDExpectedHittingTimeAtMost wordNext
      (fun w => goal (GGTiming.runMarks (next S) x w) ∨
        (GGTiming.runMarks (next S) x w).gap<x.gap)
      [] (n*(8*(2*c+1)*(H+1))) := by
  have L := (A.resolve_left G).1
  have g : 0<x.gap := L.gapPos
  have bd : x.gap-1+1<n := by have h : x.gap<n := L.noWrap; omega
  let top := rightNeighbor x.tag.iSlot
  let F : Config p c n → Prop := FixedLive x.tag.iSlot top (x.gap-1) false
  obtain ⟨q,hq⟩ := DistinctLiteralClock.concreteFixedResidualClockEight
    x.tag.ledger.config x.tag.iSlot top (x.gap-1) false hn hc rfl bd L.mc L.cv (fixed_at A G)
  let f := fun w => (GGTiming.runMarks (next S) x w).tag.ledger.config
  have eqStep (w : Word n) (e : Fin n) : f (wordNext w e) = step (f w) e := by
    unfold f wordNext
    rw [GGTiming.runMarks_append]
    change (WindowA0Ledger.next S _ e).ledger.config=_
    rw [WindowA0Ledger.physical_step]
    rfl
  have stop (w : Word n) (hf : ¬F (f w)) :
      goal (GGTiming.runMarks (next S) x w) ∨
        (GGTiming.runMarks (next S) x w).gap<x.gap := by
    by_cases hh : goal (GGTiming.runMarks (next S) x w)
    · exact .inl hh
    · right
      have hm := gap_word_le S x w
      by_cases less : (GGTiming.runMarks (next S) x w).gap<x.gap
      · exact less
      have hnG := Nat.le_of_not_gt less
      have d := Nat.le_antisymm hm hnG
      have sl := slot_word hn x w A hh d
      have N := fixed_at (close_word hn S J H x w A) hh
      rw [sl,d] at N
      exact (hf N).elim
  intro t
  have hB : x.gap-1+2≤H+1 := by have h : x.gap≤H := L.bounded; omega
  exact Nat.le_trans (word_cost_le step (fun y => ¬F y) _ f eqStep stop t [])
    (Nat.le_trans (expected_of_countdown _ _ _ q t)
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left n
        (Nat.le_trans hq (Nat.mul_le_mul_left _ hB)))))

theorem drained_mean {z : Config p c n} (S : WindowA0Ledger.Scope n)
    (J : Fin n) (H : Nat) (hn : 4≤n) (hc : 0<c) (x : St p c n)
    (A : Admitted z S J H x) :
    IIDExpectedHittingTimeAtMost (next S) goal x (x.gap*(n*(8*(2*c+1)*(H+1)))) := by
  let B := n*(8*(2*c+1)*(H+1))
  generalize he : x.gap=g
  induction g using Nat.strongRecOn generalizing x with
  | ind g ih =>
    by_cases G : goal x
    · intro t
      rw [iidHitCost_of_target _ _ _ G]
      exact Nat.zero_le _
    let f := GGTiming.runMarks (next S) x
    let P := fun w => goal (f w) ∨ (f w).gap<x.gap
    let stage : Stage (next S) x :=
      ⟨Word n,[],wordNext,f,P,fun _ => True,rfl,
        fun w e => GGTiming.runMarks_append _ _ _ _,trivial,fun _ _ _ => trivial⟩
    have D := expected_with_preparation stage goal B ((g-1)*B)
      (leg S J H hn hc x A G) (by
        intro w _ hy nd
        change goal (f w) ∨ (f w).gap<x.gap at hy
        change ¬goal (f w) at nd
        have Sg : (f w).gap<g := he ▸ hy.resolve_left nd
        have q := ih (f w).gap Sg (f w) (close_word hn S J H x w A) rfl
        exact expected_mono q (Nat.mul_le_mul_right _ (by omega)))
    have L : 0<g := he ▸ (A.resolve_left G).1.gapPos
    apply expected_mono D
    change B+(g-1)*B≤g*B
    rw [Nat.add_comm,←Nat.succ_mul,show (g-1).succ=g by omega]
    exact Nat.le_refl _

#print axioms leg
#print axioms drained_mean
#print axioms fixed_at
#print axioms slot_word
end L4.WindowCappedAdvance
