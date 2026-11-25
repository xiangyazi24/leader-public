import Leader.L4.WindowA0AdjacentRetention
import Leader.L4.WindowA0GapOneJoin

/-! The matching-door branch of the three-hit adjacent release. -/
namespace L4.WindowA0AdjacentDoor
open FixedResidual WindowA0ClosedEntry WindowA0AdjacentEntry WindowA0AdjacentMotion
  WindowA0Release WindowA0GapOneJoin

private theorem reason_none {p c n : Nat} (x : WindowA0Ledger.State p c n)
    (h : ¬WindowA0Ledger.done x) : x.reason=none := by
  cases hr : x.reason with
  | none => rfl
  | some r => exact (h (by simp [WindowA0Ledger.done,hr])).elim

/-- On a genuine kept third service at the matching door, the very
same physical pair installs the exact next COUNT (or the physical
scoped exit takes precedence). No supplementary service is inserted. -/
theorem success_handoff {p c n : Nat} {initial : Config p c n} (hn : 5≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (q : Trip (2*c))
    (z : WindowA0ClosedEntry.State p c n) (hz : Admitted initial S J H z)
    (ha : ¬WindowA0Ledger.done z.tag) (owned : WindowA0ApproachOwned.Physical J q z 1)
    (hc : 0<2*c) (w : List (Fin n)) (e : Fin n) (k : Fin 3)
    (hw : (routedState S z w).2=.waiting k)
    (hs : (WindowA0RoutedRelease.next S.group S.iTag S.jTag
      (guardBase (cut z).top) (mode z) (routedState S z w) e).2=.success)
    (hg : (GGTiming.runMarks (WindowA0ClosedEntry.next S) z w).gap=1) :
    let y := GGTiming.runMarks (WindowA0ClosedEntry.next S) z (w++[e])
    WindowA0Ledger.done y.tag ∨ continues J q y := by
  let u := GGTiming.runMarks (WindowA0ClosedEntry.next S) z w
  let y := WindowA0ClosedEntry.next S u e
  rw [GGTiming.runMarks_append]
  change WindowA0Ledger.done y.tag ∨ continues J q y
  by_cases hey : WindowA0Ledger.done y.tag
  · exact .inl hey
  have active : ¬WindowA0Ledger.done u.tag := by
    have H' := (waiting_donor_on_word hn S J H z hz ha w k hw).1
    change u.tag.reason=none at H'
    simp [WindowA0Ledger.done,H']
  have hr := reason_none u.tag active
  have kept : WindowA0Route.routeTwo S.group S.iTag S.jTag u.tag.ledger e=.keep := by
    apply Classical.byContradiction
    intro bad
    exact hey ((WindowA0Ledger.physical_exit_iff S u.tag e hr).2 bad)
  have keep : WindowA0Route.routeTwo S.group S.iTag S.jTag (routedState S z w).1 e=.keep := by
    rw [project_word]
    exact kept
  have rel := kept_success_released hn S J H q z hz ha owned w e k hw keep hs
  have htop := (kept_success_top hn S J H z hz ha w e k hw keep hs).2
  change e=(cut u).top at htop
  have hU := close_word (by omega) S J H z w hz
  have L := (hU.resolve_left active).1
  have hJ : rightNeighbor e=J := by
    have G : (cut u).gap=1 := hg
    have f := L.fixedRight
    unfold WindowA0IH.target at f
    rw [G,liftedSite_succ,liftedSite_zero,←htop] at f
    exact f
  have hm : (u.tag.ledger.config e).mark=true := by
    have g : (cut u).gap=1 := hg
    have hh := L.markRight
    rw [g] at hh
    rw [htop]
    change ((cut u).config (cut u).top).mark=true
    simpa only [Nat.sub_self,liftedSite_zero] using hh
  have hneq : rightNeighbor e≠e := by
    intro E
    have f : liftedSite e 1=liftedSite e 0 := by rw [liftedSite_succ,liftedSite_zero,E]
    have bad := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) f
    omega
  have hI : e≠u.tag.iSlot := by
    intro E
    exact hneq (E ▸ htop.symm)
  have f := WindowA0XSweep.cut_keep_fields S u e hr hey
  have ytop : rightNeighbor y.tag.iSlot=e := by
    have zS : WindowA0XSweep.topShift u e=0 := by
      simp [WindowA0XSweep.topShift,WindowFourHeadTrace.moves,hI]
    have F := f.2.1
    rw [zS,liftedSite_zero] at F
    exact F.trans htop.symm
  have phy : y.tag.ledger.config=step u.tag.ledger.config e := f.1
  change Released (u.tag.ledger.config e) (u.tag.ledger.config (rightNeighbor e)) q at rel
  unfold Released at rel
  rw [if_pos hm] at rel
  have result : WindowA0GapOneTrace.DoorResult e q y.tag := by
    refine ⟨ytop,?_,?_,?_⟩
    · rw [phy]
      simpa only [step,if_pos rfl] using rel.1
    · rw [phy]
      simpa only [step,hneq,if_true,if_false] using rel.2.1
    · rw [phy]
      simpa only [step,hneq,if_true,if_false] using rel.2.2
  have hY : Admitted initial S J H y := close (by omega) S J H u e hU
  right
  rw [←hJ] at hY ⊢
  exact relaunch_exact (by omega) S e H y q hc hY hey result

#print axioms success_handoff
end L4.WindowA0AdjacentDoor
