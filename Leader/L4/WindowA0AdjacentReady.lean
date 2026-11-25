import Leader.L4.WindowA0AdjacentMotion
import Leader.L4.WindowA0ReturnEntry

/-! Actual ordinary release into the authenticated moving return invariant. -/
namespace L4.WindowA0AdjacentReady
open FixedResidual WindowA0ClosedEntry WindowA0Release

private theorem reason_none {p c n : Nat} (x : WindowA0Ledger.State p c n)
    (h : ¬WindowA0Ledger.done x) : x.reason=none := by
  cases hr : x.reason
  · rfl
  · exact (h (by simp [WindowA0Ledger.done,hr])).elim

private theorem post_interior_off {p c n : Nat} {J : Fin n} {H : Nat}
    {x : WindowA0IH.Cut p c n} (hx : WindowA0IH.Live J H x)
    (i : Nat) (h0 : 0<i) (hi : i<x.gap) :
    (x.config (liftedSite x.top i)).source=.off := by
  apply Classical.byContradiction
  intro bad
  have ed : rightNeighbor (liftedSite x.top (i-1))=liftedSite x.top i := by
    rw [←liftedSite_succ,show i-1+1=i by omega]
  have h := (hx.cv (liftedSite x.top (i-1)) (ed.symm ▸ bad)).2
  rw [hx.openBonds _ (by omega)] at h
  cases h

/-- If the third credited mark is an ordinary body row, its actual
output is Ready at distance one. The far T trail, matching source and
cold paid donor are the only pre-existing rail/source facts needed. -/
theorem body_ready {p c n : Nat} {z0 : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat)
    (u : WindowA0ClosedEntry.State p c n) (q : Trip (2*c))
    (ha : Admitted z0 S J H u) (hlive : ¬WindowA0Ledger.done u.tag)
    (hg : 1<u.gap)
    (hrel : Released ((cut u).config (cut u).top)
      ((cut u).config (rightNeighbor (cut u).top)) q)
    (keep : ¬WindowA0Ledger.done (WindowA0ClosedEntry.next S u (cut u).top).tag)
    (trail : ∀ i, 2≤i → i<u.gap → ((cut u).config (liftedSite (cut u).top i)).rail=.t)
    (source : ((cut u).config J).source=waitingFor q)
    (cold : ((cut u).config u.tag.iSlot).leader=false ∧ ((cut u).config u.tag.iSlot).stock=false) :
    WindowA0ReturnEntry.Ready z0 S J H (WindowA0ClosedEntry.next S u (cut u).top) q 1 false := by
  let x := cut u
  let e := x.top
  let v := WindowA0ClosedEntry.next S u e
  let y := cut v
  have L := (ha.resolve_left hlive).1
  have hA : x.gap=u.gap := rfl
  have D := close hn S J H u e ha
  have N := (D.resolve_left keep).1
  have hne : rightNeighbor e≠e := by
    intro h
    have E : liftedSite e 1=liftedSite e 0 := by rw [liftedSite_succ,liftedSite_zero,h]
    have := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) E
    omega
  have hI : e≠u.tag.iSlot := by
    intro e'
    have E := congrArg rightNeighbor e'
    exact hne E
  have zm : WindowA0XSweep.topShift u e=0 := by
    simp [WindowA0XSweep.topShift,WindowFourHeadTrace.moves,hI]
  have hr := reason_none u.tag hlive
  have hf := WindowA0XSweep.cut_keep_fields S u e hr keep
  have cfg : y.config=step x.config e := hf.1
  have top : y.top=x.top := by simpa only [zm,liftedSite_zero] using hf.2.1
  have gap : v.gap=u.gap := by
    have G : y.gap=x.gap := by simpa only [zm,Nat.sub_zero] using hf.2.2
    exact G
  have hmark : (x.config e).mark=false := by
    have W := L.openBonds 0 (show 0+1<x.gap from by omega)
    simpa only [liftedSite_zero] using W
  have hrelease : (pairStep (x.config e) (x.config (rightNeighbor e))).1.rail=.e ∧
      (pairStep (x.config e) (x.config (rightNeighbor e))).2.rail=inward q := by
    change Released (x.config e) (x.config (rightNeighbor e)) q at hrel
    simpa only [Released,show (x.config e).mark=false from hmark,Bool.false_eq_true,if_false] using hrel
  have edgeOff (i : Nat) (h2 : 2≤i) (hi : i<n) :
      liftedSite x.top i≠e ∧ liftedSite x.top i≠rightNeighbor e := by
    constructor
    · intro bad
      have F : liftedSite x.top i=liftedSite x.top 0 := bad.trans (liftedSite_zero _).symm
      have := liftedSite_inj x.top hi (by omega : 0<n) F
      omega
    · intro bad
      have F : liftedSite x.top i=liftedSite x.top 1 :=
        bad.trans ((liftedSite_succ x.top 0).trans (congrArg rightNeighbor (liftedSite_zero _))).symm
      have := liftedSite_inj x.top hi (by omega : 1<n) F
      omega
  have hLead : liftedSite x.top 1=rightNeighbor e :=
    (liftedSite_succ x.top 0).trans (congrArg rightNeighbor (liftedSite_zero _))
  refine ⟨D,reason_none v.tag keep,by decide,⟨by rwa [gap],?_⟩,?_,?_,?_⟩
  · intro i hi
    change (y.config (liftedSite y.top i)).rail=railShape 1 (inward q) i
    have hi' : i<u.gap := by rwa [gap] at hi
    rw [cfg,top]
    cases i with
    | zero =>
      simpa [liftedSite_zero,step,railShape,e] using hrelease.1
    | succ i =>
      cases i with
      | zero => simpa [hLead,step,hne,railShape] using hrelease.2
      | succ i =>
        have H' : i+2<n := by have W : x.gap<n := L.noWrap; omega
        obtain ⟨A,B⟩ := edgeOff (i+2) (by omega) H'
        have hc := trail (i+2) (by omega) (by omega)
        simpa [step,A,B,railShape,
          show ¬ i+2<1 by omega,show i+2≠1 by omega] using hc
  · intro i h0 hi
    exact post_interior_off N i h0 hi
  · change (y.config J).source=waitingFor q
    have G : liftedSite x.top x.gap=J := L.fixedRight
    have K := edgeOff x.gap (by omega) L.noWrap
    rw [G] at K
    rw [cfg]
    simpa [step,K.1,K.2] using source
  · intro _
    have hk : WindowA0Route.routeTwo S.group S.iTag S.jTag u.tag.ledger e=.keep := by
      apply Classical.byContradiction
      intro bad
      exact keep ((WindowA0Ledger.physical_exit_iff S u.tag e hr).2 bad)
    have same : v.tag.iSlot=u.tag.iSlot := by
      change (WindowA0Ledger.next S u.tag e).iSlot=u.tag.iSlot
      simp [WindowA0Ledger.next,hr,hk,WindowFourHeadTrace.landing,WindowFourHeadTrace.moves,hI]
    have nr : u.tag.iSlot≠rightNeighbor e := by
      have E : liftedSite x.top (n-1)=u.tag.iSlot := by
        change liftedSite x.top (n-1)=_
        apply FreshSeparation.succ_inj
        rw [←liftedSite_succ,show n-1+1=n by omega,liftedSite_full]
        rfl
      rw [←E,←hLead]
      intro bad
      have := liftedSite_inj x.top (by omega : n-1<n) (by omega : 1<n) bad
      omega
    change (y.config v.tag.iSlot).leader=false ∧ (y.config v.tag.iSlot).stock=false
    rw [cfg,same]
    simpa [step,Ne.symm hI,nr] using cold

#print axioms body_ready

open WindowA0AdjacentEntry WindowA0AdjacentMotion

private def coldSite {p c : Nat} (u : Site p c) : Prop :=
  u.leader=false ∧ u.stock=false

private theorem cold_left {p c : Nat} (u v : Site p c)
    (hm : u.mark=true) (h : coldSite u) : coldSite (pairStep u v).1 :=
  ⟨(pair_geometric_fields u v).2.1.trans h.1,
    WindowA0Drained.marked_left_no_injection u v hm h.1 h.2⟩

private theorem at_right {p c n : Nat} (x : Config p c n) (b : Fin n) (i : Nat)
    (hi : i+1<n) :
    step x (liftedSite b i) (liftedSite b (i+1))=
      (pairStep (x (liftedSite b i)) (x (liftedSite b (i+1)))).2 := by
  have he : liftedSite b (i+1)≠liftedSite b i := by
    intro E
    have := liftedSite_inj b hi (by omega) E
    omega
  simp only [step,←liftedSite_succ,he,if_false,if_true]

private theorem cold_reference {p c n : Nat} (hn : 5≤n) (x : Config p c n)
    (b : Fin n) (s : Kind)
    (hm : (x (liftedSite b 1)).mark=true)
    (hg : (x (liftedSite b 2)).leader=false)
    (hb : (x (liftedSite b 2)).stock=false)
    (hp : s=.paid → geometricPay (x (liftedSite b 1)) (x (liftedSite b 2))=true)
    (hu : s=.unpaid → geometricPay (x (liftedSite b 1)) (x (liftedSite b 2))=false) :
    coldSite (WindowA0RoutedRelease.reference x b s 2 (liftedSite b (donorOffset s 2))) := by
  cases s with
  | paid =>
    let u := x (liftedSite b 1)
    let v := x (liftedSite b 2)
    let w := (pairStep u v).2
    have l := (pair_geometric_fields u v).2.2
    have m := (covered_pair_marks u v (fun _ => hm))
    have H : geometricPay u v=true := hp rfl
    simp only [H,if_true] at l m
    have hC : coldSite w := ⟨l.2,(WindowA0Rows.marked_paid_empty u v hm hb H).2⟩
    change coldSite (step (step x (liftedSite b 1)) (liftedSite b 2) (liftedSite b 2))
    simp only [step,if_pos rfl] at *
    -- Use the actual first selected pair, not a simultaneous switch.
    have W := at_right x b 1 (by omega)
    change coldSite (pairStep
      (step x (liftedSite b 1) (liftedSite b 2))
      (step x (liftedSite b 1) (rightNeighbor (liftedSite b 2)))).1
    rw [W]
    exact cold_left _ _ m.2.2 hC
  | unpaid =>
    have hp' := hu rfl
    rw [payer_exact _ _ hm hg] at hp'
    have hC : coldSite (x (liftedSite b 1)) := by
      have H : (x (liftedSite b 1)).stock=false ∧ (x (liftedSite b 1)).leader=false := by
        simpa only [payer,Bool.or_eq_false_iff] using hp'
      exact ⟨H.2,H.1⟩
    have h21 : liftedSite b 1≠liftedSite b 2 := by
      intro eq
      have := liftedSite_inj b (by omega : 1<n) (by omega : 2<n) eq
      omega
    have h31 : liftedSite b 1≠rightNeighbor (liftedSite b 2) := by
      rw [←liftedSite_succ]
      intro eq
      have := liftedSite_inj b (by omega : 1<n) (by omega : 2+1<n) eq
      omega
    have H : step x (liftedSite b 2) (liftedSite b 1)=x (liftedSite b 1) := by
      simp [step,h21,h31]
    change coldSite (step (step x (liftedSite b 2)) (liftedSite b 1) (liftedSite b 1))
    simp only [step,if_pos rfl]
    change coldSite (pairStep
      (step x (liftedSite b 2) (liftedSite b 1))
      (step x (liftedSite b 2) (rightNeighbor (liftedSite b 1)))).1
    rw [H]
    exact cold_left _ _ hm hC

/-- The matched two preceding guarded requests left the actual incoming
top donor cold. The argument survives arbitrary permitted padding,
using the checked guard view and the actual donor observer. -/
theorem waiting_cold {p c n : Nat} {initial : Config p c n} (hn : 5≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat)
    (z : WindowA0ClosedEntry.State p c n) (hz : Admitted initial S J H z)
    (ha : ¬WindowA0Ledger.done z.tag) (w : List (Fin n))
    (hw : (routedState S z w).2=.waiting 2) :
    let u := GGTiming.runMarks (WindowA0ClosedEntry.next S) z w
    ((cut u).config u.tag.iSlot).leader=false ∧ ((cut u).config u.tag.iSlot).stock=false := by
  let a := cut z
  let x := a.config
  let b := guardBase a.top
  let s := mode z
  let i := donorOffset s 2
  let u := GGTiming.runMarks (WindowA0ClosedEntry.next S) z w
  have L := (hz.resolve_left ha).1
  have hm : (x (liftedSite b 1)).mark=true := by rw [guard_donor]; exact L.markTop
  have hg : (x (liftedSite b 2)).leader=false := by rw [guard_top]; exact L.topGhost
  have hb : (x (liftedSite b 2)).stock=false := by
    rw [guard_top]; simpa only [liftedSite_zero] using L.empty 0 L.gapPos
  have h1 : 1≤i := by unfold i; cases s <;> decide
  have h5 : i≤5 := by unfold i; cases s <;> decide
  have hp : s=.paid → geometricPay (x (liftedSite b 1)) (x (liftedSite b 2))=true := by
    intro h
    rw [guard_donor,guard_top]
    change (if geometricPay (x (GGStage.incoming a.top 0)) (x a.top) then Kind.paid else Kind.unpaid)=.paid at h
    split at h
    · assumption
    · cases h
  have hu : s=.unpaid → geometricPay (x (liftedSite b 1)) (x (liftedSite b 2))=false := by
    intro h
    rw [guard_donor,guard_top]
    change (if geometricPay (x (GGStage.incoming a.top 0)) (x a.top) then Kind.paid else Kind.unpaid)=.unpaid at h
    split at h
    · cases h
    · rename_i E
      exact Bool.eq_false_iff.mpr E
  have C := cold_reference hn x b s hm hg hb hp hu
  have hv := WindowA0RoutedRelease.view_run S.group S.iTag S.jTag b s z.tag.ledger w
  have eq := hv 2 hw i h1 h5
  have hs := (waiting_donor_on_word hn S J H z hz ha w 2 hw).2
  change coldSite (u.tag.ledger.config u.tag.iSlot)
  rw [hs]
  change coldSite (u.tag.ledger.config (liftedSite b i))
  have E := project_word S z w
  change (routedState S z w).1=u.tag.ledger at E
  change (routedState S z w).1.config (liftedSite b i)=
    WindowA0RoutedRelease.reference x b s 2 (liftedSite b i) at eq
  rw [←E,eq]
  exact C

#print axioms waiting_cold

/-- Same-word ordinary release handoff. Remaining assumptions are the
far T suffix and the original waiting source on the kept premark;
bankruptcy of the local script or a real scoped exit cannot masquerade
as a Ready result. A door output is deliberately outside this theorem. -/
theorem kept_body_ready {p c n : Nat} {initial : Config p c n} (hn : 5≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (q : Trip (2*c))
    (z : WindowA0ClosedEntry.State p c n) (hz : Admitted initial S J H z)
    (ha : ¬WindowA0Ledger.done z.tag) (owned : WindowA0ApproachOwned.Physical J q z 1)
    (w : List (Fin n)) (e : Fin n) (k : Fin 3)
    (hw : (routedState S z w).2=.waiting k)
    (hkeep : WindowA0Route.routeTwo S.group S.iTag S.jTag (routedState S z w).1 e=.keep)
    (hs : (WindowA0RoutedRelease.next S.group S.iTag S.jTag
      (guardBase (cut z).top) (mode z) (routedState S z w) e).2=.success)
    (hg : 1<(GGTiming.runMarks (WindowA0ClosedEntry.next S) z w).gap)
    (trail : let u := GGTiming.runMarks (WindowA0ClosedEntry.next S) z w
      ∀ i, 2≤i → i<u.gap → ((cut u).config (liftedSite (cut u).top i)).rail=.t)
    (source : let u := GGTiming.runMarks (WindowA0ClosedEntry.next S) z w
      ((cut u).config J).source=waitingFor q) :
    WindowA0ReturnEntry.Ready initial S J H
      (GGTiming.runMarks (WindowA0ClosedEntry.next S) z (w++[e])) q 1 false := by
  let u := GGTiming.runMarks (WindowA0ClosedEntry.next S) z w
  have hR := kept_success_released hn S J H q z hz ha owned w e k hw hkeep hs
  obtain ⟨hactive,hto⟩ := kept_success_top hn S J H z hz ha w e k hw hkeep hs
  have hA := WindowA0ClosedEntry.close_word (by omega) S J H z w hz
  have hK : ¬WindowA0Ledger.done (WindowA0ClosedEntry.next S u e).tag := by
    have hnone := reason_none u.tag hactive
    change ¬WindowA0Ledger.done (WindowA0Ledger.next S u.tag e)
    rw [WindowA0Ledger.physical_exit_iff S u.tag e hnone]
    have eq := project_word S z w
    change (routedState S z w).1=u.tag.ledger at eq
    rw [←eq]
    exact fun h => h hkeep
  obtain ⟨_,hk⟩ := WindowA0RoutedRelease.success_on_keep S.group S.iTag S.jTag _ _
    (routedState S z w) e k hw hkeep hs
  have hk' : k=2 := Fin.ext hk
  subst k
  have cold := waiting_cold hn S J H z hz ha w hw
  rw [GGTiming.runMarks_append]
  change WindowA0ReturnEntry.Ready initial S J H (WindowA0ClosedEntry.next S u e) q 1 false
  change Released ((cut u).config e) ((cut u).config (rightNeighbor e)) q at hR
  rw [hto] at hR hK ⊢
  exact body_ready (by omega) S J H u q hA hactive hg hR hK trail source cold

#print axioms kept_body_ready

/-- The conservative paper bit marks that the refill is not being
used as an extra credit assumption. It does not assert available
stock; the literal cold witness can safely be forgotten. -/
theorem ready_refilled_conservative {p c n H d : Nat} {initial : Config p c n}
    {S : WindowA0Ledger.Scope n} {J : Fin n} {u : WindowA0ClosedEntry.State p c n}
    {q : Trip (2*c)} (h : WindowA0ReturnEntry.Ready initial S J H u q d false) :
    WindowA0ReturnEntry.Ready initial S J H u q d true :=
  { h with coldBeforeRefill := fun h' => Bool.noConfusion h' }

#print axioms ready_refilled_conservative
end L4.WindowA0AdjacentReady
