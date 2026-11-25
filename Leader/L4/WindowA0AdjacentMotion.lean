import Leader.L4.WindowA0AdjacentEntry

/-! Track the actual top through arbitrary padded adjacent release words. -/
namespace L4.WindowA0AdjacentMotion
open WindowA0AdjacentEntry WindowA0Release WindowA0ClosedEntry GGStage

open WindowA0ReleaseCredit in
/-- Donor slot during a continuing release: paid script moves it
once on its first requested mark; unpaid script keeps it fixed. -/
def donorOffset (s : Kind) (k : Fin 3) : Nat :=
  match s with
  | .paid => if k.val=0 then 1 else 2
  | .unpaid => 1

open WindowA0ReleaseCredit in
private theorem waiting_cases {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (base : Fin n) (s : Kind) (r : WindowA0RoutedRelease.State p c n) (e : Fin n)
    (j : Fin 3)
    (h : (WindowA0RoutedRelease.next S.group S.iTag S.jTag base s r e).2=.waiting j) :
    ∃ k : Fin 3, r.2=.waiting k ∧
      WindowA0Route.routeTwo S.group S.iTag S.jTag r.1 e=.keep ∧
      ((e=asked base s k ∧ j.val=k.val+1) ∨
        (e∉WindowA0Return.guardLabels base ∧ j=k)) := by
  cases hr : r.2 with
  | success | failed => simp [WindowA0RoutedRelease.next,monitorNext,hr] at h
  | waiting k =>
    by_cases hk : WindowA0Route.routeTwo S.group S.iTag S.jTag r.1 e=.keep
    · refine ⟨k,rfl,hk,?_⟩
      simp only [WindowA0RoutedRelease.next,monitorNext,hr,WindowA0RoutedRelease.early,
        hk,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,if_false] at h
      by_cases he : e=asked base s k
      · rw [if_pos he] at h
        split at h
        · exact .inl ⟨he, congrArg Fin.val (Phase.waiting.inj h).symm⟩
        · cases h
      · rw [if_neg he] at h
        split at h
        · cases h
        · rename_i out
          exact .inr ⟨out,(Phase.waiting.inj h).symm⟩
    · simp [WindowA0RoutedRelease.next,monitorNext,hr,WindowA0RoutedRelease.early,hk] at h

private theorem inside_guard {n : Nat} (base : Fin n) (i : Nat) (hi : i<6) :
    liftedSite base i ∈ WindowA0Return.guardLabels base :=
  List.mem_map.2 ⟨i,List.mem_range.2 hi,rfl⟩

private theorem at_right {p c n : Nat} (x : Config p c n) (b : Fin n) (i : Nat)
    (hi : i+1<n) :
    step x (liftedSite b i) (liftedSite b (i+1))=
      (pairStep (x (liftedSite b i)) (x (liftedSite b (i+1)))).2 := by
  have he : liftedSite b (i+1)≠liftedSite b i := by
    intro E
    have := liftedSite_inj b hi (by omega) E
    omega
  simp only [step,←liftedSite_succ,he,if_false,if_true]

private theorem ref_unpaid_cold {p c n : Nat} (hn : 5≤n) (x : Config p c n)
    (b : Fin n) (hm : (x (liftedSite b 1)).mark=true) (hg : (x (liftedSite b 2)).leader=false)
    (hp : geometricPay (x (liftedSite b 1)) (x (liftedSite b 2))=false) :
    let r := WindowA0RoutedRelease.reference x b .unpaid 1
    geometricPay (r (liftedSite b 1)) (r (liftedSite b 2))=false := by
  rw [payer_exact _ _ hm hg] at hp
  have C : (x (liftedSite b 1)).stock=false ∧ (x (liftedSite b 1)).leader=false := by
    simpa only [payer,Bool.or_eq_false_iff] using hp
  obtain ⟨hs,hl⟩ := C
  dsimp [WindowA0RoutedRelease.reference,asked,offset]
  have h21 : liftedSite b 1≠liftedSite b 2 := by
    intro eq
    have := liftedSite_inj b (by omega : 1<n) (by omega : 2<n) eq
    omega
  have h31 : liftedSite b 1≠rightNeighbor (liftedSite b 2) := by
    rw [←liftedSite_succ]
    intro eq
    have := liftedSite_inj b (by omega : 1<n) (by omega : 2+1<n) eq
    omega
  rw [show step x (liftedSite b 2) (liftedSite b 1)=x (liftedSite b 1) from by simp [step,h21,h31]]
  cases H : geometricPay (x (liftedSite b 1)) (step x (liftedSite b 2) (liftedSite b 2))
  · rfl
  · have P := RearTrace.geometricPay_ready _ _ H
    simp [payer,hl,hs] at P

private theorem ref_paid_cold {p c n : Nat} (hn : 5≤n) (x : Config p c n)
    (b : Fin n) (hm : (x (liftedSite b 1)).mark=true) (hb : (x (liftedSite b 2)).stock=false)
    (hp : geometricPay (x (liftedSite b 1)) (x (liftedSite b 2))=true) :
    let r := WindowA0RoutedRelease.reference x b .paid 1
    geometricPay (r (liftedSite b 2)) (r (liftedSite b 3))=false := by
  dsimp [WindowA0RoutedRelease.reference,asked,offset]
  rw [at_right x b 1 (by omega)]
  have H := WindowA0Rows.marked_paid_empty _ _ hm hb hp
  have L := (pair_geometric_fields (x (liftedSite b 1)) (x (liftedSite b 2))).2.2
  simp only [hp,if_true] at L
  change geometricPay (pairStep (x (liftedSite b 1)) (x (liftedSite b 2))).2
      (step x (liftedSite b 1) (liftedSite b 3))=false
  cases h : geometricPay (pairStep (x (liftedSite b 1)) (x (liftedSite b 2))).2
      (step x (liftedSite b 1) (liftedSite b 3))
  · rfl
  · have P := RearTrace.geometricPay_ready _ _ h
    simp [payer,H.2,L.2] at P


private theorem keep_slot {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (u : WindowA0ClosedEntry.State p c n) (e : Fin n)
    (h : u.tag.reason=none)
    (hk : WindowA0Route.routeTwo S.group S.iTag S.jTag u.tag.ledger e=.keep) :
    (WindowA0ClosedEntry.next S u e).tag.iSlot=
      WindowFourHeadTrace.landing u.tag.ledger e u.tag.iSlot := by
  change (WindowA0Ledger.next S u.tag e).iSlot=_
  simp [WindowA0Ledger.next,h,hk]

private theorem keep_reason {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (u : WindowA0ClosedEntry.State p c n) (e : Fin n)
    (h : u.tag.reason=none)
    (hk : WindowA0Route.routeTwo S.group S.iTag S.jTag u.tag.ledger e=.keep) :
    (WindowA0ClosedEntry.next S u e).tag.reason=none := by
  change (WindowA0Ledger.next S u.tag e).reason=_
  simp [WindowA0Ledger.next,h,hk]

private theorem next_donor {p c n : Nat} (hn : 5≤n)
    (S : WindowA0Ledger.Scope n) (x : Config p c n) (b : Fin n) (s : Kind)
    (u : WindowA0ClosedEntry.State p c n) (e : Fin n) (j k : Fin 3)
    (hstart : u.tag.reason=none)
    (hkeep : WindowA0Route.routeTwo S.group S.iTag S.jTag u.tag.ledger e=.keep)
    (hslot : u.tag.iSlot=liftedSite b (donorOffset s k))
    (hview : Agree b u.tag.ledger.config (WindowA0RoutedRelease.reference x b s k))
    (mark : (x (liftedSite b 1)).mark=true)
    (ghost : (x (liftedSite b 2)).leader=false)
    (empty : (x (liftedSite b 2)).stock=false)
    (hpaid : s=.paid → geometricPay (x (liftedSite b 1)) (x (liftedSite b 2))=true)
    (hunpaid : s=.unpaid → geometricPay (x (liftedSite b 1)) (x (liftedSite b 2))=false)
    (nxt : (e=asked b s k ∧ j.val=k.val+1) ∨
      (e∉WindowA0Return.guardLabels b ∧ j=k)) :
    (WindowA0ClosedEntry.next S u e).tag.iSlot=liftedSite b (donorOffset s j) := by
  rw [keep_slot S u e hstart hkeep]
  rcases nxt with ⟨he,hj⟩|⟨out,rfl⟩
  · subst e
    have hk : k.val=0 ∨ k.val=1 := by have := j.isLt; omega
    rcases hk with hk|hk
    · have E : k=0 := Fin.ext hk
      have J : j=1 := Fin.ext (by omega)
      subst k; subst j
      cases s with
      | paid =>
        have he : asked b .paid 0=liftedSite b 1 := rfl
        have hh : u.tag.iSlot=liftedSite b 1 := hslot
        have hpay : geometricPay (u.tag.ledger.config (liftedSite b 1))
            (u.tag.ledger.config (rightNeighbor (liftedSite b 1)))=true := by
          have H₁ := hview 1 (by decide) (by decide)
          have H₂ := hview 2 (by decide) (by decide)
          rw [←liftedSite_succ,H₁,H₂]
          exact hpaid rfl
        rw [he,hh]
        rw [←liftedSite_succ] at hpay
        simp [WindowFourHeadTrace.landing,WindowFourHeadTrace.moves,hpay,donorOffset,←liftedSite_succ]
      | unpaid =>
        have he : asked b .unpaid 0=liftedSite b 2 := rfl
        have hh : u.tag.iSlot=liftedSite b 1 := hslot
        have hne : liftedSite b 2≠liftedSite b 1 := by
          intro eq
          have := liftedSite_inj b (by omega : 2<n) (by omega : 1<n) eq
          omega
        rw [he,hh]
        simp [WindowFourHeadTrace.landing,WindowFourHeadTrace.moves,hne,donorOffset]
    · have E : k=1 := Fin.ext hk
      have J : j=2 := Fin.ext (by omega)
      subst k; subst j
      cases s with
      | paid =>
        have he : asked b .paid 1=liftedSite b 2 := rfl
        have hh : u.tag.iSlot=liftedSite b 2 := hslot
        have hpay : geometricPay (u.tag.ledger.config (liftedSite b 2))
            (u.tag.ledger.config (rightNeighbor (liftedSite b 2)))=false := by
          rw [←liftedSite_succ,hview 2 (by decide) (by decide),hview 3 (by decide) (by decide)]
          exact ref_paid_cold hn x b mark empty (hpaid rfl)
        rw [he,hh]
        simp [WindowFourHeadTrace.landing,WindowFourHeadTrace.moves,hpay,donorOffset]
      | unpaid =>
        have he : asked b .unpaid 1=liftedSite b 1 := rfl
        have hh : u.tag.iSlot=liftedSite b 1 := hslot
        have hpay : geometricPay (u.tag.ledger.config (liftedSite b 1))
            (u.tag.ledger.config (rightNeighbor (liftedSite b 1)))=false := by
          rw [←liftedSite_succ,hview 1 (by decide) (by decide),hview 2 (by decide) (by decide)]
          exact ref_unpaid_cold hn x b mark ghost (hunpaid rfl)
        rw [he,hh]
        simp [WindowFourHeadTrace.landing,WindowFourHeadTrace.moves,hpay,donorOffset]
  · have hel : e≠u.tag.iSlot := by
      intro E
      apply out
      rw [E,hslot]
      apply inside_guard
      cases s
      · simp only [donorOffset]; split <;> decide
      · change 1<6; decide
    rw [show WindowFourHeadTrace.landing u.tag.ledger e u.tag.iSlot=u.tag.iSlot from by
      simp [WindowFourHeadTrace.landing,WindowFourHeadTrace.moves,hel]]
    exact hslot


open WindowA0ReleaseCredit in
/-- Exact donor identity and absence of a prior physical exit on every
continuing padded word. This does not assume a top-location oracle. -/
theorem waiting_donor_on_word {p c n : Nat} {initial : Config p c n} (hn : 5≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat)
    (z : WindowA0ClosedEntry.State p c n) (hz : Admitted initial S J H z)
    (ha : ¬WindowA0Ledger.done z.tag) (w : List (Fin n)) (k : Fin 3)
    (hw : (routedState S z w).2=.waiting k) :
    let u := GGTiming.runMarks (WindowA0ClosedEntry.next S) z w
    u.tag.reason=none ∧ u.tag.iSlot=liftedSite (guardBase (cut z).top) (donorOffset (mode z) k) := by
  let a := cut z
  let x := a.config
  let b := guardBase a.top
  let s := mode z
  let tick := WindowA0RoutedRelease.next (p:=p) (c:=c) S.group S.iTag S.jTag b s
  let F := WindowA0ClosedEntry.next (p:=p) (c:=c) S
  let G := fun (u : WindowA0ClosedEntry.State p c n) (k : Fin 3) =>
    u.tag.reason=none ∧ u.tag.iSlot=liftedSite b (donorOffset s k)
  have live := (hz.resolve_left ha).1
  have hmark : (x (liftedSite b 1)).mark=true := by
    rw [guard_donor]; exact live.markTop
  have hghost : (x (liftedSite b 2)).leader=false := by rw [guard_top]; exact live.topGhost
  have hemt : (x (liftedSite b 2)).stock=false := by
    rw [guard_top]
    simpa only [liftedSite_zero] using live.empty 0 live.gapPos
  have paid : s=.paid → geometricPay (x (liftedSite b 1)) (x (liftedSite b 2))=true := by
    intro he
    rw [guard_donor,guard_top]
    change (if geometricPay (x (incoming a.top 0)) (x a.top) then Kind.paid else Kind.unpaid)=_ at he
    split at he
    · assumption
    · cases he
  have unpaid : s=.unpaid → geometricPay (x (liftedSite b 1)) (x (liftedSite b 2))=false := by
    intro he
    rw [guard_donor,guard_top]
    change (if geometricPay (x (incoming a.top 0)) (x a.top) then Kind.paid else Kind.unpaid)=_ at he
    split at he
    · cases he
    · rename_i hf
      exact Bool.eq_false_iff.mpr hf
  have stepG (u : WindowA0ClosedEntry.State p c n) (φ : Phase) (e : Fin n)
      (old : ∀ k, φ=.waiting k → G u k)
      (hv : WindowA0RoutedRelease.View x b s (u.tag.ledger,φ)) (j : Fin 3)
      (hj : (tick (u.tag.ledger,φ) e).2=.waiting j) : G (F u e) j := by
    obtain ⟨k,hk,he,hc⟩ := waiting_cases S b s (u.tag.ledger,φ) e j hj
    exact ⟨keep_reason S u e (old k hk).1 he,
      next_donor hn S x b s u e j k (old k hk).1 he (old k hk).2 (hv k hk)
        hmark hghost hemt paid unpaid hc⟩
  have go (u : WindowA0ClosedEntry.State p c n) (φ : Phase)
      (old : ∀ k, φ=.waiting k → G u k)
      (hv : WindowA0RoutedRelease.View x b s (u.tag.ledger,φ)) :
      ∀ k, (GGTiming.runMarks tick (u.tag.ledger,φ) w).2=.waiting k →
        G (GGTiming.runMarks F u w) k := by
    clear hw k
    induction w generalizing u φ with
    | nil => exact old
    | cons e w ih =>
      let u' := F u e
      let φ' := (tick (u.tag.ledger,φ) e).2
      have pr : (u'.tag.ledger,φ')=tick (u.tag.ledger,φ) e := by
        apply Prod.ext
        · change (WindowA0Ledger.next S u.tag e).ledger=_
          rw [WindowA0Ledger.physical_step]; rfl
        · rfl
      have newView : WindowA0RoutedRelease.View x b s (u'.tag.ledger,φ') := by
        rw [pr]
        exact WindowA0RoutedRelease.view_step S.group S.iTag S.jTag b s x (u.tag.ledger,φ) e hv
      have hh := ih u' φ' (stepG u φ e old hv) newView
      rw [pr] at hh
      exact hh
  have begin : ∀ k : Fin 3, (.waiting 0 : Phase)=.waiting k → G z k := by
    intro k hk
    have E : k=0 := (Phase.waiting.inj hk).symm
    subst k
    have hreason : z.tag.reason=none := by
      cases h : z.tag.reason
      · rfl
      · exact (ha (by simp [WindowA0Ledger.done,h])).elim
    refine ⟨hreason,?_⟩
    have hb : donorOffset s 0=1 := by cases s <;> rfl
    rw [hb,guard_donor]
    apply FreshSeparation.succ_inj
    rw [incoming_right,liftedSite_zero]
    rfl
  exact go z (.waiting 0) begin
    (WindowA0RoutedRelease.view_start b s z.tag.ledger) k hw

open WindowA0ReleaseCredit in
/-- Actual third requested label is the then-current top. The previous
two requested marks and all outside padding are accounted for. -/
theorem kept_success_top {p c n : Nat} {initial : Config p c n} (hn : 5≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat)
    (z : WindowA0ClosedEntry.State p c n) (hz : Admitted initial S J H z)
    (ha : ¬WindowA0Ledger.done z.tag) (w : List (Fin n)) (e : Fin n) (k : Fin 3)
    (hw : (routedState S z w).2=.waiting k)
    (hkeep : WindowA0Route.routeTwo S.group S.iTag S.jTag (routedState S z w).1 e=.keep)
    (hs : (WindowA0RoutedRelease.next S.group S.iTag S.jTag
      (guardBase (cut z).top) (mode z) (routedState S z w) e).2=.success) :
    let u := GGTiming.runMarks (WindowA0ClosedEntry.next S) z w
    ¬WindowA0Ledger.done u.tag ∧ e=(cut u).top := by
  obtain ⟨hE,hK⟩ := WindowA0RoutedRelease.success_on_keep S.group S.iTag S.jTag _ _
    (routedState S z w) e k hw hkeep hs
  have hslot := waiting_donor_on_word hn S J H z hz ha w k hw
  refine ⟨by simp [WindowA0Ledger.done,hslot.1],?_⟩
  let b := guardBase (cut z).top
  let s := mode z
  change e=rightNeighbor (GGTiming.runMarks (WindowA0ClosedEntry.next S) z w).tag.iSlot
  rw [hslot.2,hE,←liftedSite_succ]
  have E : k=2 := Fin.ext hK
  subst k
  change asked b s 2=liftedSite b (donorOffset s 2+1)
  cases s <;> rfl

#print axioms waiting_donor_on_word
#print axioms kept_success_top

/-- A credited adjacent release on a kept mark is a genuine physical
release or matching door row on that same raw word. No caller-supplied
top/ghost assumption is needed beyond the admitted launch snapshot. -/
theorem kept_success_released {p c n : Nat} {initial : Config p c n} (hn : 5≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (q : FixedResidual.Trip (2*c))
    (z : WindowA0ClosedEntry.State p c n) (hz : Admitted initial S J H z)
    (ha : ¬WindowA0Ledger.done z.tag) (owned : WindowA0ApproachOwned.Physical J q z 1)
    (w : List (Fin n)) (e : Fin n) (k : Fin 3)
    (hw : (routedState S z w).2=.waiting k)
    (hkeep : WindowA0Route.routeTwo S.group S.iTag S.jTag (routedState S z w).1 e=.keep)
    (hs : (WindowA0RoutedRelease.next S.group S.iTag S.jTag
      (guardBase (cut z).top) (mode z) (routedState S z w) e).2=.success) :
    let u := GGTiming.runMarks (WindowA0ClosedEntry.next S) z w
    Released (u.tag.ledger.config e) (u.tag.ledger.config (rightNeighbor e)) q := by
  obtain ⟨hactive,htop⟩ := kept_success_top hn S J H z hz ha w e k hw hkeep hs
  exact routed_release_of_adjacent hn S J H q z hz ha owned w e k hw hkeep hs hactive htop

#print axioms kept_success_released
end L4.WindowA0AdjacentMotion
