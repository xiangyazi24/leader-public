import Leader.L4.WindowA0ApproachOwned
import Leader.L4.WindowA0RoutedRelease

/-! The literal release snapshot at the owned approach's first adjacency. -/
namespace L4.WindowA0AdjacentEntry
open FixedResidual GGStage WindowA0ClosedEntry WindowA0ApproachOwned WindowA0Release WindowA0Machine

/-- Guard origin is two sites behind the actual old top. -/
def guardBase {n : Nat} (top : Fin n) : Fin n :=
  RearTrace.predecessor (RearTrace.predecessor top)

theorem guard_top {n : Nat} (top : Fin n) : liftedSite (guardBase top) 2=top := by
  rw [show 2=1+1 by decide, liftedSite_succ, show liftedSite (guardBase top) 1=
    RearTrace.predecessor top by simp [guardBase,liftedSite_succ,liftedSite_zero,RearTrace.right_predecessor],
    RearTrace.right_predecessor]

theorem guard_donor {n : Nat} (top : Fin n) : liftedSite (guardBase top) 1=incoming top 0 := by
  apply FreshSeparation.succ_inj
  rw [←liftedSite_succ,guard_top,incoming_right,liftedSite_zero]

theorem guard_worker {n : Nat} (top : Fin n) : liftedSite (guardBase top) 3=liftedSite top 1 := by
  rw [show 3=2+1 by decide,liftedSite_succ,guard_top,liftedSite_succ,liftedSite_zero]

theorem guard_next {n : Nat} (top : Fin n) : liftedSite (guardBase top) 4=liftedSite top 2 := by
  rw [show 4=3+1 by decide,liftedSite_succ,guard_worker,←liftedSite_succ]

private theorem native_payer_eq {p c : Nat} (u v : Site p c) :
    payer (native (materialize u v) v).1=payer u := by
  have hm : payer (materialize u v)=payer u := by unfold materialize; split <;> rfl
  have hf (a : Site p c) : payer (fireInitiator a)=payer a := by
    unfold fireInitiator; split <;> rfl
  have hi (a b : Site p c) : payer (impact a b).1=payer a := by
    unfold impact; split <;> (try split) <;> rfl
  have hb (g : Bool) (a b : Site p c) : payer (followerBullet g a b).1=payer a := by
    unfold followerBullet; split <;> (try split) <;> rfl
  unfold native
  have p := hi (fireInitiator (materialize u v)) (fireResponder v)
  generalize h : impact (fireInitiator (materialize u v)) (fireResponder v)=z at p ⊢
  rcases z with ⟨a,b⟩
  exact (hb (pinned a b) a b).trans (p.trans ((hf _).trans hm))

/-- A marked donor into a ghost pays on this mark iff it already
holds stock or is living. Thus a disabled donor is genuinely cold. -/
theorem payer_exact {p c : Nat} (u v : Site p c)
    (hm : u.mark=true) (hg : v.leader=false) :
    geometricPay u v=payer u := by
  have a : (materialize u v).mark=true := by simp [materialize,hm]
  have b := (FreshEpochAuthentication.native_preserves_mark (materialize u v) v).trans a
  have c := FreshEpochAuthentication.old_follower_native (materialize u v) v hg
  simp [geometricPay,b,c,native_payer_eq]

private theorem cold_of_no_pay {p c : Nat} (u v : Site p c)
    (hm : u.mark=true) (hg : v.leader=false) (h : geometricPay u v=false) :
    u.leader=false ∧ u.stock=false := by
  rw [payer_exact u v hm hg] at h
  simp [payer,Bool.or_eq_false_iff] at h
  exact ⟨h.2,h.1⟩

private theorem ghost {p c n : Nat} {J : Fin n} {H : Nat}
    {x : WindowA0IH.Cut p c n} (h : WindowA0IH.Live J H x) (i : Nat)
    (hi : i≤x.gap) : (x.config (liftedSite x.top i)).leader=false := by
  by_cases he : i=x.gap
  · rw [he]
    change (x.config (WindowA0IH.target x)).leader=false
    rw [h.fixedRight]
    exact h.rightGhost
  cases i with
  | zero => simpa only [liftedSite_zero] using h.topGhost
  | succ k =>
    apply Bool.eq_false_iff.mpr
    intro hl
    have hM := h.mc (liftedSite x.top k) (.inl (by rwa [←liftedSite_succ]))
    have hZ := h.openBonds k (by omega)
    rw [hZ] at hM
    cases hM

private theorem ordinary_flags {p c n : Nat} {J : Fin n} {H : Nat}
    {x : WindowA0IH.Cut p c n} (h : WindowA0IH.Live J H x) (i : Nat)
    (hi : i+1<x.gap) :
    (x.config (liftedSite x.top i)).mark=false ∧
      (x.config (liftedSite x.top (i+1))).residue=
        nextResidue (x.config (liftedSite x.top i)).residue ∧
      (x.config (liftedSite x.top (i+1))).source=.off := by
  refine ⟨h.openBonds i hi,?_,?_⟩
  · apply Classical.byContradiction
    intro bad
    have H := h.mc (liftedSite x.top i) (.inr (by rwa [←liftedSite_succ]))
    rw [h.openBonds i hi] at H
    cases H
  · apply Classical.byContradiction
    intro bad
    have H := (h.cv (liftedSite x.top i) (by rwa [←liftedSite_succ])).2
    rw [h.openBonds i hi] at H
    cases H

private theorem cold_rail {Q : Nat} (q : Trip Q) (r : Rail) (h : Writable q r) :
    match q with | .init => r≠.x | .count _ => r=.e ∨ r=.t := by
  cases q <;> exact h

/-- Old-pair branch choice. Competing guard marks may spoil the
script; outside marks still execute on the physical ring. -/
def mode {p c n : Nat} (z : WindowA0ClosedEntry.State p c n) : Kind :=
  let x := cut z
  if geometricPay (x.config (incoming x.top 0)) (x.config x.top) then .paid else .unpaid

/-- Canonical snapshot supplies the exact isolated-reference premise
of the routed release theorem. The paid third service uses a real
door at gap two and an ordinary trail receiver at larger gaps. -/
theorem reference_of_adjacent {p c n : Nat} {initial : Config p c n} (hn : 5≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (q : Trip (2*c))
    (z : WindowA0ClosedEntry.State p c n) (hz : Admitted initial S J H z)
    (ha : ¬WindowA0Ledger.done z.tag) (h : Physical J q z 1) :
    let x := (cut z).config
    let b := guardBase (cut z).top
    let s := mode z
    let y := WindowA0RoutedRelease.reference x b s 2
    let r := asked b s 2
    (y r).leader=true ∨ Released (y r) (y (rightNeighbor r)) q := by
  let a := cut z
  let x := a.config
  let b := guardBase a.top
  have L := (hz.resolve_left ha).1
  have hkg : 1<a.gap := h.2.inside
  have G : a.gap=z.gap := rfl
  have Z : (cut z).gap=a.gap := rfl
  have S₀ : liftedSite b 1=incoming a.top 0 := guard_donor a.top
  have S₁ : liftedSite b 2=a.top := guard_top a.top
  have S₂ : liftedSite b 3=liftedSite a.top 1 := guard_worker a.top
  have S₃ : liftedSite b 4=liftedSite a.top 2 := guard_next a.top
  have hMark : (x (liftedSite b 1)).mark=true := by rw [S₀]; exact L.markTop
  have hTop : (x (liftedSite b 2)).leader=false := by rw [S₁]; exact L.topGhost
  have hEmpty : (x (liftedSite b 2)).stock=false := by
    rw [S₁]
    simpa only [liftedSite_zero] using L.empty 0 (by omega)
  have hWorker : (x (liftedSite b 3)).leader=false := by rw [S₂]; exact ghost L 1 (by omega)
  have hwEmpty : (x (liftedSite b 3)).stock=false := by rw [S₂]; exact L.empty 1 hkg
  have hToken : (x (liftedSite b 3)).rail=outward q := by rw [S₂]; exact h.2.worker
  have hCold : Writable q (x (liftedSite b 2)).rail := by
    rw [S₁]
    have R := h.2.ahead 0 (by decide)
    change Writable q (x (liftedSite a.top 0)).rail at R
    rwa [liftedSite_zero] at R
  have hOrd := ordinary_flags L 0 (by omega : 0+1<a.gap)
  have hB : (x (liftedSite b 2)).mark=false := by
    rw [S₁]
    simpa only [liftedSite_zero] using hOrd.1
  have hRes : (x (liftedSite b 3)).residue=nextResidue (x (liftedSite b 2)).residue := by
    rw [S₁,S₂]
    simpa only [liftedSite_zero] using hOrd.2.1
  have hOff : (x (liftedSite b 3)).source=.off := by rw [S₂]; exact hOrd.2.2
  have hThird : (x (liftedSite b 4)).leader=false := by rw [S₃]; exact ghost L 2 (by omega)
  have hPort : LastPort (x (liftedSite b 3)) (x (liftedSite b 4)) q := by
    rw [S₂,S₃]
    by_cases e : a.gap=2
    · refine .door ?_ ?_
      · have R : a.gap-1=1 := by omega
        rw [←R]; exact L.markRight
      · have R : liftedSite a.top 2=J := by
          rw [←e]
          exact L.fixedRight
        rw [R]
        exact h.1
    · obtain ⟨hM,hR,hO⟩ := ordinary_flags L 1 (by omega : 1+1<a.gap)
      exact .body hM hR hO (.inr (h.2.trail 2 (by decide) (by omega)))
  change let y := WindowA0RoutedRelease.reference x b (mode z) 2
    let r := asked b (mode z) 2
    (y r).leader=true ∨ Released (y r) (y (rightNeighbor r)) q
  by_cases hp : geometricPay (x (liftedSite b 1)) (x (liftedSite b 2))=true
  · have e : mode z=.paid := by
      have R := hp
      rw [S₀,S₁] at R
      change (if geometricPay (x (incoming a.top 0)) (x a.top) then Kind.paid else Kind.unpaid)=_
      simp [R]
    rw [e]
    dsimp only
    have he : rightNeighbor (asked b .paid 2)=liftedSite b 4 := (liftedSite_succ b 3).symm
    rw [he]
    exact paid_ring_release hn x b q hMark hp hEmpty hWorker hwEmpty hToken hThird hPort
  · have hp' := Bool.eq_false_iff.mpr hp
    obtain ⟨hal,has⟩ := cold_of_no_pay _ _ hMark hTop hp'
    have e : mode z=.unpaid := by
      have R := hp'
      rw [S₀,S₁] at R
      change (if geometricPay (x (incoming a.top 0)) (x a.top) then Kind.paid else Kind.unpaid)=_
      simp [R]
    rw [e]
    dsimp only
    have he : rightNeighbor (asked b .unpaid 2)=liftedSite b 3 := (liftedSite_succ b 2).symm
    rw [he]
    exact unpaid_ring_release hn x b q hMark hal has hB hTop hEmpty hWorker hwEmpty hRes hOff hToken
      (by cases q <;> exact hCold)

#print axioms reference_of_adjacent

/-- Six distinct physical competitors whenever the ring has at least
six sites. This proof also covers guard wrap-around at residue zero. -/
theorem guard_nodup {n : Nat} (hn : 6≤n) (top : Fin n) :
    (WindowA0Return.guardLabels (guardBase top)).Nodup := by
  unfold WindowA0Return.guardLabels List.Nodup
  apply List.pairwise_map.2
  apply List.Pairwise.imp_of_mem _ List.nodup_range
  intro i j hi hj neq eq
  exact neq (liftedSite_inj (guardBase top) (by have := List.mem_range.1 hi; omega)
    (by have := List.mem_range.1 hj; omega) eq)

/-- Actual same-word release state from the admitted snapshot. -/
def routedState {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (z : WindowA0ClosedEntry.State p c n) (w : List (Fin n)) :
    WindowA0RoutedRelease.State p c n :=
  GGTiming.runMarks (WindowA0RoutedRelease.next S.group S.iTag S.jTag
    (guardBase (cut z).top) (mode z)) (z.tag.ledger,.waiting 0) w

private theorem project_word_aux {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (z : WindowA0ClosedEntry.State p c n)
    (state : WindowA0RoutedRelease.State p c n) (w : List (Fin n)) :
    (GGTiming.runMarks (WindowA0RoutedRelease.next S.group S.iTag S.jTag
      (guardBase (cut z).top) (mode z)) state w).1=SevenTagCharge.observe state.1 w := by
  induction w generalizing state with
  | nil => rfl
  | cons e w ih => exact ih _

/-- Actual routed states and the closed A0 cursor read exactly the
same ledger after every raw suffix, including after sticky decisions. -/
theorem project_word {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (z : WindowA0ClosedEntry.State p c n) (w : List (Fin n)) :
    (routedState S z w).1=(GGTiming.runMarks (WindowA0ClosedEntry.next S) z w).tag.ledger := by
  have aux (u : WindowA0ClosedEntry.State p c n) :
      (GGTiming.runMarks (WindowA0ClosedEntry.next S) u w).tag.ledger=
        SevenTagCharge.observe u.tag.ledger w := by
    induction w generalizing u with
    | nil => rfl
    | cons e w ih =>
      change (GGTiming.runMarks (WindowA0ClosedEntry.next S)
        (WindowA0ClosedEntry.next S u e) w).tag.ledger=_
      rw [ih]
      change SevenTagCharge.observe (WindowA0Ledger.next S u.tag e).ledger w=_
      rw [WindowA0Ledger.physical_step]
      rfl
  exact (project_word_aux S z _ w).trans (aux z).symm

/-- From a certified entry and actual raw marks, a third credited keep
is the physical release or door row. Its ghost test is read from the
actual continued cursor at the selected mark, not from a stale
snapshot or an unproved guard projection. -/
theorem routed_release_of_adjacent {p c n : Nat} {initial : Config p c n} (hn : 5≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (q : Trip (2*c))
    (z : WindowA0ClosedEntry.State p c n) (hz : Admitted initial S J H z)
    (ha : ¬WindowA0Ledger.done z.tag) (h : Physical J q z 1)
    (w : List (Fin n)) (e : Fin n) (k : Fin 3)
    (hs : (routedState S z w).2=.waiting k)
    (hkeep : WindowA0Route.routeTwo S.group S.iTag S.jTag (routedState S z w).1 e=.keep)
    (hnext : (WindowA0RoutedRelease.next S.group S.iTag S.jTag
      (guardBase (cut z).top) (mode z) (routedState S z w) e).2=.success)
    (hlive : ¬WindowA0Ledger.done (GGTiming.runMarks (WindowA0ClosedEntry.next S) z w).tag)
    (htop : e=(cut (GGTiming.runMarks (WindowA0ClosedEntry.next S) z w)).top) :
    let y := (GGTiming.runMarks (WindowA0ClosedEntry.next S) z w).tag.ledger.config
    Released (y e) (y (rightNeighbor e)) q := by
  let x := (cut z).config
  let b := guardBase (cut z).top
  let state := routedState S z w
  let out := GGTiming.runMarks (WindowA0ClosedEntry.next S) z w
  have Hv : WindowA0RoutedRelease.View x b (mode z) state :=
    WindowA0RoutedRelease.view_run S.group S.iTag S.jTag b (mode z) z.tag.ledger w
  have hl : WindowA0IH.Live J H (cut out) :=
    ((WindowA0ClosedEntry.close_word (by omega) S J H z w hz).resolve_left hlive).1
  have hGhost : (state.1.config e).leader=false := by
    change ((routedState S z w).1.config e).leader=false
    rw [project_word,htop]
    exact hl.topGhost
  have R := WindowA0RoutedRelease.credited_release_of_reference
    S.group S.iTag S.jTag b (mode z) q x state e k Hv hs hkeep hnext hGhost
      (reference_of_adjacent hn S J H q z hz ha h)
  change Released ((routedState S z w).1.config e)
    ((routedState S z w).1.config (rightNeighbor e)) q at R
  rwa [project_word] at R

#print axioms guard_nodup
#print axioms project_word
#print axioms routed_release_of_adjacent

end L4.WindowA0AdjacentEntry
