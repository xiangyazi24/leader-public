import Leader.L4.WindowA0AdjacentReady

/-! Literal far-trail and waiting-source retention through the adjacent release script. -/
namespace L4.WindowA0AdjacentRetention
open FixedResidual GGStage WindowA0ClosedEntry WindowA0Machine WindowA0ForwardSweep
  WindowA0AdjacentEntry WindowA0AdjacentMotion WindowA0Release

/-- Only sockets at relative index two or higher belong to the far trail. -/
def Tail {p c n : Nat} (J : Fin n) (q : Trip (2*c))
    (z : WindowA0ClosedEntry.State p c n) : Prop :=
  ((cut z).config J).source=waitingFor q ∧
  ∀ i, 2≤i → i<z.gap → ((cut z).config (liftedSite (cut z).top i)).rail=.t

private theorem reason_none {p c n : Nat} (x : WindowA0Ledger.State p c n)
    (h : ¬WindowA0Ledger.done x) : x.reason=none := by
  cases hr : x.reason
  · rfl
  · exact (h (by simp [WindowA0Ledger.done,hr])).elim

private theorem before_keep {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (z : WindowA0ClosedEntry.State p c n) (e : Fin n)
    (hy : ¬WindowA0Ledger.done (WindowA0ClosedEntry.next S z e).tag) :
    ¬WindowA0Ledger.done z.tag := by
  intro h
  apply hy
  change (WindowA0Ledger.next S z.tag e).reason.isSome=true
  rw [WindowA0Ledger.terminal_sticky S z.tag e h]
  exact h

private theorem lift_add {n : Nat} (s : Fin n) (a b : Nat) :
    liftedSite (liftedSite s a) b=liftedSite s (a+b) := by
  apply Fin.ext
  change ((s.val+a)%n+b)%n=(s.val+(a+b))%n
  simp [Nat.add_assoc]

private theorem retained_old_ghost {p c n : Nat} {J : Fin n} {H : Nat}
    {x : WindowA0IH.Cut p c n} (h : WindowA0IH.Live J H x) (i : Nat)
    (hi : i<x.gap) : (x.config (liftedSite x.top i)).leader=false := by
  cases i with
  | zero => simpa only [liftedSite_zero] using h.topGhost
  | succ i =>
    apply Bool.eq_false_iff.mpr
    intro hl
    have hm := h.mc (liftedSite x.top i) (.inl (by rwa [←liftedSite_succ]))
    rw [h.openBonds i hi] at hm
    cases hm

private theorem pair_prefix_mark {p c : Nat} (u v : Site p c) :
    (pairStep u v).1.mark=(stepPrefix u v).1.mark := by
  unfold pairStep finishBirth
  dsimp only
  split <;> rfl

private theorem pair_prefix_ghost {p c : Nat} (u v : Site p c)
    (h : (pairStep u v).2.leader=false) : (stepPrefix u v).2.leader=false := by
  unfold pairStep finishBirth at h
  dsimp only at h
  split at h
  · contradiction
  · exact h

/-- A kept mark cannot reset this waiting source: the door sees the
owned worker or trail, and any other mark sees the source only as an
initiator or not at all. -/
private theorem source_step {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (q : Trip (2*c))
    (z : WindowA0ClosedEntry.State p c n) (e : Fin n)
    (hz : Admitted initial S J H z) (h : Tail J q z)
    (hdGap : e=z.tag.jSlot → 3≤z.gap)
    (hy : ¬WindowA0Ledger.done (WindowA0ClosedEntry.next S z e).tag) :
    ((WindowA0ClosedEntry.next S z e).tag.ledger.config J).source=waitingFor q := by
  have hb := before_keep S z e hy
  have h0 := hz.resolve_left hb
  have h1 := (close hn S J H z e hz).resolve_left hy
  let x := (cut z).config
  let y := (cut (WindowA0ClosedEntry.next S z e)).config
  have f := WindowA0XSweep.cut_keep_fields S z e (reason_none z.tag hb) hy
  have hS : (x J).source=waitingFor q := h.1
  change (y J).source=_
  have fy : y=step x e := f.1
  by_cases hr : rightNeighbor e=J
  · have hd : e=z.tag.jSlot := FreshSeparation.succ_inj (hr.trans h0.2.2.symm)
    have hD : e=liftedSite (cut z).top (z.gap-1) := hd.trans (door_offset hz hb)
    have hn' : J≠e := by
      intro he
      have Q : liftedSite e 1=liftedSite e 0 := by rw [liftedSite_succ,liftedSite_zero,hr,he]
      have := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) Q
      omega
    have hdi : incoming (cut z).top (cut z).gap=e := by
      apply FreshSeparation.succ_inj
      rw [incoming_right,hr]
      exact h0.1.fixedRight
    have hB : (x e).mark=true := hD.symm ▸ h0.1.markRight
    have hpay : geometricPay (x e) (x (rightNeighbor e))=false := by
      have T := (WindowA0Drained.drained_step hn x (cut z).top e h0.1.gapPos
        h0.1.markTop (hdi.symm ▸ hB) h0.1.empty
          (fun j hj => retained_old_ghost h0.1 j hj)).1
      change moved x (cut z).top e (cut z).gap=false at T
      simpa [moved,hdi] using T
    have mark : (stepPrefix (x e) (x (rightNeighbor e))).1.mark=true := by
      rw [←pair_prefix_mark]
      have Q := covered_step_mark hn x h0.1.mc e e
      have M : (step x e e).mark=(x e).mark := by simpa [hpay] using Q
      simpa [step] using M.trans hB
    have ghost : (stepPrefix (x e) (x (rightNeighbor e))).2.leader=false := by
      apply pair_prefix_ghost
      have hghost := h1.1.rightGhost
      rw [f.1] at hghost
      simpa [step,hr,hn'] using hghost
    have E := FreshEpochAuthentication.prefix_payload (x e) (x (rightNeighbor e))
    have hs : (stepPrefix (x e) (x (rightNeighbor e))).2.source=waitingFor q :=
      E.2.2.trans (hr.symm ▸ hS)
    have hl : (stepPrefix (x e) (x (rightNeighbor e))).1.rail=outward q ∨
        (stepPrefix (x e) (x (rightNeighbor e))).1.rail=.t := by
      rw [E.1]
      right
      have G := h.2 (z.gap-1) (by have := hdGap hd; omega) (by have := hdGap hd; omega)
      exact hD.symm ▸ G
    have T := pinned_waiting_door (x e) (x (rightNeighbor e)) q ghost mark hs hl
    rw [fy]
    simpa [step,hr,hn'] using T.2.1
  · rw [fy]
    by_cases he : J=e
    · rw [he]
      simp only [step,if_true,FreshEpochAuthentication.pair_left_source]
      exact he ▸ hS
    · simpa [step,he,Ne.symm hr] using hS

private theorem waiting_trail_no_launch {Q : Nat} (q : Trip Q) :
    ¬ResidualSweep.launches (waitingFor q) .t := by
  cases q with
  | init =>
    change ¬((Source.i1 : Source Q)=.i0 ∨ ∃ k : Fin Q, Source.i1=.count k)
    simp
  | count i =>
    change ¬(Source.await i=.i0 ∨ ∃ k : Fin Q, Source.await i=.count k)
    simp

/-- Any kept step that avoids the far-tail entrance, and only services
a far door, preserves both the far trail and exact waiting source. -/
theorem tail_step {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (q : Trip (2*c))
    (z : WindowA0ClosedEntry.State p c n) (e : Fin n)
    (hz : Admitted initial S J H z) (h : Tail J q z)
    (keep : ¬WindowA0Ledger.done (WindowA0ClosedEntry.next S z e).tag)
    (away : e≠liftedSite (cut z).top 1)
    (hdGap : e=z.tag.jSlot → 3≤z.gap) : Tail J q (WindowA0ClosedEntry.next S z e) := by
  refine ⟨source_step hn S J H q z e hz h hdGap keep,?_⟩
  let a := cut z
  let y := WindowA0ClosedEntry.next S z e
  let b := cut y
  have hb := before_keep S z e keep
  have L := (hz.resolve_left hb).1
  have W := WindowA0XSweep.cut_keep_fields S z e (reason_none z.tag hb) keep
  have hG : (cut z).gap=z.gap := rfl
  have G : b.gap=y.gap := rfl
  have cap : z.gap<n := L.noWrap
  have δ : WindowA0XSweep.topShift z e=0 ∨ WindowA0XSweep.topShift z e=1 := by
    unfold WindowA0XSweep.topShift; split <;> simp
  rcases δ with hδ|hδ
  · have ht : b.top=a.top := by simpa only [hδ,liftedSite_zero] using W.2.1
    have ng : y.gap=z.gap := by
      change b.gap=a.gap
      simpa only [hδ,Nat.sub_zero] using W.2.2
    have noFresh : ¬WindowA0ReverseSweep.freshDoor z e := by
      intro he
      have hd := hdGap he.1
      have hd' : e=liftedSite a.top (z.gap-1) := he.1.trans (door_offset hz hb)
      have hR : rightNeighbor e=J := by rw [he.1]; exact (hz.resolve_left hb).2.2
      have hSrc : (z.tag.ledger.config J).source=waitingFor q := h.1
      have hT : (z.tag.ledger.config e).rail=.t :=
        hd'.symm ▸ h.2 _ (by omega) (by omega)
      have N := he.2
      rw [hR,hSrc,hT] at N
      exact waiting_trail_no_launch q N
    let t := WindowA0ForwardSweep.init z
    have hold : ¬ready t := by
      intro hh
      exact hh.elim hb (fun h' => Bool.noConfusion h')
    have hnew : ¬ready (WindowA0ForwardSweep.next S t e) := by
      intro hh
      rcases hh with hh|hh
      · exact keep (by simpa only [WindowA0ForwardSweep.project,t,WindowA0ForwardSweep.init] using hh)
      · exact ((raw_launch S t e).mp hh).elim (fun h' => Bool.noConfusion h') noFresh
    have r := stationary_rows hn S t e hz hold hnew hδ
    let old := fun i => (a.config (liftedSite a.top i)).rail
    let new := fun i => (b.config (liftedSite a.top i)).rail
    have rh : RailRows a.top z.gap e old new (waitingFor q) := by
      have rr : RailRows a.top z.gap e old new (a.config J).source := by
        simpa only [t,WindowA0ForwardSweep.init,WindowA0ForwardSweep.project,hG] using r
      rw [show (a.config J).source=waitingFor q from h.1] at rr
      exact rr
    intro i hi hgi
    have hi' : i<z.gap := by rwa [ng] at hgi
    change (b.config (liftedSite b.top i)).rail=.t
    rw [ht]
    change new i=.t
    by_cases he : e=liftedSite a.top i
    · by_cases hh : i+1<z.gap
      · have R := rh.body i hh he
        rw [show old i=.t from h.2 _ hi hi',show old (i+1)=.t from h.2 _ (by omega) hh] at R
        exact congrArg Prod.fst R
      · have E : i=z.gap-1 := by omega
        rw [E,rh.door (E ▸ he),show old (z.gap-1)=.t from h.2 _ (by omega) (by omega),
          door_wait_trail]
    · by_cases hr : rightNeighbor e=liftedSite a.top i
      · have he' : e=liftedSite a.top (i-1) := by
          apply FreshSeparation.succ_inj
          rwa [←liftedSite_succ,show i-1+1=i by omega]
        have h2 : 2≤i-1 := by
          by_cases hh : i=2
          · exact (away (by simpa [a,hh] using he')).elim
          · omega
        have R := rh.body (i-1) (by omega) he'
        rw [show i-1+1=i by omega,show old i=.t from h.2 _ hi hi',
          show old (i-1)=.t from h.2 _ h2 (by omega)] at R
        exact congrArg Prod.snd R
      · rw [rh.off i hi' he hr]
        exact h.2 _ hi hi'
  · have hm : WindowFourHeadTrace.moves z.tag.ledger e z.tag.iSlot := by
      unfold WindowA0XSweep.topShift at hδ
      split at hδ
      · assumption
      · contradiction
    have hE : rightNeighbor e=a.top := congrArg rightNeighbor hm.1
    have ht : b.top=liftedSite a.top 1 := by simpa only [hδ] using W.2.1
    have ng : y.gap=z.gap-1 := by
      change b.gap=a.gap-1; simpa only [hδ] using W.2.2
    intro i hi hgi
    have hgi' : 1+i<z.gap := by rw [ng] at hgi; omega
    change (b.config (liftedSite b.top i)).rail=.t
    rw [ht,lift_add,W.1]
    have hE₁ : liftedSite a.top (1+i)≠e := by
      intro he
      have H' := congrArg rightNeighbor he
      rw [←liftedSite_succ,hE] at H'
      have := liftedSite_inj a.top (by omega : 1+i+1<n) (by omega : 0<n)
        (H'.trans (liftedSite_zero _).symm)
      omega
    have hE₂ : liftedSite a.top (1+i)≠rightNeighbor e := by
      intro he
      rw [hE] at he
      have := liftedSite_inj a.top (by omega : 1+i<n) (by omega : 0<n)
        (he.trans (liftedSite_zero _).symm)
      omega
    have hT := h.2 (1+i) (by omega) hgi'
    change (a.config (liftedSite a.top (1+i))).rail=.t at hT
    change (step a.config e (liftedSite a.top (1+i))).rail=.t
    simpa [step,hE₁,hE₂] using hT

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

private theorem controlled_labels {p c n : Nat} {initial : Config p c n} (hn : 5≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat)
    (z u : WindowA0ClosedEntry.State p c n) (e : Fin n)
    (hz : Admitted initial S J H z) (hza : ¬WindowA0Ledger.done z.tag)
    (hu : Admitted initial S J H u) (hua : ¬WindowA0Ledger.done u.tag) (hg : 2≤z.gap)
    (s : Kind) (k : Fin 3)
    (donor : u.tag.iSlot=liftedSite (guardBase (cut z).top) (donorOffset s k))
    (allowed : (e=asked (guardBase (cut z).top) s k ∧ k.val<2) ∨
      e∉WindowA0Return.guardLabels (guardBase (cut z).top)) :
    e≠liftedSite (cut u).top 1 ∧ (e=u.tag.jSlot → 3≤u.gap) := by
  let b := guardBase (cut z).top
  let d := donorOffset s k
  have ht : (cut u).top=liftedSite b (d+1) := by
    change rightNeighbor u.tag.iSlot=_
    rw [donor,←liftedSite_succ]
  have hx : d=1 ∨ d=2 := by
    unfold d
    cases s
    · simp only [donorOffset]; split <;> decide
    · exact .inl rfl
  have after : liftedSite (cut u).top 1=liftedSite b (d+2) := by
    rw [ht,lift_add]
  have door : u.tag.jSlot=liftedSite b (d+u.gap) := by
    have g : 0<u.gap := (hu.resolve_left hua).1.gapPos
    rw [door_offset hu hua,ht,lift_add,show d+1+(u.gap-1)=d+u.gap by omega]
  have hmin : d=1 → 2≤u.gap := by
    intro hd
    have eq : (cut u).top=(cut z).top := by
      rw [ht,hd]
      exact guard_top _
    have fU := (hu.resolve_left hua).1
    have fZ := (hz.resolve_left hza).1
    have E : liftedSite (cut z).top u.gap=liftedSite (cut z).top z.gap := by
      have a : liftedSite (cut u).top u.gap=J := fU.fixedRight
      have b : liftedSite (cut z).top z.gap=J := fZ.fixedRight
      exact (congrArg (fun t => liftedSite t u.gap) eq).symm.trans (a.trans b.symm)
    have huN : u.gap<n := fU.noWrap
    have hzN : z.gap<n := fZ.noWrap
    have he : u.gap=z.gap := liftedSite_inj (cut z).top huN hzN E
    rwa [he]
  have help : ∀ l, d+2≤l → l≤4 → e≠liftedSite b l := by
    intro l hlo hhi eq
    rcases allowed with ⟨he,hk⟩|out
    · have ht : offset s k≤2 := by
        cases s
        · simp only [offset]; omega
        · simp only [offset]; split <;> decide
      have E := liftedSite_inj b (by omega : offset s k<n) (by omega : l<n)
        ((show liftedSite b (offset s k)=e from he.symm).trans eq)
      omega
    · exact out (eq.symm ▸ inside_guard b l (by omega))
  refine ⟨?_,?_⟩
  · rw [after]
    exact help _ (by omega) (by omega)
  · intro eq
    by_cases H' : 3≤u.gap
    · exact H'
    · have pos : 0<u.gap := (hu.resolve_left hua).1.gapPos
      have non : d+u.gap≤4 := by omega
      have low : 3≤d+u.gap := by
        rcases hx with hd|hd
        · have := hmin hd
          omega
        · omega
      have ee : e=liftedSite b (d+u.gap) := eq.trans door
      rcases allowed with ⟨he,hk⟩|out
      · have hs : offset s k≤2 := by
          cases s
          · simp only [offset]; omega
          · simp only [offset]; split <;> decide
        have W := liftedSite_inj b (by omega : offset s k<n) (by omega : d+u.gap<n)
          ((show liftedSite b (offset s k)=e from he.symm).trans ee)
        omega
      · exact (out (ee.symm ▸ inside_guard b _ (by omega))).elim

open WindowA0ReleaseCredit in
/-- Same-word retention for every continuing guarded release prefix.
No assumption of stutter on the exterior is used: a far door was
allowed to execute, and the actual paid prefix is rebased. -/
theorem waiting_tail {p c n : Nat} {initial : Config p c n} (hn : 5≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (q : Trip (2*c))
    (z : WindowA0ClosedEntry.State p c n) (hz : Admitted initial S J H z)
    (ha : ¬WindowA0Ledger.done z.tag) (owned : WindowA0ApproachOwned.Physical J q z 1)
    (w : List (Fin n)) (k : Fin 3) (hw : (routedState S z w).2=.waiting k) :
    Tail J q (GGTiming.runMarks (WindowA0ClosedEntry.next S) z w) := by
  let P := fun w : List (Fin n) => ∀ k : Fin 3, (routedState S z w).2=.waiting k →
    Tail J q (GGTiming.runMarks (WindowA0ClosedEntry.next S) z w)
  have hzGap : 2≤z.gap := owned.2.inside
  have base : P [] := by
    intro k _
    refine ⟨owned.1,?_⟩
    intro i hi hgi
    exact owned.2.trail i (by omega) hgi
  have append (w : List (Fin n)) (e : Fin n) (ih : P w) : P (w++[e]) := by
    intro j hj
    let r := routedState S z w
    let u := GGTiming.runMarks (WindowA0ClosedEntry.next S) z w
    let s := mode z
    let b := guardBase (cut z).top
    have hphase : (WindowA0RoutedRelease.next S.group S.iTag S.jTag b s r e).2=.waiting j := by
      unfold routedState at hj
      rw [GGTiming.runMarks_append] at hj
      exact hj
    obtain ⟨k,hk,_,he⟩ := waiting_cases S b s r e j hphase
    have ow := waiting_donor_on_word hn S J H z hz ha w k hk
    have nW := waiting_donor_on_word hn S J H z hz ha (w++[e]) j hj
    have hU : Admitted initial S J H u := close_word (by omega) S J H z w hz
    have hc : ¬WindowA0Ledger.done u.tag := by
      have hh : u.tag.reason=none := ow.1
      simp [WindowA0Ledger.done,hh]
    have away : (e=asked b s k ∧ k.val<2) ∨ e∉WindowA0Return.guardLabels b := by
      rcases he with ⟨h,jk⟩|⟨h,_⟩
      · exact .inl ⟨h,by have := j.isLt; omega⟩
      · exact .inr h
    obtain ⟨mid,door⟩ := controlled_labels hn S J H z u e hz ha hU hc hzGap s k ow.2 away
    have hn' : ¬WindowA0Ledger.done (WindowA0ClosedEntry.next S u e).tag := by
      have hp := nW.1
      rw [GGTiming.runMarks_append] at hp
      change (WindowA0ClosedEntry.next S u e).tag.reason=none at hp
      simp [WindowA0Ledger.done,hp]
    rw [GGTiming.runMarks_append]
    exact tail_step (by omega) S J H q u e hU (ih k hk) hn' mid door
  have all (v : List (Fin n)) : P v.reverse := by
    induction v with
    | nil => exact base
    | cons e v ih =>
      rw [List.reverse_cons]
      exact append v.reverse e ih
  have E := all w.reverse
  rw [List.reverse_reverse] at E
  exact E k hw

/-- From the admitted adjacent entry and actual first credited ordinary
release, the exact post-word physical cursor enters Ready. -/
theorem kept_ordinary_ready {p c n : Nat} {initial : Config p c n} (hn : 5≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (q : Trip (2*c))
    (z : WindowA0ClosedEntry.State p c n) (hz : Admitted initial S J H z)
    (ha : ¬WindowA0Ledger.done z.tag) (owned : WindowA0ApproachOwned.Physical J q z 1)
    (w : List (Fin n)) (e : Fin n) (k : Fin 3)
    (hw : (routedState S z w).2=.waiting k)
    (hkeep : WindowA0Route.routeTwo S.group S.iTag S.jTag (routedState S z w).1 e=.keep)
    (hs : (WindowA0RoutedRelease.next S.group S.iTag S.jTag
      (guardBase (cut z).top) (mode z) (routedState S z w) e).2=.success)
    (hg : 1<(GGTiming.runMarks (WindowA0ClosedEntry.next S) z w).gap) :
    WindowA0ReturnEntry.Ready initial S J H
      (GGTiming.runMarks (WindowA0ClosedEntry.next S) z (w++[e])) q 1 false := by
  have T := waiting_tail hn S J H q z hz ha owned w k hw
  exact WindowA0AdjacentReady.kept_body_ready hn S J H q z hz ha owned w e k hw hkeep hs hg T.2 T.1

end L4.WindowA0AdjacentRetention
