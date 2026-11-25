import Leader.L4.WindowA0DirtyRepeat
import Leader.L4.WindowA0Machine

/-! Rail ownership for the physical A0 outward approach. -/
namespace L4.WindowA0ApproachOwned
open FixedResidual WindowA0Machine WindowA0ClosedEntry WindowA0ForwardSweep GGStage

/-- The nominated coordinate holds the owned worker, not necessarily
the only upward rail. The initialization worker can overwrite dirty
non-X rails ahead; its trailing rail segment is clean. -/
structure Owned {Q : Nat} (q : Trip Q) (g k : Nat) (r : Nat → Rail) : Prop where
  inside : k<g
  worker : r k=outward q
  trail : ∀ i, k<i → i<g → r i=.t
  ahead : ∀ i, i<k → Writable q (r i)

abbrev rails {p c n : Nat} (z : WindowA0ClosedEntry.State p c n) : Nat → Rail :=
  fun i => ((cut z).config (liftedSite (cut z).top i)).rail

def Physical {p c n : Nat} (J : Fin n) (q : Trip (2*c))
    (z : WindowA0ClosedEntry.State p c n) (k : Nat) : Prop :=
  (z.tag.ledger.config J).source=waitingFor q ∧ Owned q z.gap k (rails z)

theorem init_owned {p c n : Nat} (J : Fin n) (z : WindowA0ClosedEntry.State p c n)
    (hg : 0<z.gap) (hsrc : (z.tag.ledger.config J).source=.i1)
    (hw : rails z (z.gap-1)=.ui) (hx : WindowA0CleanupChain.XFree z) :
    Physical J .init z (z.gap-1) := by
  refine ⟨hsrc,⟨by omega,hw,?_,?_⟩⟩
  · intro i hi hg'
    omega
  · intro i hi
    exact hx.2 i (by omega)

private theorem pass_admitted {p c n : Nat} {initial : Config p c n} {S : WindowA0Ledger.Scope n}
    {J : Fin n} {H : Nat} {z : WindowA0CleanupPass.State p c n}
    (h : WindowA0CleanupPass.Good initial S J H z) : Admitted initial S J H z.physical := by
  cases z with
  | x _ => exact h.1.1
  | reverse _ => exact h.1.1
  | forward _ => exact h.1.1
  | done _ _ => exact h.1

theorem init_after_first_terminal {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat)
    (z : WindowA0DirtyRepeat.State p c n) (e : Fin n)
    (hz : WindowA0DirtyRepeat.Good initial S J H z) (ha : ¬WindowA0DirtyRepeat.done z)
    (hd : WindowA0DirtyRepeat.done (WindowA0DirtyRepeat.next S z e))
    (hkeep : ¬WindowA0Ledger.done (WindowA0DirtyRepeat.next S z e).pass.physical.tag) :
    let out := (WindowA0DirtyRepeat.next S z e).pass.physical
    Physical J .init out (out.gap-1) := by
  let y := WindowA0DirtyRepeat.next S z e
  obtain ⟨he,hw,hs,hx⟩ := WindowA0DirtyRepeat.first_terminal_worker hn S J H z e hz ha hd hkeep
  have hG := WindowA0DirtyRepeat.good_next hn S J H z e hz
  have hp := (pass_admitted hG.1).resolve_left hkeep
  apply init_owned J y.pass.physical hp.1.gapPos hs _ hx
  change (y.pass.physical.tag.ledger.config (liftedSite (cut y.pass.physical).top
    (y.pass.physical.gap-1))).rail=.ui
  rw [←he]
  exact hw

private theorem writable_body {Q : Nat} (q : Trip Q) (u v : Rail)
    (hu : Writable q u) (hv : Writable q v) :
    Writable q (ResidualSweep.body u v).1 ∧ Writable q (ResidualSweep.body u v).2 := by
  cases q with
  | init =>
    exact ⟨ResidualSweep.body_break_left u v,ResidualSweep.body_break_right u v hu hv⟩
  | count k =>
    rcases hu with hu|hu <;> rcases hv with hv|hv <;> subst u <;> subst v <;>
      first | exact ⟨.inl rfl,.inl rfl⟩ | exact ⟨.inl rfl,.inr rfl⟩ | exact ⟨.inr rfl,.inl rfl⟩ | exact ⟨.inr rfl,.inr rfl⟩

private theorem writable_top {Q : Nat} (q : Trip Q) (r : Rail) (h : Writable q r) :
    Writable q (topRail r) := by
  cases q with
  | init => exact ResidualSweep.top_no_break r h
  | count k =>
    rcases h with h|h <;> subst r <;> simp [Writable, topRail]

private theorem trail_row {Q : Nat} (q : Trip Q) :
    ResidualSweep.body (outward q) .t=(outward q,.t) := by cases q <;> rfl

private theorem door_hold {Q : Nat} (q : Trip Q) (r : Rail)
    (hr : r=outward q ∨ r=.t) :
    (serviceDoor (waitingFor q) r).left=r := by
  rcases hr with hr|hr
  · rw [hr,door_wait_outward]
  · rw [hr,door_wait_trail]

/-- Paying at the top only removes its vacated prefix site. The old
worker and all later sites have identical rails in the new lifts. -/
theorem paid_rebase {Q : Nat} (q : Trip Q) (g k : Nat) (r s : Nat → Rail)
    (hk : 0<k) (h : Owned q g k r) (heq : ∀ i, i<g-1 → s i=r (1+i)) :
    Owned q (g-1) (k-1) s := by
  refine ⟨by have := h.inside; omega,?_,?_,?_⟩
  · rw [heq _ (by have := h.inside; omega),show 1+(k-1)=k by omega]
    exact h.worker
  · intro i hi hg
    rw [heq _ hg]
    exact h.trail _ (by omega) (by omega)
  · intro i hi
    have hg : i<g-1 := by have := h.inside; omega
    rw [heq _ hg]
    exact h.ahead _ (by omega)

/-- Exact rail transport under stationary geometry. The incoming worker
mark advances its authentic occurrence; every other mark retains its
position, including arbitrary legal changes in the dirty INIT prefix. -/
theorem stationary_owned {n Q : Nat} (base e : Fin n) (q : Trip Q)
    (g k : Nat) (hg : g<n) (hk : 2≤k) (r s : Nat → Rail)
    (h : Owned q g k r) (rows : RailRows base g e r s (waitingFor q)) :
    Owned q g (if e=liftedSite base (k-1) then k-1 else k) s := by
  have hkg := h.inside
  let l := if e=liftedSite base (k-1) then k-1 else k
  have hsmall : l≤k := by dsimp [l]; split <;> omega
  have hlarge : k-1≤l := by dsimp [l]; split <;> omega
  have hit : l<k → e=liftedSite base (k-1) := by
    intro hl
    by_cases hh : e=liftedSite base (k-1)
    · exact hh
    · simp [l,hh] at hl
  have move : e=liftedSite base (k-1) →
      (s (k-1),s k)=(outward q,.t) := by
    intro he
    have R := rows.body (k-1) (by omega) he
    rw [show k-1+1=k by omega,h.worker] at R
    exact R.trans (body_authentic_worker q _ (h.ahead _ (by omega)))
  have inject {i j : Nat} (hi : i<g) (hj : j<g)
      (he : liftedSite base i=liftedSite base j) : i=j :=
    liftedSite_inj base (by omega) (by omega) he
  refine ⟨by omega,?_,?_,?_⟩
  · change s l=outward q
    by_cases he : e=liftedSite base (k-1)
    · simpa only [l,if_pos he] using congrArg Prod.fst (move he)
    · rw [show l=k by simp [l,he]]
      have hR : rightNeighbor e≠liftedSite base k := by
        intro bad
        exact he (FreshSeparation.succ_inj (by rwa [←liftedSite_succ,show k-1+1=k by omega]))
      by_cases hm : e=liftedSite base k
      · by_cases hb : k+1<g
        · have R := rows.body k hb hm
          rw [h.worker,h.trail _ (by omega) hb,trail_row] at R
          exact congrArg Prod.fst R
        · have hd : k=g-1 := by omega
          rw [hd,rows.door (hd ▸ hm),←hd,door_hold q _ (.inl h.worker)]
          exact h.worker
      · rw [rows.off k hkg hm hR]; exact h.worker
  · intro i hi hig
    change l<i at hi
    by_cases hik : i=k
    · subst i
      exact congrArg Prod.snd (move (hit hi))
    · have hlt : k<i := by omega
      by_cases he : e=liftedSite base i
      · by_cases hb : i+1<g
        · have R := rows.body i hb he
          rw [h.trail _ hlt hig,h.trail _ (by omega) hb] at R
          exact congrArg Prod.fst R
        · have hd : i=g-1 := by omega
          rw [hd,rows.door (hd ▸ he),←hd,door_hold q _ (.inr (h.trail i hlt hig))]
          exact h.trail i hlt hig
      · by_cases hR : rightNeighbor e=liftedSite base i
        · have he' : e=liftedSite base (i-1) :=
            FreshSeparation.succ_inj (by rwa [←liftedSite_succ,show i-1+1=i by omega])
          have R := rows.body (i-1) (by omega) he'
          rw [show i-1+1=i by omega,h.trail i hlt hig] at R
          by_cases hi' : i-1=k
          · rw [hi',h.worker,trail_row] at R
            exact congrArg Prod.snd R
          · rw [h.trail (i-1) (by omega) (by omega)] at R
            exact congrArg Prod.snd R
        · rw [rows.off i hig he hR]; exact h.trail i hlt hig
  · intro i hi
    change i<l at hi
    have hig : i<g := by omega
    by_cases he : e=liftedSite base i
    · have hi' : i+1<k := by
        by_cases hb : i+1<k
        · exact hb
        · have eq : i=k-1 := by omega
          have he' : e=liftedSite base (k-1) := eq ▸ he
          simp [l,he',eq] at hi
      have R := congrArg Prod.fst (rows.body i (by omega) he)
      dsimp only at R
      rw [R]
      exact (writable_body q _ _ (h.ahead i (by omega)) (h.ahead _ hi')).1
    · by_cases hR : rightNeighbor e=liftedSite base i
      · cases i with
        | zero =>
          have he' : e=incoming base 0 := FreshSeparation.succ_inj (by rwa [incoming_right])
          rw [rows.top he']
          exact writable_top q _ (h.ahead 0 (by omega))
        | succ j =>
          have he' : e=liftedSite base j := FreshSeparation.succ_inj (by rwa [←liftedSite_succ])
          have R := congrArg Prod.snd (rows.body j hig he')
          dsimp only at R
          rw [R]
          exact (writable_body q _ _ (h.ahead j (by omega)) (h.ahead _ (by omega))).2
      · rw [rows.off i hig he hR]; exact h.ahead i (by omega)

private theorem waiting_no_launch {Q : Nat} (q : Trip Q) (r : Rail)
    (h : r=outward q ∨ r=.t) : ¬ResidualSweep.launches (waitingFor q) r := by
  rcases h with h|h <;> subst r <;> cases q with
  | init =>
    change ¬((Source.i1 : Source Q)=.i0 ∨ ∃ k : Fin Q, Source.i1=.count k)
    simp
  | count i =>
    change ¬(Source.await i=.i0 ∨ ∃ k : Fin Q, Source.await i=.count k)
    simp

private theorem last_owned {Q : Nat} (q : Trip Q) (g k : Nat) (r : Nat → Rail)
    (h : Owned q g k r) : r (g-1)=outward q ∨ r (g-1)=.t := by
  have hi := h.inside
  by_cases hk : k=g-1
  · exact .inl (hk ▸ h.worker)
  · exact .inr (h.trail _ (by omega) (by omega))

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

/-- Stationary physical corridor supplies exactly the rail rows needed
by the ownership argument. The cleanup row reader is reused without
running a new cleanup or suppressing any actual mark. -/
theorem stationary_physical_rails {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (q : Trip (2*c))
    (z : WindowA0ClosedEntry.State p c n) (e : Fin n) (k : Nat)
    (hz : Admitted initial S J H z) (h : Physical J q z k)
    (hy : ¬WindowA0Ledger.done (WindowA0ClosedEntry.next S z e).tag)
    (hδ : WindowA0XSweep.topShift z e=0) (K : 2≤k) :
    let y := WindowA0ClosedEntry.next S z e
    y.gap=z.gap ∧ (cut y).top=(cut z).top ∧
      Owned q y.gap (if e=liftedSite (cut z).top (k-1) then k-1 else k) (rails y) := by
  have hb := before_keep S z e hy
  have hd := door_offset hz hb
  have hLive := (hz.resolve_left hb).1
  have r := WindowA0XSweep.cut_keep_fields S z e (reason_none z.tag hb) hy
  have hs : ¬WindowA0ReverseSweep.freshDoor z e := by
    intro he
    apply waiting_no_launch q (rails z (z.gap-1)) (last_owned q z.gap k _ h.2)
    have hR : rightNeighbor e=J := by rw [he.1]; exact (hz.resolve_left hb).2.2
    have E := he.2
    rw [hR,h.1] at E
    rw [show e=liftedSite (cut z).top (z.gap-1) from he.1.trans hd] at E
    exact E
  let t := WindowA0ForwardSweep.init z
  have hold : ¬ready t := by
    intro hh
    exact hh.elim hb (fun h' => Bool.noConfusion h')
  have hnew : ¬ready (WindowA0ForwardSweep.next S t e) := by
    intro hh
    rcases hh with hh|hh
    · exact hy (by simpa only [WindowA0ForwardSweep.project,t,WindowA0ForwardSweep.init] using hh)
    · exact ((raw_launch S t e).mp hh).elim (fun h' => Bool.noConfusion h') hs
  have r' := stationary_rows hn S t e hz hold hnew hδ
  have hsrc : ((cut z).config J).source=waitingFor q := h.1
  have htop : (cut (WindowA0ClosedEntry.next S z e)).top=(cut z).top := by
    simpa only [hδ,liftedSite_zero] using r.2.1
  have rb : RailRows (cut z).top z.gap e (rails z)
      (rails (WindowA0ClosedEntry.next S z e)) (waitingFor q) := by
    have rr : RailRows (cut z).top z.gap e (rails z)
        (fun i => ((cut (WindowA0ClosedEntry.next S z e)).config (liftedSite (cut z).top i)).rail)
        ((cut z).config J).source := by
      have hg : (cut z).gap=z.gap := rfl
      simpa only [t,WindowA0ForwardSweep.init,WindowA0ForwardSweep.project,hg] using r'
    have heq : rails (WindowA0ClosedEntry.next S z e)=
        (fun i => ((cut (WindowA0ClosedEntry.next S z e)).config (liftedSite (cut z).top i)).rail) := by
      funext i
      change ((cut (WindowA0ClosedEntry.next S z e)).config
        (liftedSite (cut (WindowA0ClosedEntry.next S z e)).top i)).rail=_
      rw [htop]
    rwa [heq,←hsrc]
  have g : (WindowA0ClosedEntry.next S z e).gap=z.gap := by
    change (cut (WindowA0ClosedEntry.next S z e)).gap=(cut z).gap
    simpa only [hδ,Nat.sub_zero] using r.2.2
  refine ⟨g,htop,?_⟩
  rw [g]
  exact stationary_owned (cut z).top e q z.gap k hLive.noWrap K _ _ h.2 rb

private theorem lift_add {n : Nat} (s : Fin n) (a b : Nat) :
    liftedSite (liftedSite s a) b=liftedSite s (a+b) := by
  apply Fin.ext
  change ((s.val+a)%n+b)%n=(s.val+(a+b))%n
  simp [Nat.add_assoc]

/-- The discarded old top is the only retained-site operand of a
surviving payment there. All rails in the rebase are literal holds. -/
theorem paid_physical_rails {p c n : Nat} {initial : Config p c n}
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (q : Trip (2*c))
    (z : WindowA0ClosedEntry.State p c n) (e : Fin n) (k : Nat)
    (hz : Admitted initial S J H z) (h : Physical J q z k)
    (hy : ¬WindowA0Ledger.done (WindowA0ClosedEntry.next S z e).tag)
    (hδ : WindowA0XSweep.topShift z e=1) (K : 2≤k) :
    let y := WindowA0ClosedEntry.next S z e
    e=incoming (cut z).top 0 ∧ y.gap=z.gap-1 ∧
      (cut y).top=liftedSite (cut z).top 1 ∧ Physical J q y (k-1) := by
  let y := WindowA0ClosedEntry.next S z e
  have hb := before_keep S z e hy
  have hLive := (hz.resolve_left hb).1
  have r := WindowA0XSweep.cut_keep_fields S z e (reason_none z.tag hb) hy
  have hm : WindowFourHeadTrace.moves z.tag.ledger e z.tag.iSlot := by
    unfold WindowA0XSweep.topShift at hδ
    split at hδ
    · assumption
    · contradiction
  have hE : rightNeighbor e=(cut z).top := congrArg rightNeighbor hm.1
  have hI : e=incoming (cut z).top 0 := by
    apply FreshSeparation.succ_inj
    rwa [incoming_right,liftedSite_zero]
  have ht : (cut y).top=liftedSite (cut z).top 1 := by simpa only [hδ] using r.2.1
  have g : y.gap=z.gap-1 := by
    change (cut y).gap=(cut z).gap-1
    simpa only [hδ] using r.2.2
  have hold (i : Nat) (hi : 0<i) (hi' : i<z.gap) :
      (cut y).config (liftedSite (cut z).top i)=
        (cut z).config (liftedSite (cut z).top i) := by
    have hN : z.gap<n := hLive.noWrap
    have h1 : liftedSite (cut z).top i≠e := by
      intro he
      have he' := congrArg rightNeighbor he
      rw [←liftedSite_succ,hE] at he'
      have hh : liftedSite (cut z).top (i+1)=liftedSite (cut z).top 0 :=
        he'.trans (liftedSite_zero _).symm
      have Eq := liftedSite_inj (cut z).top (by omega : i+1<n) (by omega : 0<n) hh
      omega
    have h2 : liftedSite (cut z).top i≠rightNeighbor e := by
      intro he
      rw [hE] at he
      have hh : liftedSite (cut z).top i=liftedSite (cut z).top 0 :=
        he.trans (liftedSite_zero _).symm
      have Eq := liftedSite_inj (cut z).top (by omega : i<n) (by omega : 0<n) hh
      omega
    rw [r.1]
    simp [step,h1,h2]
  have hsrc : (y.tag.ledger.config J).source=waitingFor q := by
    change ((cut y).config J).source=waitingFor q
    rw [r.1]
    have hRJ : rightNeighbor e≠J := by
      intro he
      have hx : liftedSite (cut z).top 0=liftedSite (cut z).top z.gap := by
        exact (liftedSite_zero _).trans (hE.symm.trans (he.trans hLive.fixedRight.symm))
      have eq := liftedSite_inj (cut z).top (by have := hLive.gapPos; have := hLive.noWrap; omega : 0<n)
        hLive.noWrap hx
      exact (Nat.ne_of_gt hLive.gapPos) eq.symm
    by_cases hJ : J=e
    · rw [hJ]
      simp only [step,if_true,FreshEpochAuthentication.pair_left_source]
      exact hJ ▸ h.1
    · have hOld : ((cut z).config J).source=waitingFor q := h.1
      simpa [step,hJ,Ne.symm hRJ] using hOld
  have hre : ∀ i, i<z.gap-1 → rails y i=rails z (1+i) := by
    intro i hi
    change ((cut y).config (liftedSite (cut y).top i)).rail=_
    rw [ht,lift_add,hold _ (by omega) (by omega)]
  refine ⟨hI,g,ht,hsrc,?_⟩
  rw [g]
  exact paid_rebase q z.gap k _ _ (by omega) h.2 hre

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
theorem waiting_source_step {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (q : Trip (2*c))
    (z : WindowA0ClosedEntry.State p c n) (e : Fin n) (k : Nat)
    (hz : Admitted initial S J H z) (h : Physical J q z k)
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
      have G := last_owned q z.gap k _ h.2
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

/-- An approach hit is exactly the raw mark entering the currently
owned worker. This relative coordinate never goes below one on the
first admission mark. Neither physical exit nor padding is filtered. -/
noncomputable def workerHit {p c n : Nat} (z : WindowA0ClosedEntry.State p c n)
    (k : Nat) (e : Fin n) : Nat := if e=liftedSite (cut z).top (k-1) then 1 else 0

theorem physical_step {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (q : Trip (2*c))
    (z : WindowA0ClosedEntry.State p c n) (e : Fin n) (k : Nat)
    (hz : Admitted initial S J H z) (h : Physical J q z k)
    (hy : ¬WindowA0Ledger.done (WindowA0ClosedEntry.next S z e).tag) (K : 2≤k) :
    let y := WindowA0ClosedEntry.next S z e
    let d := WindowA0XSweep.topShift z e
    let j := workerHit z k e
    d+j≤1 ∧ 1≤k-d-j ∧ y.gap=z.gap-d ∧
      (cut y).top=liftedSite (cut z).top d ∧ Physical J q y (k-d-j) := by
  classical
  let y := WindowA0ClosedEntry.next S z e
  let d := WindowA0XSweep.topShift z e
  let j := workerHit z k e
  change d+j≤1 ∧ 1≤k-d-j ∧ y.gap=z.gap-d ∧ (cut y).top=liftedSite (cut z).top d ∧ Physical J q y (k-d-j)
  have hull : d=0 ∨ d=1 := by unfold d WindowA0XSweep.topShift; split <;> simp
  rcases hull with h0|h1
  · obtain ⟨hg,ht,hs⟩ := stationary_physical_rails hn S J H q z e k hz h hy h0 K
    have hsrc := waiting_source_step hn S J H q z e k hz h hy
    have hH : j≤1 := by unfold j workerHit; split <;> omega
    have ht' : (cut y).top=liftedSite (cut z).top d := by rw [h0,liftedSite_zero]; exact ht
    have hh : k-d-j=(if e=liftedSite (cut z).top (k-1) then k-1 else k) := by
      rw [h0]
      unfold j workerHit
      split <;> omega
    refine ⟨by omega,by omega,?_,ht',hsrc,?_⟩
    · rw [h0,Nat.sub_zero]; exact hg
    · rw [hh]; exact hs
  · obtain ⟨he,hg,ht,hp⟩ := paid_physical_rails S J H q z e k hz h hy h1 K
    have hL := (hz.resolve_left (before_keep S z e hy)).1
    have hN : k<n := by have hh := h.2.inside; have hh' := hL.noWrap; change z.gap<n at hh'; omega
    have hn' : e≠liftedSite (cut z).top (k-1) := by
      intro eq
      have ex := congrArg rightNeighbor (he.symm.trans eq)
      rw [incoming_right,←liftedSite_succ,show k-1+1=k by omega] at ex
      have bad := liftedSite_inj (cut z).top (by omega : 0<n) hN ex
      omega
    have hj : j=0 := by simp [j,workerHit,hn']
    rw [h1,hj]
    exact ⟨by omega,by omega,hg,ht,hp⟩

/-- The owned approach observer carries a relative coordinate. Even
after its local admission or global terminal decision every raw
letter continues to update the physical ledger. -/
structure State (p c n : Nat) where
  physical : WindowA0ClosedEntry.State p c n
  worker : Nat

def done {p c n : Nat} (z : State p c n) : Prop :=
  WindowA0Ledger.done z.physical.tag ∨ z.worker≤1

noncomputable def approachNext {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (z : State p c n) (e : Fin n) : State p c n := by
  classical
  exact ⟨WindowA0ClosedEntry.next S z.physical e,
    if done z then z.worker else
      z.worker-WindowA0XSweep.topShift z.physical e-workerHit z.physical z.worker e⟩

theorem approach_project {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (z : State p c n) (e : Fin n) :
    (approachNext S z e).physical=WindowA0ClosedEntry.next S z.physical e := rfl

theorem approach_sticky {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (z : State p c n) (e : Fin n) (hd : done z) : done (approachNext S z e) := by
  classical
  rcases hd with hd|hd
  · left
    exact Classical.byContradiction (fun hg => before_keep S z.physical e hg hd)
  · right
    unfold approachNext
    dsimp only
    split
    · exact hd
    · rename_i hf
      exact (hf (.inr hd)).elim

/-- The first nonphysical approach exit from a far state is at exact
relative offset one; offset zero is only the initial gap-one case. -/
theorem first_adjacency {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (q : Trip (2*c))
    (z : State p c n) (e : Fin n)
    (hz : Admitted initial S J H z.physical) (h : Physical J q z.physical z.worker)
    (hfar : ¬done z) (hy : done (approachNext S z e))
    (hkeep : ¬WindowA0Ledger.done (approachNext S z e).physical.tag) :
    (approachNext S z e).worker=1 ∧ Physical J q (approachNext S z e).physical 1 := by
  have K : 2≤z.worker := by
    have hh : ¬z.worker≤1 := fun h => hfar (.inr h)
    omega
  have R := physical_step hn S J H q z.physical e z.worker hz h hkeep K
  have he : (approachNext S z e).worker=
      z.worker-WindowA0XSweep.topShift z.physical e-workerHit z.physical z.worker e := by
    simp only [approachNext,if_neg hfar]
  have hk := hy.resolve_left hkeep
  have H₁ := R.2.1
  have H₂ := R.2.2.2.2
  have E : (approachNext S z e).worker=1 := by omega
  refine ⟨E,?_⟩
  rw [←E,he,approach_project]
  exact H₂

/-- Raw mean to physical exit or first admission, including zero-time
admission when the owned launch is already at or next to the top. -/
theorem expected_approach {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (q : Trip (2*c))
    (z : State p c n) (hz : Admitted initial S J H z.physical)
    (h : Physical J q z.physical z.worker) :
    IIDExpectedHittingTimeAtMost (approachNext S) done z (n*z.worker) := by
  classical
  let B := fun x : State p c n => if done x then 0 else x.worker
  let N := fun x : State p c n => liftedSite (cut x.physical).top (x.worker-1)
  let good := fun x : State p c n =>
    done x ∨ Admitted initial S J H x.physical ∧ Physical J q x.physical x.worker
  have row (x : State p c n) (e : Fin n) (hx : good x) (ha : ¬done x)
      (hb : ¬done (approachNext S x e)) :
      good (approachNext S x e) ∧
        (approachNext S x e).worker+(if e=N x then 1 else 0)≤x.worker := by
    obtain ⟨hx,hP⟩ := hx.resolve_left ha
    have hp : ¬WindowA0Ledger.done (approachNext S x e).physical.tag := fun hh => hb (.inl hh)
    have K : 2≤x.worker := by
      have hh : ¬x.worker≤1 := fun h => ha (.inr h)
      omega
    have R := physical_step hn S J H q x.physical e x.worker hx hP hp K
    have hT := close hn S J H x.physical e hx
    have hW := R.2.1
    have hP' := R.2.2.2.2
    simp only [approachNext,if_neg ha,good]
    refine ⟨.inr ⟨hT,hP'⟩,?_⟩
    change x.worker-WindowA0XSweep.topShift x.physical e-workerHit x.physical x.worker e+
      workerHit x.physical x.worker e≤x.worker
    omega
  have H' := mean_of_reachable_budget (approachNext S) done good B N
    (fun x e hx ha => by
      by_cases hb : done (approachNext S x e)
      · exact .inl hb
      · exact (row x e hx ha hb).1)
    (fun x e hx ha => by
      by_cases hb : done (approachNext S x e)
      · have hk : 2≤x.worker := by
          have hh : ¬x.worker≤1 := fun h => ha (.inr h)
          omega
        simp only [B,if_pos hb,if_neg ha,Nat.zero_add]
        split <;> omega
      · simpa only [B,if_neg hb,if_neg ha] using (row x e hx ha hb).2)
    z (.inr ⟨hz,h⟩) (approach_sticky S)
  have Hb : B z≤z.worker := by unfold B; split <;> omega
  intro t
  exact Nat.le_trans (H' t) (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ Hb))

end L4.WindowA0ApproachOwned
