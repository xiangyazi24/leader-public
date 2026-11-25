import Leader.L4.WindowA0CleanupPass
import Leader.L4.TimerAssembly

/-! The physical fixed J timer rank after the first observed dirty COUNT.
The X stage is never reused between observed launches. -/
namespace L4.WindowA0DirtyRank
open WindowA0ClosedEntry FixedResidual ResidualSweep GGStage Classical

private theorem left_source {p c : Nat} (u v : Site p c) : (pairStep u v).1.source=u.source := by
  have hm : (materialize u v).source=u.source := by unfold materialize; split <;> rfl
  have hf : (fireInitiator (materialize u v)).source=u.source := by
    unfold fireInitiator
    split <;> exact hm
  generalize hU : fireInitiator (materialize u v)=a at hf
  generalize hV : fireResponder v=b
  have hi : (impact a b).1.source=a.source := by unfold impact; split <;> rfl
  have hFol (g : Bool) (a b : Site p c) : (followerBullet g a b).1.source=a.source := by
    unfold followerBullet
    split
    · dsimp only
      split <;> rfl
    · rfl
  have hp (a b : Site p c) : (payment a b).1.source=a.source := by
    unfold payment
    split
    · rfl
    · split
      · rfl
      · split <;> rfl
  have hPre : (stepPrefix u v).1.source=u.source := by
    unfold stepPrefix native
    rw [hU,hV]
    dsimp only
    rw [hp,hFol,hi,hf]
  unfold pairStep finishBirth
  dsimp only
  split <;> exact hPre

private theorem mark_prefix {p c : Nat} (u v : Site p c) :
    (pairStep u v).1.mark=(stepPrefix u v).1.mark := by
  unfold pairStep finishBirth
  dsimp only
  split <;> rfl

theorem door_source_exact {p c : Nat} (u v : Site p c)
    (hm : (stepPrefix u v).1.mark=true) (hg : (pairStep u v).2.leader=false) :
    (pairStep u v).2.source=(serviceDoor v.source u.rail).source ∧
      (serviceDoor v.source u.rail).fire=false := by
  let a := (stepPrefix u v).1
  let b := (stepPrefix u v).2
  have hB : b.leader=false := by
    unfold pairStep finishBirth at hg
    dsimp only at hg
    split at hg
    · contradiction
    · exact hg
  have pp := FreshEpochAuthentication.prefix_payload u v
  let m := patrol true true false b.source a.rail b.rail
  have eq : pairStep u v=finishBirth m.fire (patrolWrite a b m).1 (patrolWrite a b m).2 := by
    unfold pairStep
    dsimp only
    change finishBirth _ _ _=_
    simp only [show (stepPrefix u v).2.leader=false from hB,hm,Bool.false_or,
      pinned,Bool.not_false,Bool.true_and]
    rfl
  have hf : m.fire=false := by
    apply Bool.eq_false_iff.mpr
    intro hF
    rw [eq] at hg
    have p : pinned (patrolWrite a b m).1 (patrolWrite a b m).2=true := by
      simp only [pinned,patrolWrite,hB,show a.mark=true from hm,Bool.not_false,Bool.true_and]
    simp [finishBirth,p,hF] at hg
  have h : m.source=(serviceDoor v.source u.rail).source ∧
      m.fire=(serviceDoor v.source u.rail).fire := by
    have hh := door_exact b.source a.rail b.rail
    exact ⟨by simpa only [m,show b.source=v.source from pp.2.2,show a.rail=u.rail from pp.1] using hh.1,
      by simpa only [m,show b.source=v.source from pp.2.2,show a.rail=u.rail from pp.1] using hh.2.2⟩
  exact ⟨by rw [eq]; simp [finishBirth,hf,patrolWrite,h.1],h.2.symm.trans hf⟩

private theorem right_ne {n : Nat} (hn : 4≤n) (e : Fin n) : rightNeighbor e≠e := by
  intro h
  have F : liftedSite e 1=liftedSite e 0 := by simpa [liftedSite_succ,liftedSite_zero] using h
  have := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) F
  omega

theorem physical_source {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J e : Fin n) (H : Nat)
    (z : WindowA0ClosedEntry.State p c n) (hz : Admitted initial S J H z)
    (hNext : ¬WindowA0Ledger.done (next S z e).tag) :
    let x := z.tag.ledger.config
    let y := (next S z e).tag.ledger.config
    if e=z.tag.jSlot then
      (y J).source=(serviceDoor (x J).source (x e).rail).source ∧
      (serviceDoor (x J).source (x e).rail).fire=false
    else (y J).source=(x J).source := by
  let x := z.tag.ledger.config
  let y := (next S z e).tag.ledger.config
  have hy : y=step x e := by
    exact congrArg SevenTagCharge.Ledger.config (WindowA0Ledger.physical_step S z.tag e)
  have hz' := (close hn S J H z e hz).resolve_left hNext
  have hOld : ¬WindowA0Ledger.done z.tag := fun ho => hNext (by
    change (WindowA0Ledger.next S z.tag e).reason.isSome=true
    rw [WindowA0Ledger.terminal_sticky S z.tag e ho]
    exact ho)
  have ho := hz.resolve_left hOld
  have hGhost : (y J).leader=false := hz'.1.rightGhost
  have hNoMint (k : Nat) (hk : k<(cut z).gap) :
      (x (liftedSite (cut z).top k)).leader=false := by
    cases k with
    | zero => rw [liftedSite_zero]; exact ho.1.topGhost
    | succ k =>
      apply Bool.eq_false_iff.mpr
      intro h
      have hm := ho.1.mc (liftedSite (cut z).top k) (.inl (by rwa [←liftedSite_succ]))
      rw [ho.1.openBonds k hk] at hm
      cases hm
  have hslot : incoming (cut z).top (cut z).gap=z.tag.jSlot := by
    apply FreshSeparation.succ_inj
    rw [incoming_right]
    exact ho.1.fixedRight.trans ho.2.2.symm
  by_cases he : e=z.tag.jSlot
  · rw [if_pos he]
    have hE : rightNeighbor e=J := (congrArg rightNeighbor he).trans ho.2.2
    have hm : (x e).mark=true := by
      have H' := ho.2.1.1.covers z.tag.jSlot
      have hJtag := ho.2.1.2.2.2.1
      simpa [x,he,hJtag] using H'.symm
    have hp : geometricPay (x e) (x (rightNeighbor e))=false := by
      have q := (WindowA0Drained.drained_step hn x (cut z).top e ho.1.gapPos ho.1.markTop
        ((he.trans hslot.symm) ▸ hm) ho.1.empty hNoMint).1
      have hs : e=incoming (cut z).top (cut z).gap := he.trans hslot.symm
      simp [moved,beq_iff_eq.mpr hs] at q
      exact q
    have hpM : (stepPrefix (x e) (x (rightNeighbor e))).1.mark=true := by
      rw [←mark_prefix]
      have q := covered_step_mark hn x ho.1.mc e e
      simp [hp,step] at q
      exact q.trans hm
    have hPost : (pairStep (x e) (x (rightNeighbor e))).2.leader=false := by
      rw [hy,←hE] at hGhost
      simpa [step,right_ne hn e] using hGhost
    have F := door_source_exact _ _ hpM hPost
    change (y J).source=_ ∧ _
    rw [hy,←hE]
    simpa [step,right_ne hn e] using F
  · rw [if_neg he]
    have hE : rightNeighbor e≠J := fun h => he (FreshSeparation.succ_inj (h.trans ho.2.2.symm))
    change (y J).source=_
    rw [hy]
    by_cases H' : J=e
    · subst e
      simpa [step] using left_source (x J) (x (rightNeighbor J))
    · simp [step,H',Ne.symm hE]
      rfl

def L1 {p c n : Nat} (z : WindowA0ClosedEntry.State p c n) (e : Fin n) : Prop :=
  e=z.tag.jSlot ∧
    (doorArrivals (z.tag.ledger.config (rightNeighbor e)).source (z.tag.ledger.config e).rail).source=.i0

theorem row_launch_kind {Q : Nat} (s : Source Q) (r : Rail) :
    ((doorArrivals s r).source=.i0 → (serviceDoor s r).source=.i1) ∧
    (∀ k, (doorArrivals s r).source=.count k → (serviceDoor s r).source=.await k) := by
  have wire : (serviceDoor s r).source=(launch (doorArrivals s r)).source := by
    change (turn true (launch (doorArrivals s r))).source=_
    cases h : (launch (doorArrivals s r)).right <;> simp [turn,h]
  rw [wire]
  constructor
  · intro h
    unfold launch
    rw [h]
  · intro k h
    unfold launch
    rw [h]

/-- With a genuine previous L2(k) retained and no physical D, the
fixed J source stutters if this mark does not launch; a non-L1 launch
strictly advances k. The test is on the actual old J-door edge. -/
theorem await_step {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J e : Fin n) (H : Nat)
    (z : WindowA0ClosedEntry.State p c n) (hz : Admitted initial S J H z)
    (hNext : ¬WindowA0Ledger.done (next S z e).tag)
    (k : Fin (2*c)) (hK : (z.tag.ledger.config J).source=.await k) :
    if WindowA0ReverseSweep.freshDoor z e then
      (L1 z e ∧ ((next S z e).tag.ledger.config J).source=.i1) ∨
        (¬L1 z e ∧ ∃ j : Fin (2*c), k.val<j.val ∧
          ((next S z e).tag.ledger.config J).source=.await j)
    else ((next S z e).tag.ledger.config J).source=.await k := by
  classical
  have good := physical_source hn S J e H z hz hNext
  dsimp only at good
  have hold : ¬WindowA0Ledger.done z.tag := by
    intro h
    apply hNext
    change (WindowA0Ledger.next S z.tag e).reason.isSome=true
    rw [WindowA0Ledger.terminal_sticky S z.tag e h]
    exact h
  by_cases he : e=z.tag.jSlot
  · rw [if_pos he] at good
    rw [hK] at good
    have hE : rightNeighbor e=J := (congrArg rightNeighbor he).trans (hz.resolve_left hold).2.2
    let r := (z.tag.ledger.config e).rail
    have F : WindowA0ReverseSweep.freshDoor z e ↔ launches (.await k) r := by
      rw [WindowA0ReverseSweep.freshDoor,hE,hK]
      exact and_iff_right he
    have G : L1 z e ↔ (doorArrivals (.await k) r).source=.i0 := by
      rw [L1,hE,hK]
      exact and_iff_right he
    by_cases hL : launches (.await k) r
    · rw [if_pos (F.mpr hL)]
      rcases hL with h|⟨j,h⟩
      · exact .inl ⟨G.mpr h,good.1.trans ((row_launch_kind _ _).1 h)⟩
      · have ng : ¬L1 z e := fun b => by
          have h' := G.mp b
          rw [h] at h'
          contradiction
        exact .inr ⟨ng,j,next_launch_index k j r h,good.1.trans ((row_launch_kind _ _).2 j h)⟩
    · rw [if_neg (fun h => hL (F.mp h))]
      exact good.1.trans (await_no_exit k r hL (by rw [good.2]; decide))
  · have hL : ¬WindowA0ReverseSweep.freshDoor z e := fun h => he h.1
    rw [if_neg hL]
    rw [if_neg he] at good
    exact good.trans hK

theorem birthless_launch_shape {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J e : Fin n) (H : Nat)
    (z : WindowA0ClosedEntry.State p c n) (hz : Admitted initial S J H z)
    (hd : ¬WindowA0Ledger.done (next S z e).tag)
    (hL : WindowA0ReverseSweep.freshDoor z e) :
    (L1 z e ∧ ((next S z e).tag.ledger.config J).source=.i1) ∨
      (¬L1 z e ∧ ∃ j : Fin (2*c), ((next S z e).tag.ledger.config J).source=.await j) := by
  have hO : ¬WindowA0Ledger.done z.tag := by
    intro h
    apply hd
    change (WindowA0Ledger.next S z.tag e).reason.isSome=true
    rw [WindowA0Ledger.terminal_sticky S z.tag e h]
    exact h
  have H' := physical_source hn S J e H z hz hd
  dsimp only at H'
  rw [if_pos hL.1] at H'
  let a := (z.tag.ledger.config J).source
  let r := (z.tag.ledger.config e).rail
  have hJ : rightNeighbor e=J := (congrArg rightNeighbor hL.1).trans (hz.resolve_left hO).2.2
  have h := hL.2
  rw [hJ] at h
  change launches a r at h
  have E : L1 z e ↔ (doorArrivals a r).source=.i0 := by
    unfold L1
    rw [hJ]
    exact and_iff_right hL.1
  rcases h with h|⟨k,h⟩
  · exact .inl ⟨E.mpr h,H'.1.trans ((row_launch_kind _ _).1 h)⟩
  · exact .inr ⟨fun hL => by
      have G := E.mp hL
      rw [h] at G
      contradiction, k,H'.1.trans ((row_launch_kind _ _).2 k h)⟩

/-- An L1 mark writes a new INIT worker on the initiator. It can be
identified by the originating mark rather than a scan of dirty rails. -/
theorem actual_l1_worker {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J e : Fin n) (H : Nat)
    (z : WindowA0ClosedEntry.State p c n) (hz : Admitted initial S J H z)
    (hd : ¬WindowA0Ledger.done (next S z e).tag)
    (hL : L1 z e) :
    ((next S z e).tag.ledger.config e).rail=.ui := by
  let x := z.tag.ledger.config
  have hO : ¬WindowA0Ledger.done z.tag := by
    intro h
    apply hd
    change (WindowA0Ledger.next S z.tag e).reason.isSome=true
    rw [WindowA0Ledger.terminal_sticky S z.tag e h]
    exact h
  have ho := hz.resolve_left hO
  have hp := (close hn S J H z e hz).resolve_left hd
  have hJ : rightNeighbor e=J := (congrArg rightNeighbor hL.1).trans ho.2.2
  have hSlot : e=incoming (cut z).top (cut z).gap := by
    apply FreshSeparation.succ_inj
    rw [incoming_right]
    exact hJ.trans ho.1.fixedRight.symm
  have hNoMint (k : Nat) (hk : k<(cut z).gap) :
      (x (liftedSite (cut z).top k)).leader=false := by
    cases k with
    | zero => rw [liftedSite_zero]; exact ho.1.topGhost
    | succ k =>
      apply Bool.eq_false_iff.mpr
      intro h
      have hm := ho.1.mc (liftedSite (cut z).top k) (.inl (by rwa [←liftedSite_succ]))
      rw [ho.1.openBonds k hk] at hm
      cases hm
  have hm : (x e).mark=true := by
    have H' := ho.2.1.1.covers z.tag.jSlot
    have hJtag := ho.2.1.2.2.2.1
    simpa [x,hL.1,hJtag] using H'.symm
  have hpay : geometricPay (x e) (x (rightNeighbor e))=false := by
    have q := (WindowA0Drained.drained_step hn x (cut z).top e ho.1.gapPos ho.1.markTop
      (hSlot ▸ hm) ho.1.empty hNoMint).1
    simpa [moved,beq_iff_eq.mpr hSlot] using q
  have hmark : (stepPrefix (x e) (x (rightNeighbor e))).1.mark=true := by
    rw [←mark_prefix]
    have q := covered_step_mark hn x ho.1.mc e e
    simp [hpay,step] at q
    exact q.trans hm
  have phy : (next S z e).tag.ledger.config=step x e :=
    congrArg SevenTagCharge.Ledger.config (WindowA0Ledger.physical_step S z.tag e)
  have hghost := hp.1.rightGhost
  change ((next S z e).tag.ledger.config J).leader=false at hghost
  rw [phy,←hJ] at hghost
  have hg : (pairStep (x e) (x (rightNeighbor e))).2.leader=false := by
    simpa [step,right_ne hn e] using hghost
  have hpre : (stepPrefix (x e) (x (rightNeighbor e))).2.leader=false := by
    unfold pairStep finishBirth at hg
    dsimp only at hg
    split at hg
    · contradiction
    · exact hg
  have hr := (WindowA0Cleanup.pinned_rails (x e) (x (rightNeighbor e)) hpre hmark).1
  have frame := FreshEpochAuthentication.prefix_payload (x e) (x (rightNeighbor e))
  rw [frame.1,frame.2.2] at hr
  have H' : (serviceDoor (x (rightNeighbor e)).source (x e).rail).left=.ui := by
    have hf := hL.2
    unfold serviceDoor patrol
    rw [show ∀ a : Patrol (2*c), move true a=a from fun _ => rfl]
    change (turn true (launch (doorArrivals (x (rightNeighbor e)).source (x e).rail))).left=.ui
    have hturn (a : Patrol (2*c)) : (turn true a).left=a.left := by
      cases ha : a.right <;> simp [turn,ha]
    rw [hturn]
    change (doorArrivals (x (rightNeighbor e)).source (x e).rail).source=.i0 at hf
    unfold launch
    rw [hf]
  rw [phy]
  simpa [step] using hr.trans H'

theorem launch_preserves_xfree {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat)
    (z : WindowA0CleanupPass.State p c n) (e : Fin n)
    (hz : WindowA0CleanupPass.Good initial S J H z)
    (ha : ¬WindowA0CleanupPass.ready z)
    (hl : WindowA0CleanupPass.launchDecision (WindowA0CleanupPass.next S z e)) :
    WindowA0CleanupChain.XFree (WindowA0CleanupPass.next S z e).physical := by
  have H' := (WindowA0CleanupPass.first_launch_iff z e hz ha).mp hl
  have hn' : ¬WindowA0Ledger.done (next S z.physical e).tag := by
    simpa only [WindowA0CleanupPass.projects] using H'.2.2
  rw [WindowA0CleanupPass.projects]
  refine WindowA0CleanupChain.xfree_next (initial:=initial) hn S J H z.physical e ?_ ?_ hn'
  · cases z with
    | x _ | done _ _ => exact False.elim H'.1
    | reverse z => exact hz.1.1
    | forward z => exact hz.1.1
  · cases z with
    | x _ | done _ _ => exact False.elim H'.1
    | reverse z => exact hz.2.2
    | forward z => exact (hz.1.2.resolve_left hz.2).2.1

end L4.WindowA0DirtyRank
