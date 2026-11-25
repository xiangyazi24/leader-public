import Leader.L4.RearSwept
import Leader.L4.RearTrackGeometry

namespace L4.RearTrace
open TaggedTrace

def LiveSweep {p c n : Nat} (s : Observer p c n) (b : Fin n) : Prop :=
  s.phase = .pinned ∨ ∀ d, FirstRear s.tag.config b d →
    Swept s.tag.config b d s.tag.moveCount

theorem firstRear_unique {p c n d e : Nat} {x : Config p c n} {b : Fin n}
    (h : FirstRear x b d) (g : FirstRear x b e) : d = e := by
  rcases Nat.lt_trichotomy d e with hd | he | he
  · exact False.elim (g.before d hd h.marked)
  · exact he
  · exact False.elim (h.before e he g.marked)

theorem rearMoves_le_step {p c n : Nat} (i e : Fin n) (s : Observer p c n) :
    s.rearMoves ≤ (rearAdvance i s e).rearMoves := by
  unfold rearAdvance
  split
  · exact Nat.le_refl _
  · exact Nat.le_add_right _ _

theorem liveSweep_step {p c n d0 : Nat} (hn : 4 ≤ n) (i e b b' : Fin n)
    (s : Observer p c n) (hm : MCOV s.tag.config)
    (hb : s.tag.carrier = some b) (hb' : (rearAdvance i s e).tag.carrier = some b')
    (hg : LiveGeometry d0 s b) (hs : LiveSweep s b) :
    LiveSweep (rearAdvance i s e) b' := by
  let t := rearAdvance i s e
  have hg' := liveGeometry_step hn i e b b' s hm hb hb' hg
  have hc : t.tag.config = step s.tag.config e := by
    rw [rearAdvance_tag,projection_step]
  have ht : carrierStep s.tag.config e (some b) = some b' := by
    simpa [t,rearAdvance_tag,advance,hb] using hb'
  have hN : t.tag.moveCount = s.tag.moveCount + (b == e).toNat := by
    simp [t,rearAdvance_tag,advance,hb,ht]
  cases hg' with
  | pinned hp _ => exact Or.inl hp
  | tracking hp d' _ hd' hgap' =>
    refine Or.inr ?_
    intro d'' hd''
    rw [firstRear_unique hd'' hd']
    cases hg with
    | pinned hp0 _ =>
      exfalso
      apply hp
      cases hr : s.rear <;> simp [rearAdvance,hr,phaseAfter,hp0]
    | tracking hp0 d _ hd hgap =>
      have hSweep := (hs.resolve_left hp0) d hd
      have hM := rearMoves_le_step i e s
      change t.tag.moveCount + d0 = t.rearMoves + d' at hgap'
      change s.rearMoves ≤ t.rearMoves at hM
      by_cases he : b = e
      · subst e
        obtain ⟨rfl,htr⟩ := carrierStep_selected_survives s.tag.config b b' ht
        have hN' : t.tag.moveCount = s.tag.moveCount + 1 := by simpa using hN
        have hBound : d' ≤ d+1 := by omega
        rw [hc,hN']
        have hh := swept_moves hn s.tag.config b hd hSweep htr
        exact ⟨fun k hk hkN => hh.1 k (by omega) hkN,hh.2⟩
      · have hEq := carrierStep_not_selected_stays s.tag.config e b b' he ht
        subst b'
        have hN' : t.tag.moveCount = s.tag.moveCount := by simpa [show (b == e) = false from Bool.eq_false_iff.mpr (fun h => he (beq_iff_eq.mp h))] using hN
        have hBound : d' ≤ d := by omega
        rw [hc,hN']
        apply swept_stationary hm b e hd hSweep hBound (Ne.symm he)
        intro h
        by_cases hR : tagResident (s.tag.config e) (s.tag.config b) = true
        · exact hR
        · simp [carrierStep,he,h,hR] at ht


theorem liveSweep_fold {p c n d0 : Nat} (hn : 4 ≤ n) (i : Fin n)
    (s : Observer p c n) (b b' : Fin n) (w : List (Fin n))
    (hm : MCOV s.tag.config) (hb : s.tag.carrier = some b)
    (hb' : (rearFold i s w).tag.carrier = some b')
    (hg : LiveGeometry d0 s b) (hs : LiveSweep s b) :
    LiveGeometry d0 (rearFold i s w) b' ∧ LiveSweep (rearFold i s w) b' := by
  induction w generalizing s b with
  | nil =>
    have hEq : b = b' := Option.some.inj (hb.symm.trans hb')
    subst b'
    exact ⟨hg,hs⟩
  | cons e w ih =>
    let t := rearAdvance i s e
    have hc : t.tag.config = step s.tag.config e := by
      rw [rearAdvance_tag,projection_step]
    have hmc : MCOV t.tag.config := hc.symm ▸ mcov_step hn _ hm e
    cases ht : t.tag.carrier with
    | none =>
      have hEnd := ended_run t.tag w ht
      rw [← rearFold_tag] at hEnd
      have hx : some b' = none := hb'.symm.trans hEnd
      contradiction
    | some j =>
      exact ih t j hmc ht hb'
        (liveGeometry_step hn i e b j s hm hb ht hg)
        (liveSweep_step hn i e b j s hm hb ht hg hs)

theorem liveSweep_track {p c n : Nat} (x : Config p c n) (i b : Fin n)
    (w : List (Fin n)) (h : LiveCoveredTrace x i w)
    (hb : (rearTrack x i w).tag.carrier = some b) :
    ∃ d0, LiveGeometry d0 (rearTrack x i w) b ∧ LiveSweep (rearTrack x i w) b := by
  obtain ⟨_,_,hn,hnd,hm,_,hAlive⟩ := h
  obtain ⟨d0,hd0⟩ := firstRear_exists x i hnd
  have hi : (init x i).carrier = some i := by
    unfold init
    dsimp only
    split
    · rfl
    · exact False.elim (hAlive (ended_run _ w (by simp_all [ended,init])))
  have hg : LiveGeometry d0 (rearInit x i) i :=
    .tracking (by exact Phase.noConfusion) d0 (rearAt_eq_back hd0) hd0 (by rfl)
  have hs : LiveSweep (rearInit x i) i := Or.inr (fun d _ => swept_initial x i d)
  exact ⟨d0, liveSweep_fold hn i (rearInit x i) i b w hm hi hb hg hs⟩


private theorem birth_eq {p c : Nat} (u v : Site p c)
    (hv : v.leader = false) :
    (pairStep u v).2.leader = true →
      tagBirth u v = true ∧ (pairStep u v).2.shield = true ∧
        (pairStep u v).2.signal = .zero := by
  have hprefix : (stepPrefix u v).2.leader = false := by
    have hf : fireResponder v = v := by simp [fireResponder,hv]
    unfold stepPrefix native
    rw [hf]
    generalize fireInitiator (materialize u v) = a
    have hi : impact a v = (a,v) := by simp [impact,hv]
    rw [hi]
    dsimp only
    have hpay (l r : Site p c) : (payment l r).2.leader = r.leader := by
      unfold payment
      split
      · rfl
      · split
        · rfl
        · split <;> rfl
    simp only [hpay]
    unfold followerBullet
    split
    · split <;> exact hv
    · exact hv
  unfold pairStep tagBirth
  generalize stepPrefix u v = uv at hprefix ⊢
  rcases uv with ⟨a,b⟩
  dsimp only at hprefix ⊢
  generalize patrol (b.leader || a.mark) (pinned a b) b.leader b.source a.rail b.rail = r
  cases hm : a.mark <;> cases hf : r.fire <;> simp [pinned,patrolWrite,finishBirth,hprefix,hm]

private theorem distinct {n : Nat} (hn : 4 ≤ n) (i : Fin n) : rightNeighbor i ≠ i := by
  intro h
  have h' : liftedSite i 1 = liftedSite i 0 := by simpa [liftedSite_succ,liftedSite_zero] using h
  have hb := liftedSite_inj i (by omega : 1<n) (by omega : 0<n) h'
  omega

private theorem right_ne_pred {n : Nat} (hn : 4 ≤ n) (i : Fin n) :
    rightNeighbor i ≠ predecessor i := by
  intro h
  have h' : liftedSite i 1 = liftedSite i (n-1) := by
    simpa [liftedSite_succ,liftedSite_zero,predecessor,back] using h
  have hb := liftedSite_inj i (by omega : 1<n) (by omega : n-1<n) h'
  omega

theorem rear_shift_landing_nonleader {p c n d : Nat} (hn : 4 ≤ n)
    {x : Config p c n} (hm : MCOV x) (b : Fin n) (hf : FirstRear x b d)
    (hd : 0 < d) :
    (step x (predecessor (back b d)) (rightNeighbor (back b d))).leader = false := by
  have hdn := hf.lt
  have hpred := predecessor_back b (d-1) (by omega)
  rw [show d-1+1=d by omega] at hpred
  have hr : rightNeighbor (back b d) = back b (d-1) := by rw [← hpred,right_predecessor]
  have hb : (x (rightNeighbor (back b d))).leader = false := by
    apply Bool.eq_false_iff.mpr
    intro hl
    apply hf.before (d-1) (by omega)
    rw [hpred]
    exact hm _ (Or.inl hl)
  simpa [step,right_predecessor,right_ne_pred hn,distinct hn] using hb

/-- In a surviving tracked ghost→final transition, the original rear stays
put, the selected bond is its incoming bond, and the new shield and zero
signal come from the literal P5 commit row. -/
theorem ghost_to_final_is_birth {p c n d : Nat} (hn : 4 ≤ n) (i e b b' : Fin n)
    (s : Observer p c n) (hm : MCOV s.tag.config)
    (hb : s.tag.carrier = some b) (hb' : (rearAdvance i s e).tag.carrier = some b')
    (hg : s.phase = .ghost) (hr : s.rear = some (back b d))
    (hf : FirstRear s.tag.config b d)
    (hphase : (rearAdvance i s e).phase = .finalLeader)
    (hGhost : (s.tag.config (back b d)).leader = false) :
    let r := back b d
    (rearAdvance i s e).rear = some r ∧ e = predecessor r ∧
      tagBirth (s.tag.config e) (s.tag.config r) = true ∧
      (0 < d) ∧
      ((rearAdvance i s e).tag.config r).leader = true ∧
      ((rearAdvance i s e).tag.config r).shield = true ∧
      ((rearAdvance i s e).tag.config r).signal = .zero := by
  let r := back b d
  let x := s.tag.config
  let t := rearAdvance i s e
  have hconf : t.tag.config = step x e := by rw [rearAdvance_tag,projection_step]
  have hN : rearShifts s e r = false := by
    cases hs : rearShifts s e r
    · rfl
    · have he := ((paid_moves_rear_iff hm i e r s rfl).1 hs).1
      by_cases hd : d = 0
      · have hEq : s.tag.carrier = s.rear := by rw [hb,hr,hd,back_zero]
        simp [rearAdvance,hr,hg,show (Phase.ghost == Phase.pinned) = false from rfl,show rearShifts s e (back b d) = true from hs,
          phaseAfter,hEq] at hphase
      · have hL : (step x e (rightNeighbor r)).leader = false := by
          simpa [he] using rear_shift_landing_nonleader hn hm b hf (Nat.pos_of_ne_zero hd)
        have hh : ((advance s.tag e).config (rightNeighbor r)).leader = false := by
          rw [projection_step]; exact hL
        simp [rearAdvance,hr,hg,show (Phase.ghost == Phase.pinned) = false from rfl,show rearShifts s e (back b d) = true from hs,phaseAfter,
          show ((advance s.tag e).config (rightNeighbor (back b d))).leader = false from hh] at hphase
        split at hphase <;> contradiction
  have hR : t.rear = some r := by
    simp [t,rearAdvance,hr,hg,show rearShifts s e (back b d) = false from hN,r]
  have hL : (step x e r).leader = true := by
    have h' : (advance s.tag e).config = step x e := projection_step _ _
    by_cases hl : (step x e r).leader = true
    · exact hl
    · have hz : (step x e (back b d)).leader = false := Bool.eq_false_iff.mpr hl
      simp [rearAdvance,hr,hg,show (Phase.ghost == Phase.pinned) = false from rfl,show rearShifts s e (back b d) = false from hN,phaseAfter,h',hz] at hphase
  have he : e ≠ r := by
    intro he
    have hh := (pair_geometric_fields (x e) (x (rightNeighbor e))).2.1
    rw [he] at hh
    have h' : (step x r r).leader = false := by simpa [step] using hh.trans hGhost
    rw [he,h'] at hL
    contradiction
  have her : rightNeighbor e = r := by
    by_cases hh : rightNeighbor e = r
    · exact hh
    · have h' : (step x e r).leader = false := by
        simpa [step,Ne.symm he,Ne.symm hh] using hGhost
      rw [h'] at hL
      contradiction
  have hra : e = predecessor r := by rw [← her,predecessor_right]
  have hl' : (pairStep (x e) (x r)).2.leader = true := by
    simpa [step,Ne.symm he,her] using hL
  obtain ⟨hB,hS,hZ⟩ := birth_eq (x e) (x r) hGhost hl'
  have hd : 0 < d := by
    apply Nat.pos_of_ne_zero
    intro hd
    have hrb : r = b := by simp [r,hd,back_zero]
    have hCarrier : carrierStep x e (some b) = some b' := by
      simpa [rearAdvance_tag,advance,hb,x] using hb'
    have hR' : tagResident (x e) (x r) = true := by
      by_cases hs : tagResident (x e) (x r) = true
      · exact hs
      · have hne : b ≠ e := hrb ▸ Ne.symm he
        simp [carrierStep,hne,her,hrb,show ¬ tagResident (x e) (x b) = true by exact hrb ▸ hs] at hCarrier
    have hnB := (tagResident_no_birth_iff (x e) (x r)).mp hR'
    simp [hB] at hnB
  refine ⟨hR,hra,hB,hd,?_,?_,?_⟩ <;> rw [hconf]
  · exact hL
  · change (step x e r).shield = true
    simpa [step,Ne.symm he,her] using hS
  · change (step x e r).signal = .zero
    simpa [step,Ne.symm he,her] using hZ

/-- A final rear cannot die, shift, unshield, or change phase once its
swept successor is available. The old and new rear identities coincide. -/
theorem final_rear_protected {p c n d N : Nat} (hn : 4 ≤ n) (i e b : Fin n)
    (s : Observer p c n) (hm : MCOV s.tag.config)
    (hr : s.rear = some (back b d)) (hf : FirstRear s.tag.config b d)
    (hs : Swept s.tag.config b d N) (hd : 0 < d) (hdN : d ≤ N)
    (hp : s.phase = .finalLeader)
    (hL : (s.tag.config (back b d)).leader = true)
    (hS : (s.tag.config (back b d)).shield = true)
    (hZ : (s.tag.config (back b d)).signal ≠ .one) :
    let r := back b d
    let t := rearAdvance i s e
    t.phase = .finalLeader ∧ t.rear = some r ∧ t.rearMoves = s.rearMoves ∧
      (t.tag.config r).leader = true ∧ (t.tag.config r).shield = true ∧
      (t.tag.config r).signal ≠ .one := by
  let r := back b d
  let x := s.tag.config
  have hKeep := swept_fixed_rear hm b e hf hs hd hdN hL hS hZ
  have hNo : rearShifts s e r = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨he,hpay⟩ := (paid_moves_rear_iff hm i e r s rfl).mp hh
    have her : rightNeighbor e = r := by rw [he,right_predecessor]
    have hne : r ≠ e := by
      intro heq
      exact distinct hn e (her.trans heq)
    have hfalse := geometricPay_responder_nonleader (x e) (x (rightNeighbor e)) hpay
    have hl' : (step x e r).leader = false := by
      simpa [step,hne,Ne.symm hne,her] using hfalse
    have ht' : (step x e r).leader = true := hKeep.1
    rw [hl'] at ht'
    contradiction
  have hphase : (Phase.finalLeader == Phase.pinned) = false := rfl
  have hconf : (rearAdvance i s e).tag.config = step x e := by
    rw [rearAdvance_tag,projection_step]
  refine ⟨?_,?_,?_,?_⟩
  · simp [rearAdvance,hr,hp,hphase,show rearShifts s e (back b d) = false from hNo,
      phaseAfter]
  · simp [rearAdvance,hr,hp,hphase,show rearShifts s e (back b d) = false from hNo]
  · simp [rearAdvance,hr,hp,hphase,show rearShifts s e (back b d) = false from hNo]
  · rw [hconf]
    exact hKeep

/-- A physically protected final rear at a positive distance after the cut. -/
def FinalRear {p c n : Nat} (s : Observer p c n) (b : Fin n) : Prop :=
  s.phase = .finalLeader ∧ 2*n ≤ s.tag.moveCount ∧
    ∃ d, 0 < d ∧ FirstRear s.tag.config b d ∧ s.rear = some (back b d) ∧
      (s.tag.config (back b d)).leader = true ∧
      (s.tag.config (back b d)).shield = true ∧
      (s.tag.config (back b d)).signal ≠ .one

theorem tagMoves_le_step {p c n : Nat} (i e : Fin n) (s : Observer p c n) :
    s.tag.moveCount ≤ (rearAdvance i s e).tag.moveCount := by
  rw [rearAdvance_tag]
  unfold advance
  split
  · exact Nat.le_refl _
  · exact Nat.le_add_right _ _

theorem finalRear_step {p c n d0 : Nat} (hn : 4 ≤ n) (i e b b' : Fin n)
    (s : Observer p c n) (hm : MCOV s.tag.config)
    (hb : s.tag.carrier = some b) (hb' : (rearAdvance i s e).tag.carrier = some b')
    (hg : LiveGeometry d0 s b) (hs : LiveSweep s b) (hF : FinalRear s b) :
    FinalRear (rearAdvance i s e) b' := by
  obtain ⟨hp,hcut,d,hd,hf,hr,hL,hS,hZ⟩ := hF
  have hdN : d ≤ s.tag.moveCount := by have := hf.lt; omega
  have hsw := (hs.resolve_left (by rw [hp]; exact Phase.noConfusion)) d hf
  obtain ⟨hp',hr',hM,hL',hS',hZ'⟩ :=
    final_rear_protected hn i e b s hm hr hf hsw hd hdN hp hL hS hZ
  have hN := tagMoves_le_step i e s
  have hg' := liveGeometry_step hn i e b b' s hm hb hb' hg
  have hg0 : s.tag.moveCount + d0 = s.rearMoves + d := by
    cases hg with
    | pinned hP _ => rw [hp] at hP; contradiction
    | tracking _ d' _ hd' hh => rwa [firstRear_unique hd' hf] at hh
  refine ⟨hp',Nat.le_trans hcut hN,?_⟩
  cases hg' with
  | pinned hP _ => rw [hp'] at hP; contradiction
  | tracking _ d' hr'' hf' hGap =>
    have he : back b' d' = back b d := Option.some.inj (hr''.symm.trans hr')
    rw [hM] at hGap
    exact ⟨d',by omega,hf',hr'',he.symm ▸ hL',he.symm ▸ hS',he.symm ▸ hZ'⟩

theorem finalRear_of_ghost_birth {p c n d0 d : Nat} (hn : 4 ≤ n) (i e b b' : Fin n)
    (s : Observer p c n) (hm : MCOV s.tag.config)
    (hb : s.tag.carrier = some b) (hb' : (rearAdvance i s e).tag.carrier = some b')
    (hg : s.phase = .ghost) (hr : s.rear = some (back b d))
    (hf : FirstRear s.tag.config b d)
    (hg0 : LiveGeometry d0 s b) (hcut : 2*n ≤ s.tag.moveCount)
    (hp : (rearAdvance i s e).phase = .finalLeader)
    (hGhost : (s.tag.config (back b d)).leader = false) :
    FinalRear (rearAdvance i s e) b' := by
  obtain ⟨hr',_,_,hd,hL,hS,hZ⟩ :=
    ghost_to_final_is_birth hn i e b b' s hm hb hb' hg hr hf hp hGhost
  let r := back b d
  have hNo : rearShifts s e r = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    have hr'' : (rearAdvance i s e).rear = some (rightNeighbor r) := by
      simp [rearAdvance,hr,hg,show (Phase.ghost == Phase.pinned) = false from rfl,
        show rearShifts s e (back b d) = true from hh]; rfl
    exact distinct hn r (Option.some.inj (hr''.symm.trans hr'))
  have hM : (rearAdvance i s e).rearMoves = s.rearMoves := by
    simp [rearAdvance,hr,hg,show rearShifts s e (back b d) = false from hNo]
  have hN := tagMoves_le_step i e s
  have hg' := liveGeometry_step hn i e b b' s hm hb hb' hg0
  have hG : s.tag.moveCount + d0 = s.rearMoves + d := by
    cases hg0 with
    | pinned hP _ => rw [hg] at hP; contradiction
    | tracking _ d' _ hd' hh => rwa [firstRear_unique hd' hf] at hh
  refine ⟨hp,Nat.le_trans hcut hN,?_⟩
  cases hg' with
  | pinned hP _ => rw [hp] at hP; contradiction
  | tracking _ d' hr'' hf' hGap =>
    have he : back b' d' = back b d := Option.some.inj (hr''.symm.trans hr')
    rw [hM] at hGap
    have hh : ((rearAdvance i s e).tag.config (back b d)).signal ≠ .one := by
      rw [hZ]; exact Signal.noConfusion
    exact ⟨d',by omega,hf',hr'',he.symm ▸ hL,he.symm ▸ hS,he.symm ▸ hh⟩

theorem finalRear_fold {p c n d0 : Nat} (hn : 4 ≤ n) (i : Fin n)
    (s : Observer p c n) (b b' : Fin n) (w : List (Fin n))
    (hm : MCOV s.tag.config) (hb : s.tag.carrier = some b)
    (hb' : (rearFold i s w).tag.carrier = some b')
    (hg : LiveGeometry d0 s b) (hs : LiveSweep s b) (hF : FinalRear s b) :
    FinalRear (rearFold i s w) b' := by
  induction w generalizing s b with
  | nil =>
    have hEq : b = b' := Option.some.inj (hb.symm.trans hb')
    subst b'
    exact hF
  | cons e w ih =>
    let t := rearAdvance i s e
    have hc : t.tag.config = step s.tag.config e := by
      rw [rearAdvance_tag,projection_step]
    have hmc : MCOV t.tag.config := hc.symm ▸ mcov_step hn _ hm e
    cases ht : t.tag.carrier with
    | none =>
      have hEnd := ended_run t.tag w ht
      rw [← rearFold_tag] at hEnd
      have hx : some b' = none := hb'.symm.trans hEnd
      contradiction
    | some j =>
      exact ih t j hmc ht hb'
        (liveGeometry_step hn i e b j s hm hb ht hg)
        (liveSweep_step hn i e b j s hm hb ht hg hs)
        (finalRear_step hn i e b j s hm hb ht hg hs hF)

/-- Physical interpretation of the four unpinned observer phases. -/
def PhasePhysical {p c n : Nat} (s : Observer p c n) (b : Fin n) : Prop :=
  (s.phase = .initial → s.tag.moveCount < 2*n) ∧
  (s.phase = .initialLeader → 2*n ≤ s.tag.moveCount ∧
    ∃ r, s.rear = some r ∧ (s.tag.config r).leader = true) ∧
  (s.phase = .ghost → 2*n ≤ s.tag.moveCount ∧
    ∃ r, s.rear = some r ∧ (s.tag.config r).leader = false) ∧
  (s.phase = .finalLeader → FinalRear s b)

private theorem phase_label {p c n : Nat} (s : Observer p c n) (t : Obs p c n)
    (r : Fin n) (m : Bool) (hcut : s.phase ≠ .initial → 2*n ≤ t.moveCount) :
    (phaseAfter s t r m = .initial → t.moveCount < 2*n) ∧
    (phaseAfter s t r m = .initialLeader → 2*n ≤ t.moveCount ∧ (t.config r).leader = true) ∧
    (phaseAfter s t r m = .ghost → 2*n ≤ t.moveCount ∧ (t.config r).leader = false) ∧
    (phaseAfter s t r m = .finalLeader → s.phase = .ghost ∨ s.phase = .finalLeader) := by
  unfold phaseAfter
  split
  · constructor <;> simp
  · cases hp : s.phase
    · by_cases hn : 2*n ≤ t.moveCount <;> cases hL : (t.config r).leader <;>
        simp [hn,Nat.lt_of_not_ge]
    · have hh := hcut (hp ▸ Phase.noConfusion)
      cases hL : (t.config r).leader <;> simp [hh]
    · have hh := hcut (hp ▸ Phase.noConfusion)
      cases hL : (t.config r).leader <;> simp [hh]
    · simp
    · simp

theorem phasePhysical_step {p c n d0 : Nat} (hn : 4 ≤ n) (i e b b' : Fin n)
    (s : Observer p c n) (hm : MCOV s.tag.config)
    (hb : s.tag.carrier = some b) (hb' : (rearAdvance i s e).tag.carrier = some b')
    (hg : LiveGeometry d0 s b) (hs : LiveSweep s b) (hP : PhasePhysical s b) :
    PhasePhysical (rearAdvance i s e) b' := by
  let t := rearAdvance i s e
  cases hg with
  | pinned hp _ =>
    have hp' : t.phase = .pinned := by
      cases hr : s.rear <;> simp [t,rearAdvance,hr,phaseAfter,hp]
    change PhasePhysical t b'
    simp [PhasePhysical,hp']
  | tracking hnp d hr hf hGap =>
    let r := back b d
    let m := !(s.phase == .pinned) && rearShifts s e r
    let r' := if m then rightNeighbor r else r
    have hp' : t.phase = phaseAfter s t.tag r' m := by
      rw [rearAdvance_tag]
      simp [t,rearAdvance,hr,r',m,r]
    have hr' : t.rear = some r' := by simp [t,rearAdvance,hr,r',m,r]
    have hc : s.phase ≠ .initial → 2*n ≤ t.tag.moveCount := by
      intro hi
      apply Nat.le_trans _ (tagMoves_le_step i e s)
      cases hp : s.phase with
      | initial => exact (hi hp).elim
      | initialLeader => exact (hP.2.1 hp).1
      | ghost => exact (hP.2.2.1 hp).1
      | finalLeader => exact (hP.2.2.2 hp).2.1
      | pinned => exact (hnp hp).elim
    obtain ⟨hI,hL,hG,hF⟩ := phase_label s t.tag r' m hc
    rw [← hp'] at hI hL hG hF
    refine ⟨hI,?_,?_,?_⟩
    · intro h
      exact ⟨(hL h).1,r',hr',(hL h).2⟩
    · intro h
      exact ⟨(hG h).1,r',hr',(hG h).2⟩
    · intro h
      have hg : LiveGeometry d0 s b := .tracking (by assumption) d hr hf hGap
      rcases hF h with hOld | hOld
      · obtain ⟨hcut, r0,hr0,hG0⟩ := hP.2.2.1 hOld
        have hEq : r0 = back b d := Option.some.inj (hr0.symm.trans hr)
        exact finalRear_of_ghost_birth hn i e b b' s hm hb hb' hOld hr hf hg hcut h (hEq ▸ hG0)
      · exact finalRear_step hn i e b b' s hm hb hb' hg hs (hP.2.2.2 hOld)

theorem phasePhysical_fold {p c n d0 : Nat} (hn : 4 ≤ n) (i : Fin n)
    (s : Observer p c n) (b b' : Fin n) (w : List (Fin n))
    (hm : MCOV s.tag.config) (hb : s.tag.carrier = some b)
    (hb' : (rearFold i s w).tag.carrier = some b')
    (hg : LiveGeometry d0 s b) (hs : LiveSweep s b) (hP : PhasePhysical s b) :
    PhasePhysical (rearFold i s w) b' := by
  induction w generalizing s b with
  | nil =>
    have hEq : b = b' := Option.some.inj (hb.symm.trans hb')
    subst b'
    exact hP
  | cons e w ih =>
    let t := rearAdvance i s e
    have hc : t.tag.config = step s.tag.config e := by
      rw [rearAdvance_tag,projection_step]
    have hmc : MCOV t.tag.config := hc.symm ▸ mcov_step hn _ hm e
    cases ht : t.tag.carrier with
    | none =>
      have hEnd := ended_run t.tag w ht
      rw [← rearFold_tag] at hEnd
      have hx : some b' = none := hb'.symm.trans hEnd
      contradiction
    | some j =>
      exact ih t j hmc ht hb'
        (liveGeometry_step hn i e b j s hm hb ht hg)
        (liveSweep_step hn i e b j s hm hb ht hg hs)
        (phasePhysical_step hn i e b j s hm hb ht hg hs hP)

theorem phasePhysical_track {p c n : Nat} (x : Config p c n) (i b : Fin n)
    (w : List (Fin n)) (h : LiveCoveredTrace x i w)
    (hb : (rearTrack x i w).tag.carrier = some b) :
    PhasePhysical (rearTrack x i w) b := by
  obtain ⟨_,_,hn,hnd,hm,_,hAlive⟩ := h
  obtain ⟨d0,hd0⟩ := firstRear_exists x i hnd
  have hi : (init x i).carrier = some i := by
    unfold init
    dsimp only
    split
    · rfl
    · exact False.elim (hAlive (ended_run _ w (by simp_all [ended,init])))
  have hg : LiveGeometry d0 (rearInit x i) i :=
    .tracking (by exact Phase.noConfusion) d0 (rearAt_eq_back hd0) hd0 (by rfl)
  have hs : LiveSweep (rearInit x i) i := Or.inr (fun d _ => swept_initial x i d)
  have hP : PhasePhysical (rearInit x i) i := by
    simp [PhasePhysical,rearInit,init]
    omega
  exact phasePhysical_fold hn i (rearInit x i) i b w hm hi hb hg hs hP

end L4.RearTrace

#print axioms L4.RearTrace.liveSweep_step
#print axioms L4.RearTrace.liveSweep_fold
#print axioms L4.RearTrace.liveSweep_track
#print axioms L4.RearTrace.ghost_to_final_is_birth

#print axioms L4.RearTrace.final_rear_protected

#print axioms L4.RearTrace.finalRear_step

#print axioms L4.RearTrace.finalRear_of_ghost_birth
#print axioms L4.RearTrace.finalRear_fold

#print axioms L4.RearTrace.phasePhysical_step

#print axioms L4.RearTrace.phasePhysical_fold
#print axioms L4.RearTrace.phasePhysical_track
