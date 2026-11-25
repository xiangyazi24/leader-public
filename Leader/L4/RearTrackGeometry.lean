import Leader.L4.RearGeometry

/-! # Tracking the actual rear identity until it pins the carrier -/

namespace L4.RearTrace
open TaggedTrace

theorem phaseAfter_pinned {p c n : Nat} (s : Observer p c n) (t : Obs p c n)
    (r : Fin n) (m : Bool) :
    phaseAfter s t r m = .pinned ↔
      s.phase = .pinned ∨ (m = true ∧ s.tag.carrier = s.rear) := by
  unfold phaseAfter
  classical
  have h : ((s.phase == Phase.pinned) || (m && s.tag.carrier == s.rear)) = true ↔
      s.phase = .pinned ∨ (m = true ∧ s.tag.carrier = s.rear) := by
    have hp (q : Phase) : (q == .pinned) = true ↔ q = .pinned := by cases q <;> decide
    simp only [Bool.or_eq_true,Bool.and_eq_true,hp,beq_iff_eq]
  by_cases hz : ((s.phase == Phase.pinned) || (m && s.tag.carrier == s.rear)) = true
  · simp only [if_pos hz,h.mp hz]
  · rw [if_neg hz]
    have hne := fun h' => hz (h.mpr h')
    rw [iff_false_intro hne]
    have hp : s.phase ≠ .pinned := fun hh => hne (Or.inl hh)
    cases hs : s.phase <;> simp [hs] at hp ⊢
    all_goals split <;> (try split) <;> decide

/-- A pinned carrier has an incoming-marked responder immediately ahead
(on its own outgoing edge). Otherwise the actual current rear is the
closest backward mark and its gap equals the two lifted displacements. -/
inductive LiveGeometry {p c n : Nat} (d0 : Nat) (s : Observer p c n) (b : Fin n) : Prop
  | pinned (phase : s.phase = .pinned) (mark : (s.tag.config b).mark = true)
  | tracking (phase : s.phase ≠ .pinned) (d : Nat)
      (rear : s.rear = some (back b d)) (closest : FirstRear s.tag.config b d)
      (gap : s.tag.moveCount + d0 = s.rearMoves + d)

theorem advance_moveCount {p c n : Nat} (s : Obs p c n) (e b b' : Fin n)
    (hb : s.carrier = some b) (hb' : (advance s e).carrier = some b') :
    (advance s e).moveCount = s.moveCount + (b == e).toNat := by
  have hstep : carrierStep s.config e (some b) = some b' := by
    simpa [advance,hb] using hb'
  simp [advance,hb,hstep]

theorem advance_carrier {p c n : Nat} (s : Obs p c n) (e b : Fin n)
    (hb : s.carrier = some b) :
    (advance s e).carrier = carrierStep s.config e (some b) := by simp [advance,hb]

theorem post_fields {p c n : Nat} (i e r : Fin n) (s : Observer p c n)
    (hr : s.rear = some r) :
    let m := !(s.phase == .pinned) && rearShifts s e r
    let r' := if m then rightNeighbor r else r
    let t := rearAdvance i s e
    t.rear = some r' ∧ t.rearMoves = s.rearMoves+m.toNat ∧
      t.phase = phaseAfter s (advance s.tag e) r' m := by
  simp [rearAdvance,hr]

theorem no_move_of_pin {p c n : Nat} (i e : Fin n) (s : Observer p c n)
    (h : s.phase = .pinned) :
    (rearAdvance i s e).phase = .pinned := by
  cases hr : s.rear with
  | none => simp [rearAdvance,hr,h]
  | some r => simp [rearAdvance,phaseAfter,hr,h]

theorem keep_outmark {p c n : Nat} (hn : 4 ≤ n) (x : Config p c n)
    (hc : MCOV x) (b e : Fin n) (hne : b ≠ e) (hm : (x b).mark = true) :
    (step x e b).mark = true := by
  rw [covered_step_mark hn x hc]
  split <;> simp [hm]

theorem liveGeometry_step {p c n d0 : Nat} (hn : 4 ≤ n) (i e b b' : Fin n)
    (s : Observer p c n) (hm : MCOV s.tag.config)
    (hb : s.tag.carrier = some b) (hb' : (rearAdvance i s e).tag.carrier = some b')
    (hg : LiveGeometry d0 s b) :
    LiveGeometry d0 (rearAdvance i s e) b' := by
  rw [rearAdvance_tag] at hb'
  have ht := (advance_carrier s.tag e b hb).symm.trans hb'
  have hconf : (rearAdvance i s e).tag.config = step s.tag.config e := by
    rw [rearAdvance_tag,projection_step]
  have hN := advance_moveCount s.tag e b b' hb hb'
  cases hg with
  | pinned hp hmark =>
    have he : b ≠ e := by
      intro he
      subst e
      have h' := (carrierStep_selected_survives s.tag.config b b' ht).2
      have hx := ((tagTransfer_iff _ _).mp h').2.2.2.1
      simp [hmark] at hx
    have hEq := carrierStep_not_selected_stays s.tag.config e b b' he ht
    subst b'
    exact .pinned (no_move_of_pin i e s hp)
      (hconf.symm ▸ keep_outmark hn s.tag.config hm b e he hmark)
  | tracking hp d hr hd hgap =>
    let r := back b d
    have hfields := post_fields i e r s hr
    dsimp only at hfields
    have hpg := paid_moves_rear_iff hm i e r s rfl
    have hnp : (s.phase == .pinned) = false := by
      cases he : s.phase <;> first | exact (hp he).elim | decide
    by_cases hsel : b=e
    · subst e
      obtain ⟨hEq,htr⟩ := carrierStep_selected_survives s.tag.config b b' ht
      subst b'
      obtain ⟨hnext,heq⟩ := firstRear_tag_moves hn s.tag.config hm b hd htr
      have hshift : rearShifts s b r = false := by
        cases hs : rearShifts s b r
        · rfl
        · have hh := paid_was_marked hm b (hpg.mp hs).2
          have hfalse := ((tagTransfer_iff _ _).mp htr).2.2.2.1
          simp [hfalse] at hh
      simp only [hnp,Bool.not_false,Bool.true_and,hshift,Bool.false_eq_true,if_false,
        Bool.toNat_false,Nat.add_zero] at hfields
      have hP : (rearAdvance i s b).phase ≠ .pinned := by
        rw [hfields.2.2]
        intro h
        simpa [hp] using (phaseAfter_pinned _ _ _ _).mp h
      refine .tracking hP (d+1) ?_ (hconf.symm ▸ hnext) ?_
      · rw [heq]; exact hfields.1
      · rw [rearAdvance_tag,hN,hfields.2.1]
        simp
        omega
    · have hEq := carrierStep_not_selected_stays s.tag.config e b b' hsel ht
      subst b'
      have hcN : (rearAdvance i s e).tag.moveCount = s.tag.moveCount := by
        rw [rearAdvance_tag,hN]; simp [hsel]
      by_cases hs : rearShifts s e r = true
      · obtain ⟨he,hpay⟩ := hpg.mp hs
        have hp' : geometricPay (s.tag.config (predecessor (back b d)))
            (s.tag.config (back b d)) = true := by
          simpa [he,r,right_predecessor] using hpay
        have hh := firstRear_moves hn s.tag.config hm b hd hp'
        simp only [hnp,Bool.not_false,Bool.true_and,hs,if_true,Bool.toNat_true] at hfields
        by_cases hz : d=0
        · subst d
          have hmark : (step s.tag.config e b).mark = true := by
            simpa [he,r] using hh
          have hP : (rearAdvance i s e).phase = .pinned := by
            rw [hfields.2.2,phaseAfter_pinned]
            exact Or.inr ⟨rfl,by rw [hb,hr,back_zero]⟩
          exact .pinned hP (hconf.symm ▸ hmark)
        · have hrearNot : s.tag.carrier ≠ s.rear := by
            rw [hb,hr]
            intro heq
            have ht := Option.some.inj heq
            have hpre := congrArg predecessor ht
            have hp0 : (s.tag.config (predecessor (back b 0))).mark = true := by
              rw [back_zero,hpre]; exact hd.marked
            exact hd.before 0 (by omega) hp0
          have hP : (rearAdvance i s e).phase ≠ .pinned := by
            rw [hfields.2.2]
            intro h
            simpa [hp,hrearNot] using (phaseAfter_pinned _ _ _ _).mp h
          have hh' : FirstRear (step s.tag.config e) b (d-1) ∧
                back b (d-1) = rightNeighbor (back b d) := by
            simpa [hz,he,r] using hh
          refine .tracking hP (d-1) ?_ (hconf.symm ▸ hh'.1) ?_
          · rw [hh'.2]; exact hfields.1
          · rw [hcN,hfields.2.1]; omega
      · have hs' := Bool.eq_false_iff.mpr hs
        simp only [hnp,Bool.not_false,Bool.true_and,hs',Bool.false_eq_true,if_false,
          Bool.toNat_false,Nat.add_zero] at hfields
        have hnext := firstRear_stationary hn s.tag.config hm b e hd (fun h => hs (hpg.mpr h))
        have hP : (rearAdvance i s e).phase ≠ .pinned := by
          rw [hfields.2.2]
          intro h
          simpa [hp] using (phaseAfter_pinned _ _ _ _).mp h
        exact .tracking hP d hfields.1 (hconf.symm ▸ hnext)
          (by rwa [hcN,hfields.2.1])

theorem geometry_run {p c n d0 : Nat} (hn : 4 ≤ n) (i : Fin n)
    (s : Observer p c n) (w : List (Fin n)) (hm : MCOV s.tag.config)
    (b b' : Fin n) (hb : s.tag.carrier = some b)
    (hg : LiveGeometry d0 s b) (hfinal : (rearFold i s w).tag.carrier = some b') :
    LiveGeometry d0 (rearFold i s w) b' := by
  induction w generalizing s b with
  | nil =>
    have h : b = b' := Option.some.inj (hb.symm.trans hfinal)
    subst b'; exact hg
  | cons e w ih =>
    let t := rearAdvance i s e
    have htail : (rearFold i t w).tag.carrier = some b' := hfinal
    have hs : t.tag.carrier ≠ none := by
      intro h
      have he := ended_run t.tag w h
      rw [← rearFold_tag i t w] at he
      change (rearFold i t w).tag.carrier = none at he
      rw [htail] at he
      contradiction
    cases hC : t.tag.carrier with
    | none => exact (hs hC).elim
    | some j =>
      have hm' : MCOV t.tag.config := by
        dsimp only [t]; rw [rearAdvance_tag,projection_step]
        exact mcov_step hn s.tag.config hm e
      exact ih t hm' j hC (liveGeometry_step hn i e b j s hm hb hC hg) htail

theorem concrete_geometry {p c n : Nat} (hn : 4 ≤ n) (x : Config p c n)
    (i b : Fin n) (w : List (Fin n)) (hm : MCOV x) (hnd : ∃ j : Fin n, (x j).mark=true)
    (hab : (rearTrack x i w).tag.carrier = some b) :
    ∃ d0, FirstRear x i d0 ∧ LiveGeometry d0 (rearTrack x i w) b := by
  obtain ⟨d0,hd,hrear⟩ := rearInit_has_nearest i hnd
  have hi : (rearInit x i).tag.carrier = some i := by
    by_cases he : ((x i).bullet == .live) = true
    · simp [rearInit,init,he]
    · exfalso
      have he' : (rearInit x i).tag.carrier = none := by simp [rearInit,init,he]
      have hend := ended_run (rearInit x i).tag w he'
      rw [← rearFold_tag i (rearInit x i) w] at hend
      change (rearTrack x i w).tag.carrier = none at hend
      rw [hab] at hend
      contradiction
  have hg : LiveGeometry d0 (rearInit x i) i :=
    .tracking (by change Phase.initial ≠ Phase.pinned; decide) d0 hrear hd (by simp [rearInit,init])
  exact ⟨d0,hd,geometry_run hn i (rearInit x i) w hm i b hi hg hab⟩

theorem rearMoves_change {p c n : Nat} (i e : Fin n) (s : Observer p c n) :
    ∃ dx : Nat, dx ≤ 1 ∧ (rearAdvance i s e).rearMoves = s.rearMoves+dx := by
  unfold rearAdvance
  split
  · exact ⟨0,by omega,by simp⟩
  · rename_i r h
    let m := !(s.phase == .pinned) && rearShifts s e r
    exact ⟨m.toNat,by cases m <;> decide,rfl⟩

/-- A pinning transition never advances the distinguished tag; a pinned
tag may then remain resident but cannot advance while live. -/
theorem pinned_moveCount {p c n d0 : Nat} (i e b j : Fin n) (s : Observer p c n)
    (_hm : MCOV s.tag.config) (h : LiveGeometry d0 s b) (hb : s.tag.carrier = some b)
    (hj : (rearAdvance i s e).tag.carrier = some j) (hp : (rearAdvance i s e).phase = .pinned) :
    (rearAdvance i s e).tag.moveCount = s.tag.moveCount := by
  rw [rearAdvance_tag] at hj ⊢
  rw [advance_moveCount s.tag e b j hb hj]
  by_cases he : b = e
  · subst e
    exfalso
    have hstep := (advance_carrier s.tag b b hb).symm.trans hj
    have htr := (carrierStep_selected_survives s.tag.config b j hstep).2
    have hmark := ((tagTransfer_iff _ _).mp htr).2.2.2.1
    cases h with
    | pinned hp0 hm0 => simp [hmark] at hm0
    | tracking hup d hr hd hgap =>
      let r := back b d
      have hf := post_fields i b r s hr
      dsimp only at hf
      have hshift : rearShifts s b r = false := by simp [rearShifts,hmark]
      have hpold : (s.phase == Phase.pinned) = false := by
        cases heq : s.phase <;> first | exact (hup heq).elim | decide
      have hh : phaseAfter s (advance s.tag b) r false = .pinned := by
        simpa only [hpold,hshift,Bool.not_false,Bool.true_and,Bool.false_eq_true,if_false] using hf.2.2.symm.trans hp
      have hz := (phaseAfter_pinned _ _ _ _).mp hh
      simp [hup] at hz
  · simp [he]

end L4.RearTrace

