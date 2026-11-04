import Leader.Wu.ShortGap.TwoEpochLineageClosure

/-!
# Adjacent-gap JOIN effects

C7 in the imported source is the history/completed-denial clause, not
NeighborSkew. This file preserves that definition. Skew is discharged
separately from pre-step receipt provenance.
-/
namespace ShortGapLineage2ClosureB
open ShortGapLiteralGapRows ShortGapLiteralRingRows ShortGapOwnerRoundSlice
open ShortGapCurrentCohort ShortGapLineage ShortGapLineageRetained
open ShortGapDenialTransportLiteral ShortGapGenerationMask ShortGapTwoEpoch
open ShortGapJoinedIncidenceBalance FiniteUniformStoppingTree
open ShortGapLineage2Closure
set_option autoImplicit false

/-- JOIN support uses the old counter and the two old neighbor counters. -/
theorem join_requires_neighbors_of_lineage2 (R : RFrame) (s : GhostRing2 R)
    (hs : Lineage2 R s) (e : Vtx R) (i : Fin R.m)
    (hi : fires R (physical2 R s) e i = true) :
    s.k i ≤ s.k (next R i) ∧ s.k i ≤ s.k (prev R i) :=
  join_requires_neighbors_of_lineage R (view R s) hs.coherent e i hi

/-- This skew theorem does not discharge the distinct C7 history clause. -/
theorem neighborSkew_step_of_lineage2 (R : RFrame) (s : GhostRing2 R)
    (hs : Lineage2 R s) (e : Vtx R) : NeighborSkew R (physical2 R (ghostStep2 R s e)) :=
  neighborSkew_step_of_lineage R (view R s) hs.coherent e

private theorem row_left_ccw (c : Choice) (cw : CwPort) (ccw : CcwPort) (b : Agent) :
    (row (.root c cw ccw) b).1.ccwPort = some ccw := by
  cases b with
  | interior t => cases t <;> cases cw <;> rfl
  | root d dw dd => cases cw <;> cases dd <;> rfl

/-- An unscheduled gap's right port is unchanged by the raw row. The
shared root may still JOIN afterward, which is handled separately. -/
theorem raw_ccw_other (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (hg : g ≠ e.1) :
    (rawAt R s.cfg e (rootV R (next R g))).ccwPort =
      (s.cfg (rootV R (next R g))).ccwPort := by
  have hn : rootV R (next R g) ≠ rn R e := by
    by_cases hp : e.2.val+1 < R.h
    · rw [rn_of_lt R e hp]
      intro h
      have hv := congrArg (fun v : Vtx R => v.2.val) h
      change 0 = e.2.val+1 at hv
      omega
    · rw [rn_of_last R e hp]
      intro h
      have hnext : next R g = next R e.1 := congrArg Prod.fst h
      have hprev := congrArg (prev R) hnext
      exact hg (by simpa only [prev_next] using hprev)
  by_cases ht : rootV R (next R g) = e
  · obtain ⟨c,cw,ccw,hroot⟩ := hs.coherent.roots (next R g)
    change s.cfg (rootV R (next R g)) = .root c cw ccw at hroot
    have hl : s.cfg e = .root c cw ccw := ht ▸ hroot
    rw [rawAt,if_pos ht,hl,hroot]
    exact row_left_ccw c cw ccw _
  · rw [rawAt,if_neg ht,if_neg hn]

/-- For an unscheduled gap, a right JOIN requires a receipt that was
already present before the raw row. -/
theorem other_right_join_held (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (hg : g ≠ e.1)
    (hf : fires R (physical2 R s) e (next R g) = true) :
    CcwHeld (s.cfg (rootV R (next R g))).ccwPort := by
  obtain ⟨_,c,hc⟩ := (fires_iff R (physical2 R s) e (next R g)).mp hf
  change rawAt R s.cfg e (rootV R (next R g)) = .root c .heldDenial .heldDenial at hc
  have hp := raw_ccw_other R s hs e g hg
  rw [hc] at hp
  rw [← hp]
  trivial

/-- Outside the scheduled gap, the two annotations change only through
owner transfer and right retirement, with right retirement taking precedence. -/
theorem epoch_other (R : RFrame) (s : GhostRing2 R) (e : Vtx R) (g : Fin R.m)
    (hg : g ≠ e.1) :
    ((ghostStep2 R s e).epoch g).cur =
      (if fires R (physical2 R s) e g then .idle else (s.epoch g).cur) ∧
    ((ghostStep2 R s e).epoch g).prev =
      (if fires R (physical2 R s) e (next R g) then .idle
       else if fires R (physical2 R s) e g then (s.epoch g).cur else (s.epoch g).prev) := by
  have he : rawEpochs R (curView R s) e g = (s.epoch g).cur := if_neg hg
  constructor
  · change (epochStep2 R s e g).cur = _
    rw [epochStep2_cur,he]
  · change (epochStep2 R s e g).prev = _
    cases ho : fires R (physical2 R s) e g <;>
      cases hr : fires R (physical2 R s) e (next R g) <;>
      simp [epochStep2,ho,hr,he,hg]

/-- The effective completed-prefix epoch of an unscheduled gap is
unchanged, even when either or both shared roots JOIN. A cleared archive
is reconstructed from the owner's counter and immutable history. -/
theorem view_epoch_other (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (hg : g ≠ e.1) :
    (view R (ghostStep2 R s e)).epoch g = (view R s).epoch g := by
  obtain ⟨hcur,hprev⟩ := epoch_other R s e g hg
  have hshape := hs.coherent.shape g
  have ht := hs.current g
  cases he : (s.epoch g).cur with
  | outbound q c =>
    have hO : fires R (physical2 R s) e g = false := by
      cases hf : fires R (physical2 R s) e g with
      | false => rfl
      | true =>
        obtain ⟨x,y,hc⟩ := ShortGapTwoEpochLaws.other_join_current_delivered R s hs e g hg hf
        rw [he] at hc; cases hc
    simp [view,prefixView,combinedView,hcur,hO,he]
  | returning q c d =>
    have hO : fires R (physical2 R s) e g = false := by
      cases hf : fires R (physical2 R s) e g with
      | false => rfl
      | true =>
        obtain ⟨x,y,hc⟩ := ShortGapTwoEpochLaws.other_join_current_delivered R s hs e g hg hf
        rw [he] at hc; cases hc
    simp [view,prefixView,combinedView,hcur,hO,he]
  | delivered q c d =>
    have hq : q = s.k g := by simpa only [he,CurrentTag] using ht
    simp only [prefixView,combinedView,he,EpochShape] at hshape
    have hL := history2_monotone R s e g q c hshape.2.2.1
    have hR := history2_monotone R s e (next R g) q d hshape.2.2.2.1
    cases hO : fires R (physical2 R s) e g <;>
      cases hJ : fires R (physical2 R s) e (next R g) <;>
      simp [view,prefixView,combinedView,hcur,hprev,hO,hJ,he,ghostStep2_k,← hq,hL,hR]
  | idle =>
    have hO : fires R (physical2 R s) e g = false := by
      cases hf : fires R (physical2 R s) e g with
      | false => rfl
      | true =>
        obtain ⟨x,y,hc⟩ := ShortGapTwoEpochLaws.other_join_current_delivered R s hs e g hg hf
        rw [he] at hc; cases hc
    have hk : (ghostStep2 R s e).k g = s.k g := by simp [ghostStep2_k,hO]
    have hp := hs.previous g
    cases hep : (s.epoch g).prev with
    | outbound q c => simp only [PrevShape,hep] at hp
    | returning q c d => simp only [PrevShape,hep] at hp
    | delivered q c d =>
      simp only [PrevShape,hep] at hp
      have hL := history2_monotone R s e g q c hp.2.2.1
      have hR := history2_monotone R s e (next R g) q d hp.2.2.2
      cases hJ : fires R (physical2 R s) e (next R g) <;>
        simp [view,prefixView,combinedView,hcur,hprev,hO,hJ,he,hep,hk,hp.1,hL,hR]
    | idle =>
      by_cases hz : s.k g = 0
      · simp [view,prefixView,combinedView,hcur,hprev,hO,he,hep,hk,hz]
      · simp only [prefixView,combinedView,he,hep,hz,if_false,EpochShape] at hshape
        have hL := history2_monotone R s e g (s.k g-1) _ hshape.2.2.1
        have hR := history2_monotone R s e (next R g) (s.k g-1) _ hshape.2.2.2.1
        simp [view,prefixView,combinedView,hcur,hprev,hO,he,hep,hk,hz,hL,hR]

/-- Adjacent-gap receipt equality includes the optional clear performed
by right JOIN. The raw interaction itself does not write this port. -/
theorem ccw_other_step (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (hg : g ≠ e.1) :
    ((ghostStep2 R s e).cfg (rootV R (next R g))).ccwPort =
      if fires R (physical2 R s) e (next R g) then some .free
      else (s.cfg (rootV R (next R g))).ccwPort := by
  cases hf : fires R (physical2 R s) e (next R g) with
  | true => rw [root_cfg_join R s e (next R g) hf]; rfl
  | false =>
    rw [root_cfg_no_join R s e (next R g) hf]
    exact raw_ccw_other R s hs e g hg

theorem other_owner_join_view (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (hg : g ≠ e.1)
    (hf : fires R (physical2 R s) e g = true) :
    ∃ c d, (view R s).epoch g = .delivered (s.k g) c d := by
  obtain ⟨c,d,hc⟩ := ShortGapTwoEpochLaws.other_join_current_delivered R s hs e g hg hf
  exact ⟨c,d,by simp [view,prefixView,combinedView,hc]⟩

theorem other_right_join_compared (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (hg : g ≠ e.1)
    (hf : fires R (physical2 R s) e (next R g) = true) :
    ComparedAt ((view R s).epoch g) (s.k (next R g)) :=
  (hs.coherent.incoming g).mp (other_right_join_held R s hs e g hg hf)

private theorem empty_other (R : RFrame) (s : GhostRing2 R) (e : Vtx R) (g : Fin R.m)
    (hg : g ≠ e.1) (h : EmptyGap R (view R s) g) : EmptyGap R (view R (ghostStep2 R s e)) g := by
  intro a ha
  change (ghostStep2 R s e).cfg (g,a) = _
  rw [other_gap_interior R s e g hg a ha]
  exact h a ha

private theorem token_other (R : RFrame) (s : GhostRing2 R) (e : Vtx R) (g : Fin R.m)
    (hg : g ≠ e.1) (t : Slot) (h : OneToken R (view R s) g t) :
    OneToken R (view R (ghostStep2 R s e)) g t := by
  obtain ⟨p,hp,hslots⟩ := h
  refine ⟨p,hp,?_⟩
  intro a ha
  change (ghostStep2 R s e).cfg (g,a) = _
  rw [other_gap_interior R s e g hg a ha]
  exact hslots a ha

/-- C1 for every unscheduled gap, including both adjacent gaps and
all four combinations of its endpoint JOINs. No global band is assumed. -/
theorem C1_step_adjacent (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (hg : g ≠ e.1) :
    EpochShape R (view R (ghostStep2 R s e)) g := by
  have hp := hs.coherent.shape g
  have heq := view_epoch_other R s hs e g hg
  have hO := other_owner_join_view R s hs e g hg
  have hR := other_right_join_compared R s hs e g hg
  cases he : (view R s).epoch g with
  | idle =>
    have ho : fires R (physical2 R s) e g = false := by
      cases hf : fires R (physical2 R s) e g with
      | false => rfl
      | true => obtain ⟨c,d,hc⟩ := hO hf; rw [he] at hc; cases hc
    have hr : fires R (physical2 R s) e (next R g) = false := by
      cases hf : fires R (physical2 R s) e (next R g) with
      | false => rfl
      | true => have h := hR hf; rw [he] at h; exact False.elim h
    change EpochShape R (view R s) g at hp
    rw [EpochShape,he] at hp
    rw [EpochShape,heq,he]
    exact ⟨by simpa [view,prefixView,combinedView,ghostStep2_k,ho] using hp.1,
      by simpa [view,prefixView,combinedView,ghostStep2_k,hr] using hp.2.1,
      empty_other R s e g hg hp.2.2⟩
  | outbound q c =>
    have ho : fires R (physical2 R s) e g = false := by
      cases hf : fires R (physical2 R s) e g with
      | false => rfl
      | true => obtain ⟨c,d,hc⟩ := hO hf; rw [he] at hc; cases hc
    change EpochShape R (view R s) g at hp
    rw [EpochShape,he] at hp
    rw [EpochShape,heq,he]
    refine ⟨?_,?_,history2_monotone R s e g q c hp.2.2.1,token_other R s e g hg _ hp.2.2.2⟩
    · change (ghostStep2 R s e).k g = q
      simpa [view,prefixView,combinedView,ghostStep2_k,ho] using hp.1
    · change (ghostStep2 R s e).k (next R g) = q ∨ (ghostStep2 R s e).k (next R g)+1 = q
      rw [ghostStep2_k]
      cases hf : fires R (physical2 R s) e (next R g) with
      | false => simpa [view,prefixView,combinedView] using hp.2.1
      | true =>
        have h := hR hf
        rw [he] at h
        change s.k (next R g) < q at h
        have hb : s.k (next R g) = q ∨ s.k (next R g)+1 = q := hp.2.1
        exact Or.inl (by simp only [if_true]; omega)
  | returning q c d =>
    have ho : fires R (physical2 R s) e g = false := by
      cases hf : fires R (physical2 R s) e g with
      | false => rfl
      | true => obtain ⟨c,d,hc⟩ := hO hf; rw [he] at hc; cases hc
    change EpochShape R (view R s) g at hp
    rw [EpochShape,he] at hp
    rw [EpochShape,heq,he]
    refine ⟨?_,?_,history2_monotone R s e g q c hp.2.2.1,
      history2_monotone R s e (next R g) q d hp.2.2.2.1,token_other R s e g hg _ hp.2.2.2.2⟩
    · change (ghostStep2 R s e).k g = q
      simpa [view,prefixView,combinedView,ghostStep2_k,ho] using hp.1
    · change (ghostStep2 R s e).k (next R g) = q ∨ (ghostStep2 R s e).k (next R g) = q+1
      rw [ghostStep2_k]
      cases hf : fires R (physical2 R s) e (next R g) with
      | false => simpa [view,prefixView,combinedView] using hp.2.1
      | true =>
        have h := hR hf
        rw [he] at h
        change s.k (next R g) ≤ q at h
        have hb : s.k (next R g) = q ∨ s.k (next R g) = q+1 := hp.2.1
        exact Or.inr (by simp only [if_true]; omega)
  | delivered q c d =>
    change EpochShape R (view R s) g at hp
    rw [EpochShape,he] at hp
    rw [EpochShape,heq,he]
    refine ⟨?_,?_,history2_monotone R s e g q c hp.2.2.1,
      history2_monotone R s e (next R g) q d hp.2.2.2.1,empty_other R s e g hg hp.2.2.2.2⟩
    · change (ghostStep2 R s e).k g = q ∨ (ghostStep2 R s e).k g = q+1
      rw [ghostStep2_k]
      cases hf : fires R (physical2 R s) e g with
      | false => simpa [view,prefixView,combinedView] using hp.1
      | true =>
        obtain ⟨x,y,hc⟩ := hO hf
        rw [he] at hc
        have hk : q = s.k g := by cases hc; rfl
        exact Or.inr (by simp [hk])
    · change (ghostStep2 R s e).k (next R g) = q ∨ (ghostStep2 R s e).k (next R g) = q+1
      rw [ghostStep2_k]
      cases hf : fires R (physical2 R s) e (next R g) with
      | false => simpa [view,prefixView,combinedView] using hp.2.1
      | true =>
        have h := hR hf
        rw [he] at h
        change s.k (next R g) ≤ q at h
        have hb : s.k (next R g) = q ∨ s.k (next R g) = q+1 := hp.2.1
        exact Or.inr (by simp only [if_true]; omega)

/-- A right JOIN consumes the last comparison belonging to that root's
old generation; the effective epoch cannot cover its incremented counter. -/
theorem other_right_join_exhausts_compared (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (hg : g ≠ e.1)
    (hf : fires R (physical2 R s) e (next R g) = true) :
    ¬ ComparedAt ((view R s).epoch g) (s.k (next R g)+1) := by
  have hp := hs.coherent.shape g
  have hc := other_right_join_compared R s hs e g hg hf
  have hkL : (view R s).k g = s.k g := rfl
  have hkR : (view R s).k (next R g) = s.k (next R g) := rfl
  change EpochShape R (view R s) g at hp
  cases he : (view R s).epoch g <;> rw [EpochShape,he] at hp
  all_goals simp only [he,ComparedAt] at hc ⊢
  all_goals first | exact False.elim hc | omega

private theorem currentResult_compared (R : RFrame) (s : GhostRing2 R) (g : Fin R.m)
    (q : Nat) (hc : CurrentResult (s.epoch g).cur q) : ComparedAt ((view R s).epoch g) q := by
  cases he : (s.epoch g).cur <;> simp only [he,CurrentResult] at hc
  all_goals first | exact False.elim hc |
    (simpa only [view,prefixView,combinedView,he,ComparedAt,hc] using Nat.le_refl q)

/-- All three C3 clauses hold for every unscheduled gap, with no
assumption of post-state lineage and no restriction on endpoint JOINs. -/
theorem C3_step_adjacent (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (hg : g ≠ e.1) : C3At R (ghostStep2 R s e) g := by
  have heq := view_epoch_other R s hs e g hg
  have hw := ccw_other_step R s hs e g hg
  obtain ⟨hcur,hprev⟩ := epoch_other R s e g hg
  have hk := ghostStep2_k R s e (next R g)
  unfold C3At
  rw [heq,hw,hk]
  cases hR : fires R (physical2 R s) e (next R g) with
  | false =>
    simp only [Bool.false_eq_true,if_false,Nat.add_zero]
    refine ⟨hs.coherent.incoming g,?_,?_⟩
    · intro h
      obtain ⟨c,d,hc,hd,hv⟩ := hs.coherent.incomingValue g h
      exact ⟨c,d,history2_monotone R s e g _ c hc,history2_monotone R s e (next R g) _ d hd,hv⟩
    · rw [hcur,hprev,hR]
      cases hO : fires R (physical2 R s) e g with
      | false => simpa only [Bool.false_eq_true,if_false] using hs.incoming g
      | true =>
        obtain ⟨c,d,he⟩ := ShortGapTwoEpochLaws.other_join_current_delivered R s hs e g hg hO
        have hsupport := join_requires_neighbors_of_lineage2 R s hs e g hO
        have hn := previous_not_current R s hs g hsupport.1
        have hi := hs.incoming g
        simp only [he,CurrentResult,hn,or_false] at hi
        simpa only [Bool.false_eq_true,if_false,if_true,he,CurrentResult,PreviousResult,false_or] using hi
  | true =>
    simp only [if_true]
    have hn := other_right_join_exhausts_compared R s hs e g hg hR
    refine ⟨⟨False.elim,fun h => False.elim (hn h)⟩,?_,?_⟩
    · intro h; exact False.elim (hn h)
    · rw [hcur,hprev,hR]
      cases hO : fires R (physical2 R s) e g with
      | true => exact ⟨False.elim,fun h => h.elim id id⟩
      | false =>
        refine ⟨False.elim,?_⟩
        intro h
        rcases h with h | h
        · exact hn (currentResult_compared R s g _ h)
        · exact h

/-- Historical payload and strict-denial prefixes for every unscheduled
gap persist because its effective epoch is unchanged. -/
theorem prefix_step_adjacent (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (hg : g ≠ e.1) :
    (∀ q, ComparedAt ((view R (ghostStep2 R s e)).epoch g) q →
      ∃ c d, (ghostStep2 R s e).hist g q = some c ∧ (ghostStep2 R s e).hist (next R g) q = some d) ∧
    (∀ q, BeforeLatest ((view R (ghostStep2 R s e)).epoch g) q →
      HistoricalDenial R (view R (ghostStep2 R s e)) g q) := by
  have he := view_epoch_other R s hs e g hg
  constructor
  · intro q hq
    rw [he] at hq
    obtain ⟨c,d,hc,hd⟩ := hs.coherent.prefixPayloads g q hq
    exact ⟨c,d,history2_monotone R s e g q c hc,history2_monotone R s e (next R g) q d hd⟩
  · intro q hq
    rw [he] at hq
    exact historicalDenial_step R s e g q (hs.coherent.prefixDenials g q hq)

private theorem resCw_denial (c d : Choice) (h : resCw c d = .heldDenial) : res c d = .denial := by
  cases c <;> cases d <;> simp_all [resCw,res,Verdict.cw]

private theorem resCcw_denial (c d : Choice) (h : resCcw c d = .heldDenial) : res c d = .denial := by
  cases c <;> cases d <;> simp_all [resCcw,res,Verdict.ccw]

theorem raw_current_tag (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) : CurrentTag (s.k g) (rawEpochs R (curView R s) e g) := by
  by_cases hg : g = e.1
  · rw [rawEpochs,if_pos hg]
    exact ShortGapTwoEpochLaws.currentTag_rowEpoch _ _ _ _ (hs.current g)
  · rw [rawEpochs,if_neg hg]
    exact hs.current g

/-- The new completed owner round has an outgoing historical denial:
its raw delivered payloads agree with the physical denial consumed by JOIN. -/
theorem joined_outgoing_denial (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (hf : fires R (physical2 R s) e g = true) :
    HistoricalDenial R (view R (ghostStep2 R s e)) g (s.k g) := by
  obtain ⟨q,c,d,he⟩ := owner_join_raw_delivered R s hs e g hf
  have ht := raw_current_tag R s hs e g
  have hq : q = s.k g := by simpa only [he,CurrentTag] using ht
  obtain ⟨_,x,hraw⟩ := (fires_iff R (physical2 R s) e g).mp hf
  change rawAt R s.cfg e (rootV R g) = .root x .heldDenial .heldDenial at hraw
  have hp := raw_owner_port_exact R s hs e g
  rw [hraw,he] at hp
  have hd : resCw c d = .heldDenial := (Option.some.inj hp).symm
  have hh := raw_delivered_payloads R s hs e g q c d he
  exact hq ▸ ⟨c,d,hh.1,hh.2,resCw_denial c d hd⟩

private theorem row_right_ccw_no_compare (a : Agent) (d : Choice) (cw : CwPort) (ccw : CcwPort)
    (hn : compares a (.root d cw ccw) = false) :
    (row a (.root d cw ccw)).2.ccwPort = some ccw := by
  cases a with
  | interior t => cases t <;> cases ccw <;> first | rfl | cases hn
  | root c x y => cases x <;> cases ccw <;> first | rfl | cases hn

/-- When no comparison is performed, every raw right-facing receipt
is preserved, including the scheduled gap's receipt. -/
theorem raw_ccw_no_compare (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (hn : compares (s.cfg e) (s.cfg (rn R e)) = false) :
    (rawAt R s.cfg e (rootV R (next R g))).ccwPort =
      (s.cfg (rootV R (next R g))).ccwPort := by
  obtain ⟨c,cw,ccw,hroot⟩ := hs.coherent.roots (next R g)
  change s.cfg (rootV R (next R g)) = .root c cw ccw at hroot
  by_cases hl : rootV R (next R g) = e
  · have he : s.cfg e = .root c cw ccw := hl ▸ hroot
    rw [rawAt,if_pos hl,he,hroot]
    exact row_left_ccw _ _ _ _
  · by_cases hr : rootV R (next R g) = rn R e
    · have he : s.cfg (rn R e) = .root c cw ccw := hr ▸ hroot
      rw [rawAt,if_neg hl,if_pos hr,he,hroot]
      exact row_right_ccw_no_compare _ _ _ _ (by simpa only [he] using hn)
    · rw [rawAt,if_neg hl,if_neg hr]

private theorem comparison_inputs (a b : Agent) (h : compares a b = true) :
    (∃ c d cw, a = .interior (.decl c) ∧ b = .root d cw .free) ∨
    (∃ c ccw d cw, a = .root c .toSend ccw ∧ b = .root d cw .free) := by
  cases a with
  | interior t =>
    cases b with
    | interior u => cases t <;> cases u <;> cases h
    | root d cw ccw =>
      cases t <;> cases ccw <;> first | exact Or.inl ⟨_,_,_,rfl,rfl⟩ | cases h
  | root c cw ccw =>
    cases b with
    | interior u => cases cw <;> cases u <;> cases h
    | root d dw dd =>
      cases cw <;> cases dd <;> first | exact Or.inr ⟨_,_,_,_,rfl,rfl⟩ | cases h

private theorem root_input_zero (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (c : Choice) (cw : CwPort) (ccw : CcwPort) (he : s.cfg e = .root c cw ccw) :
    e.2.val = 0 := by
  by_cases hp : 0 < e.2.val
  · obtain ⟨t,ht⟩ := interior_roles R _ hs.coherent e.1 e.2 hp
    change s.cfg e = .interior t at ht
    rw [he] at ht; cases ht
  · omega

private theorem root_receiver_last (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (c : Choice) (cw : CwPort) (ccw : CcwPort)
    (he : s.cfg (rn R e) = .root c cw ccw) :
    e.2.val+1 = R.h ∧ rn R e = rootV R (next R e.1) := by
  have hz := root_input_zero R s hs (rn R e) c cw ccw he
  have hn : ¬ e.2.val+1 < R.h := by
    intro h
    rw [rn_of_lt R e h] at hz
    change e.2.val+1 = 0 at hz
    omega
  exact ⟨by have := e.2.isLt; omega,rn_of_last R e hn⟩

/-- The raw denial at a gap's right root is a historical denial in that
root's old generation, whether inherited or newly written by K1/P1. -/
theorem raw_right_denial_history (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m)
    (hd : (rawAt R s.cfg e (rootV R (next R g))).ccwPort = some .heldDenial) :
    HistoricalDenial R (view R (ghostStep2 R s e)) g (s.k (next R g)) := by
  have old : (s.cfg (rootV R (next R g))).ccwPort = some .heldDenial →
      HistoricalDenial R (view R (ghostStep2 R s e)) g (s.k (next R g)) := by
    intro hp
    have hc := (hs.coherent.incoming g).mp (by change CcwHeld (s.cfg (rootV R (next R g))).ccwPort; rw [hp]; trivial)
    obtain ⟨c,d,hc,hd',hv⟩ := hs.coherent.incomingValue g hc
    change (s.cfg (rootV R (next R g))).ccwPort = some (resCcw c d) at hv
    rw [hp] at hv
    exact ⟨c,d,history2_monotone R s e g _ c hc,history2_monotone R s e (next R g) _ d hd',
      resCcw_denial c d (Option.some.inj hv).symm⟩
  by_cases hg : g = e.1
  · cases hcomp : compares (s.cfg e) (s.cfg (rn R e)) with
    | false => exact old ((raw_ccw_no_compare R s hs e g hcomp).symm.trans hd)
    | true =>
      rcases comparison_inputs _ _ hcomp with ⟨c,d,cw,hl,hr⟩ | ⟨c,ccw,d,cw,hl,hr⟩
      · obtain ⟨hlast,hrn⟩ := root_receiver_last R s hs e d cw .free hr
        rw [← hg] at hrn
        have ha : 0 < e.2.val := by
          by_cases hz : e.2.val = 0
          · have he : e = rootV R g := by
              apply Prod.ext
              · exact hg.symm
              · exact Fin.ext hz
            obtain ⟨x,xw,xc,hroot⟩ := hs.coherent.roots g
            change s.cfg (rootV R g) = .root x xw xc at hroot
            rw [he,hroot] at hl; cases hl
          · omega
        have he : e = (g,e.2) := Prod.ext hg.symm rfl
        have hl' : s.cfg (g,e.2) = .interior (.decl c) := he ▸ hl
        have hr' : s.cfg (rootV R (next R g)) = .root d cw .free := hrn ▸ hr
        have hcur := (declaration_epoch R s hs g e.2 ha c hl').1
        have hgen := comparison_generations R s hs g c hcur (by rw [hr']; rfl)
        have hx := boundary_comparison R s hs g e.2 ha hlast c d cw hl' hr'
        have hnr : rootV R (next R g) ≠ e := by rw [← hrn]; exact rn_ne_self R e
        rw [rawAt,if_neg hnr,if_pos hrn.symm,hl,hr] at hd
        have hv : resCcw c (resolveResp d) = .heldDenial := Option.some.inj hd
        rw [hgen,he]
        exact ⟨c,resolveResp d,hx.2.2.2.2.1,hx.2.2.2.2.2.1,resCcw_denial _ _ hv⟩
      · obtain ⟨hlast,hrn⟩ := root_receiver_last R s hs e d cw .free hr
        rw [← hg] at hrn
        have hz := root_input_zero R s hs e c .toSend ccw hl
        have he : e = rootV R g := by
          apply Prod.ext
          · exact hg.symm
          · exact Fin.ext hz
        have hl' : s.cfg (rootV R g) = .root c .toSend ccw := he ▸ hl
        have hr' : s.cfg (rootV R (next R g)) = .root d cw .free := hrn ▸ hr
        have hgen := direct_generations R (view R s) hs.coherent g
          (by change (s.cfg (rootV R g)).cwPort = _; rw [hl']; rfl)
          (by change (s.cfg (rootV R (next R g))).ccwPort = _; rw [hr']; rfl)
        change s.k g = s.k (next R g) at hgen
        have hraw : rawEpochs R (curView R s) e g = .delivered (s.k g) (resolveInit c) (resolveResp d) := by
          rw [rawEpochs,if_pos hg]
          change rowEpoch (s.k g) (s.epoch g).cur (s.cfg e) (s.cfg (rn R e)) = _
          rw [hl,hr]; rfl
        have hpay := raw_delivered_payloads R s hs e g (s.k g) (resolveInit c) (resolveResp d) hraw
        have hnr : rootV R (next R g) ≠ e := by rw [← hrn]; exact rn_ne_self R e
        rw [rawAt,if_neg hnr,if_pos hrn.symm,hl,hr] at hd
        have hv : resCcw (resolveInit c) (resolveResp d) = .heldDenial := Option.some.inj hd
        rw [← hgen]
        exact ⟨resolveInit c,resolveResp d,hpay.1,hpay.2,resCcw_denial _ _ hv⟩
  · exact old ((raw_ccw_other R s hs e g hg).symm.trans hd)

/-- JOIN consumes an incoming denial in the root's old generation. -/
theorem joined_incoming_denial (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (i : Fin R.m) (hf : fires R (physical2 R s) e i = true) :
    HistoricalDenial R (view R (ghostStep2 R s e)) (prev R i) (s.k i) := by
  obtain ⟨_,c,hc⟩ := (fires_iff R (physical2 R s) e i).mp hf
  change rawAt R s.cfg e (rootV R i) = .root c .heldDenial .heldDenial at hc
  have hd : (rawAt R s.cfg e (rootV R (next R (prev R i)))).ccwPort = some .heldDenial := by
    rw [next_prev,hc]; rfl
  simpa only [next_prev] using raw_right_denial_history R s hs e (prev R i) hd

/-- Every completed post-step round has both historical denials. -/
theorem completed_denials_step (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (i : Fin R.m) (r : Nat) (hr : r < (ghostStep2 R s e).k i) :
    HistoricalDenial R (view R (ghostStep2 R s e)) i r ∧
    HistoricalDenial R (view R (ghostStep2 R s e)) (prev R i) r := by
  by_cases ho : r < s.k i
  · have hh := hs.coherent.joinedDenials i r ho
    exact ⟨historicalDenial_step R s e i r hh.2.2.1,
      historicalDenial_step R s e (prev R i) r hh.2.2.2⟩
  · rw [ghostStep2_k] at hr
    cases hf : fires R (physical2 R s) e i with
    | false => simp only [hf,Bool.false_eq_true,if_false,Nat.add_zero] at hr; omega
    | true =>
      simp only [hf,if_true] at hr
      have he : r = s.k i := by omega
      subst r
      exact ⟨joined_outgoing_denial R s hs e i hf,joined_incoming_denial R s hs e i hf⟩

/-- Shape alone places completed owner rounds in both incident prefixes. -/
theorem completed_coverage_of_C1 (R : RFrame) (s : GhostRing2 R) (h1 : C1 R s)
    (i : Fin R.m) (r : Nat) (hr : r < s.k i) :
    DeliveredAt ((view R s).epoch i) r ∧ ComparedAt ((view R s).epoch (prev R i)) r := by
  have hl := h1 i
  have hp := h1 (prev R i)
  have hk : (view R s).k i = s.k i := rfl
  have hn : (view R s).k (next R (prev R i)) = s.k i := by rw [next_prev]; rfl
  constructor
  · cases he : (view R s).epoch i <;>
      simp only [EpochShape,he] at hl <;> simp only [DeliveredAt] <;> omega
  · cases he : (view R s).epoch (prev R i) <;>
      simp only [EpochShape,he] at hp <;> simp only [ComparedAt] <;> omega

/-- C7 follows from shape and the two denial records of completed rounds.
This derives the actual historical-prefix clause, not just neighbour skew. -/
theorem C7_of_C1_completed_denials (R : RFrame) (s : GhostRing2 R) (h1 : C1 R s)
    (hd : ∀ i r, r < s.k i → HistoricalDenial R (view R s) i r ∧
      HistoricalDenial R (view R s) (prev R i) r) : C7 R s := by
  have pay : ∀ i r, r < s.k i → ∃ c d, s.hist i r = some c ∧ s.hist (next R i) r = some d := by
    intro i r hr
    obtain ⟨c,d,hc,hd,_⟩ := (hd i r hr).1
    exact ⟨c,d,hc,hd⟩
  refine ⟨?_,?_,?_⟩
  · intro g r hc
    have hg := h1 g
    have hk : (view R s).k g = s.k g := rfl
    cases he : (view R s).epoch g with
    | idle => simp only [he,ComparedAt] at hc
    | outbound q c =>
      simp only [he,ComparedAt] at hc
      simp only [he,EpochShape] at hg
      exact pay g r (by omega)
    | returning q c d =>
      simp only [he,ComparedAt] at hc
      simp only [he,EpochShape] at hg
      by_cases hq : r < q
      · exact pay g r (by omega)
      · have heq : r = q := by omega
        subst r
        exact ⟨c,d,hg.2.2.1,hg.2.2.2.1⟩
    | delivered q c d =>
      simp only [he,ComparedAt] at hc
      simp only [he,EpochShape] at hg
      by_cases hq : r < q
      · exact pay g r (by omega)
      · have heq : r = q := by omega
        subst r
        exact ⟨c,d,hg.2.2.1,hg.2.2.2.1⟩
  · intro g r hr
    have hg := h1 g
    have hk : (view R s).k g = s.k g := rfl
    apply (hd g r ?_).1
    cases he : (view R s).epoch g <;>
      simp only [he,BeforeLatest] at hr <;> simp only [he,EpochShape] at hg <;> omega
  · intro i r hr
    exact ⟨(completed_coverage_of_C1 R s h1 i r hr).1,
      (completed_coverage_of_C1 R s h1 i r hr).2,hd i r hr⟩

/-- The only remaining premise for historical-prefix preservation is C1. -/
theorem C7_step_of_C1 (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (h1 : C1 R (ghostStep2 R s e)) : C7 R (ghostStep2 R s e) :=
  C7_of_C1_completed_denials R _ h1 (completed_denials_step R s hs e)

private theorem view_epoch_of_unchanged (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m)
    (he : (ghostStep2 R s e).epoch g = s.epoch g)
    (hk : (ghostStep2 R s e).k g = s.k g) :
    (view R (ghostStep2 R s e)).epoch g = (view R s).epoch g := by
  have hc : (combinedView R (ghostStep2 R s e)).epoch g = (combinedView R s).epoch g := by
    simp only [combinedView,he]
  change (prefixView R (combinedView R (ghostStep2 R s e))).epoch g = _
  simp only [prefixView,hc]
  cases hh : (combinedView R s).epoch g <;> try rfl
  change (if (ghostStep2 R s e).k g = 0 then GapEpoch.idle else
    GapEpoch.delivered ((ghostStep2 R s e).k g-1)
      (((ghostStep2 R s e).hist g ((ghostStep2 R s e).k g-1)).getD .race)
      (((ghostStep2 R s e).hist (next R g) ((ghostStep2 R s e).k g-1)).getD .race)) = _
  rw [hk]
  by_cases hz : s.k g = 0
  · simp only [combinedView,hz,if_true]
  · have hp := hs.coherent.shape g
    change EpochShape R (prefixView R (combinedView R s)) g at hp
    simp only [EpochShape,prefixView,hh] at hp
    simp only [combinedView,hz,if_false] at hp
    have hl := history2_monotone R s e g _ _ hp.2.2.1
    have hr := history2_monotone R s e (next R g) _ _ hp.2.2.2.1
    simp only [combinedView,hz,if_false,hl,hr,Option.getD_some]

/-- A row with unchanged annotations and counters preserves the selected
clauses once its literal slot motion and right receipt have been checked. -/
theorem C1_C3_step_transport (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m)
    (he : (ghostStep2 R s e).epoch g = s.epoch g)
    (hk : (ghostStep2 R s e).k g = s.k g)
    (hr : (ghostStep2 R s e).k (next R g) = s.k (next R g))
    (hw : ((ghostStep2 R s e).cfg (rootV R (next R g))).ccwPort =
      (s.cfg (rootV R (next R g))).ccwPort)
    (hE : EmptyGap R (view R s) g → EmptyGap R (view R (ghostStep2 R s e)) g)
    (hT : ∀ t, OneToken R (view R s) g t → OneToken R (view R (ghostStep2 R s e)) g t) :
    EpochShape R (view R (ghostStep2 R s e)) g ∧ C3At R (ghostStep2 R s e) g := by
  have hv := view_epoch_of_unchanged R s hs e g he hk
  have hk' : (view R (ghostStep2 R s e)).k g = (view R s).k g := hk
  have hr' : (view R (ghostStep2 R s e)).k (next R g) = (view R s).k (next R g) := hr
  constructor
  · have hp := hs.coherent.shape g
    change EpochShape R (view R s) g at hp
    cases hh : (view R s).epoch g <;> simp only [EpochShape,hv,hh,hk',hr'] at hp ⊢
    · exact ⟨hp.1,hp.2.1,hE hp.2.2⟩
    · exact ⟨hp.1,hp.2.1,history2_monotone R s e _ _ _ hp.2.2.1,hT _ hp.2.2.2⟩
    · exact ⟨hp.1,hp.2.1,history2_monotone R s e _ _ _ hp.2.2.1,
        history2_monotone R s e _ _ _ hp.2.2.2.1,hT _ hp.2.2.2.2⟩
    · exact ⟨hp.1,hp.2.1,history2_monotone R s e _ _ _ hp.2.2.1,
        history2_monotone R s e _ _ _ hp.2.2.2.1,hE hp.2.2.2.2⟩
  · unfold C3At
    rw [hv,he,hr,hw]
    refine ⟨hs.coherent.incoming g,?_,hs.incoming g⟩
    intro h
    obtain ⟨c,d,hc,hd,hv⟩ := hs.coherent.incomingValue g h
    exact ⟨c,d,history2_monotone R s e _ _ _ hc,history2_monotone R s e _ _ _ hd,hv⟩

private theorem no_joins_of_row (R : RFrame) (s : GhostRing2 R) (e : Vtx R)
    (hl : joinReady (row (s.cfg e) (s.cfg (rn R e))).1 = false)
    (hr : joinReady (row (s.cfg e) (s.cfg (rn R e))).2 = false) :
    ∀ i, fires R (physical2 R s) e i = false := by
  intro i
  by_cases h0 : rootV R i = e
  · simp [fires,physical2,rawAt,h0,hl]
  · by_cases h1 : rootV R i = rn R e
    · simp [fires,physical2,rawAt,h1,rn_ne_self,hr]
    · simp [fires,physical2,incident,h0,h1]

private theorem epoch_unchanged_of_quiet (R : RFrame) (s : GhostRing2 R)
    (e : Vtx R) (g : Fin R.m)
    (hf : ∀ i, fires R (physical2 R s) e i = false)
    (hc : compares (s.cfg e) (s.cfg (rn R e)) = false)
    (he : rawEpochs R (curView R s) e g = (s.epoch g).cur) :
    (ghostStep2 R s e).epoch g = s.epoch g := by
  change epochStep2 R s e g = _
  simp [epochStep2,hf,hc,he]

private theorem C1_C3_step_quiet (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m)
    (hf : ∀ i, fires R (physical2 R s) e i = false)
    (hc : compares (s.cfg e) (s.cfg (rn R e)) = false)
    (he : rawEpochs R (curView R s) e g = (s.epoch g).cur)
    (hE : EmptyGap R (view R s) g → EmptyGap R (view R (ghostStep2 R s e)) g)
    (hT : ∀ t, OneToken R (view R s) g t → OneToken R (view R (ghostStep2 R s e)) g t) :
    EpochShape R (view R (ghostStep2 R s e)) g ∧ C3At R (ghostStep2 R s e) g := by
  apply C1_C3_step_transport R s hs e g (epoch_unchanged_of_quiet R s e g hf hc he)
    (by simp [ghostStep2_k,hf]) (by simp [ghostStep2_k,hf]) _ hE hT
  rw [root_cfg_no_join R s e (next R g) (hf _)]
  exact raw_ccw_no_compare R s hs e g hc

/-- Erase only root choices; ports and interior payloads remain literal. -/
private def portsSlots : Agent → Agent
  | .root _ cw ccw => .root .race cw ccw
  | .interior t => .interior t

private theorem joinReady_portsSlots (a : Agent) : joinReady (portsSlots a) = joinReady a := by
  cases a with
  | interior t => rfl
  | root c cw ccw => cases cw <;> cases ccw <;> rfl

private theorem normalized_vertex (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (v : Vtx R) : joinReady (s.cfg v) = false := by
  by_cases hp : 0 < v.2.val
  · obtain ⟨t,ht⟩ := interior_roles R _ hs.coherent v.1 v.2 hp
    change s.cfg v = .interior t at ht
    rw [ht]; rfl
  · have hv : v = rootV R v.1 := Prod.ext rfl (Fin.ext (by change v.2.val = 0; omega))
    rw [hv]
    exact hs.coherent.normalized v.1

/-- Resolution-only rows preserve C1 and C3 even when the history at
the current generation is first recorded during this interaction. -/
theorem C1_C3_step_resolution (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R)
    (hl : portsSlots (row (s.cfg e) (s.cfg (rn R e))).1 = portsSlots (s.cfg e))
    (hr : portsSlots (row (s.cfg e) (s.cfg (rn R e))).2 = portsSlots (s.cfg (rn R e)))
    (hc : compares (s.cfg e) (s.cfg (rn R e)) = false)
    (he : rawEpochs R (curView R s) e e.1 = (s.epoch e.1).cur) :
    EpochShape R (view R (ghostStep2 R s e)) e.1 ∧ C3At R (ghostStep2 R s e) e.1 := by
  have hf := no_joins_of_row R s e
    (by rw [← joinReady_portsSlots,hl,joinReady_portsSlots]; exact normalized_vertex R s hs e)
    (by rw [← joinReady_portsSlots,hr,joinReady_portsSlots]; exact normalized_vertex R s hs (rn R e))
  have hslots : ∀ a : Fin R.h, 0 < a.val →
      (ghostStep2 R s e).cfg (e.1,a) = s.cfg (e.1,a) := by
    intro a ha
    obtain ⟨t,ht⟩ := interior_roles R _ hs.coherent e.1 a ha
    change s.cfg (e.1,a) = .interior t at ht
    have get : ∀ b : Agent, portsSlots b = .interior t → b = .interior t := by
      intro b hb
      cases b with
      | interior u => exact hb
      | root c cw ccw => cases hb
    rw [ShortGapTwoEpochLaws.cfg_step_pair]
    by_cases h0 : (e.1,a) = e
    · rw [if_pos h0]
      have hh : s.cfg e = .interior t := h0 ▸ ht
      have hb := hl
      rw [hh] at hb
      have hb' := get _ hb
      rw [hh,hb',ht]; rfl
    · rw [if_neg h0]
      by_cases h1 : (e.1,a) = rn R e
      · rw [if_pos h1]
        have hb := hr
        rw [← h1,ht] at hb
        have hb' := get _ hb
        rw [← h1,ht,hb']; rfl
      · rw [if_neg h1]
  apply C1_C3_step_quiet R s hs e e.1 hf hc he
  · intro h a ha
    change (ghostStep2 R s e).cfg (e.1,a) = _
    rw [hslots a ha]
    exact h a ha
  · intro t h
    obtain ⟨p,hp,h⟩ := h
    refine ⟨p,hp,?_⟩
    intro a ha
    change (ghostStep2 R s e).cfg (e.1,a) = _
    rw [hslots a ha]
    exact h a ha

/-- Interior transport preserves both selected clauses for either
direction; the payload and unique-token position are checked literally. -/
theorem C1_C3_step_move (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (a b p p' : Fin R.h) (t : Slot)
    (ha : 0 < a.val) (hb : 0 < b.val) (hp : 0 < p.val) (hp' : 0 < p'.val)
    (ht : t ≠ .empty) (hl : e = (g,a)) (hr : rn R e = (g,b))
    (hpos : p = a ∨ p = b) (hpos' : p' = a ∨ p' = b)
    (hslots : ∀ x : Fin R.h, 0 < x.val → s.cfg (g,x) = .interior (if x = p then t else .empty))
    (hrow : row (s.cfg e) (s.cfg (rn R e)) =
      (.interior (if a = p' then t else .empty),.interior (if b = p' then t else .empty))) :
    EpochShape R (view R (ghostStep2 R s e)) g ∧ C3At R (ghostStep2 R s e) g := by
  have hf := no_joins_of_row R s e (by rw [hrow]; rfl) (by rw [hrow]; rfl)
  have hc : compares (s.cfg e) (s.cfg (rn R e)) = false := by
    rw [hr,hl,hslots a ha,hslots b hb]
    split <;> split <;> cases t <;> rfl
  have he : rawEpochs R (curView R s) e g = (s.epoch g).cur := by
    have hg : g = e.1 := by rw [hl]
    rw [rawEpochs,if_pos hg]
    change rowEpoch (s.k g) (s.epoch g).cur (s.cfg e) (s.cfg (rn R e)) = _
    rw [hr,hl,hslots a ha,hslots b hb]
    split <;> split <;> cases t <;> rfl
  have hpost := ShortGapTwoEpochLaws.token_move_pair R s e g a b p p' t t
    hl hr hpos hpos' hslots hrow
  have hcfg : s.cfg (g,p) = .interior t := by simpa using hslots p hp
  apply C1_C3_step_quiet R s hs e g hf hc he
  · intro hempty
    have hh := hempty p hp
    change s.cfg (g,p) = .interior .empty at hh
    rw [hcfg] at hh
    exact False.elim (ht (Agent.interior.inj hh))
  · intro u hu
    obtain ⟨q,hq,hqslots⟩ := hu
    have hh := hqslots p hp
    change s.cfg (g,p) = .interior (if p = q then u else .empty) at hh
    rw [hcfg] at hh
    have htu : t = u := by
      by_cases heq : p = q
      · rw [if_pos heq] at hh; exact Agent.interior.inj hh
      · rw [if_neg heq] at hh; exact False.elim (ht (Agent.interior.inj hh))
    subst u
    exact ⟨p',hp',hpost⟩

private theorem send_current_idle (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (hw : (s.cfg (rootV R g)).cwPort = some .toSend) :
    (s.epoch g).cur = .idle := by
  have hh := owner_port_exact R s hs g
  rw [hw] at hh
  cases he : (s.epoch g).cur with
  | idle => rfl
  | outbound q c => simp only [he,epochCw] at hh; cases hh
  | returning q c d => simp only [he,epochCw] at hh; cases hh
  | delivered q c d => cases c <;> cases d <;> simp [he,epochCw,resCw,res,Verdict.cw] at hh

/-- An idle current transaction exposes precisely the completed strict
prefix, including the synthetic prefix after both archives were cleared. -/
theorem idle_prefix (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (hi : (s.epoch g).cur = .idle) :
    (s.k (next R g) = s.k g ∨ s.k (next R g)+1 = s.k g) ∧
    ∀ r, ComparedAt ((view R s).epoch g) r ↔ r < s.k g := by
  have hp := hs.previous g
  have hshape := hs.coherent.shape g
  cases he : (s.epoch g).prev with
  | outbound q c => simp only [PrevShape,he] at hp
  | returning q c d => simp only [PrevShape,he] at hp
  | delivered q c d =>
    simp only [PrevShape,he] at hp
    constructor
    · omega
    · intro r
      simp only [view,prefixView,combinedView,hi,he,ComparedAt]
      omega
  | idle =>
    by_cases hz : s.k g = 0
    · simp only [prefixView,combinedView,hi,he,hz,if_true,EpochShape] at hshape
      constructor
      · exact Or.inl (hshape.2.1.trans hz.symm)
      · intro r; simp [view,prefixView,combinedView,hi,he,hz,ComparedAt]
    · simp only [prefixView,combinedView,hi,he,hz,if_false,EpochShape] at hshape
      have hk : (view R s).k (next R g) = s.k (next R g) := rfl
      have hb : s.k (next R g) = s.k g-1 ∨ s.k (next R g) = s.k g-1+1 := hshape.2.1
      constructor
      · omega
      · intro r
        simp only [view,prefixView,combinedView,hi,he,hz,if_false,ComparedAt]
        omega

/-- L1 closes the selected clauses for arbitrary positive gap length. -/
theorem C1_C3_step_L1 (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (c : Choice) (ccw : CcwPort)
    (hl : s.cfg (rootV R g) = .root c .toSend ccw) (hh : 1 < R.h) :
    EpochShape R (view R (ghostStep2 R s (rootV R g))) g ∧
      C3At R (ghostStep2 R s (rootV R g)) g := by
  have hf := ShortGapTwoEpochLaws.prelaunch_no_joins R s hs g c ccw hl hh
  have hcur := ShortGapTwoEpochLaws.prelaunch_current_epoch R s hs g c ccw hl hh
  have hrow := ShortGapTwoEpochLaws.prelaunch_row R s hs g c ccw hl hh
  have hslot := ShortGapTwoEpochLaws.toSend_empty_gap2 R s hs g (by rw [hl]; rfl)
    ⟨1,hh⟩ (Nat.zero_lt_succ 0)
  have hn : compares (s.cfg (rootV R g)) (s.cfg (rn R (rootV R g))) = false := by
    rw [ShortGapTwoEpochLaws.rn_root_first R g hh,hl]
    change s.cfg (g,⟨1,hh⟩) = .interior .empty at hslot
    rw [hslot]; rfl
  have hi := send_current_idle R s hs g (by rw [hl]; rfl)
  obtain ⟨hb,hprefix⟩ := idle_prefix R s hs g hi
  have hprev : ((ghostStep2 R s (rootV R g)).epoch g).prev = (s.epoch g).prev := by
    change (epochStep2 R s (rootV R g) g).prev = _
    simp [epochStep2,hf,hn]
  have hk : ∀ i, (ghostStep2 R s (rootV R g)).k i = s.k i := by
    intro i; simp [ghostStep2_k,hf]
  have hv : (view R (ghostStep2 R s (rootV R g))).epoch g =
      .outbound (s.k g) (resolveInit c) := by simp [view,prefixView,combinedView,hcur]
  have hw : ((ghostStep2 R s (rootV R g)).cfg (rootV R (next R g))).ccwPort =
      (s.cfg (rootV R (next R g))).ccwPort := by
    rw [root_cfg_no_join R s (rootV R g) (next R g) (hf _)]
    exact raw_ccw_no_compare R s hs (rootV R g) g hn
  have hpay := raw_choice_recorded R s hs (rootV R g) g (by simp [incident]) (resolveInit c)
    (by rw [rawAt,if_pos rfl,hrow]; rfl)
  constructor
  · rw [EpochShape,hv]
    exact ⟨hk g,by simpa only [view,prefixView,combinedView,hk] using hb,hpay,
      ShortGapTwoEpochLaws.prelaunch_token R s hs g c ccw hl hh⟩
  · unfold C3At
    rw [hv,hcur,hprev,hk,hw]
    refine ⟨(hs.coherent.incoming g).trans (hprefix _),?_,?_⟩
    · intro h
      obtain ⟨c,d,hc,hd,hv⟩ := hs.coherent.incomingValue g ((hprefix _).mpr h)
      exact ⟨c,d,history2_monotone R s (rootV R g) _ _ _ hc,
        history2_monotone R s (rootV R g) _ _ _ hd,hv⟩
    · simpa only [hi,CurrentResult] using hs.incoming g

/-- A physical reply identifies its retained declaration payload and
the unique live return position. -/
theorem reply_epoch (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (a : Fin R.h) (ha : 0 < a.val) (d : Choice)
    (hc : s.cfg (g,a) = .interior (.reply d)) :
    ∃ c, (s.epoch g).cur = .returning (s.k g) c d ∧
      ∀ x : Fin R.h, 0 < x.val → s.cfg (g,x) = .interior (if x = a then .reply d else .empty) := by
  have ht := hs.current g
  have hshape := current_token_shape R s hs g
  cases he : (s.epoch g).cur with
  | idle =>
    rw [he] at hshape
    have hx := hshape a ha
    change s.cfg (g,a) = .interior .empty at hx
    rw [hc] at hx; cases hx
  | delivered q x y =>
    rw [he] at hshape
    have hx := hshape a ha
    change s.cfg (g,a) = .interior .empty at hx
    rw [hc] at hx; cases hx
  | outbound q x =>
    rw [he] at hshape
    obtain ⟨p,hp,hslots⟩ := hshape
    have hx := hslots a ha
    change s.cfg (g,a) = _ at hx
    rw [hc] at hx
    split at hx <;> cases hx
  | returning q x y =>
    have hq : q = s.k g := by simpa only [he,CurrentTag] using ht
    rw [he] at hshape
    obtain ⟨p,hp,hslots⟩ := hshape
    have hx := hslots a ha
    change s.cfg (g,a) = _ at hx
    rw [hc] at hx
    by_cases hap : a = p
    · rw [if_pos hap] at hx
      cases hx
      exact ⟨x,by rw [hq],by simpa only [curView,← hap] using hslots⟩
    · rw [if_neg hap] at hx; cases hx

private theorem interior_input_positive (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (t : Slot) (he : s.cfg e = .interior t) : 0 < e.2.val := by
  by_cases hz : e.2.val = 0
  · have hv : e = rootV R e.1 := Prod.ext rfl (Fin.ext hz)
    obtain ⟨c,cw,ccw,hc⟩ := hs.coherent.roots e.1
    change s.cfg (rootV R e.1) = .root c cw ccw at hc
    rw [hv,hc] at he; cases he
  · omega

private theorem interior_receiver_next (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (t : Slot) (he : s.cfg (rn R e) = .interior t) : e.2.val+1 < R.h := by
  have hp := interior_input_positive R s hs (rn R e) t he
  by_cases hn : e.2.val+1 < R.h
  · exact hn
  · rw [rn_of_last R e hn] at hp
    change 0 < 0 at hp
    omega

/-- All literal selected-edge rows, including L1, F1, B1 and the
resolution-only rows omitted from the earlier selected-gap lemmas. -/
theorem C1_C3_step_selected (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) : EpochShape R (view R (ghostStep2 R s e)) e.1 ∧ C3At R (ghostStep2 R s e) e.1 := by
  cases hl : s.cfg e with
  | interior a =>
    have ha := interior_input_positive R s hs e a hl
    cases hr : s.cfg (rn R e) with
    | interior b =>
      have hn := interior_receiver_next R s hs e b hr
      let j : Fin R.h := ⟨e.2.val+1,hn⟩
      have hj : 0 < j.val := by change 0 < e.2.val+1; omega
      have hrn : rn R e = (e.1,j) := rn_of_lt R e hn
      have hne : e.2 ≠ j := by intro h; have := congrArg Fin.val h; change e.2.val = e.2.val+1 at this; omega
      cases a <;> cases b
      all_goals first |
        (exact C1_C3_step_resolution R s hs e (by rw [hl,hr]; rfl) (by rw [hl,hr]; rfl)
          (by rw [hl,hr]; rfl) (by simp [rawEpochs,curView,hl,hr,rowEpoch])) | skip
      · obtain ⟨c,_,hslots⟩ := reply_epoch R s hs e.1 j hj _ (hrn ▸ hr)
        exact C1_C3_step_move R s hs e e.1 e.2 j j e.2 _ ha hj hj ha
          (by intro h; cases h) rfl hrn (Or.inr rfl) (Or.inl rfl) hslots
          (by rw [hl,hr]; simp [row,Ne.symm hne])
      · obtain ⟨_,hslots⟩ := declaration_epoch R s hs e.1 e.2 ha _ hl
        exact C1_C3_step_move R s hs e e.1 e.2 j e.2 j _ ha hj ha hj
          (by intro h; cases h) rfl hrn (Or.inl rfl) (Or.inr rfl) hslots
          (by rw [hl,hr]; simp [row,hne])
    | root d cw ccw =>
      obtain ⟨hlast,hrn⟩ := root_receiver_last R s hs e d cw ccw hr
      cases a <;> cases ccw
      all_goals first |
        (exact C1_C3_step_resolution R s hs e (by rw [hl,hr]; rfl) (by rw [hl,hr]; rfl)
          (by rw [hl,hr]; rfl) (by simp [rawEpochs,curView,hl,hr,rowEpoch])) | skip
      exact C1_C3_step_comparison R s hs e.1 e.2 ha hlast _ d cw hl (hrn ▸ hr)
  | root c cw ccw =>
    have hz := root_input_zero R s hs e c cw ccw hl
    have he : e = rootV R e.1 := Prod.ext rfl (Fin.ext hz)
    cases hr : s.cfg (rn R e) with
    | interior t =>
      have hn := interior_receiver_next R s hs e t hr
      have hh : 1 < R.h := by omega
      cases cw <;> cases t
      all_goals first |
        (exact C1_C3_step_resolution R s hs e (by rw [hl,hr]; rfl) (by rw [hl,hr]; rfl)
          (by rw [hl,hr]; rfl) (by simp [rawEpochs,curView,hl,hr,rowEpoch])) | skip
      · have h := C1_C3_step_L1 R s hs e.1 c ccw (he ▸ hl) hh
        simpa only [← he] using h
      all_goals
        have hrn : rn R e = (e.1,⟨1,hh⟩) := by
          rw [he,ShortGapTwoEpochLaws.rn_root_first R e.1 hh]
        obtain ⟨x,hcur,hslots⟩ := reply_epoch R s hs e.1 ⟨1,hh⟩ (Nat.zero_lt_succ 0) _ (hrn ▸ hr)
        have h := C1_C3_step_V1 R s hs e.1 (s.k e.1) x _ hh hcur (by
          intro a ha
          have hiff : a = (⟨1,hh⟩ : Fin R.h) ↔ a.val = 1 := ⟨congrArg Fin.val,fun h => Fin.ext h⟩
          simpa only [hiff] using hslots a ha)
        simpa only [← he] using h
    | root d dw dd =>
      obtain ⟨hlast,hrn⟩ := root_receiver_last R s hs e d dw dd hr
      have hh : R.h = 1 := by omega
      cases cw <;> cases dd
      all_goals first |
        (exact C1_C3_step_resolution R s hs e (by rw [hl,hr]; rfl) (by rw [hl,hr]; rfl)
          (by rw [hl,hr]; rfl) (by simp [rawEpochs,curView,hl,hr,rowEpoch])) | skip
      have h := C1_C3_step_P1 R s hs hh e.1 c d ccw dw (he ▸ hl) (hrn ▸ hr)
      simpa only [← he] using h

/-- The scheduled gap and every unscheduled gap satisfy post-step shape. -/
theorem C1_step (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s) (e : Vtx R) :
    C1 R (ghostStep2 R s e) := by
  intro g
  by_cases hg : g = e.1
  · subst g; exact (C1_C3_step_selected R s hs e).1
  · exact C1_step_adjacent R s hs e g hg

/-- Both prefix and two-epoch right-port agreements hold after every edge. -/
theorem C3_step (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s) (e : Vtx R) :
    C3 R (ghostStep2 R s e) := by
  apply (C3_iff_forall R _).mpr
  intro g
  by_cases hg : g = e.1
  · subst g; exact (C1_C3_step_selected R s hs e).2
  · exact C3_step_adjacent R s hs e g hg

/-- All three actual C7 history clauses are preserved unconditionally. -/
theorem C7_step (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s) (e : Vtx R) :
    C7 R (ghostStep2 R s e) := C7_step_of_C1 R s hs e (C1_step R s hs e)

/-- Full two-epoch lineage closure for every physical edge and every
state satisfying Lineage2; no post-state clause is assumed. -/
theorem lineage2_step (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s) (e : Vtx R) :
    Lineage2 R (ghostStep2 R s e) :=
  lineage2_step_of_remaining_clauses R s hs e
    (C1_step R s hs e) (C3_step R s hs e) (C7_step R s hs e)

/-- A denial-only cohort step stays in its domain or reaches the
corrected virtual-candidate stopping port. -/
theorem dom_step_or_success (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Dom R r s) (e : Vtx R) :
    Dom R r (ghostStep2 R s e) ∨ VirtualSuccess R r (ghostStep2 R s e) :=
  dom_step_or_success_of_lineage R r s hs e (lineage2_step R s hs.1 e)

/-- The corrected stopped process now has a proved closure argument. -/
noncomputable def stoppedStep (R : RFrame) (r : Nat) :
    Active R r → Fin R.n → StopNode (Active R r) :=
  stoppedStepOfClosure R r (fun s hs e => lineage2_step R s hs.1 e)

/-- Unconditional Bellman super-solution for the literal two-epoch
carrier, with the max-generation virtual-candidate stopping port. -/
theorem genPipelined2_natBellmanSuperSolution (R : RFrame) (r : Nat) :
    NatBellmanSuperSolution (stoppedStep R r) 1 (stoppedPotential R r) :=
  genPipelined2_natBellmanSuperSolution_of_lineage2_step R r
    (fun s hs e => lineage2_step R s hs.1 e)

theorem stoppedStep_success_iff (R : RFrame) (r : Nat) (s : Active R r) (e : Fin R.n) :
    stoppedStep R r s e = .success ↔ VirtualSuccess R r (ghostStep2 R s.val (edgeVtx R e)) :=
  ShortGapLineage2Closure.stoppedStep_success_iff R r _ s e

theorem stoppedStep_failure_iff (R : RFrame) (r : Nat) (s : Active R r) (e : Fin R.n) :
    stoppedStep R r s e = .failure ↔ RoundFailure R r (ghostStep2 R s.val (edgeVtx R e)) :=
  ShortGapLineage2Closure.stoppedStep_failure_iff R r _ s e

theorem stoppedStep_failure_uniform (R : RFrame) (r : Nat) (s : Active R r) (e : Fin R.n)
    (hf : stoppedStep R r s e = .failure) :
    PeriodHIncidenceChoice.Constant (word2 R r (ghostStep2 R s.val (edgeVtx R e))) :=
  ShortGapLineage2Closure.stoppedStep_failure_uniform R r _ s e hf

theorem stoppedPotential_start (R : RFrame) :
    stoppedPotential R 1 (.active (startActive R)) = 2 * R.n * R.m * R.h :=
  ShortGapLineage2Closure.stoppedPotential_start R

#print axioms C1_step_adjacent
#print axioms C3_step_adjacent
#print axioms C1_C3_step_selected
#print axioms completed_denials_step
#print axioms C1_step
#print axioms C3_step
#print axioms C7_step
#print axioms lineage2_step
#print axioms dom_step_or_success
#print axioms genPipelined2_natBellmanSuperSolution
#print axioms stoppedStep_success_iff
#print axioms stoppedStep_failure_iff
#print axioms stoppedStep_failure_uniform
#print axioms stoppedPotential_start

end ShortGapLineage2ClosureB
