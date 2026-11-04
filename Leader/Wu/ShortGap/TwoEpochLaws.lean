import Leader.Wu.ShortGap.TwoEpoch

/-!
# Any-round virtual stopping and literal two-epoch obligations

Success includes every historical word up to the accounting round, so a
predecessor candidate uses the sidecar success port. The physical rows,
generation counters, history monitor and two-epoch update are unchanged.
Dom contains only lineage, the entry cut and absence of this success;
it does not carry any closure, simulation, debt or Bellman conclusion.
-/
namespace ShortGapTwoEpochLaws
open ShortGapLiteralGapRows ShortGapLiteralRingRows ShortGapOwnerRoundSlice
open ShortGapCurrentCohort ShortGapLineage ShortGapLineageRetained
open ShortGapDenialTransportLiteral ShortGapGenerationMask ShortGapTwoEpoch
open ShortGapJoinedIncidenceBalance FiniteUniformStoppingTree ShortGapChoiceStopping
set_option autoImplicit false

/-- Sidecar success includes the accounting word and every predecessor. -/
def VirtualSuccess (R : RFrame) (r : Nat) (s : GhostRing2 R) : Prop :=
  ∃ q, q ≤ r ∧ VirtualCandidate2 R q s

def Dom (R : RFrame) (r : Nat) (s : GhostRing2 R) : Prop :=
  Lineage2 R s ∧ CohortEntered2 R r s ∧ ¬ VirtualSuccess R r s

theorem current_candidate_success (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (hc : VirtualCandidate2 R r s) : VirtualSuccess R r s := ⟨r,Nat.le_refl _,hc⟩

theorem virtualSuccess_persists (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (e : Vtx R) (hs : VirtualSuccess R r s) : VirtualSuccess R r (ghostStep2 R s e) := by
  obtain ⟨q,hq,hc⟩ := hs
  exact ⟨q,hq,virtualCandidate2_persists R q s e hc⟩

/-- Absence of sidecar success implies denial-only predecessor history.
Unlike the old domain, the alternative predecessor candidate is now terminal. -/
theorem dom_denial (R : RFrame) (r : Nat) (s : GhostRing2 R) (hs : Dom R r s) :
    DenialOnly2 R r s := by
  rcases denial2_or_predecessor_candidate R r s with hd | hc
  · exact hd
  · exact False.elim (hs.2.2 ⟨r-1,Nat.sub_le _ _,hc⟩)

theorem no_virtualSuccess_start (R : RFrame) (r : Nat) :
    ¬ VirtualSuccess R r (ghostStart2 R) := by
  rintro ⟨q,_,g,hg⟩
  cases q with
  | zero =>
    have h0 : choiceToWord R.b = .out1 := hg.1
    have h1 : choiceToWord R.b = .in0 := hg.2
    rw [h0] at h1
    cases h1
  | succ q =>
    have h0 := hg.1
    change (word2 R (q+1) (ghostStart2 R) g) = .out1 at h0
    simp [word2,wordOf,curView,ghostStart2,ghostStart,choiceToWord] at h0

theorem dom_start (R : RFrame) : Dom R 1 (ghostStart2 R) :=
  ⟨lineage2_start R,cohortEntered2_start R,no_virtualSuccess_start R 1⟩

/-- The previously failing predecessor comparison is absorbed as success
both before and after its physical candidate-receipt write. -/
theorem predecessor_counterexample_stops :
    VirtualSuccess T 2 beforeCandidate2 ∧ VirtualSuccess T 2 afterCandidate2 := by
  have h : VirtualSuccess T 2 beforeCandidate2 := ⟨1,by decide,predecessor_virtual_candidate⟩
  exact ⟨h,virtualSuccess_persists T 2 beforeCandidate2 candidateEdge h⟩

/-- Uniform failure is exactly a frozen accounting word without any
sidecar success. It does not silently swallow invariant exits. -/
def RoundFailure (R : RFrame) (r : Nat) (s : GhostRing2 R) : Prop :=
  PeriodHIncidenceChoice.Frozen (word2 R r s) ∧ ¬ VirtualSuccess R r s

theorem roundFailure_uniform (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (hf : RoundFailure R r s) : PeriodHIncidenceChoice.Constant (word2 R r s) :=
  PeriodHIncidenceChoice.frozen_noCandidate_constant (ring R) (word2 R r s) hf.1
    (fun g hg => hf.2 (current_candidate_success R r s ⟨g,hg⟩))

/-- The declared source of prelaunch emptiness: a toSend owner cannot
still have a live reply or declaration in the coherent gap. -/
theorem toSend_empty_gap2 (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (hc : (s.cfg (rootV R g)).cwPort = some .toSend) :
    EmptyGap R (curView R s) g :=
  toSend_empty_gap R (prefixView R (combinedView R s)) hs.coherent g hc

/-- In particular, L1's first interior slot is empty for an idle cur.
The h=1 case has no interior slot and is handled by direct P1. -/
theorem prelaunch_first_slot_empty (R : RFrame) (s : GhostRing2 R)
    (hs : Lineage2 R s) (g : Fin R.m) (hi : (s.epoch g).cur = .idle) (hh : 1 < R.h) :
    s.cfg (g,⟨1,hh⟩) = .interior .empty :=
  toSend_empty_gap2 R s hs g (hs.idleSend g hi) ⟨1,hh⟩ (Nat.zero_lt_succ 0)

theorem unjoined_debt_on_dom (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Dom R r s) (i : Fin R.m) (hi : s.k i < r) : 0 < latentDebt2 R r s :=
  unjoined_gen_has_debt2 R r s hs.1 (dom_denial R r s hs) i hi

theorem zero_debt_step_on_dom (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Dom R r s) (hz : latentDebt2 R r s = 0) (e : Vtx R) :
    latentDebt2 R r (ghostStep2 R s e) = 0 :=
  latentDebt2_zero_step R r s hs.1 (dom_denial R r s hs) hz e

/-! Local physical row infrastructure and the prelaunch branch. -/

/-- Explicit physical pair update, including each endpoint's JOIN. -/
theorem cfg_step_pair (R : RFrame) (s : GhostRing2 R) (e v : Vtx R) :
    (ghostStep2 R s e).cfg v =
      if v = e then ShortGapLiteralRingRows.joinA (row (s.cfg e) (s.cfg (rn R e))).1
      else if v = rn R e then ShortGapLiteralRingRows.joinA (row (s.cfg e) (s.cfg (rn R e))).2
      else s.cfg v := by
  rw [ghostStep2_physical]
  by_cases h0 : v = e
  · simp [ShortGapOwnerRoundSlice.ringStepU,joinTick,rawAt,incident,h0]
  · by_cases h1 : v = rn R e
    · simp [ShortGapOwnerRoundSlice.ringStepU,joinTick,rawAt,incident,h1,rn_ne_self]
    · simp [ShortGapOwnerRoundSlice.ringStepU,incident,h0,h1]

/-- With no owner JOIN, an unscheduled gap's entire accounting token
stutters, not merely its debt. -/
theorem other_gap_token_eq (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (e : Vtx R) (g : Fin R.m) (hg : g ≠ e.1)
    (hf : fires R (physical2 R s) e g = false) :
    tokens2 R r (ghostStep2 R s e) g = tokens2 R r s g := by
  cases r with
  | zero => rfl
  | succ q =>
    have hk : (curView R (ghostStep2 R s e)).k g = (curView R s).k g := by
      change (ghostStep2 R s e).k g = s.k g
      simp [ghostStep2_k,hf]
    have he : (curView R (ghostStep2 R s e)).epoch g = (curView R s).epoch g := by
      change (epochStep2 R s e g).cur = _
      rw [epochStep2_cur,hf]
      simp [rawEpochs,hg]
    have hp := other_gap_tokenPos R s e g hg
    change cohortToken R q (curView R (ghostStep2 R s e)) g =
      cohortToken R q (curView R s) g
    simp only [cohortToken,hk,he,hp]

/-- The first edge of a nontrivial gap has a genuine interior receiver. -/
theorem rn_root_first (R : RFrame) (g : Fin R.m) (hh : 1 < R.h) :
    rn R (rootV R g) = (g,⟨1,hh⟩) := by
  exact rn_of_lt R (rootV R g) hh

/-- The actual L1 row, with the first slot's emptiness derived from lineage. -/
theorem prelaunch_row (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (c : Choice) (ccw : CcwPort)
    (hc : s.cfg (rootV R g) = .root c .toSend ccw) (hh : 1 < R.h) :
    row (s.cfg (rootV R g)) (s.cfg (rn R (rootV R g))) =
      (.root (resolveInit c) .waiting ccw,.interior (.decl (resolveInit c))) := by
  have hempty := toSend_empty_gap2 R s hs g (by rw [hc]; rfl)
  have hslot : s.cfg (g,⟨1,hh⟩) = .interior .empty := hempty ⟨1,hh⟩ (Nat.zero_lt_succ 0)
  rw [rn_root_first R g hh,hc,hslot]
  rfl

/-- L1 leaves every root outside JOIN: the owner is waiting and the
other endpoint is an interior slot. -/
theorem prelaunch_no_joins (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (c : Choice) (ccw : CcwPort)
    (hc : s.cfg (rootV R g) = .root c .toSend ccw) (hh : 1 < R.h) :
    ∀ i, fires R (physical2 R s) (rootV R g) i = false := by
  have hr := prelaunch_row R s hs g c ccw hc hh
  intro i
  have hright : rootV R i ≠ rn R (rootV R g) := by
    rw [rn_root_first R g hh]
    intro h
    have hv := congrArg (fun v : Vtx R => v.2.val) h
    change 0 = 1 at hv
    omega
  by_cases hi : rootV R i = rootV R g
  · simp [fires,physical2,incident,rawAt,hi,hr,joinReady]
  · simp [fires,physical2,incident,hi,hright]

/-- A genuine L1 launch creates exactly one declaration at slot 1. -/
theorem prelaunch_token (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (c : Choice) (ccw : CcwPort)
    (hc : s.cfg (rootV R g) = .root c .toSend ccw) (hh : 1 < R.h) :
    OneToken R (curView R (ghostStep2 R s (rootV R g))) g (.decl (resolveInit c)) := by
  have hr := prelaunch_row R s hs g c ccw hc hh
  have hempty := toSend_empty_gap2 R s hs g (by rw [hc]; rfl)
  refine ⟨⟨1,hh⟩,Nat.zero_lt_succ 0,?_⟩
  intro a ha
  have hleft : (g,a) ≠ rootV R g := by
    intro h
    have hv := congrArg (fun v : Vtx R => v.2.val) h
    change a.val = 0 at hv
    omega
  have hright : (g,a) = rn R (rootV R g) ↔ a = ⟨1,hh⟩ := by
    rw [rn_root_first R g hh]
    exact ⟨fun h => congrArg Prod.snd h,fun h => congrArg (g,·) h⟩
  change (ghostStep2 R s (rootV R g)).cfg (g,a) = _
  rw [cfg_step_pair,if_neg hleft,hr]
  by_cases he : a = ⟨1,hh⟩
  · rw [if_pos (hright.mpr he),if_pos he]; rfl
  · rw [if_neg (fun h => he (hright.mp h)),if_neg he]
    exact hempty a ha

/-- Hence the real bounded scan identifies the new token's position. -/
theorem prelaunch_tokenPos (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (c : Choice) (ccw : CcwPort)
    (hc : s.cfg (rootV R g) = .root c .toSend ccw) (hh : 1 < R.h) :
    tokenPos R (curView R (ghostStep2 R s (rootV R g))) g = 1 := by
  obtain ⟨p,hp,hslots⟩ := prelaunch_token R s hs g c ccw hc hh
  have hfirst := hslots ⟨1,hh⟩ (Nat.zero_lt_succ 0)
  have hpone : p = ⟨1,hh⟩ := by
    by_cases he : p = ⟨1,hh⟩
    · exact he
    · have hp' : (⟨1,hh⟩ : Fin R.h) ≠ p := Ne.symm he
      rw [if_neg hp'] at hfirst
      have hslot := (prelaunch_token R s hs g c ccw hc hh)
      have hr := prelaunch_row R s hs g c ccw hc hh
      have hne : (g,(⟨1,hh⟩ : Fin R.h)) ≠ rootV R g := by
        intro heq
        have hv := congrArg (fun v : Vtx R => v.2.val) heq
        change 1 = 0 at hv; omega
      change (ghostStep2 R s (rootV R g)).cfg (g,⟨1,hh⟩) = .interior .empty at hfirst
      rw [cfg_step_pair,if_neg hne,← rn_root_first R g hh,if_pos rfl,hr] at hfirst
      cases hfirst
  rw [tokenPos2_of_unique R (ghostStep2 R s (rootV R g)) g p hp
    (.decl (resolveInit c)) (by intro h; cases h) hslots]
  rw [hpone]

theorem prelaunch_current_epoch (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (c : Choice) (ccw : CcwPort)
    (hc : s.cfg (rootV R g) = .root c .toSend ccw) (hh : 1 < R.h) :
    ((ghostStep2 R s (rootV R g)).epoch g).cur = .outbound (s.k g) (resolveInit c) := by
  have hf := prelaunch_no_joins R s hs g c ccw hc hh g
  have hslot := toSend_empty_gap2 R s hs g (by rw [hc]; rfl) ⟨1,hh⟩ (Nat.zero_lt_succ 0)
  change s.cfg (g,⟨1,hh⟩) = .interior .empty at hslot
  change (epochStep2 R s (rootV R g) g).cur = _
  rw [epochStep2_cur,hf]
  simp only [Bool.false_eq_true,if_false]
  rw [rawEpochs,if_pos rfl]
  change rowEpoch (s.k g) (s.epoch g).cur (s.cfg (rootV R g)) (s.cfg (rn R (rootV R g))) = _
  rw [hc,rn_root_first R g hh,hslot]
  rfl

/-- L1 lowers the selected predecessor token by exactly one physical hop. -/
theorem prelaunch_token_debt_drop (R : RFrame) (q : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (g : Fin R.m) (c : Choice) (ccw : CcwPort)
    (hc : s.cfg (rootV R g) = .root c .toSend ccw) (hh : 1 < R.h)
    (hq : s.k g = q) (hi : (s.epoch g).cur = .idle) :
    (tokens2 R (q+1) (ghostStep2 R s (rootV R g)) g).hops + 1 =
      (tokens2 R (q+1) s g).hops := by
  have hf := prelaunch_no_joins R s hs g c ccw hc hh g
  have hk0 : (curView R s).k g = q := hq
  have hk1 : (curView R (ghostStep2 R s (rootV R g))).k g = q := by
    change (ghostStep2 R s (rootV R g)).k g = q
    simp [ghostStep2_k,hf,hq]
  have he0 : (curView R s).epoch g = .idle := hi
  have he1 : (curView R (ghostStep2 R s (rootV R g))).epoch g = .outbound q (resolveInit c) := by
    change ((ghostStep2 R s (rootV R g)).epoch g).cur = _
    rw [prelaunch_current_epoch R s hs g c ccw hc hh,hq]
  have hp := prelaunch_tokenPos R s hs g c ccw hc hh
  simp [tokens2,tokensOf',cohortToken,hk0,hk1,he0,he1,hp,ofPhase,hh,LitGapState.hops]
  omega

private theorem sum_one_drop {m : Nat} (f g : Fin m → Nat) (i : Fin m)
    (hi : f i + 1 = g i) (ho : ∀ j, j ≠ i → f j = g j) :
    (List.ofFn f).sum + 1 = (List.ofFn g).sum := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    rw [List.ofFn_succ,List.sum_cons,List.ofFn_succ,List.sum_cons]
    by_cases hz : i = 0
    · subst i
      have ht := ofFn_sum_eq (fun j : Fin m => f j.succ) (fun j => g j.succ)
        (fun j => ho j.succ (by intro he; have hv := congrArg Fin.val he; simp at hv))
      omega
    · have hp : 0 < i.val := by
        have hn : i.val ≠ 0 := fun h => hz (Fin.ext h)
        omega
      let j : Fin m := ⟨i.val-1,by have := i.isLt; omega⟩
      have hj : j.succ = i := Fin.ext (by simp [j]; omega)
      have ht := ih (fun j : Fin m => f j.succ) (fun j => g j.succ) j
        (by simpa only [hj] using hi) (by
          intro k hk
          apply ho k.succ
          intro he
          rw [← hj] at he
          exact hk (Fin.succ_inj.mp he))
      have h0 := ho 0 (Ne.symm hz)
      omega

/-- Complete arbitrary-h prelaunch progress, including the total debt:
all other tokens stutter because L1 fires no JOIN at any root. -/
theorem prelaunch_lowers_latentDebt2 (R : RFrame) (q : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (g : Fin R.m) (hq : s.k g = q)
    (hi : (s.epoch g).cur = .idle) (hh : 1 < R.h) :
    latentDebt2 R (q+1) (ghostStep2 R s (rootV R g)) + 1 = latentDebt2 R (q+1) s := by
  obtain ⟨c,cw,ccw,hroot⟩ := hs.coherent.roots g
  change s.cfg (rootV R g) = .root c cw ccw at hroot
  have hc := hs.idleSend g hi
  rw [hroot] at hc
  have hcw : cw = .toSend := Option.some.inj hc
  subst cw
  apply sum_one_drop _ _ g
  · exact prelaunch_token_debt_drop R q s hs g c ccw hroot hh hq hi
  · intro j hj
    rw [other_gap_token_eq R (q+1) s (rootV R g) j hj
      (prelaunch_no_joins R s hs g c ccw hroot hh j)]

/-! Shared-root JOIN does not charge another gap's token. -/

/-- Every literal row leaves a right root's clockwise receipt unchanged. -/
theorem row_right_cw (a : Agent) (c : Choice) (cw : CwPort) (ccw : CcwPort) :
    ((row a (.root c cw ccw)).2).cwPort = some cw := by
  cases a with
  | root d dw dd => cases dw <;> cases ccw <;> rfl
  | interior t => cases t <;> cases ccw <;> rfl

theorem raw_cw_other (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (hg : g ≠ e.1) :
    (rawAt R s.cfg e (rootV R g)).cwPort = (s.cfg (rootV R g)).cwPort := by
  have hleft : rootV R g ≠ e := fun h => hg (congrArg Prod.fst h)
  obtain ⟨c,cw,ccw,hroot⟩ := hs.coherent.roots g
  change s.cfg (rootV R g) = .root c cw ccw at hroot
  by_cases hright : rootV R g = rn R e
  · have hr : s.cfg (rn R e) = .root c cw ccw := by rw [← hright]; exact hroot
    rw [rawAt,if_neg hleft,if_pos hright,hr,hroot]
    exact row_right_cw _ _ _ _
  · rw [rawAt,if_neg hleft,if_neg hright]

/-- A shared-root JOIN can affect an unscheduled owner only after its
own current transaction is delivered. This is derived from port agreement. -/
theorem other_join_current_delivered (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (hg : g ≠ e.1)
    (hf : fires R (physical2 R s) e g = true) :
    ∃ c d, (s.epoch g).cur = .delivered (s.k g) c d := by
  have hj := (fires_iff R (physical2 R s) e g).mp hf
  obtain ⟨c,hc⟩ := hj.2
  change rawAt R s.cfg e (rootV R g) = .root c .heldDenial .heldDenial at hc
  have hcw : (s.cfg (rootV R g)).cwPort = some .heldDenial := by
    rw [← raw_cw_other R s hs e g hg,hc]
    rfl
  cases he : (s.epoch g).cur with
  | idle =>
    have hh := hs.idleSend g he
    rw [hcw] at hh
    cases hh
  | outbound q c =>
    have hh := (hs.waiting g).mpr (by rw [he]; trivial)
    rw [hcw] at hh
    cases hh
  | returning q c d =>
    have hh := (hs.waiting g).mpr (by rw [he]; trivial)
    rw [hcw] at hh
    cases hh
  | delivered q c d =>
    have ht := hs.current g
    simp only [he,CurrentTag] at ht
    exact ⟨c,d,by rw [ht]⟩

/-- Transfer of a delivered current epoch to prev, with owner increment,
preserves every accounting token: past tokens stay discharged and future
tokens stay latent. -/
theorem token_eq_of_delivered_join (R : RFrame) (r : Nat) (s t : GhostRing2 R)
    (g : Fin R.m) (c d : Choice) (hc : (s.epoch g).cur = .delivered (s.k g) c d)
    (hk : t.k g = s.k g + 1) (he : (t.epoch g).cur = .idle) :
    tokens2 R r t g = tokens2 R r s g := by
  cases r with
  | zero => rfl
  | succ q =>
    have he0 : (curView R s).epoch g = .delivered ((curView R s).k g) c d := hc
    have he1 : (curView R t).epoch g = .idle := he
    have hk' : (curView R t).k g = (curView R s).k g + 1 := hk
    by_cases hp : q < (curView R s).k g
    · have hp' : q < (curView R t).k g := by rw [hk']; omega
      simp only [tokens2,tokensOf'_past R q _ g hp,tokensOf'_past R q _ g hp']
    · by_cases hq : q = (curView R s).k g
      · have hp' : q < (curView R t).k g := by rw [hk',hq]; omega
        simp [tokens2,tokensOf',cohortToken,he0,hk',hq]
      · have hfuture : (curView R s).k g < q := by omega
        have hnotpast : ¬ q < (curView R t).k g := by rw [hk']; omega
        simp only [tokens2,tokensOf',cohortToken,if_neg hp,if_pos hfuture,
          if_neg hnotpast,he1,ite_self]

/-- Under lineage, every unscheduled gap's token stutters exactly, even
when its owner JOINs as the right endpoint of the scheduled interaction. -/
theorem other_gap_token_eq_lineage (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (e : Vtx R) (g : Fin R.m) (hg : g ≠ e.1) :
    tokens2 R r (ghostStep2 R s e) g = tokens2 R r s g := by
  cases hf : fires R (physical2 R s) e g with
  | false => exact other_gap_token_eq R r s e g hg hf
  | true =>
    obtain ⟨c,d,hc⟩ := other_join_current_delivered R s hs e g hg hf
    apply token_eq_of_delivered_join R r s (ghostStep2 R s e) g c d hc
    · simp [ghostStep2_k,hf]
    · change (epochStep2 R s e g).cur = .idle
      simp [epochStep2_cur,hf]

/-- A delivered annotation can only be replaced by a new launch, whose
left input must be a toSend root. -/
theorem rowEpoch_delivered (k q : Nat) (c d : Choice) (a b : Agent)
    (ha : a.cwPort ≠ some .toSend) :
    rowEpoch k (.delivered q c d) a b = .delivered q c d := by
  cases a with
  | interior t =>
    cases b with
    | root x cw ccw => cases t <;> cases ccw <;> rfl
    | interior u => cases t <;> rfl
  | root x cw ccw =>
    cases cw with
    | toSend => exact False.elim (ha rfl)
    | waiting => cases b with
      | root y yw yy => rfl
      | interior t => cases t <;> rfl
    | heldDenial => cases b with
      | root y yw yy => rfl
      | interior t => cases t <;> rfl
    | heldCandidate => cases b with
      | root y yw yy => rfl
      | interior t => cases t <;> rfl

theorem delivered_raw_epoch (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (q : Nat) (c d : Choice) (he : (s.epoch e.1).cur = .delivered q c d) :
    rawEpochs R (curView R s) e e.1 = .delivered q c d := by
  have hk := hs.current e.1
  simp only [he,CurrentTag] at hk
  have hheld := (hs.coherent.outgoing e.1).mpr (by
    simp [prefixView,combinedView,he,DeliveredAt,hk])
  have hnot : (s.cfg e).cwPort ≠ some .toSend := by
    by_cases ha : e.2.val = 0
    · have heRoot : e = rootV R e.1 := Prod.ext rfl (Fin.ext ha)
      rw [heRoot]
      intro hc
      change CwHeld (s.cfg (rootV R e.1)).cwPort at hheld
      rw [hc] at hheld
      exact hheld
    · have hp : 0 < e.2.val := by omega
      have hempty := current_token_shape R s hs e.1
      rw [he] at hempty
      have hslot : s.cfg e = .interior .empty := hempty e.2 hp
      rw [hslot]
      intro h; cases h
  rw [rawEpochs,if_pos rfl]
  change rowEpoch (s.k e.1) (s.epoch e.1).cur (s.cfg e) (s.cfg (rn R e)) = _
  rw [he]
  exact rowEpoch_delivered _ _ _ _ _ _ hnot

/-- A delivered selected token stutters through any physical interaction,
including owner JOIN. This discharges the complete delivered branch. -/
theorem delivered_selected_token_eq (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (e : Vtx R) (q : Nat) (c d : Choice)
    (he : (s.epoch e.1).cur = .delivered q c d) :
    tokens2 R r (ghostStep2 R s e) e.1 = tokens2 R r s e.1 := by
  have hq := hs.current e.1
  simp only [he,CurrentTag] at hq
  cases hf : fires R (physical2 R s) e e.1 with
  | true =>
    apply token_eq_of_delivered_join R r s (ghostStep2 R s e) e.1 c d
      (by rw [he,hq])
    · simp [ghostStep2_k,hf]
    · change (epochStep2 R s e e.1).cur = .idle
      simp [epochStep2_cur,hf]
  | false =>
    have hk : (curView R (ghostStep2 R s e)).k e.1 = (curView R s).k e.1 := by
      change (ghostStep2 R s e).k e.1 = s.k e.1
      simp [ghostStep2_k,hf]
    have he0 : (curView R s).epoch e.1 = .delivered q c d := he
    have he1 : (curView R (ghostStep2 R s e)).epoch e.1 = .delivered q c d := by
      change (epochStep2 R s e e.1).cur = _
      simp [epochStep2_cur,hf,delivered_raw_epoch R s hs e q c d he]
    cases r with
    | zero => rfl
    | succ t => simp only [tokens2,tokensOf',cohortToken,hk,he0,he1]

/-- Once the receiver has entered q, an owner's preceding record cannot
account for a still-held receipt when that owner is itself at q. -/
theorem previous_not_current_at_cut (R : RFrame) (q : Nat) (s : GhostRing2 R)
    (hs : Dom R (q+1) s) (g : Fin R.m) (hk : s.k g = q) :
    ¬ PreviousResult (s.epoch g).prev (s.k (next R g)) := by
  have hp := hs.1.previous g
  have hcut : q ≤ s.k (next R g) := hs.2.1 (next R g)
  intro hh
  cases he : (s.epoch g).prev
  all_goals simp only [he,PreviousResult] at hh
  simp only [PrevShape,he] at hp
  omega

/-- The entry cut supplies the receiver-free guard needed by direct P1
and by the last declaration comparison. This is derived, not assumed. -/
theorem right_free_at_cut (R : RFrame) (q : Nat) (s : GhostRing2 R)
    (hs : Dom R (q+1) s) (g : Fin R.m) (hk : s.k g = q)
    (hc : ¬ CurrentResult (s.epoch g).cur (s.k (next R g))) :
    (s.cfg (rootV R (next R g))).ccwPort = some .free := by
  have hn : ¬ CcwHeld (s.cfg (rootV R (next R g))).ccwPort := by
    intro hh
    rcases (hs.1.incoming g).mp hh with hh | hh
    · exact hc hh
    · exact previous_not_current_at_cut R q s hs g hk hh
  obtain ⟨c,cw,ccw,hroot⟩ := hs.1.coherent.roots (next R g)
  change s.cfg (rootV R (next R g)) = .root c cw ccw at hroot
  rw [hroot] at hn ⊢
  cases ccw with
  | free => rfl
  | heldDenial => exact False.elim (hn trivial)
  | heldCandidate => exact False.elim (hn trivial)

/-- Direct P1 discharges the one-hop latent token, regardless of whether
its comparison produces a denial or immediately uses the success port. -/
theorem direct_prelaunch_drop (R : RFrame) (q : Nat) (s : GhostRing2 R)
    (hs : Dom R (q+1) s) (g : Fin R.m) (hk : s.k g = q)
    (hi : (s.epoch g).cur = .idle) (hh : R.h = 1) :
    latentDebt2 R (q+1) (ghostStep2 R s (rootV R g)) + 1 = latentDebt2 R (q+1) s := by
  have hfree := right_free_at_cut R q s hs g hk (by rw [hi]; exact id)
  obtain ⟨c,cw,ccw,hroot⟩ := hs.1.coherent.roots g
  change s.cfg (rootV R g) = .root c cw ccw at hroot
  have hsend := hs.1.idleSend g hi
  rw [hroot] at hsend
  have hcw : cw = .toSend := Option.some.inj hsend
  subst cw
  obtain ⟨d,dw,dd,hrecv⟩ := hs.1.coherent.roots (next R g)
  change s.cfg (rootV R (next R g)) = .root d dw dd at hrecv
  rw [hrecv] at hfree
  have hdd : dd = .free := Option.some.inj hfree
  subst dd
  have hrn : rn R (rootV R g) = rootV R (next R g) :=
    rn_of_last R (rootV R g) (by change ¬ 1 < R.h; omega)
  have hraw : rawEpochs R (curView R s) (rootV R g) g =
      .delivered q (resolveInit c) (resolveResp d) := by
    rw [rawEpochs,if_pos rfl]
    change rowEpoch (s.k g) (s.epoch g).cur (s.cfg (rootV R g)) (s.cfg (rn R (rootV R g))) = _
    rw [hrn,hroot,hrecv,hk]
    rfl
  have hk0 : (curView R s).k g = q := hk
  have he0 : (curView R s).epoch g = .idle := hi
  have hbefore : (tokens2 R (q+1) s g).hops = 1 := by
    simp [tokens2,tokensOf',cohortToken,hk0,he0,LitGapState.hops,hh]
  have hafter : (tokens2 R (q+1) (ghostStep2 R s (rootV R g)) g).hops = 0 := by
    cases hf : fires R (physical2 R s) (rootV R g) g with
    | true =>
      have hp : q < (curView R (ghostStep2 R s (rootV R g))).k g := by
        change q < (ghostStep2 R s (rootV R g)).k g
        simp [ghostStep2_k,hf,hk]
      exact congrArg LitGapState.hops (tokensOf'_past R q _ g hp)
    | false =>
      have hk1 : (curView R (ghostStep2 R s (rootV R g))).k g = q := by
        change (ghostStep2 R s (rootV R g)).k g = q
        simp [ghostStep2_k,hf,hk]
      have he1 : (curView R (ghostStep2 R s (rootV R g))).epoch g =
          .delivered q (resolveInit c) (resolveResp d) := by
        change (epochStep2 R s (rootV R g) g).cur = _
        simp [epochStep2_cur,hf,hraw]
      simp [tokens2,tokensOf',cohortToken,hk1,he1,LitGapState.hops]
  apply sum_one_drop _ _ g
  · omega
  · intro j hj
    rw [other_gap_token_eq_lineage R (q+1) s hs.1 (rootV R g) j hj]

/-- The full latent-prelaunch branch for every h>0, with its actual
advancing physical edge and exactly one unit of total debt removed. -/
theorem prelaunch_drop_on_dom (R : RFrame) (q : Nat) (s : GhostRing2 R)
    (hs : Dom R (q+1) s) (g : Fin R.m) (hk : s.k g = q)
    (hi : (s.epoch g).cur = .idle) :
    latentDebt2 R (q+1) (ghostStep2 R s (rootV R g)) + 1 = latentDebt2 R (q+1) s := by
  by_cases hh : R.h = 1
  · exact direct_prelaunch_drop R q s hs g hk hi hh
  · exact prelaunch_lowers_latentDebt2 R q s hs.1 g hk hi (by have := R.hh; omega)

/-! Interior transport. -/

theorem no_owner_join_at_positive (R : RFrame) (s : GhostRing2 R) (e : Vtx R)
    (hp : 0 < e.2.val) : fires R (physical2 R s) e e.1 = false := by
  have hl : rootV R e.1 ≠ e := by
    intro h
    have hv := congrArg (fun v : Vtx R => v.2.val) h
    change 0 = e.2.val at hv
    omega
  have hr : rootV R e.1 ≠ rn R e := by
    by_cases he : e.2.val+1 < R.h
    · rw [rn_of_lt R e he]
      intro h
      have hv := congrArg (fun v : Vtx R => v.2.val) h
      change 0 = e.2.val+1 at hv
      omega
    · rw [rn_of_last R e he]
      intro h
      have hv := congrArg Prod.fst h
      exact next_ne_self R e.1 hv.symm
  simp [fires,incident,hl,hr]

/-- A pair-local move of a single token. The payload may change at the
same occupied slot, as it does at declaration/reply comparison. -/
theorem token_move_pair (R : RFrame) (s : GhostRing2 R) (e : Vtx R) (g : Fin R.m)
    (a b p p' : Fin R.h) (t u : Slot)
    (hl : e = (g,a)) (hr : rn R e = (g,b))
    (hp : p = a ∨ p = b) (hp' : p' = a ∨ p' = b)
    (hslots : ∀ x : Fin R.h, 0 < x.val →
      s.cfg (g,x) = .interior (if x = p then t else .empty))
    (hrow : row (s.cfg e) (s.cfg (rn R e)) =
      (.interior (if a = p' then u else .empty),.interior (if b = p' then u else .empty))) :
    ∀ x : Fin R.h, 0 < x.val → (ghostStep2 R s e).cfg (g,x) =
      .interior (if x = p' then u else .empty) := by
  intro x hx
  rw [cfg_step_pair,hrow]
  by_cases h0 : (g,x) = e
  · rw [if_pos h0]
    have hxa : x = a := congrArg Prod.snd (h0.trans hl)
    subst x; rfl
  · rw [if_neg h0]
    by_cases h1 : (g,x) = rn R e
    · rw [if_pos h1]
      have hxb : x = b := congrArg Prod.snd (h1.trans hr)
      subst x; rfl
    · rw [if_neg h1,hslots x hx]
      have hn : x ≠ p := by
        intro he; subst x
        rcases hp with hp | hp
        · exact h0 (by rw [hl,hp])
        · exact h1 (by rw [hr,hp])
      have hn' : x ≠ p' := by
        intro he; subst x
        rcases hp' with hp' | hp'
        · exact h0 (by rw [hl,hp'])
        · exact h1 (by rw [hr,hp'])
      rw [if_neg hn,if_neg hn']

/-- Interior F1 advances an outbound token by one position and lowers
the total accounting debt exactly once, for arbitrary ring and gap size. -/
theorem forwarding_lowers_latentDebt2 (R : RFrame) (q : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (g : Fin R.m) (c : Choice) (p : Fin R.h)
    (hp : 0 < p.val) (hpnext : p.val+1 < R.h) (hk : s.k g = q)
    (he : (s.epoch g).cur = .outbound q c)
    (hslots : ∀ x : Fin R.h, 0 < x.val →
      s.cfg (g,x) = .interior (if x = p then .decl c else .empty)) :
    latentDebt2 R (q+1) (ghostStep2 R s (g,p)) + 1 = latentDebt2 R (q+1) s := by
  let p' : Fin R.h := ⟨p.val+1,hpnext⟩
  have hp' : 0 < p'.val := by change 0 < p.val+1; omega
  have hne : p ≠ p' := by intro h; have hv := congrArg Fin.val h; change p.val = p.val+1 at hv; omega
  have hrn : rn R (g,p) = (g,p') := rn_of_lt R (g,p) hpnext
  have hl : s.cfg (g,p) = .interior (.decl c) := by simpa using hslots p hp
  have hr : s.cfg (rn R (g,p)) = .interior .empty := by
    rw [hrn,hslots p' hp',if_neg (Ne.symm hne)]
  have hrow : row (s.cfg (g,p)) (s.cfg (rn R (g,p))) =
      (.interior .empty,.interior (.decl c)) := by rw [hl,hr]; rfl
  have hpost := token_move_pair R s (g,p) g p p' p p' (.decl c) (.decl c)
    rfl hrn (Or.inl rfl) (Or.inr rfl) hslots (by simpa [hne] using hrow)
  have hpos0 := tokenPos2_of_unique R s g p hp (.decl c) (by intro h; cases h) hslots
  have hpos1 := tokenPos2_of_unique R (ghostStep2 R s (g,p)) g p' hp'
    (.decl c) (by intro h; cases h) hpost
  have hf := no_owner_join_at_positive R s (g,p) hp
  have hk0 : (curView R s).k g = q := hk
  have hk1 : (curView R (ghostStep2 R s (g,p))).k g = q := by
    change (ghostStep2 R s (g,p)).k g = q
    simp [ghostStep2_k,hf,hk]
  have he0 : (curView R s).epoch g = .outbound q c := he
  have he1 : (curView R (ghostStep2 R s (g,p))).epoch g = .outbound q c := by
    change (epochStep2 R s (g,p) g).cur = _
    rw [epochStep2_cur,hf]
    simp only [Bool.false_eq_true,if_false]
    rw [rawEpochs,if_pos rfl]
    change rowEpoch (s.k g) (s.epoch g).cur (s.cfg (g,p)) (s.cfg (rn R (g,p))) = _
    rw [he,hl,hr]
    rfl
  apply sum_one_drop _ _ g
  · simp [tokens2,tokensOf',cohortToken,hk0,hk1,he0,he1,hpos0,hpos1,
      ofPhase,p.isLt,p'.isLt,LitGapState.hops]
    change 2*R.h-1-(p.val+1)+1 = 2*R.h-1-p.val
    omega
  · intro j hj
    rw [other_gap_token_eq_lineage R (q+1) s hs (g,p) j hj]

/-- Interior B1 moves a reply one slot toward its owner and lowers the
total debt exactly once. -/
theorem backward_lowers_latentDebt2 (R : RFrame) (q : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (g : Fin R.m) (c d : Choice) (p : Fin R.h)
    (hp : 1 < p.val) (hk : s.k g = q) (he : (s.epoch g).cur = .returning q c d)
    (hslots : ∀ x : Fin R.h, 0 < x.val →
      s.cfg (g,x) = .interior (if x = p then .reply d else .empty)) :
    let p' : Fin R.h := ⟨p.val-1,by have := p.isLt; omega⟩
    latentDebt2 R (q+1) (ghostStep2 R s (g,p')) + 1 = latentDebt2 R (q+1) s := by
  dsimp only
  let p' : Fin R.h := ⟨p.val-1,by have := p.isLt; omega⟩
  change latentDebt2 R (q+1) (ghostStep2 R s (g,p')) + 1 = latentDebt2 R (q+1) s
  have hp' : 0 < p'.val := by change 0 < p.val-1; omega
  have hnext : p'.val+1 < R.h := by have := p.isLt; change p.val-1+1 < R.h; omega
  have hne : p' ≠ p := by intro h; have hv := congrArg Fin.val h; change p.val-1 = p.val at hv; omega
  have hrn : rn R (g,p') = (g,p) := by
    rw [rn_of_lt R (g,p') hnext]
    apply Prod.ext
    · rfl
    · apply Fin.ext
      change p.val-1+1 = p.val
      omega
  have hl : s.cfg (g,p') = .interior .empty := by rw [hslots p' hp',if_neg hne]
  have hr : s.cfg (rn R (g,p')) = .interior (.reply d) := by
    rw [hrn,hslots p (by omega),if_pos rfl]
  have hrow : row (s.cfg (g,p')) (s.cfg (rn R (g,p'))) =
      (.interior (.reply d),.interior .empty) := by rw [hl,hr]; rfl
  have hpost := token_move_pair R s (g,p') g p' p p p' (.reply d) (.reply d)
    rfl hrn (Or.inr rfl) (Or.inl rfl) hslots (by simpa [Ne.symm hne] using hrow)
  have hpos0 := tokenPos2_of_unique R s g p (by omega) (.reply d) (by intro h; cases h) hslots
  have hpos1 := tokenPos2_of_unique R (ghostStep2 R s (g,p')) g p' hp'
    (.reply d) (by intro h; cases h) hpost
  have hf := no_owner_join_at_positive R s (g,p') hp'
  have hk0 : (curView R s).k g = q := hk
  have hk1 : (curView R (ghostStep2 R s (g,p'))).k g = q := by
    change (ghostStep2 R s (g,p')).k g = q
    simp [ghostStep2_k,hf,hk]
  have he0 : (curView R s).epoch g = .returning q c d := he
  have he1 : (curView R (ghostStep2 R s (g,p'))).epoch g = .returning q c d := by
    change (epochStep2 R s (g,p') g).cur = _
    rw [epochStep2_cur,hf]
    simp only [Bool.false_eq_true,if_false]
    rw [rawEpochs,if_pos rfl]
    change rowEpoch (s.k g) (s.epoch g).cur (s.cfg (g,p')) (s.cfg (rn R (g,p'))) = _
    rw [he,hl,hr]
    rfl
  have hb0 : 1 ≤ p.val ∧ p.val ≤ R.h-1 := by have := p.isLt; omega
  have hb1 : 1 ≤ p'.val ∧ p'.val ≤ R.h-1 := by have := p'.isLt; omega
  apply sum_one_drop _ _ g
  · simp [tokens2,tokensOf',cohortToken,hk0,hk1,he0,he1,hpos0,hpos1,
      ofPhase,hb0.1,hb0.2,hb1.1,hb1.2,LitGapState.hops]
    change p.val-1+1 = p.val
    omega
  · intro j hj
    rw [other_gap_token_eq_lineage R (q+1) s hs (g,p') j hj]

/-- Replacing the payload in the final interior slot leaves that slot
as the unique occupied position, even if the right root JOINs. -/
theorem boundary_token_replace (R : RFrame) (s : GhostRing2 R) (g : Fin R.m)
    (p : Fin R.h) (_hp : 0 < p.val) (hlast : p.val+1 = R.h) (t u : Slot)
    (hslots : ∀ x : Fin R.h, 0 < x.val →
      s.cfg (g,x) = .interior (if x = p then t else .empty))
    (hrow : (row (s.cfg (g,p)) (s.cfg (rn R (g,p)))).1 = .interior u) :
    ∀ x : Fin R.h, 0 < x.val → (ghostStep2 R s (g,p)).cfg (g,x) =
      .interior (if x = p then u else .empty) := by
  intro x hx
  have hrn : rn R (g,p) = rootV R (next R g) :=
    rn_of_last R (g,p) (by change ¬ p.val+1 < R.h; omega)
  have hr : (g,x) ≠ rn R (g,p) := by
    rw [hrn]
    intro h
    have hv := congrArg (fun v : Vtx R => v.2.val) h
    change x.val = 0 at hv
    omega
  rw [cfg_step_pair]
  by_cases he : x = p
  · have hl : (g,x) = (g,p) := congrArg (g,·) he
    rw [if_pos hl,hrow,if_pos he]
    rfl
  · have hl : (g,x) ≠ (g,p) := fun h => he (congrArg Prod.snd h)
    rw [if_neg hl,if_neg hr,hslots x hx,if_neg he,if_neg he]

/-- K1/K2 comparison turns the last declaration into a reply in the same
slot. The entry cut proves that the receiver is free; no extra hop is charged. -/
theorem comparison_lowers_latentDebt2 (R : RFrame) (q : Nat) (s : GhostRing2 R)
    (hs : Dom R (q+1) s) (g : Fin R.m) (c : Choice) (p : Fin R.h)
    (hp : 0 < p.val) (hlast : p.val+1 = R.h) (hk : s.k g = q)
    (he : (s.epoch g).cur = .outbound q c)
    (hslots : ∀ x : Fin R.h, 0 < x.val →
      s.cfg (g,x) = .interior (if x = p then .decl c else .empty)) :
    latentDebt2 R (q+1) (ghostStep2 R s (g,p)) + 1 = latentDebt2 R (q+1) s := by
  have hfree := right_free_at_cut R q s hs g hk (by rw [he]; exact id)
  obtain ⟨d,dw,dd,hrecv⟩ := hs.1.coherent.roots (next R g)
  change s.cfg (rootV R (next R g)) = .root d dw dd at hrecv
  rw [hrecv] at hfree
  have hdd : dd = .free := Option.some.inj hfree
  subst dd
  have hrn : rn R (g,p) = rootV R (next R g) :=
    rn_of_last R (g,p) (by change ¬ p.val+1 < R.h; omega)
  have hl : s.cfg (g,p) = .interior (.decl c) := by simpa using hslots p hp
  have hr : s.cfg (rn R (g,p)) = .root d dw .free := by rw [hrn]; exact hrecv
  have hrow : (row (s.cfg (g,p)) (s.cfg (rn R (g,p)))).1 = .interior (.reply (resolveResp d)) := by
    rw [hl,hr]; rfl
  have hpost := boundary_token_replace R s g p hp hlast (.decl c) (.reply (resolveResp d)) hslots hrow
  have hpos0 := tokenPos2_of_unique R s g p hp (.decl c) (by intro h; cases h) hslots
  have hpos1 := tokenPos2_of_unique R (ghostStep2 R s (g,p)) g p hp
    (.reply (resolveResp d)) (by intro h; cases h) hpost
  have hf := no_owner_join_at_positive R s (g,p) hp
  have hk0 : (curView R s).k g = q := hk
  have hk1 : (curView R (ghostStep2 R s (g,p))).k g = q := by
    change (ghostStep2 R s (g,p)).k g = q
    simp [ghostStep2_k,hf,hk]
  have he0 : (curView R s).epoch g = .outbound q c := he
  have he1 : (curView R (ghostStep2 R s (g,p))).epoch g = .returning q c (resolveResp d) := by
    change (epochStep2 R s (g,p) g).cur = _
    rw [epochStep2_cur,hf]
    simp only [Bool.false_eq_true,if_false]
    rw [rawEpochs,if_pos rfl]
    change rowEpoch (s.k g) (s.epoch g).cur (s.cfg (g,p)) (s.cfg (rn R (g,p))) = _
    rw [he,hl,hr]
    rfl
  have hb : 1 ≤ p.val ∧ p.val ≤ R.h-1 := by omega
  apply sum_one_drop _ _ g
  · simp [tokens2,tokensOf',cohortToken,hk0,hk1,he0,he1,hpos0,hpos1,
      ofPhase,p.isLt,hb.1,hb.2,LitGapState.hops]
    omega
  · intro j hj
    rw [other_gap_token_eq_lineage R (q+1) s hs.1 (g,p) j hj]

/-- A delivered raw current result discharges its accounting token both
with and without the owner's post-row JOIN. -/
theorem token_zero_of_raw_delivered (R : RFrame) (q : Nat) (s : GhostRing2 R)
    (e : Vtx R) (g : Fin R.m) (c d : Choice) (hk : s.k g = q)
    (hr : rawEpochs R (curView R s) e g = .delivered q c d) :
    (tokens2 R (q+1) (ghostStep2 R s e) g).hops = 0 := by
  cases hf : fires R (physical2 R s) e g with
  | true =>
    have hp : q < (curView R (ghostStep2 R s e)).k g := by
      change q < (ghostStep2 R s e).k g
      simp [ghostStep2_k,hf,hk]
    exact congrArg LitGapState.hops (tokensOf'_past R q _ g hp)
  | false =>
    have hk1 : (curView R (ghostStep2 R s e)).k g = q := by
      change (ghostStep2 R s e).k g = q
      simp [ghostStep2_k,hf,hk]
    have he1 : (curView R (ghostStep2 R s e)).epoch g = .delivered q c d := by
      change (epochStep2 R s e g).cur = _
      simp [epochStep2_cur,hf,hr]
    simp [tokens2,tokensOf',cohortToken,hk1,he1,LitGapState.hops]

/-- V1 consumes a reply in slot 1. Its selected token disappears whether
the owner retains its receipt or JOINs immediately; all other tokens stutter. -/
theorem delivery_lowers_latentDebt2 (R : RFrame) (q : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (g : Fin R.m) (c d : Choice) (p : Fin R.h)
    (hp : p.val = 1) (hk : s.k g = q) (he : (s.epoch g).cur = .returning q c d)
    (hslots : ∀ x : Fin R.h, 0 < x.val →
      s.cfg (g,x) = .interior (if x = p then .reply d else .empty)) :
    latentDebt2 R (q+1) (ghostStep2 R s (rootV R g)) + 1 = latentDebt2 R (q+1) s := by
  have hh : 1 < R.h := by have := p.isLt; omega
  have hp0 : 0 < p.val := by omega
  obtain ⟨x,cw,ccw,hroot⟩ := hs.coherent.roots g
  change s.cfg (rootV R g) = .root x cw ccw at hroot
  have hw := (hs.waiting g).mpr (by rw [he]; trivial)
  rw [hroot] at hw
  have hcw : cw = .waiting := Option.some.inj hw
  subst cw
  have hrn : rn R (rootV R g) = (g,p) := by
    rw [rn_root_first R g hh]
    exact congrArg (g,·) (Fin.ext hp.symm)
  have hright : s.cfg (rn R (rootV R g)) = .interior (.reply d) := by
    rw [hrn,hslots p hp0,if_pos rfl]
  have hraw : rawEpochs R (curView R s) (rootV R g) g = .delivered q c d := by
    rw [rawEpochs,if_pos rfl]
    change rowEpoch (s.k g) (s.epoch g).cur (s.cfg (rootV R g)) (s.cfg (rn R (rootV R g))) = _
    rw [he,hroot,hright]
    rfl
  have hafter := token_zero_of_raw_delivered R q s (rootV R g) g c d hk hraw
  have hpos := tokenPos2_of_unique R s g p hp0 (.reply d) (by intro h; cases h) hslots
  have hk0 : (curView R s).k g = q := hk
  have he0 : (curView R s).epoch g = .returning q c d := he
  have hbefore : (tokens2 R (q+1) s g).hops = 1 := by
    have hbound : 1 ≤ R.h-1 := by omega
    simp [tokens2,tokensOf',cohortToken,hk0,he0,hpos,ofPhase,hp,hbound,LitGapState.hops]
  apply sum_one_drop _ _ g
  · omega
  · intro j hj
    rw [other_gap_token_eq_lineage R (q+1) s hs (rootV R g) j hj]

/-- Positive debt exposes a genuine useful physical edge. The proof
selects a positive gap, uses the cut to identify its owner generation,
then uses slot 0, the declaration's position, or the reply's predecessor
position according to cur. Each branch proves exactly one total hop. -/
theorem advancing_edge_lowers_latentDebt2 (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Dom R r s) (hp : 0 < latentDebt2 R r s) :
    ∃ e : Vtx R, latentDebt2 R r (ghostStep2 R s e) + 1 = latentDebt2 R r s := by
  classical
  have hex : ∃ g, 0 < (tokens2 R r s g).hops := by
    apply Classical.byContradiction
    intro hn
    have hz : ∀ g, (tokens2 R r s g).hops = 0 := by
      intro g
      have hnot : ¬ 0 < (tokens2 R r s g).hops := fun h => hn ⟨g,h⟩
      omega
    have heq := ofFn_sum_eq (fun g => (tokens2 R r s g).hops) (fun _ => 0) hz
    rw [ofFn_sum_const] at heq
    change latentDebt2 R r s = R.m*0 at heq
    omega
  obtain ⟨g,hg⟩ := hex
  cases r with
  | zero => change 0 < 0 at hg; omega
  | succ q =>
    have hk : s.k g = q := by
      have hc : q ≤ s.k g := hs.2.1 g
      by_cases hgt : q < s.k g
      · have ht := tokensOf'_past R q (curView R s) g hgt
        change 0 < (tokensOf' R (q+1) (curView R s) g).hops at hg
        rw [ht] at hg
        change 0 < 0 at hg
        omega
      · omega
    have ht := hs.1.current g
    have hshape := current_token_shape R s hs.1 g
    cases he : (s.epoch g).cur with
    | idle => exact ⟨rootV R g,prelaunch_drop_on_dom R q s hs g hk he⟩
    | outbound t c =>
      have hq : t = q := by simpa only [he,CurrentTag,hk] using ht
      subst t
      rw [he] at hshape
      obtain ⟨p,hp0,hslots⟩ := hshape
      change ∀ x : Fin R.h, 0 < x.val → s.cfg (g,x) = .interior (if x = p then .decl c else .empty) at hslots
      by_cases hnext : p.val+1 < R.h
      · exact ⟨(g,p),forwarding_lowers_latentDebt2 R q s hs.1 g c p hp0 hnext hk he hslots⟩
      · have hlast : p.val+1 = R.h := by have := p.isLt; omega
        exact ⟨(g,p),comparison_lowers_latentDebt2 R q s hs g c p hp0 hlast hk he hslots⟩
    | returning t c d =>
      have hq : t = q := by simpa only [he,CurrentTag,hk] using ht
      subst t
      rw [he] at hshape
      obtain ⟨p,hp0,hslots⟩ := hshape
      change ∀ x : Fin R.h, 0 < x.val → s.cfg (g,x) = .interior (if x = p then .reply d else .empty) at hslots
      by_cases hp1 : p.val = 1
      · exact ⟨rootV R g,delivery_lowers_latentDebt2 R q s hs.1 g c d p hp1 hk he hslots⟩
      · have hp2 : 1 < p.val := by omega
        exact ⟨(g,⟨p.val-1,by have := p.isLt; omega⟩),
          backward_lowers_latentDebt2 R q s hs.1 g c d p hp2 hk he hslots⟩
    | delivered t c d =>
      have hq : t = q := by simpa only [he,CurrentTag,hk] using ht
      have hk0 : (curView R s).k g = q := hk
      have he0 : (curView R s).epoch g = .delivered q c d := by rw [← hq]; exact he
      simp [tokens2,tokensOf',cohortToken,hk0,he0,LitGapState.hops] at hg

/-- If the selected left endpoint and every interior right endpoint are
unchanged by the pair row, the selected token stutters. A right root may
still resolve its choice or JOIN. -/
theorem selected_token_stutters (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (e : Vtx R)
    (hl : (row (s.cfg e) (s.cfg (rn R e))).1 = s.cfg e)
    (hr : 0 < (rn R e).2.val → (row (s.cfg e) (s.cfg (rn R e))).2 = s.cfg (rn R e))
    (he : rawEpochs R (curView R s) e e.1 = (s.epoch e.1).cur) :
    tokens2 R r (ghostStep2 R s e) e.1 = tokens2 R r s e.1 := by
  have hf : fires R (physical2 R s) e e.1 = false := by
    by_cases hp : 0 < e.2.val
    · exact no_owner_join_at_positive R s e hp
    · have hz : e = rootV R e.1 := by
        apply Prod.ext
        · rfl
        · apply Fin.ext; change e.2.val = 0; omega
      have hn := hs.coherent.normalized e.1
      change joinReady (s.cfg (rootV R e.1)) = false at hn
      have hleft : rootV R e.1 = e := hz.symm
      simp only [fires,physical2,rawAt,if_pos hleft,hl]
      rw [hz,hn]
      exact Bool.and_false _
  have hslots : ∀ a : Fin R.h, 0 < a.val →
      (ghostStep2 R s e).cfg (e.1,a) = s.cfg (e.1,a) := by
    intro a ha
    obtain ⟨t,ht⟩ := interior_roles R _ hs.coherent e.1 a ha
    change s.cfg (e.1,a) = .interior t at ht
    rw [cfg_step_pair]
    by_cases h0 : (e.1,a) = e
    · rw [if_pos h0,hl,← h0,ht]; rfl
    · rw [if_neg h0]
      by_cases h1 : (e.1,a) = rn R e
      · have hp : 0 < (rn R e).2.val := by rw [← h1]; exact ha
        rw [if_pos h1,hr hp,← h1,ht]; rfl
      · rw [if_neg h1]
  have hp : tokenPos R (curView R (ghostStep2 R s e)) e.1 = tokenPos R (curView R s) e.1 := by
    have hp' : (fun a : Fin R.h => decide (0 < a.val) &&
        match (ghostStep2 R s e).cfg (e.1,a) with
        | .interior (.decl _) | .interior (.reply _) => true | _ => false) =
      (fun a : Fin R.h => decide (0 < a.val) &&
        match s.cfg (e.1,a) with
        | .interior (.decl _) | .interior (.reply _) => true | _ => false) := by
      funext a
      by_cases ha : 0 < a.val
      · rw [hslots a ha]
      · simp [ha]
    exact congrArg (fun p : Fin R.h → Bool =>
      (((List.finRange R.h).find? p).map Fin.val).getD 0) hp'
  have hk : (curView R (ghostStep2 R s e)).k e.1 = (curView R s).k e.1 := by
    change (ghostStep2 R s e).k e.1 = s.k e.1
    simp [ghostStep2_k,hf]
  have hep : (curView R (ghostStep2 R s e)).epoch e.1 = (curView R s).epoch e.1 := by
    change (epochStep2 R s e e.1).cur = (s.epoch e.1).cur
    simp [epochStep2_cur,hf,he]
  cases r with
  | zero => rfl
  | succ q =>
    change cohortToken R q (curView R (ghostStep2 R s e)) e.1 = cohortToken R q (curView R s) e.1
    simp only [cohortToken,hk,hep,hp]

/-- An outbound token stutters on every edge except the one starting
at its occupied position. -/
theorem outbound_wrong_edge (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (g : Fin R.m) (a p : Fin R.h) (q : Nat) (c : Choice)
    (hp : 0 < p.val) (hne : a ≠ p) (he : (s.epoch g).cur = .outbound q c)
    (hslots : ∀ x : Fin R.h, 0 < x.val →
      s.cfg (g,x) = .interior (if x = p then .decl c else .empty)) :
    tokens2 R r (ghostStep2 R s (g,a)) g = tokens2 R r s g := by
  have hrow : (row (s.cfg (g,a)) (s.cfg (rn R (g,a)))).1 = s.cfg (g,a) ∧
      (0 < (rn R (g,a)).2.val →
        (row (s.cfg (g,a)) (s.cfg (rn R (g,a)))).2 = s.cfg (rn R (g,a))) ∧
      rowEpoch (s.k g) (s.epoch g).cur (s.cfg (g,a)) (s.cfg (rn R (g,a))) = (s.epoch g).cur := by
    by_cases ha : 0 < a.val
    · have hl : s.cfg (g,a) = .interior .empty := by rw [hslots a ha,if_neg hne]
      by_cases hn : a.val+1 < R.h
      · let b : Fin R.h := ⟨a.val+1,hn⟩
        have hrn : rn R (g,a) = (g,b) := rn_of_lt R (g,a) hn
        have hb : 0 < b.val := by change 0 < a.val+1; omega
        rw [hl,hrn,hslots b hb]
        by_cases hbp : b = p <;> simp [hbp,row,rowEpoch]
      · have hrn : rn R (g,a) = rootV R (next R g) := rn_of_last R (g,a) hn
        obtain ⟨d,cw,ccw,hr⟩ := hs.coherent.roots (next R g)
        change s.cfg (rootV R (next R g)) = .root d cw ccw at hr
        rw [hl,hrn,hr]
        cases ccw <;> simp [row,rowEpoch]
    · have haz : (g,a) = rootV R g := by
        apply Prod.ext
        · rfl
        · apply Fin.ext; change a.val = 0; omega
      have hh : 1 < R.h := by have := p.isLt; omega
      obtain ⟨d,cw,ccw,hl⟩ := hs.coherent.roots g
      change s.cfg (rootV R g) = .root d cw ccw at hl
      have hw := (hs.waiting g).mpr (by rw [he]; trivial)
      rw [hl] at hw
      have hc : cw = .waiting := Option.some.inj hw
      subst cw
      rw [haz,rn_root_first R g hh,hl,hslots ⟨1,hh⟩ (Nat.zero_lt_succ 0)]
      by_cases hb : (⟨1,hh⟩ : Fin R.h) = p <;> simp [hb,row,rowEpoch]
  apply selected_token_stutters R r s hs (g,a) hrow.1 hrow.2.1
  exact (if_pos rfl).trans hrow.2.2

/-- A reply stutters unless the selected edge ends at its position. -/
theorem returning_wrong_edge (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (g : Fin R.m) (a p : Fin R.h) (q : Nat) (c d : Choice)
    (hp : 0 < p.val) (hne : a.val+1 ≠ p.val) (he : (s.epoch g).cur = .returning q c d)
    (hslots : ∀ x : Fin R.h, 0 < x.val →
      s.cfg (g,x) = .interior (if x = p then .reply d else .empty)) :
    tokens2 R r (ghostStep2 R s (g,a)) g = tokens2 R r s g := by
  have hrow : (row (s.cfg (g,a)) (s.cfg (rn R (g,a)))).1 = s.cfg (g,a) ∧
      (0 < (rn R (g,a)).2.val →
        (row (s.cfg (g,a)) (s.cfg (rn R (g,a)))).2 = s.cfg (rn R (g,a))) ∧
      rowEpoch (s.k g) (s.epoch g).cur (s.cfg (g,a)) (s.cfg (rn R (g,a))) = (s.epoch g).cur := by
    by_cases ha : 0 < a.val
    · by_cases hn : a.val+1 < R.h
      · let b : Fin R.h := ⟨a.val+1,hn⟩
        have hrn : rn R (g,a) = (g,b) := rn_of_lt R (g,a) hn
        have hb : 0 < b.val := by change 0 < a.val+1; omega
        have hbp : b ≠ p := fun h => hne (congrArg Fin.val h)
        rw [hrn,hslots a ha,hslots b hb,if_neg hbp]
        by_cases hap : a = p <;> simp [hap,row,rowEpoch]
      · have hrn : rn R (g,a) = rootV R (next R g) := rn_of_last R (g,a) hn
        obtain ⟨x,cw,ccw,hr⟩ := hs.coherent.roots (next R g)
        change s.cfg (rootV R (next R g)) = .root x cw ccw at hr
        rw [hrn,hr,hslots a ha]
        by_cases hap : a = p <;> cases ccw <;> simp [hap,row,rowEpoch]
    · have hav : a.val = 0 := by omega
      have haz : (g,a) = rootV R g := by
        apply Prod.ext
        · rfl
        · exact Fin.ext hav
      have hh : 1 < R.h := by have := p.isLt; omega
      obtain ⟨x,cw,ccw,hl⟩ := hs.coherent.roots g
      change s.cfg (rootV R g) = .root x cw ccw at hl
      have hw := (hs.waiting g).mpr (by rw [he]; trivial)
      rw [hl] at hw
      have hc : cw = .waiting := Option.some.inj hw
      subst cw
      have hb : (⟨1,hh⟩ : Fin R.h) ≠ p := by
        intro h
        have hv := congrArg Fin.val h
        apply hne
        simpa [hav] using hv
      rw [haz,rn_root_first R g hh,hl,hslots ⟨1,hh⟩ (Nat.zero_lt_succ 0),if_neg hb]
      simp [row,rowEpoch]
  apply selected_token_stutters R r s hs (g,a) hrow.1 hrow.2.1
  exact (if_pos rfl).trans hrow.2.2

/-- Every physical edge weakly decreases the accounting debt on Dom.
The only live-token changes are F1, K1/K2, B1 and V1; all other live
rows stutter. Idle and delivered epochs use their separate reductions. -/
theorem latentDebt2_step_le (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Dom R r s) (e : Vtx R) :
    latentDebt2 R r (ghostStep2 R s e) ≤ latentDebt2 R r s := by
  rcases e with ⟨g,a⟩
  cases r with
  | zero => exact Nat.le_refl _
  | succ q =>
    by_cases hgt : q < s.k g
    · apply latentDebt2_step_le_of_scheduled_gap R (q+1) s (g,a) hs.2.1
      have hp : q < (curView R (ghostStep2 R s (g,a))).k g :=
        Nat.lt_of_lt_of_le hgt (Nat.le_add_right _ _)
      change (tokensOf' R (q+1) (curView R (ghostStep2 R s (g,a))) g).hops ≤
        (tokensOf' R (q+1) (curView R s) g).hops
      rw [tokensOf'_past R q _ g hp,tokensOf'_past R q _ g hgt]
      exact Nat.le_refl _
    · have hk : s.k g = q := by have hc : q ≤ s.k g := hs.2.1 g; omega
      have ht := hs.1.current g
      have hshape := current_token_shape R s hs.1 g
      cases he : (s.epoch g).cur with
      | idle =>
        apply latentDebt2_step_le_of_scheduled_gap R (q+1) s (g,a) hs.2.1
        exact idle_gap_token_debt_le R (q+1) s (g,a) g he
      | delivered t c d =>
        apply latentDebt2_step_le_of_scheduled_gap R (q+1) s (g,a) hs.2.1
        rw [delivered_selected_token_eq R (q+1) s hs.1 (g,a) t c d he]
        exact Nat.le_refl _
      | outbound t c =>
        have hq : t = q := by simpa only [he,CurrentTag,hk] using ht
        subst t
        rw [he] at hshape
        obtain ⟨p,hp,hslots⟩ := hshape
        change ∀ x : Fin R.h, 0 < x.val → s.cfg (g,x) = .interior (if x = p then .decl c else .empty) at hslots
        by_cases hap : a = p
        · subst a
          by_cases hn : p.val+1 < R.h
          · have hd := forwarding_lowers_latentDebt2 R q s hs.1 g c p hp hn hk he hslots
            omega
          · have hl : p.val+1 = R.h := by have := p.isLt; omega
            have hd := comparison_lowers_latentDebt2 R q s hs g c p hp hl hk he hslots
            omega
        · apply latentDebt2_step_le_of_scheduled_gap R (q+1) s (g,a) hs.2.1
          rw [outbound_wrong_edge R (q+1) s hs.1 g a p q c hp hap he hslots]
          exact Nat.le_refl _
      | returning t c d =>
        have hq : t = q := by simpa only [he,CurrentTag,hk] using ht
        subst t
        rw [he] at hshape
        obtain ⟨p,hp,hslots⟩ := hshape
        change ∀ x : Fin R.h, 0 < x.val → s.cfg (g,x) = .interior (if x = p then .reply d else .empty) at hslots
        by_cases hap : a.val+1 = p.val
        · by_cases hp1 : p.val = 1
          · have ha : (g,a) = rootV R g := by
              apply Prod.ext
              · rfl
              · apply Fin.ext; change a.val = 0; omega
            rw [ha]
            have hd := delivery_lowers_latentDebt2 R q s hs.1 g c d p hp1 hk he hslots
            omega
          · have hp2 : 1 < p.val := by omega
            have hd := backward_lowers_latentDebt2 R q s hs.1 g c d p hp2 hk he hslots
            have ha : a = (⟨p.val-1,by have := p.isLt; omega⟩ : Fin R.h) := by
              apply Fin.ext
              change a.val = p.val-1
              omega
            rw [ha]
            omega
        · apply latentDebt2_step_le_of_scheduled_gap R (q+1) s (g,a) hs.2.1
          rw [returning_wrong_edge R (q+1) s hs.1 g a p q c d hp hap he hslots]
          exact Nat.le_refl _

/-- The raw child sum now has no debt-law or simulation premises. -/
theorem genPipelined2_childSum (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Dom R r s) (hr : PeriodHIncidenceChoice.HasRace (word2 R r s)) :
    1 + (List.ofFn (fun e : Fin R.n => roundDebt2 R r (ghostStep2 R s (edgeVtx R e)))).sum ≤
      R.n * roundDebt2 R r s :=
  genPipelined2_childSum_of_debt_laws R r s hs.1 (dom_denial R r s hs) hr
    (latentDebt2_step_le R r s hs) (advancing_edge_lowers_latentDebt2 R r s hs)

/-! Local balance for the enlarged success predicate. -/

noncomputable def successEdgeCount (R : RFrame) (r : Nat) (s : GhostRing2 R) : Nat := by
  classical
  exact (List.ofFn (fun e : Fin R.n =>
    if VirtualSuccess R r (ghostStep2 R s (edgeVtx R e)) then 1 else 0)).sum

noncomputable def failureEdgeCount (R : RFrame) (r : Nat) (s : GhostRing2 R) : Nat := by
  classical
  exact (List.ofFn (fun e : Fin R.n =>
    if RoundFailure R r (ghostStep2 R s (edgeVtx R e)) then 1 else 0)).sum

private theorem frame_n_gt_one (R : RFrame) : 1 < R.n := by
  have hm := R.hm
  have hx : R.m ≤ R.m * R.h := by simpa using Nat.mul_le_mul_left R.m R.hh
  change 1 < R.m * R.h
  omega

/-- The joined good/bad count theorem still applies to each fixed-base
word, with the actual pre-step generation mask. -/
theorem joined_localBalance (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (b : PeriodHIncidenceChoice.FrozenValue)
    (hb : PeriodHIncidenceChoice.BaseOrRace b (word2 R r s))
    (hr : PeriodHIncidenceChoice.HasRace (word2 R r s)) :
    joinedBadEdgeCount b (placement R) (genMask2 R r s) (word2 R r s) ≤
      joinedGoodEdgeCount (ring R) (placement R) (genMask2 R r s) (word2 R r s) :=
  joinedGoodEdgeCount_ge_joinedBadEdgeCount (ring R) R.hm (placement R)
    (frame_n_gt_one R) b _ _ hb hr

/-- Unconditional balance on the requested domain. If a Race root has
not joined, no edge can freeze the word. Otherwise all joined steps equal
bare incidence, whose general balance theorem handles fixed-base, mixed
and all-Race words. Enlarging success can only reduce failure and increase
success counts. No extra BaseOrRace premise is imposed on Dom. -/
theorem genPipelined2_localBalance (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Dom R r s) (hr : PeriodHIncidenceChoice.HasRace (word2 R r s)) :
    failureEdgeCount R r s ≤ successEdgeCount R r s := by
  classical
  by_cases hall : ∀ i, word2 R r s i = .race → genMask2 R r s i = true
  · let state : CandidateDrainState (ring R) :=
      ⟨word2 R r s,hr,fun i hi => hs.2.2 (current_candidate_success R r s ⟨i,hi⟩)⟩
    have hw : ∀ e : Fin R.n, word2 R r (ghostStep2 R s (edgeVtx R e)) =
        PeriodHIncidenceChoice.incidenceStep (placement R) state.configuration e := by
      intro e
      rw [wordOf2_step R r s _ hs.1,encode_edgeVtx]
      exact joinedIncidenceStep_eq_of_all_joined _ _ _ _ hall
    have hf : failureEdgeCount R r s ≤
        (List.ofFn (fun e : Fin R.n => failureWeight (candidateDrainStep (ring R) (placement R) state e))).sum := by
      apply ofFn_sum_le
      intro e
      by_cases hfail : RoundFailure R r (ghostStep2 R s (edgeVtx R e))
      · have hold : candidateDrainStep (ring R) (placement R) state e = .failure := by
          apply (candidateDrainStep_eq_failure_iff _ _ _ _).mpr
          constructor
          · intro g hg
            apply hfail.2
            apply current_candidate_success
            refine ⟨g,?_⟩
            change PeriodHIncidenceChoice.Candidate10 (ring R)
              (word2 R r (ghostStep2 R s (edgeVtx R e))) g
            rw [hw]
            exact hg
          · simpa only [hw] using hfail.1
        simp only [if_pos hfail,hold,failureWeight]
        exact Nat.le_refl _
      · simp only [if_neg hfail]
        exact Nat.zero_le _
    have hsucc :
        (List.ofFn (fun e : Fin R.n => successWeight (candidateDrainStep (ring R) (placement R) state e))).sum ≤
          successEdgeCount R r s := by
      apply ofFn_sum_le
      intro e
      by_cases hold : candidateDrainStep (ring R) (placement R) state e = .success
      · have hg := (candidateDrainStep_eq_success_iff _ _ _ _).mp hold
        have hnew : VirtualSuccess R r (ghostStep2 R s (edgeVtx R e)) := by
          apply current_candidate_success
          change ∃ g, PeriodHIncidenceChoice.Candidate10 (ring R)
            (word2 R r (ghostStep2 R s (edgeVtx R e))) g
          rw [hw]
          exact hg
        simp only [hold,successWeight,if_pos hnew]
        exact Nat.le_refl _
      · have hz : successWeight (candidateDrainStep (ring R) (placement R) state e) = 0 := by
          cases he : candidateDrainStep (ring R) (placement R) state e
          · rfl
          · exact False.elim (hold he)
          · rfl
        rw [hz]
        exact Nat.zero_le _
    exact Nat.le_trans hf (Nat.le_trans
      (candidateDrain_localBalance (ring R) R.hm (placement R) (frame_n_gt_one R) state) hsucc)
  · have hn : ∀ e : Fin R.n, ¬ RoundFailure R r (ghostStep2 R s (edgeVtx R e)) := by
      intro e hf
      apply hall
      have hfr := hf.1
      rw [wordOf2_step R r s _ hs.1] at hfr
      exact all_joined_of_frozen _ _ _ _ hfr
    have hz : failureEdgeCount R r s = 0 := by
      simp [failureEdgeCount,hn,ofFn_sum_const]
    rw [hz]
    exact Nat.zero_le _

/-! A general annotation clause of lineage closure. -/

theorem currentTag_rowEpoch (k : Nat) (E : GapEpoch) (a b : Agent)
    (ht : CurrentTag k E) : CurrentTag k (rowEpoch k E a b) := by
  cases a with
  | root c cw ccw =>
    cases b with
    | interior t => cases cw <;> cases t <;> cases E <;> simp_all [rowEpoch,CurrentTag]
    | root d dw dd => cases cw <;> cases dd <;> simp_all [rowEpoch,CurrentTag]
  | interior t =>
    cases b with
    | interior u => cases t <;> cases u <;> exact ht
    | root d dw dd => cases t <;> cases dd <;> cases E <;> simp_all [rowEpoch,CurrentTag]

/-- Current generation tags are preserved by every raw row, owner
transfer and right retirement, independently of Dom's stopping condition. -/
theorem currentTag_step (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) :
    CurrentTag ((ghostStep2 R s e).k g) ((ghostStep2 R s e).epoch g).cur := by
  change CurrentTag ((ghostStep2 R s e).k g) (epochStep2 R s e g).cur
  rw [epochStep2_cur,ghostStep2_k]
  cases hf : fires R (physical2 R s) e g with
  | true => trivial
  | false =>
    simp only [Bool.false_eq_true,if_false,Nat.add_zero]
    by_cases hg : g = e.1
    · rw [rawEpochs,if_pos hg]
      exact currentTag_rowEpoch _ _ _ _ (hs.current g)
    · rw [rawEpochs,if_neg hg]
      exact hs.current g

/-! The remaining closure obligation is explicit in the following
stopped-process reduction. It is not a field of Dom or an established
lineage2_step theorem. No invariant exit is labeled uniform failure. -/

theorem dom_step_or_success_of_lineage (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Dom R r s) (e : Vtx R) (hl : Lineage2 R (ghostStep2 R s e)) :
    Dom R r (ghostStep2 R s e) ∨ VirtualSuccess R r (ghostStep2 R s e) := by
  classical
  by_cases hv : VirtualSuccess R r (ghostStep2 R s e)
  · exact Or.inr hv
  · exact Or.inl ⟨hl,cohortEntered2_step R r s e hs.2.1,hv⟩

/-- Only nonterminal Dom states are active. Frozen states are handled
by the failure port when the process is initialized or stepped. -/
def Active (R : RFrame) (r : Nat) :=
  {s : GhostRing2 R // Dom R r s ∧ PeriodHIncidenceChoice.HasRace (word2 R r s)}

/-- Conditional construction: the explicit argument is the entire
unproved lineage closure law, separate from the state invariant. -/
noncomputable def stoppedStepOfClosure (R : RFrame) (r : Nat)
    (hclose : ∀ s, Dom R r s → ∀ e, Lineage2 R (ghostStep2 R s e))
    (s : Active R r) (e : Fin R.n) : StopNode (Active R r) := by
  classical
  let t := ghostStep2 R s.val (edgeVtx R e)
  exact if hv : VirtualSuccess R r t then .success
    else if hr : PeriodHIncidenceChoice.HasRace (word2 R r t) then
      .active ⟨t,⟨hclose s.val s.property.1 _,
        cohortEntered2_step R r s.val _ s.property.1.2.1,hv⟩,hr⟩
    else .failure

def stoppedPotential (R : RFrame) (r : Nat) : StopNode (Active R r) → Nat
  | .active s => R.n * roundDebt2 R r s.val
  | .success | .failure => 0

theorem stoppedStepOfClosure_success_iff (R : RFrame) (r : Nat)
    (hclose : ∀ s, Dom R r s → ∀ e, Lineage2 R (ghostStep2 R s e))
    (s : Active R r) (e : Fin R.n) :
    stoppedStepOfClosure R r hclose s e = .success ↔
      VirtualSuccess R r (ghostStep2 R s.val (edgeVtx R e)) := by
  classical
  unfold stoppedStepOfClosure
  dsimp only
  split <;> simp_all
  split <;> simp_all

theorem stoppedStepOfClosure_failure_iff (R : RFrame) (r : Nat)
    (hclose : ∀ s, Dom R r s → ∀ e, Lineage2 R (ghostStep2 R s e))
    (s : Active R r) (e : Fin R.n) :
    stoppedStepOfClosure R r hclose s e = .failure ↔
      RoundFailure R r (ghostStep2 R s.val (edgeVtx R e)) := by
  classical
  have hf : PeriodHIncidenceChoice.Frozen (word2 R r (ghostStep2 R s.val (edgeVtx R e))) ↔
      ¬ PeriodHIncidenceChoice.HasRace (word2 R r (ghostStep2 R s.val (edgeVtx R e))) := by
    simp only [PeriodHIncidenceChoice.Frozen,PeriodHIncidenceChoice.HasRace,not_exists]
  unfold stoppedStepOfClosure
  dsimp only
  split
  · simp_all [RoundFailure]
  · split <;> simp_all [RoundFailure]

/-- All Bellman arithmetic is discharged. Only physical lineage closure
is an explicit hypothesis; the two debt laws are proved above. -/
theorem genPipelined2_natBellmanSuperSolution_of_lineage2_step (R : RFrame) (r : Nat)
    (hclose : ∀ s, Dom R r s → ∀ e, Lineage2 R (ghostStep2 R s e)) :
    NatBellmanSuperSolution (stoppedStepOfClosure R r hclose) 1 (stoppedPotential R r) := by
  classical
  refine ⟨rfl,rfl,?_⟩
  intro s
  have hc := genPipelined2_childSum R r s.val s.property.1 s.property.2
  have hsum : (List.ofFn (fun e => stoppedPotential R r (stoppedStepOfClosure R r hclose s e))).sum ≤
      (List.ofFn (fun e : Fin R.n => R.n * roundDebt2 R r (ghostStep2 R s.val (edgeVtx R e)))).sum := by
    apply ofFn_sum_le
    intro e
    unfold stoppedStepOfClosure
    dsimp only
    split
    · exact Nat.zero_le _
    · split
      · exact Nat.le_refl _
      · exact Nat.zero_le _
  rw [ofFn_sum_mul_left] at hsum
  have hm := Nat.mul_le_mul_left R.n hc
  rw [Nat.mul_add,Nat.mul_one] at hm
  change 1 * R.n + _ ≤ R.n * (R.n * roundDebt2 R r s.val)
  rw [Nat.one_mul]
  omega

/-- The numerical cut budget is unconditional in closure and reachability. -/
theorem stoppedPotential_le_cut_budget (R : RFrame) (r : Nat) (s : Active R r) :
    stoppedPotential R r (.active s) ≤ 2 * R.n * R.m * R.h := by
  have h := potential2_le_cut_budget R r s.val
  have he : R.n * R.m * (2 * R.h) = 2 * R.n * R.m * R.h := by ac_rfl
  exact he ▸ h

/-- The uniform initial state is a nonterminal accounting-round-1 cut. -/
def startActive (R : RFrame) : Active R 1 :=
  ⟨ghostStart2 R,dom_start R,⟨⟨0,by have := R.hm; omega⟩,rfl⟩⟩

theorem stoppedPotential_start (R : RFrame) :
    stoppedPotential R 1 (.active (startActive R)) = 2 * R.n * R.m * R.h := by
  change R.n * roundDebt2 R 1 (ghostStart2 R) = _
  rw [potential2_start]
  ac_rfl

/-!
STALL REPORT (no counterexample claimed):

The general lineage2_step theorem is not declared. CurrentTag closure
is proved, but the full Lineage2.coherent, previous and receipt clauses
have not been assembled across boundary comparison, delivery and the
coupled owner/right JOIN update. In particular, debt progress does not
by itself prove prefixView/completed-prefix or previous-result closure.

Consequently dom_step_or_success and the unconditional
genPipelined2_natBellmanSuperSolution are not declared. The explicitly
named _of_lineage / _of_lineage2_step reductions expose that remaining
obligation as a hypothesis. Their hypotheses are not part of Dom, and
stoppedStepOfClosure never treats an invariant exit as a failure port.

The four requested debt/child-sum/balance headlines below are general
theorems on exactly the specified Dom, with no closure or simulation
hypothesis. All ring sizes and positive gap lengths are covered.
-/

#print axioms virtualSuccess_persists
#print axioms dom_denial
#print axioms dom_start
#print axioms predecessor_counterexample_stops
#print axioms prelaunch_first_slot_empty
#print axioms currentTag_step
#print axioms other_gap_token_eq_lineage
#print axioms prelaunch_drop_on_dom
#print axioms latentDebt2_step_le
#print axioms advancing_edge_lowers_latentDebt2
#print axioms genPipelined2_childSum
#print axioms genPipelined2_localBalance
#print axioms dom_step_or_success_of_lineage
#print axioms genPipelined2_natBellmanSuperSolution_of_lineage2_step
#print axioms stoppedStepOfClosure_success_iff
#print axioms stoppedStepOfClosure_failure_iff
#print axioms stoppedPotential_le_cut_budget
#print axioms stoppedPotential_start
end ShortGapTwoEpochLaws
