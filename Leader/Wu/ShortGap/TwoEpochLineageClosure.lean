import Leader.Wu.ShortGap.TwoEpochLaws

/-!
# Two-epoch clauses and closure

The success port uses the maximum generation present, independently of
the accounting round. The clause decomposition below preserves every
field of the existing Lineage2 predicate.
-/
namespace ShortGapLineage2Closure
open ShortGapLiteralGapRows ShortGapLiteralRingRows ShortGapOwnerRoundSlice
open ShortGapCurrentCohort ShortGapLineage ShortGapLineageRetained
open ShortGapDenialTransportLiteral ShortGapGenerationMask ShortGapTwoEpoch
open ShortGapJoinedIncidenceBalance FiniteUniformStoppingTree
set_option autoImplicit false

/-- Maximum of a finite generation vector, with zero for the empty vector. -/
def generationMax : {m : Nat} → (Fin m → Nat) → Nat
  | 0, _ => 0
  | _+1, k => max (k 0) (generationMax (fun i => k i.succ))

theorem le_generationMax {m : Nat} (k : Fin m → Nat) (i : Fin m) :
    k i ≤ generationMax k := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih (fun j => k j.succ) j) (Nat.le_max_right _ _)

theorem generationMax_mono {m : Nat} (k l : Fin m → Nat) (h : ∀ i, k i ≤ l i) :
    generationMax k ≤ generationMax l := by
  induction m with
  | zero => exact Nat.le_refl _
  | succ m ih =>
    have h0 := h 0
    have ht := ih (fun i => k i.succ) (fun i => l i.succ) (fun i => h i.succ)
    change max (k 0) _ ≤ max (l 0) _
    omega

/-- The stopping horizon includes every generation physically present. -/
def maxGen (R : RFrame) (s : GhostRing2 R) : Nat := generationMax s.k

theorem maxGen_step (R : RFrame) (s : GhostRing2 R) (e : Vtx R) :
    maxGen R s ≤ maxGen R (ghostStep2 R s e) :=
  generationMax_mono _ _ (fun _ => Nat.le_add_right _ _)

/-- The round argument selects accounting only; success observes every
candidate up to the maximum generation in the state. -/
def VirtualSuccess (R : RFrame) (_r : Nat) (s : GhostRing2 R) : Prop :=
  ∃ q, q ≤ maxGen R s ∧ VirtualCandidate2 R q s

def Dom (R : RFrame) (r : Nat) (s : GhostRing2 R) : Prop :=
  Lineage2 R s ∧ CohortEntered2 R r s ∧ ¬ VirtualSuccess R r s

/-- A candidate's first payload is recorded; histFuture therefore bounds
its round by that owner's generation and hence by maxGen. -/
theorem candidate_round_le_maxGen (R : RFrame) (s : GhostRing2 R)
    (hs : Lineage2 R s) (q : Nat) (hc : VirtualCandidate2 R q s) : q ≤ maxGen R s := by
  obtain ⟨g,hg⟩ := hc
  have hh : s.hist g q = some .out1 := by
    have h := hg.1
    change choiceToWord ((s.hist g q).getD .race) = .out1 at h
    cases he : s.hist g q with
    | none => simp [he,choiceToWord] at h
    | some c => cases c <;> simp_all [choiceToWord]
  have hq : q ≤ s.k g := by
    by_cases h : s.k g < q
    · have hn := hs.coherent.histFuture g q h
      change s.hist g q = none at hn
      rw [hn] at hh
      cases hh
    · omega
  exact Nat.le_trans hq (le_generationMax s.k g)

theorem virtualSuccess_iff_any_candidate (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) : VirtualSuccess R r s ↔ ∃ q, VirtualCandidate2 R q s :=
  ⟨fun ⟨q,_,h⟩ => ⟨q,h⟩,
    fun ⟨q,h⟩ => ⟨q,candidate_round_le_maxGen R s hs q h,h⟩⟩

theorem virtualSuccess_persists (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (e : Vtx R) (hs : VirtualSuccess R r s) : VirtualSuccess R r (ghostStep2 R s e) := by
  obtain ⟨q,hq,hc⟩ := hs
  exact ⟨q,Nat.le_trans hq (maxGen_step R s e),virtualCandidate2_persists R q s e hc⟩

/-- The corrected domain supplies the earlier accounting domain, so
the already verified debt and balance laws remain applicable. -/
theorem dom_accounting (R : RFrame) (r : Nat) (s : GhostRing2 R) (hs : Dom R r s) :
    ShortGapTwoEpochLaws.Dom R r s := by
  refine ⟨hs.1,hs.2.1,?_⟩
  rintro ⟨q,_,hc⟩
  exact hs.2.2 ⟨q,candidate_round_le_maxGen R s hs.1 q hc,hc⟩

theorem dom_start (R : RFrame) : Dom R 1 (ghostStart2 R) := by
  refine ⟨lineage2_start R,cohortEntered2_start R,?_⟩
  rintro ⟨q,_,hc⟩
  exact ShortGapTwoEpochLaws.no_virtualSuccess_start R q ⟨q,Nat.le_refl _,hc⟩

/-! Exact clause decomposition. Receipt values and completed-prefix
denials are retained explicitly; no derivation goal is inserted as a field. -/

abbrev view (R : RFrame) (s : GhostRing2 R) := prefixView R (combinedView R s)

/-- C0: root roles, normalized ports, and the fresh form of Race roots. -/
structure C0 (R : RFrame) (s : GhostRing2 R) : Prop where
  roots : ∀ i, ∃ c cw ccw, s.cfg (rootV R i) = .root c cw ccw
  normalized : ∀ i, joinReady (s.cfg (rootV R i)) = false
  raceReady : ∀ i, (s.cfg (rootV R i)).choice = some .race →
    s.cfg (rootV R i) = .root .race .toSend .free

/-- C1: full epoch shape, including unique token position, endpoint
generation ranges, and the payloads represented by that epoch. -/
def C1 (R : RFrame) (s : GhostRing2 R) : Prop := ∀ g, EpochShape R (view R s) g

/-- C2: owner ports, exact outgoing values, and current-epoch agreement. -/
structure C2 (R : RFrame) (s : GhostRing2 R) : Prop where
  waitingPrefix : ∀ g, (s.cfg (rootV R g)).cwPort = some .waiting ↔ Live ((view R s).epoch g)
  outgoing : ∀ g, CwHeld (s.cfg (rootV R g)).cwPort ↔ DeliveredAt ((view R s).epoch g) (s.k g)
  outgoingValue : ∀ g, DeliveredAt ((view R s).epoch g) (s.k g) →
    ∃ c d, s.hist g (s.k g) = some c ∧ s.hist (next R g) (s.k g) = some d ∧
      (s.cfg (rootV R g)).cwPort = some (resCw c d)
  idleSend : ∀ g, (s.epoch g).cur = .idle → (s.cfg (rootV R g)).cwPort = some .toSend
  waiting : ∀ g, (s.cfg (rootV R g)).cwPort = some .waiting ↔ Live (s.epoch g).cur

/-- C3: both historical and two-epoch right-port readings, with exact values. -/
structure C3 (R : RFrame) (s : GhostRing2 R) : Prop where
  incomingPrefix : ∀ g, CcwHeld (s.cfg (rootV R (next R g))).ccwPort ↔
    ComparedAt ((view R s).epoch g) (s.k (next R g))
  incomingValue : ∀ g, ComparedAt ((view R s).epoch g) (s.k (next R g)) →
    ∃ c d, s.hist g (s.k (next R g)) = some c ∧ s.hist (next R g) (s.k (next R g)) = some d ∧
      (s.cfg (rootV R (next R g))).ccwPort = some (resCcw c d)
  incoming : ∀ g, CcwHeld (s.cfg (rootV R (next R g))).ccwPort ↔
    CurrentResult (s.epoch g).cur (s.k (next R g)) ∨ PreviousResult (s.epoch g).prev (s.k (next R g))

/-- C4: exact history domain and non-Race recorded values. -/
structure C4 (R : RFrame) (s : GhostRing2 R) : Prop where
  values : ∀ i r c, s.hist i r = some c → c ≠ .race
  past : ∀ i r, r < s.k i → ∃ c, s.hist i r = some c
  now : ∀ i c cw ccw, s.cfg (rootV R i) = .root c cw ccw → s.hist i (s.k i) = resolvedOpt c
  future : ∀ i r, s.k i < r → s.hist i r = none

/-- C5 retains the original previous-result condition verbatim. A stale
previous result may belong to the right root's immediately prior round. -/
def C5 (R : RFrame) (s : GhostRing2 R) : Prop := ∀ g, PrevShape R s g

/-- C6 binds current epochs to their owner's generation. -/
def C6 (R : RFrame) (s : GhostRing2 R) : Prop := ∀ g, CurrentTag (s.k g) (s.epoch g).cur

/-- C7: completed payloads, strict-prefix denials, and both denials
required for every completed owner round. -/
structure C7 (R : RFrame) (s : GhostRing2 R) : Prop where
  payloads : ∀ g r, ComparedAt ((view R s).epoch g) r →
    ∃ c d, s.hist g r = some c ∧ s.hist (next R g) r = some d
  denials : ∀ g r, BeforeLatest ((view R s).epoch g) r → HistoricalDenial R (view R s) g r
  joined : ∀ i r, r < s.k i →
    DeliveredAt ((view R s).epoch i) r ∧ ComparedAt ((view R s).epoch (prev R i)) r ∧
    HistoricalDenial R (view R s) i r ∧ HistoricalDenial R (view R s) (prev R i) r

def Clauses (R : RFrame) (s : GhostRing2 R) : Prop :=
  C0 R s ∧ C1 R s ∧ C2 R s ∧ C3 R s ∧ C4 R s ∧ C5 R s ∧ C6 R s ∧ C7 R s

/-- Every original field occurs in the decomposition, in both directions. -/
theorem lineage2_iff_clauses (R : RFrame) (s : GhostRing2 R) : Lineage2 R s ↔ Clauses R s := by
  constructor
  · intro h
    exact ⟨⟨h.coherent.roots,h.coherent.normalized,h.coherent.raceReady⟩,h.coherent.shape,
      ⟨h.coherent.waiting,h.coherent.outgoing,h.coherent.outgoingValue,h.idleSend,h.waiting⟩,
      ⟨h.coherent.incoming,h.coherent.incomingValue,h.incoming⟩,
      ⟨h.coherent.histValues,h.coherent.histPast,h.coherent.histNow,h.coherent.histFuture⟩,
      h.previous,h.current,⟨h.coherent.prefixPayloads,h.coherent.prefixDenials,h.coherent.joinedDenials⟩⟩
  · rintro ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
    exact ⟨⟨h0.roots,h0.normalized,h4.values,h4.past,h4.now,h4.future,h0.raceReady,h1,
      h2.waitingPrefix,h2.outgoing,h3.incomingPrefix,h7.payloads,h7.denials,h7.joined,
      h2.outgoingValue,h3.incomingValue⟩,h5,h6,h2.idleSend,h2.waiting,h3.incoming⟩

theorem C6_step (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s) (e : Vtx R) :
    C6 R (ghostStep2 R s e) := ShortGapTwoEpochLaws.currentTag_step R s hs e

/-! Root and history clauses use an endpoint-local fact: every incident
root resolves to a non-Race raw choice, preserving an already frozen one.
The post-row JOIN then either keeps it or resets it to the fresh form. -/

private theorem resolveInit_fixed (c : Choice) (hc : c ≠ .race) : resolveInit c = c := by
  cases c <;> simp_all [resolveInit]

private theorem resolveResp_fixed (c : Choice) (hc : c ≠ .race) : resolveResp c = c := by
  cases c <;> simp_all [resolveResp]

private theorem left_root (c : Choice) (cw : CwPort) (ccw : CcwPort) (b : Agent) :
    ∃ d dw dd, (row (.root c cw ccw) b).1 = .root d dw dd ∧ (c ≠ .race → d = c) := by
  cases b with
  | interior t =>
    cases t <;> cases cw <;> simp only [row,reduceCtorEq,if_true,if_false]
    all_goals refine ⟨_,_,_,rfl,?_⟩
    all_goals first | exact fun _ => rfl | exact resolveInit_fixed c
  | root d dw dd =>
    cases cw <;> cases dd <;> simp only [row,reduceCtorEq,if_true,if_false]
    all_goals exact ⟨_,_,_,rfl,resolveInit_fixed c⟩

private theorem right_root (a : Agent) (c : Choice) (cw : CwPort) (ccw : CcwPort) :
    ∃ d dw dd, (row a (.root c cw ccw)).2 = .root d dw dd ∧ (c ≠ .race → d = c) := by
  cases a with
  | interior t =>
    cases t <;> cases ccw <;> simp only [row,reduceCtorEq,if_true,if_false]
    all_goals refine ⟨_,_,_,rfl,?_⟩
    all_goals first | exact fun _ => rfl | exact resolveResp_fixed c
  | root d dw dd =>
    cases dw <;> cases ccw <;> simp only [row,reduceCtorEq,if_true,if_false]
    all_goals refine ⟨_,_,_,rfl,?_⟩
    all_goals first | exact fun _ => rfl | exact resolveResp_fixed c

private theorem left_fresh_choice (a : Agent) :
    (row (.root .race .toSend .free) a).1.choice = some .out1 := by
  cases a with
  | root c cw ccw => cases ccw <;> simp [row,resolveInit,Agent.choice]
  | interior t => cases t <;> simp [row,resolveInit,Agent.choice]

private theorem right_fresh_choice (a : Agent) :
    (row a (.root .race .toSend .free)).2.choice = some .in0 := by
  cases a with
  | root c cw ccw => cases cw <;> simp [row,resolveResp,Agent.choice]
  | interior t => cases t <;> simp [row,resolveResp,Agent.choice]

/-- The raw endpoint has a resolved choice and agrees with every
previously recorded current choice. This covers all literal row kinds. -/
theorem raw_root_resolved (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (i : Fin R.m) (hi : incident R e (rootV R i)) :
    ∃ d cw ccw, rawAt R s.cfg e (rootV R i) = .root d cw ccw ∧ d ≠ .race ∧
      (s.hist i (s.k i) = none ∨ s.hist i (s.k i) = some d) := by
  obtain ⟨c,cw,ccw,hc⟩ := hs.coherent.roots i
  change s.cfg (rootV R i) = .root c cw ccw at hc
  have hh := hs.coherent.histNow i c cw ccw hc
  change s.hist i (s.k i) = resolvedOpt c at hh
  have hraw : ∃ d dw dd, rawAt R s.cfg e (rootV R i) = .root d dw dd ∧
      (c ≠ .race → d = c) ∧ (c = .race → d ≠ .race) := by
    by_cases ht : rootV R i = e
    · obtain ⟨d,dw,dd,hr,hd⟩ := left_root c cw ccw (s.cfg (rn R e))
      refine ⟨d,dw,dd,?_,hd,?_⟩
      · have hce : s.cfg e = .root c cw ccw := ht ▸ hc
        rw [rawAt,if_pos ht,hce,hr]
      · intro hcr
        have hf := hs.coherent.raceReady i (by change (s.cfg (rootV R i)).choice = _; rw [hc,hcr]; rfl)
        change s.cfg (rootV R i) = .root .race .toSend .free at hf
        have heq := hc.symm.trans hf
        cases heq
        have hx := left_fresh_choice (s.cfg (rn R e))
        rw [hr] at hx
        have hdv : d = .out1 := Option.some.inj hx
        rw [hdv]; intro h; cases h
    · have ht' : rootV R i = rn R e := hi.resolve_left ht
      obtain ⟨d,dw,dd,hr,hd⟩ := right_root (s.cfg e) c cw ccw
      refine ⟨d,dw,dd,?_,hd,?_⟩
      · have hce : s.cfg (rn R e) = .root c cw ccw := ht' ▸ hc
        rw [rawAt,if_neg ht,if_pos ht',hce,hr]
      · intro hcr
        have hf := hs.coherent.raceReady i (by change (s.cfg (rootV R i)).choice = _; rw [hc,hcr]; rfl)
        change s.cfg (rootV R i) = .root .race .toSend .free at hf
        have heq := hc.symm.trans hf
        cases heq
        have hx := right_fresh_choice (s.cfg e)
        rw [hr] at hx
        have hdv : d = .in0 := Option.some.inj hx
        rw [hdv]; intro h; cases h
  obtain ⟨d,dw,dd,hr,hd,hfresh⟩ := hraw
  refine ⟨d,dw,dd,hr,?_,?_⟩
  · by_cases hcr : c = .race
    · exact hfresh hcr
    · rw [hd hcr]; exact hcr
  · by_cases hcr : c = .race
    · exact Or.inl (by simpa [hcr,resolvedOpt] using hh)
    · right
      rw [hd hcr]
      cases c <;> simp_all [resolvedOpt]

/-- All roots remain roots, JOIN-normalized, and fresh whenever Race. -/
theorem C0_step (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s) (e : Vtx R) :
    C0 R (ghostStep2 R s e) := by
  have hp : ∀ i, (∃ c cw ccw, (ghostStep2 R s e).cfg (rootV R i) = .root c cw ccw) ∧
      joinReady ((ghostStep2 R s e).cfg (rootV R i)) = false ∧
      (((ghostStep2 R s e).cfg (rootV R i)).choice = some .race →
        (ghostStep2 R s e).cfg (rootV R i) = .root .race .toSend .free) := by
    intro i
    by_cases hi : incident R e (rootV R i)
    · obtain ⟨c,cw,ccw,hr,hc,_⟩ := raw_root_resolved R s hs e i hi
      have he : (ghostStep2 R s e).cfg (rootV R i) = ShortGapLiteralRingRows.joinA (.root c cw ccw) := by
        rw [ghostStep2_physical]
        simp only [ShortGapOwnerRoundSlice.ringStepU,if_pos hi,joinTick,hr]
      rw [he]
      cases c <;> cases cw <;> cases ccw <;>
        simp_all [ShortGapLiteralRingRows.joinA,joinReady,Agent.choice]
    · have he : (ghostStep2 R s e).cfg (rootV R i) = s.cfg (rootV R i) := by
        rw [ghostStep2_physical]
        exact if_neg hi
      rw [he]
      exact ⟨hs.coherent.roots i,hs.coherent.normalized i,hs.coherent.raceReady i⟩
  exact ⟨fun i => (hp i).1,fun i => (hp i).2.1,fun i => (hp i).2.2⟩

private theorem record_record (H : Nat → Option Choice) (k : Nat) (d : Choice) :
    record (record H k d) k d = record H k d := by
  funext r
  by_cases hr : r = k
  · subst r
    cases hh : H k <;> simp [record,hh]
  · simp [record,hr]

private theorem updateHistory_resolved (d : Choice) (cw : CwPort) (ccw : CcwPort)
    (hd : d ≠ .race) (k : Nat) (H : Nat → Option Choice) :
    updateHistory (.root d cw ccw) k H = record H k d := by
  cases d <;> cases cw <;> cases ccw <;>
    simp_all [updateHistory,observeHistory,tickHistory,record_record]

theorem history_step_record (R : RFrame) (s : GhostRing2 R) (e : Vtx R)
    (i : Fin R.m) (hi : incident R e (rootV R i)) (d : Choice) (cw : CwPort) (ccw : CcwPort)
    (hr : rawAt R s.cfg e (rootV R i) = .root d cw ccw) (hd : d ≠ .race) :
    (ghostStep2 R s e).hist i = record (s.hist i) (s.k i) d := by
  change (if incident R e (rootV R i) then updateHistory (rawAt R s.cfg e (rootV R i)) (s.k i) (s.hist i)
    else s.hist i) = _
  rw [if_pos hi,hr,updateHistory_resolved d cw ccw hd]

private theorem record_current (H : Nat → Option Choice) (k : Nat) (d : Choice)
    (hh : H k = none ∨ H k = some d) : record H k d k = some d := by
  rcases hh with hh | hh <;> simp [record,hh]

/-- Every history clause is preserved, including exact current and future
domains after each of the four possible endpoint JOIN combinations. -/
theorem C4_step (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s) (e : Vtx R) :
    C4 R (ghostStep2 R s e) := by
  have hh : ∀ i, (∀ r c, (ghostStep2 R s e).hist i r = some c → c ≠ .race) ∧
      (∀ r, r < (ghostStep2 R s e).k i → ∃ c, (ghostStep2 R s e).hist i r = some c) ∧
      (∀ c cw ccw, (ghostStep2 R s e).cfg (rootV R i) = .root c cw ccw →
        (ghostStep2 R s e).hist i ((ghostStep2 R s e).k i) = resolvedOpt c) ∧
      (∀ r, (ghostStep2 R s e).k i < r → (ghostStep2 R s e).hist i r = none) := by
    intro i
    by_cases hi : incident R e (rootV R i)
    · obtain ⟨d,cw,ccw,hraw,hd,hcur⟩ := raw_root_resolved R s hs e i hi
      have hhist := history_step_record R s e i hi d cw ccw hraw hd
      have hcfg : (ghostStep2 R s e).cfg (rootV R i) = ShortGapLiteralRingRows.joinA (.root d cw ccw) := by
        rw [ghostStep2_physical]
        simp only [ShortGapOwnerRoundSlice.ringStepU,if_pos hi,joinTick,hraw]
      have hk : (ghostStep2 R s e).k i = s.k i + if joinReady (.root d cw ccw) then 1 else 0 := by
        rw [ghostStep2_k]
        simp [fires,physical2,hi,hraw]
      rw [hhist,hcfg,hk]
      refine ⟨?_,?_,?_,?_⟩
      · intro r c hc
        unfold record at hc
        split at hc
        · cases hc; exact hd
        · exact hs.coherent.histValues i r c hc
      · intro r hr
        by_cases hlt : r < s.k i
        · obtain ⟨c,hc⟩ := hs.coherent.histPast i r hlt
          exact ⟨c,record_monotone _ _ _ _ _ hc⟩
        · have heq : r = s.k i := by split at hr <;> omega
          subst r
          exact ⟨d,record_current _ _ _ hcur⟩
      · intro c cwa ccwa hc
        have hn : record (s.hist i) (s.k i) d (s.k i+1) = none := by
          have hf := hs.coherent.histFuture i (s.k i+1) (Nat.lt_succ_self _)
          change s.hist i (s.k i+1) = none at hf
          simp [record,hf]
        have hz := record_current (s.hist i) (s.k i) d hcur
        cases cw <;> cases ccw <;>
          simp only [ShortGapLiteralRingRows.joinA,joinReady,Bool.false_eq_true,if_false,if_true,Nat.add_zero] at hc ⊢
        all_goals cases hc
        all_goals first | exact hn | (cases d <;> simp_all [resolvedOpt])
      · intro r hr
        have hlt : s.k i < r := by split at hr <;> omega
        have hf := hs.coherent.histFuture i r hlt
        change s.hist i r = none at hf
        simp [record,Nat.ne_of_gt hlt,hf]
    · have hf : fires R (physical2 R s) e i = false := by simp [fires,hi]
      have hhist : (ghostStep2 R s e).hist i = s.hist i := by
        change (if incident R e (rootV R i) then _ else _) = _
        exact if_neg hi
      have hcfg : (ghostStep2 R s e).cfg (rootV R i) = s.cfg (rootV R i) := by
        rw [ghostStep2_physical]; exact if_neg hi
      rw [hhist,hcfg,ghostStep2_k,hf]
      simp only [Bool.false_eq_true,if_false,Nat.add_zero]
      exact ⟨hs.coherent.histValues i,hs.coherent.histPast i,hs.coherent.histNow i,hs.coherent.histFuture i⟩
  exact ⟨fun i => (hh i).1,fun i => (hh i).2.1,fun i => (hh i).2.2.1,fun i => (hh i).2.2.2⟩

/-- A waiting owner has the physical root form needed for the V1/L2 rows. -/
theorem waiting_root (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (hl : Live (s.epoch g).cur) :
    ∃ c ccw, s.cfg (rootV R g) = .root c .waiting ccw := by
  obtain ⟨c,cw,ccw,hc⟩ := hs.coherent.roots g
  change s.cfg (rootV R g) = .root c cw ccw at hc
  have hw := (hs.waiting g).mpr hl
  rw [hc] at hw
  have he : cw = .waiting := Option.some.inj hw
  exact ⟨c,ccw,he ▸ hc⟩

/-- Every owner JOIN transfers a genuinely delivered raw epoch. L1 and
outbound L2/L3 cannot JOIN; V1 and direct P1 are the delivery producers.
An owner JOIN caused by another gap uses its retained current delivery. -/
theorem owner_join_raw_delivered (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (hf : fires R (physical2 R s) e g = true) :
    ∃ q c d, rawEpochs R (curView R s) e g = .delivered q c d := by
  by_cases hg : g ≠ e.1
  · obtain ⟨c,d,he⟩ := ShortGapTwoEpochLaws.other_join_current_delivered R s hs e g hg hf
    exact ⟨s.k g,c,d,by simp [rawEpochs,hg,he,curView]⟩
  · have hge : g = e.1 := Classical.not_not.mp hg
    have hp : e.2.val = 0 := by
      by_cases hp : 0 < e.2.val
      · have hn := ShortGapTwoEpochLaws.no_owner_join_at_positive R s e hp
        rw [← hge,hf] at hn
        cases hn
      · omega
    have he : e = rootV R g := by
      apply Prod.ext
      · exact hge.symm
      · exact Fin.ext hp
    rw [he] at hf ⊢
    have hshape := current_token_shape R s hs g
    cases hc : (s.epoch g).cur with
    | delivered q c d =>
      exact ⟨q,c,d,ShortGapTwoEpochLaws.delivered_raw_epoch R s hs (rootV R g) q c d hc⟩
    | idle =>
      obtain ⟨c,cw,ccw,hroot⟩ := hs.coherent.roots g
      change s.cfg (rootV R g) = .root c cw ccw at hroot
      have hw := hs.idleSend g hc
      rw [hroot] at hw
      have hcw : cw = .toSend := Option.some.inj hw
      subst cw
      by_cases hh : 1 < R.h
      · have hn := ShortGapTwoEpochLaws.prelaunch_no_joins R s hs g c ccw hroot hh g
        rw [hf] at hn; cases hn
      · have hh1 : R.h = 1 := by have := R.hh; omega
        have hrn : rn R (rootV R g) = rootV R (next R g) := rn_of_last R _ (by change ¬0+1<R.h; omega)
        obtain ⟨d,dw,dd,hr⟩ := hs.coherent.roots (next R g)
        change s.cfg (rootV R (next R g)) = .root d dw dd at hr
        cases dd with
        | free =>
          refine ⟨s.k g,resolveInit c,resolveResp d,?_⟩
          rw [rawEpochs,if_pos rfl]
          change rowEpoch (s.k g) (s.epoch g).cur (s.cfg (rootV R g)) (s.cfg (rn R (rootV R g))) = _
          rw [hroot,hrn,hr]; rfl
        | heldDenial => simp [fires,physical2,rawAt,hroot,hrn,hr,row,joinReady] at hf
        | heldCandidate => simp [fires,physical2,rawAt,hroot,hrn,hr,row,joinReady] at hf
    | outbound q c =>
      obtain ⟨x,ccw,hroot⟩ := waiting_root R s hs g (by rw [hc]; trivial)
      rw [hc] at hshape
      obtain ⟨p,hp,hslots⟩ := hshape
      have hh : 1 < R.h := by have := p.isLt; omega
      have hrn := ShortGapTwoEpochLaws.rn_root_first R g hh
      have hslot := hslots ⟨1,hh⟩ (Nat.zero_lt_succ 0)
      change s.cfg (g,⟨1,hh⟩) = _ at hslot
      by_cases hp1 : (⟨1,hh⟩ : Fin R.h) = p
      · rw [if_pos hp1] at hslot
        simp [fires,physical2,rawAt,hroot,hrn,hslot,row,joinReady] at hf
      · rw [if_neg hp1] at hslot
        simp [fires,physical2,rawAt,hroot,hrn,hslot,row,joinReady] at hf
    | returning q c d =>
      obtain ⟨x,ccw,hroot⟩ := waiting_root R s hs g (by rw [hc]; trivial)
      rw [hc] at hshape
      obtain ⟨p,hp,hslots⟩ := hshape
      have hh : 1 < R.h := by have := p.isLt; omega
      have hrn := ShortGapTwoEpochLaws.rn_root_first R g hh
      have hslot := hslots ⟨1,hh⟩ (Nat.zero_lt_succ 0)
      change s.cfg (g,⟨1,hh⟩) = _ at hslot
      by_cases hp1 : (⟨1,hh⟩ : Fin R.h) = p
      · rw [if_pos hp1] at hslot
        refine ⟨q,c,d,?_⟩
        rw [rawEpochs,if_pos rfl]
        change rowEpoch (s.k g) (s.epoch g).cur (s.cfg (rootV R g)) (s.cfg (rn R (rootV R g))) = _
        rw [hc,hroot,hrn,hslot]; rfl
      · rw [if_neg hp1] at hslot
        simp [fires,physical2,rawAt,hroot,hrn,hslot,row,joinReady] at hf

/-- Reading a resolved raw root at its departing generation gives the
actual post-step history record, also when JOIN erases that choice. -/
theorem raw_choice_recorded (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (i : Fin R.m) (hi : incident R e (rootV R i)) (c : Choice)
    (hc : (rawAt R s.cfg e (rootV R i)).choice = some c) :
    (ghostStep2 R s e).hist i (s.k i) = some c := by
  obtain ⟨d,cw,ccw,hr,hd,hh⟩ := raw_root_resolved R s hs e i hi
  rw [hr] at hc
  have hdc : d = c := Option.some.inj hc
  rw [history_step_record R s e i hi d cw ccw hr hd,record_current _ _ _ hh,hdc]

private theorem rowEpoch_delivery_origin (k : Nat) (E : GapEpoch) (a b : Agent)
    (q : Nat) (c d : Choice) (h : rowEpoch k E a b = .delivered q c d) :
    E = .delivered q c d ∨ E = .returning q c d ∨
      ∃ x X y Y, a = .root x .toSend X ∧ b = .root y Y .free ∧
        q = k ∧ c = resolveInit x ∧ d = resolveResp y := by
  cases a with
  | interior t =>
    cases b with
    | interior u => cases t <;> cases u <;> exact Or.inl h
    | root y Y Z =>
      cases t <;> cases Z <;> cases E <;> simp only [rowEpoch] at h
      all_goals first | (exact Or.inl h) | (cases h <;> exact Or.inl rfl)
  | root x X Z =>
    cases b with
    | interior t =>
      cases X <;> cases t <;> cases E <;> simp only [rowEpoch] at h
      all_goals first | (exact Or.inl h) | (cases h <;> exact Or.inl rfl) |
        (cases h <;> exact Or.inr (Or.inl rfl))
    | root y Y W =>
      cases X <;> cases W <;> simp only [rowEpoch] at h
      all_goals first | (exact Or.inl h) |
        (cases h <;> exact Or.inr (Or.inr ⟨_,_,_,_,rfl,rfl,rfl,rfl,rfl⟩))

/-- A delivered raw epoch carries the two immutable history payloads.
The only new pair is direct P1; its guards force equal generations. -/
theorem raw_delivered_payloads (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) (q : Nat) (c d : Choice)
    (he : rawEpochs R (curView R s) e g = .delivered q c d) :
    (ghostStep2 R s e).hist g q = some c ∧ (ghostStep2 R s e).hist (next R g) q = some d := by
  have old : (s.epoch g).cur = .delivered q c d ∨ (s.epoch g).cur = .returning q c d →
      (ghostStep2 R s e).hist g q = some c ∧ (ghostStep2 R s e).hist (next R g) q = some d := by
    intro hc
    have ht := hs.coherent.shape g
    rcases hc with hc | hc
    all_goals simp only [EpochShape,prefixView,combinedView,hc] at ht
    all_goals exact ⟨history2_monotone R s e g q c ht.2.2.1,
      history2_monotone R s e (next R g) q d ht.2.2.2.1⟩
  by_cases hg : g = e.1
  · rw [rawEpochs,if_pos hg] at he
    rcases rowEpoch_delivery_origin _ _ _ _ q c d he with hc | hc | hnew
    · exact old (Or.inl hc)
    · exact old (Or.inr hc)
    · obtain ⟨x,X,y,Y,hl,hr,hq,hc,hd⟩ := hnew
      change s.cfg e = .root x .toSend X at hl
      change s.cfg (rn R e) = .root y Y .free at hr
      have hz : e.2.val = 0 := by
        by_cases hp : 0 < e.2.val
        · obtain ⟨t,ht⟩ := interior_roles R _ hs.coherent e.1 e.2 hp
          change s.cfg e = .interior t at ht
          rw [hl] at ht; cases ht
        · omega
      have hleft : e = rootV R g := by
        apply Prod.ext
        · exact hg.symm
        · exact Fin.ext hz
      have hlast : ¬ e.2.val+1 < R.h := by
        intro hp
        have hrn := rn_of_lt R e hp
        obtain ⟨t,ht⟩ := interior_roles R _ hs.coherent e.1 ⟨e.2.val+1,hp⟩ (Nat.zero_lt_succ _)
        change s.cfg (e.1,⟨e.2.val+1,hp⟩) = .interior t at ht
        rw [hrn,ht] at hr; cases hr
      have hright : rn R e = rootV R (next R g) := by rw [rn_of_last R e hlast,← hg]
      have hgen := direct_generations R (view R s) hs.coherent g
        (by change (s.cfg (rootV R g)).cwPort = _; rw [← hleft,hl]; rfl)
        (by change (s.cfg (rootV R (next R g))).ccwPort = _; rw [← hright,hr]; rfl)
      change s.k g = s.k (next R g) at hgen
      have hq' : q = s.k g := hq
      have hrawL : (rawAt R s.cfg e (rootV R g)).choice = some c := by
        rw [rawAt,if_pos hleft.symm,hl,hr,hc]
        rfl
      have hnr : rootV R (next R g) ≠ e := by
        rw [← hright]; exact rn_ne_self R e
      have hrawR : (rawAt R s.cfg e (rootV R (next R g))).choice = some d := by
        rw [rawAt,if_neg hnr,if_pos hright.symm,hl,hr,hd]
        rfl
      rw [hq']
      exact ⟨raw_choice_recorded R s hs e g (Or.inl hleft.symm) c hrawL,
        hgen ▸ raw_choice_recorded R s hs e (next R g) (Or.inr hright.symm) d hrawR⟩
  · have hc : (s.epoch g).cur = .delivered q c d := by simpa [rawEpochs,hg,curView] using he
    exact old (Or.inl hc)

/-- The archive clause is preserved for all four JOIN combinations.
Right JOIN clears it; owner JOIN transfers a delivered result; otherwise
comparison clears it or the previous record persists with unchanged counters. -/
theorem C5_step (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s) (e : Vtx R) :
    C5 R (ghostStep2 R s e) := by
  intro g
  cases hR : fires R (physical2 R s) e (next R g) with
  | true =>
    have hp : ((ghostStep2 R s e).epoch g).prev = .idle := by
      change (epochStep2 R s e g).prev = _
      simp [epochStep2,hR]
    simp only [PrevShape,hp]
  | false =>
    have hkR : (ghostStep2 R s e).k (next R g) = s.k (next R g) := by simp [ghostStep2_k,hR]
    cases hO : fires R (physical2 R s) e g with
    | true =>
      obtain ⟨q,c,d,he⟩ := owner_join_raw_delivered R s hs e g hO
      have ht : CurrentTag (s.k g) (rawEpochs R (curView R s) e g) := by
        by_cases hg : g = e.1
        · rw [rawEpochs,if_pos hg]
          exact ShortGapTwoEpochLaws.currentTag_rowEpoch _ _ _ _ (hs.current g)
        · rw [rawEpochs,if_neg hg]
          exact hs.current g
      have hq : q = s.k g := by simpa only [he,CurrentTag] using ht
      have hkO : (ghostStep2 R s e).k g = q+1 := by simp [ghostStep2_k,hO,hq]
      have hsupport := join_requires_neighbors_of_lineage R (view R s) hs.coherent e g hO
      have hskew := neighborSkew_of_lineage2 R s hs g
      change s.k g ≤ s.k (next R g) ∧ s.k g ≤ s.k (prev R g) at hsupport
      change s.k g ≤ s.k (next R g)+1 ∧ s.k (next R g) ≤ s.k g+1 at hskew
      have hbound : s.k (next R g) = q ∨ s.k (next R g) = q+1 := by omega
      have hp : ((ghostStep2 R s e).epoch g).prev = .delivered q c d := by
        change (epochStep2 R s e g).prev = _
        simp [epochStep2,hR,hO,he]
      rw [PrevShape,hp]
      exact ⟨hkO,hkR ▸ hbound,raw_delivered_payloads R s hs e g q c d he⟩
    | false =>
      have hkO : (ghostStep2 R s e).k g = s.k g := by simp [ghostStep2_k,hO]
      by_cases hc : g = e.1 ∧ compares (s.cfg e) (s.cfg (rn R e)) = true
      · have hp : ((ghostStep2 R s e).epoch g).prev = .idle := by
          change (epochStep2 R s e g).prev = _
          simp only [epochStep2,hR,hO,Bool.false_eq_true,if_false,if_pos hc]
        simp only [PrevShape,hp]
      · have hp : ((ghostStep2 R s e).epoch g).prev = (s.epoch g).prev := by
          change (epochStep2 R s e g).prev = _
          simp [epochStep2,hR,hO,hc]
        have hsP := hs.previous g
        cases he : (s.epoch g).prev with
        | idle => simp only [PrevShape,hp,he]
        | outbound q c => simp only [PrevShape,he] at hsP
        | returning q c d => simp only [PrevShape,he] at hsP
        | delivered q c d =>
          simp only [PrevShape,he] at hsP
          rw [PrevShape,hp,he,hkO,hkR]
          exact ⟨hsP.1,hsP.2.1,history2_monotone R s e g q c hsP.2.2.1,
            history2_monotone R s e (next R g) q d hsP.2.2.2⟩

/-- The archive contributes completed history but never a live owner
transaction or a delivery in the owner's current generation. -/
theorem view_owner_tests (R : RFrame) (s : GhostRing2 R) (h5 : C5 R s) (h6 : C6 R s)
    (g : Fin R.m) :
    (Live ((view R s).epoch g) ↔ Live (s.epoch g).cur) ∧
    (DeliveredAt ((view R s).epoch g) (s.k g) ↔ ∃ q c d, (s.epoch g).cur = .delivered q c d) := by
  have ht := h6 g
  cases hc : (s.epoch g).cur with
  | idle =>
    have hp := h5 g
    cases he : (s.epoch g).prev with
    | idle =>
      by_cases hz : s.k g = 0
      · simp [view,prefixView,combinedView,hc,he,hz,Live,DeliveredAt]
      · have hn : ¬ s.k g ≤ s.k g-1 := by omega
        simp [view,prefixView,combinedView,hc,he,hz,Live,DeliveredAt,hn]
    | outbound q c => simp only [PrevShape,he] at hp
    | returning q c d => simp only [PrevShape,he] at hp
    | delivered q c d =>
      simp only [PrevShape,he] at hp
      have hk : s.k g = q+1 := hp.1
      simp [view,prefixView,combinedView,hc,he,Live,DeliveredAt,hk]
  | outbound q c =>
    have hq : q = s.k g := by simpa [hc,CurrentTag] using ht
    simp [view,prefixView,combinedView,hc,Live,DeliveredAt,hq]
  | returning q c d =>
    have hq : q = s.k g := by simpa [hc,CurrentTag] using ht
    simp [view,prefixView,combinedView,hc,Live,DeliveredAt,hq]
  | delivered q c d =>
    have hq : q = s.k g := by simpa [hc,CurrentTag] using ht
    simp [view,prefixView,combinedView,hc,Live,DeliveredAt,hq]

/-- Exact owner-port encoding of the current transaction. -/
def epochCw : GapEpoch → CwPort
  | .idle => .toSend
  | .outbound _ _ | .returning _ _ _ => .waiting
  | .delivered _ c d => resCw c d

theorem owner_port_exact (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s) (g : Fin R.m) :
    (s.cfg (rootV R g)).cwPort = some (epochCw (s.epoch g).cur) := by
  cases he : (s.epoch g).cur with
  | idle => exact hs.idleSend g he
  | outbound q c => exact (hs.waiting g).mpr (by rw [he]; trivial)
  | returning q c d => exact (hs.waiting g).mpr (by rw [he]; trivial)
  | delivered q c d =>
    have hv := (view_owner_tests R s hs.previous hs.current g).2.mpr ⟨q,c,d,he⟩
    obtain ⟨x,y,hx,hy,hw⟩ := hs.coherent.outgoingValue g hv
    have ht := hs.current g
    have hq : q = s.k g := by simpa [he,CurrentTag] using ht
    have hshape := hs.coherent.shape g
    simp only [EpochShape,prefixView,combinedView,he] at hshape
    change s.hist g (s.k g) = some x at hx
    change s.hist (next R g) (s.k g) = some y at hy
    have hxc : x = c := Option.some.inj (hx.symm.trans (hq ▸ hshape.2.2.1))
    have hyd : y = d := Option.some.inj (hy.symm.trans (hq ▸ hshape.2.2.2.1))
    change (s.cfg (rootV R g)).cwPort = some (resCw x y) at hw
    simpa only [he,epochCw,hxc,hyd] using hw

/-- A live or delivered current payload is the owner's actual choice. -/
theorem owner_choice_of_current (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (q : Nat) (c : Choice)
    (he : (s.epoch g).cur = .outbound q c ∨
      ∃ d, (s.epoch g).cur = .returning q c d ∨ (s.epoch g).cur = .delivered q c d) :
    (s.cfg (rootV R g)).choice = some c := by
  obtain ⟨x,cw,ccw,hroot⟩ := hs.coherent.roots g
  change s.cfg (rootV R g) = .root x cw ccw at hroot
  have hhist : s.hist g q = some c ∧ q = s.k g := by
    have ht := hs.current g
    have hshape := hs.coherent.shape g
    rcases he with he | ⟨d,he | he⟩
    all_goals simp only [he,CurrentTag] at ht
    all_goals simp only [he,prefixView,combinedView,EpochShape] at hshape
    · exact ⟨hshape.2.2.1,ht⟩
    · exact ⟨hshape.2.2.1,ht⟩
    · exact ⟨hshape.2.2.1,ht⟩
  have hh := hs.coherent.histNow g x cw ccw hroot
  change s.hist g (s.k g) = resolvedOpt x at hh
  have hx : resolvedOpt x = some c := hh.symm.trans (hhist.2 ▸ hhist.1)
  rw [hroot]
  cases x <;> simp_all [resolvedOpt,Agent.choice]

private theorem epochCw_interior_row (k : Nat) (E : GapEpoch) (t : Slot) (b : Agent) :
    epochCw (rowEpoch k E (.interior t) b) = epochCw E := by
  cases b with
  | interior u => cases t <;> cases u <;> rfl
  | root c cw ccw => cases t <;> cases ccw <;> cases E <;> rfl

private theorem raw_owner_positive (R : RFrame) (s : GhostRing2 R) (e : Vtx R)
    (hp : 0 < e.2.val) : rawAt R s.cfg e (rootV R e.1) = s.cfg (rootV R e.1) := by
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
  simp [rawAt,hl,hr]

/-- The owner port agrees exactly with the raw current epoch before JOIN.
This checks L1, the clean L2/L3 cases, V1, P1/P2/P3, and interior activity. -/
theorem raw_owner_port_exact (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) :
    (rawAt R s.cfg e (rootV R g)).cwPort = some (epochCw (rawEpochs R (curView R s) e g)) := by
  by_cases hg : g = e.1
  · subst g
    by_cases hp : 0 < e.2.val
    · obtain ⟨t,ht⟩ := interior_roles R _ hs.coherent e.1 e.2 hp
      change s.cfg e = .interior t at ht
      rw [raw_owner_positive R s e hp,rawEpochs,if_pos rfl]
      change (s.cfg (rootV R e.1)).cwPort = some (epochCw (rowEpoch (s.k e.1) (s.epoch e.1).cur (s.cfg e) (s.cfg (rn R e))))
      rw [ht,epochCw_interior_row]
      exact owner_port_exact R s hs e.1
    · have he : e = rootV R e.1 := by
        apply Prod.ext
        · rfl
        · apply Fin.ext; change e.2.val = 0; omega
      generalize hg : e.1 = g at he ⊢
      rw [he,rawAt,if_pos rfl,rawEpochs,if_pos rfl]
      change (row (s.cfg (rootV R g)) (s.cfg (rn R (rootV R g)))).1.cwPort =
        some (epochCw (rowEpoch (s.k g) (s.epoch g).cur (s.cfg (rootV R g)) (s.cfg (rn R (rootV R g)))))
      obtain ⟨x,cw,ccw,hroot⟩ := hs.coherent.roots g
      change s.cfg (rootV R g) = .root x cw ccw at hroot
      have hport := owner_port_exact R s hs g
      rw [hroot] at hport
      have hcw : cw = epochCw (s.epoch g).cur := Option.some.inj hport
      subst cw
      have hshape := current_token_shape R s hs g
      cases hc : (s.epoch g).cur with
      | idle =>
        rw [hc] at hshape hroot
        by_cases hh : 1 < R.h
        · have ht := hshape ⟨1,hh⟩ (Nat.zero_lt_succ 0)
          change s.cfg (g,⟨1,hh⟩) = .interior .empty at ht
          rw [ShortGapTwoEpochLaws.rn_root_first R g hh,hroot,ht]
          rfl
        · have hrn : rn R (rootV R g) = rootV R (next R g) := rn_of_last R _ (by change ¬0+1<R.h; omega)
          obtain ⟨d,dw,dd,hr⟩ := hs.coherent.roots (next R g)
          change s.cfg (rootV R (next R g)) = .root d dw dd at hr
          rw [hrn,hroot,hr]
          cases dd <;> rfl
      | outbound q c =>
        rw [hc] at hshape hroot
        obtain ⟨p,hp,hslots⟩ := hshape
        have hh : 1 < R.h := by have := p.isLt; omega
        have ht := hslots ⟨1,hh⟩ (Nat.zero_lt_succ 0)
        change s.cfg (g,⟨1,hh⟩) = _ at ht
        rw [ShortGapTwoEpochLaws.rn_root_first R g hh,hroot,ht]
        split <;> rfl
      | returning q c d =>
        have hx := owner_choice_of_current R s hs g q c (Or.inr ⟨d,Or.inl hc⟩)
        rw [hroot] at hx
        have hxc : x = c := Option.some.inj hx
        subst x
        rw [hc] at hshape hroot
        obtain ⟨p,hp,hslots⟩ := hshape
        have hh : 1 < R.h := by have := p.isLt; omega
        have ht := hslots ⟨1,hh⟩ (Nat.zero_lt_succ 0)
        change s.cfg (g,⟨1,hh⟩) = _ at ht
        rw [ShortGapTwoEpochLaws.rn_root_first R g hh,hroot,ht]
        split <;> rfl
      | delivered q c d =>
        rw [hc] at hshape hroot
        by_cases hh : 1 < R.h
        · have ht := hshape ⟨1,hh⟩ (Nat.zero_lt_succ 0)
          change s.cfg (g,⟨1,hh⟩) = .interior .empty at ht
          rw [ShortGapTwoEpochLaws.rn_root_first R g hh,hroot,ht]
          cases c <;> cases d <;> rfl
        · have hrn : rn R (rootV R g) = rootV R (next R g) := rn_of_last R _ (by change ¬0+1<R.h; omega)
          obtain ⟨y,dw,dd,hr⟩ := hs.coherent.roots (next R g)
          change s.cfg (rootV R (next R g)) = .root y dw dd at hr
          rw [hrn,hroot,hr]
          cases c <;> cases d <;> cases dd <;> rfl
  · rw [ShortGapTwoEpochLaws.raw_cw_other R s hs e g hg,rawEpochs,if_neg hg]
    exact owner_port_exact R s hs g

private theorem joinA_eq_of_not_ready (a : Agent) (ha : joinReady a = false) :
    ShortGapLiteralRingRows.joinA a = a := by
  cases a with
  | interior t => rfl
  | root c cw ccw => cases cw <;> cases ccw <;> simp_all [joinReady,ShortGapLiteralRingRows.joinA]

/-- Without a root JOIN, the physical root equals its raw row output. -/
theorem root_cfg_no_join (R : RFrame) (s : GhostRing2 R) (e : Vtx R) (g : Fin R.m)
    (hf : fires R (physical2 R s) e g = false) :
    (ghostStep2 R s e).cfg (rootV R g) = rawAt R s.cfg e (rootV R g) := by
  by_cases hi : incident R e (rootV R g)
  · have hr : joinReady (rawAt R s.cfg e (rootV R g)) = false := by
      simpa [fires,physical2,hi] using hf
    rw [ghostStep2_physical]
    simp only [ShortGapOwnerRoundSlice.ringStepU,if_pos hi,joinTick,joinA_eq_of_not_ready _ hr]
  · have hl : rootV R g ≠ e := fun h => hi (Or.inl h)
    have hr : rootV R g ≠ rn R e := fun h => hi (Or.inr h)
    rw [ghostStep2_physical]
    simp [ShortGapOwnerRoundSlice.ringStepU,hi,rawAt,hl,hr]

/-- A firing root has the fresh physical form after JOIN. -/
theorem root_cfg_join (R : RFrame) (s : GhostRing2 R) (e : Vtx R) (g : Fin R.m)
    (hf : fires R (physical2 R s) e g = true) :
    (ghostStep2 R s e).cfg (rootV R g) = .root .race .toSend .free := by
  obtain ⟨hi,c,hc⟩ := (fires_iff R (physical2 R s) e g).mp hf
  change rawAt R s.cfg e (rootV R g) = .root c .heldDenial .heldDenial at hc
  rw [ghostStep2_physical]
  simp only [ShortGapOwnerRoundSlice.ringStepU,if_pos hi,joinTick,hc]
  rfl

theorem owner_port_exact_step (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (g : Fin R.m) :
    ((ghostStep2 R s e).cfg (rootV R g)).cwPort =
      some (epochCw ((ghostStep2 R s e).epoch g).cur) := by
  change _ = some (epochCw (epochStep2 R s e g).cur)
  rw [epochStep2_cur]
  cases hf : fires R (physical2 R s) e g with
  | true => rw [root_cfg_join R s e g hf]; rfl
  | false =>
    simp only [Bool.false_eq_true,if_false]
    rw [root_cfg_no_join R s e g hf]
    exact raw_owner_port_exact R s hs e g

private theorem epochCw_waiting (E : GapEpoch) : epochCw E = .waiting ↔ Live E := by
  cases E with
  | idle => simp [epochCw,Live]
  | outbound q c => simp [epochCw,Live]
  | returning q c d => simp [epochCw,Live]
  | delivered q c d => cases c <;> cases d <;> simp [epochCw,Live,resCw,res,Verdict.cw]

private theorem epochCw_held (E : GapEpoch) :
    CwHeld (some (epochCw E)) ↔ ∃ q c d, E = .delivered q c d := by
  cases E with
  | idle => simp [epochCw,CwHeld]
  | outbound q c => simp [epochCw,CwHeld]
  | returning q c d => simp [epochCw,CwHeld]
  | delivered q c d => cases c <;> cases d <;> simp [epochCw,CwHeld,resCw,res,Verdict.cw]

/-- All five owner-port clauses, including exact receipt payloads, are
preserved. The archive and tag lemmas translate the current encoding
back into the original completed-prefix interpretation. -/
theorem C2_step (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s) (e : Vtx R) :
    C2 R (ghostStep2 R s e) := by
  have ht := C6_step R s hs e
  have hp := C5_step R s hs e
  have hw := owner_port_exact_step R s hs e
  have hv := view_owner_tests R (ghostStep2 R s e) hp ht
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro g
    rw [hw g,(hv g).1]
    simpa only [Option.some.injEq] using epochCw_waiting ((ghostStep2 R s e).epoch g).cur
  · intro g
    rw [hw g,(hv g).2]
    exact epochCw_held _
  · intro g h
    obtain ⟨q,c,d,hc⟩ := (hv g).2.mp h
    have htag := ht g
    have hq : q = (ghostStep2 R s e).k g := by simpa only [hc,CurrentTag] using htag
    have hr : rawEpochs R (curView R s) e g = .delivered q c d := by
      change (epochStep2 R s e g).cur = _ at hc
      rw [epochStep2_cur] at hc
      split at hc
      · cases hc
      · exact hc
    have hpay := raw_delivered_payloads R s hs e g q c d hr
    refine ⟨c,d,hq ▸ hpay.1,hq ▸ hpay.2,?_⟩
    simpa only [hc,epochCw] using hw g
  · intro g hc
    simpa only [hc,epochCw] using hw g
  · intro g
    rw [hw g]
    simpa only [Option.some.injEq] using epochCw_waiting ((ghostStep2 R s e).epoch g).cur

/-- A physical declaration identifies its current epoch, payload and
unique occupied position. No symbolic token scan is assumed. -/
theorem declaration_epoch (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (a : Fin R.h) (ha : 0 < a.val) (c : Choice)
    (hc : s.cfg (g,a) = .interior (.decl c)) :
    (s.epoch g).cur = .outbound (s.k g) c ∧
      ∀ x : Fin R.h, 0 < x.val → s.cfg (g,x) = .interior (if x = a then .decl c else .empty) := by
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
    have hq : q = s.k g := by simpa only [he,CurrentTag] using ht
    rw [he] at hshape
    obtain ⟨p,hp,hslots⟩ := hshape
    have hx := hslots a ha
    change s.cfg (g,a) = _ at hx
    rw [hc] at hx
    by_cases hap : a = p
    · rw [if_pos hap] at hx
      cases hx
      exact ⟨by rw [hq],by simpa only [curView,← hap] using hslots⟩
    · rw [if_neg hap] at hx; cases hx
  | returning q x y =>
    rw [he] at hshape
    obtain ⟨p,hp,hslots⟩ := hshape
    have hx := hslots a ha
    change s.cfg (g,a) = _ at hx
    rw [hc] at hx
    split at hx <;> cases hx

/-- K1/K2's free receiver belongs to exactly the declaration's round. -/
theorem comparison_generations (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (c : Choice) (hc : (s.epoch g).cur = .outbound (s.k g) c)
    (hf : (s.cfg (rootV R (next R g))).ccwPort = some .free) :
    s.k (next R g) = s.k g := by
  have hshape := hs.coherent.shape g
  simp only [prefixView,combinedView,hc,EpochShape] at hshape
  have hn : ¬ s.k (next R g) < s.k g := by
    intro h
    have hi := (hs.coherent.incoming g).mpr (by
      change ComparedAt ((view R s).epoch g) (s.k (next R g))
      simpa only [view,prefixView,combinedView,hc,ComparedAt] using h)
    change CcwHeld (s.cfg (rootV R (next R g))).ccwPort at hi
    rw [hf] at hi
    exact hi
  rcases hshape.2.1 with he | he
  · exact he
  · omega

/-- General K1/K2 boundary package: comparison records the receiver,
creates a unique reply, retires prev, and handles either right-root JOIN
outcome. The selected owner cannot JOIN at this positive-offset edge. -/
theorem boundary_comparison (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (a : Fin R.h) (ha : 0 < a.val) (hlast : a.val+1 = R.h)
    (c d : Choice) (cw : CwPort)
    (hl : s.cfg (g,a) = .interior (.decl c))
    (hr : s.cfg (rootV R (next R g)) = .root d cw .free) :
    let t := ghostStep2 R s (g,a)
    let q := s.k g
    (t.epoch g).cur = .returning q c (resolveResp d) ∧
    (t.epoch g).prev = .idle ∧ t.k g = q ∧
    t.k (next R g) = q + (if fires R (physical2 R s) (g,a) (next R g) then 1 else 0) ∧
    t.hist g q = some c ∧ t.hist (next R g) q = some (resolveResp d) ∧
    OneToken R (curView R t) g (.reply (resolveResp d)) ∧
    (t.cfg (rootV R (next R g))).ccwPort = some
      (if fires R (physical2 R s) (g,a) (next R g) then .free else resCcw c (resolveResp d)) := by
  dsimp only
  obtain ⟨he,hslots⟩ := declaration_epoch R s hs g a ha c hl
  have hgen := comparison_generations R s hs g c he (by rw [hr]; rfl)
  have hrn : rn R (g,a) = rootV R (next R g) := rn_of_last R _ (by change ¬a.val+1<R.h; omega)
  have hraw : rawEpochs R (curView R s) (g,a) g = .returning (s.k g) c (resolveResp d) := by
    rw [rawEpochs,if_pos rfl]
    change rowEpoch (s.k g) (s.epoch g).cur (s.cfg (g,a)) (s.cfg (rn R (g,a))) = _
    rw [he,hl,hrn,hr]; rfl
  have hO := ShortGapTwoEpochLaws.no_owner_join_at_positive R s (g,a) ha
  have hcur : ((ghostStep2 R s (g,a)).epoch g).cur = .returning (s.k g) c (resolveResp d) := by
    change (epochStep2 R s (g,a) g).cur = _
    simp [epochStep2_cur,hO,hraw]
  have hprev : ((ghostStep2 R s (g,a)).epoch g).prev = .idle := by
    change (epochStep2 R s (g,a) g).prev = _
    simp [epochStep2,hO,hl,hrn,hr,compares]
  have hk : (ghostStep2 R s (g,a)).k g = s.k g := by simp [ghostStep2_k,hO]
  have hkR : (ghostStep2 R s (g,a)).k (next R g) = s.k g +
      (if fires R (physical2 R s) (g,a) (next R g) then 1 else 0) := by rw [ghostStep2_k,hgen]
  have hshape := hs.coherent.shape g
  simp only [prefixView,combinedView,he,EpochShape] at hshape
  have hpayL := history2_monotone R s (g,a) g (s.k g) c hshape.2.2.1
  have hnr : rootV R (next R g) ≠ (g,a) := by
    intro h
    have hz := congrArg (fun v : Vtx R => v.2.val) h
    change 0 = a.val at hz
    omega
  have hrraw : rawAt R s.cfg (g,a) (rootV R (next R g)) =
      .root (resolveResp d) cw (resCcw c (resolveResp d)) := by
    rw [rawAt,if_neg hnr,if_pos hrn.symm,hl,hrn,hr]; rfl
  have hpayR := raw_choice_recorded R s hs (g,a) (next R g) (Or.inr hrn.symm)
    (resolveResp d) (by rw [hrraw]; rfl)
  rw [hgen] at hpayR
  have hslots' := ShortGapTwoEpochLaws.boundary_token_replace R s g a ha hlast
    (.decl c) (.reply (resolveResp d)) hslots (by rw [hl,hrn,hr]; rfl)
  refine ⟨hcur,hprev,hk,hkR,hpayL,hpayR,⟨a,ha,hslots'⟩,?_⟩
  cases hf : fires R (physical2 R s) (g,a) (next R g) with
  | true => rw [root_cfg_join R s (g,a) (next R g) hf]; rfl
  | false => rw [root_cfg_no_join R s (g,a) (next R g) hf,hrraw]; rfl

/-- The three original right-port clauses at one gap. -/
def C3At (R : RFrame) (s : GhostRing2 R) (g : Fin R.m) : Prop :=
  (CcwHeld (s.cfg (rootV R (next R g))).ccwPort ↔ ComparedAt ((view R s).epoch g) (s.k (next R g))) ∧
  (ComparedAt ((view R s).epoch g) (s.k (next R g)) →
    ∃ c d, s.hist g (s.k (next R g)) = some c ∧ s.hist (next R g) (s.k (next R g)) = some d ∧
      (s.cfg (rootV R (next R g))).ccwPort = some (resCcw c d)) ∧
  (CcwHeld (s.cfg (rootV R (next R g))).ccwPort ↔
    CurrentResult (s.epoch g).cur (s.k (next R g)) ∨ PreviousResult (s.epoch g).prev (s.k (next R g)))

theorem C3_iff_forall (R : RFrame) (s : GhostRing2 R) : C3 R s ↔ ∀ g, C3At R s g := by
  constructor
  · intro h g; exact ⟨h.incomingPrefix g,h.incomingValue g,h.incoming g⟩
  · intro h; exact ⟨fun g => (h g).1,fun g => (h g).2.1,fun g => (h g).2.2⟩

/-- C1 and all three C3 clauses for the selected K1/K2 gap, including
the receiver's optional JOIN in the very same physical interaction. -/
theorem C1_C3_step_comparison (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (a : Fin R.h) (ha : 0 < a.val) (hlast : a.val+1 = R.h)
    (c d : Choice) (cw : CwPort)
    (hl : s.cfg (g,a) = .interior (.decl c))
    (hr : s.cfg (rootV R (next R g)) = .root d cw .free) :
    EpochShape R (view R (ghostStep2 R s (g,a))) g ∧ C3At R (ghostStep2 R s (g,a)) g := by
  obtain ⟨hc,hp,hk,hkR,hcH,hdH,hslots,hw⟩ := boundary_comparison R s hs g a ha hlast c d cw hl hr
  have hv : (view R (ghostStep2 R s (g,a))).epoch g = .returning (s.k g) c (resolveResp d) := by
    simp [view,prefixView,combinedView,hc]
  constructor
  · rw [EpochShape,hv]
    refine ⟨hk,?_,hcH,hdH,hslots⟩
    change (ghostStep2 R s (g,a)).k (next R g) = s.k g ∨
      (ghostStep2 R s (g,a)).k (next R g) = s.k g+1
    rw [hkR]
    split
    · exact Or.inr rfl
    · exact Or.inl (Nat.add_zero _)
  · have hh : CcwHeld (some (resCcw c (resolveResp d))) := by
      cases c <;> cases d <;> trivial
    unfold C3At
    rw [hv,hc,hp,hkR,hw]
    cases hf : fires R (physical2 R s) (g,a) (next R g) with
    | true =>
      simp [ComparedAt,CurrentResult,PreviousResult,CcwHeld]
      intro h
      omega
    | false =>
      simp only [Bool.false_eq_true,if_false,Nat.add_zero]
      refine ⟨?_,?_,?_⟩
      · exact ⟨fun _ => Nat.le_refl _,fun _ => hh⟩
      · intro _; exact ⟨c,resolveResp d,hcH,hdH,rfl⟩
      · exact ⟨fun _ => Or.inl rfl,fun _ => hh⟩

/-- Already established historical denials persist under every physical step. -/
theorem historicalDenial_step (R : RFrame) (s : GhostRing2 R) (e : Vtx R)
    (g : Fin R.m) (q : Nat) (h : HistoricalDenial R (view R s) g q) :
    HistoricalDenial R (view R (ghostStep2 R s e)) g q := by
  obtain ⟨c,d,hc,hd,hr⟩ := h
  exact ⟨c,d,history2_monotone R s e g q c hc,history2_monotone R s e (next R g) q d hd,hr⟩

/-- K1/K2 extends the selected gap's payload prefix by its newly compared
round and preserves every strict-prefix denial. -/
theorem prefix_step_comparison (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (a : Fin R.h) (ha : 0 < a.val) (hlast : a.val+1 = R.h)
    (c d : Choice) (cw : CwPort)
    (hl : s.cfg (g,a) = .interior (.decl c))
    (hr : s.cfg (rootV R (next R g)) = .root d cw .free) :
    (∀ q, ComparedAt ((view R (ghostStep2 R s (g,a))).epoch g) q →
      ∃ x y, (ghostStep2 R s (g,a)).hist g q = some x ∧
        (ghostStep2 R s (g,a)).hist (next R g) q = some y) ∧
    (∀ q, BeforeLatest ((view R (ghostStep2 R s (g,a))).epoch g) q →
      HistoricalDenial R (view R (ghostStep2 R s (g,a))) g q) := by
  obtain ⟨he,_⟩ := declaration_epoch R s hs g a ha c hl
  obtain ⟨hc,_,_,_,hcH,hdH,_,_⟩ := boundary_comparison R s hs g a ha hlast c d cw hl hr
  have hv : (view R (ghostStep2 R s (g,a))).epoch g = .returning (s.k g) c (resolveResp d) := by
    simp [view,prefixView,combinedView,hc]
  constructor
  · intro q hq
    rw [hv] at hq
    change q ≤ s.k g at hq
    by_cases hlt : q < s.k g
    · have hpre : ComparedAt ((view R s).epoch g) q := by
        simpa only [view,prefixView,combinedView,he,ComparedAt] using hlt
      obtain ⟨x,y,hx,hy⟩ := hs.coherent.prefixPayloads g q hpre
      exact ⟨x,y,history2_monotone R s (g,a) g q x hx,history2_monotone R s (g,a) (next R g) q y hy⟩
    · have hqeq : q = s.k g := by omega
      exact hqeq ▸ ⟨c,resolveResp d,hcH,hdH⟩
  · intro q hq
    have hpre : BeforeLatest ((view R s).epoch g) q := by
      simpa only [view,prefixView,combinedView,he,hc,BeforeLatest] using hq
    exact historicalDenial_step R s (g,a) g q (hs.coherent.prefixDenials g q hpre)

/-- Direct P1 preserves the selected gap's epoch shape and all right-port
clauses for all four combinations of endpoint JOINs. If both JOIN, the
completed-prefix interpretation reconstructs the delivered round from
the two records written by this same physical edge. -/
theorem C1_C3_step_P1 (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (hh : R.h = 1) (g : Fin R.m) (c d : Choice) (ccw : CcwPort) (cw : CwPort)
    (hl : s.cfg (rootV R g) = .root c .toSend ccw)
    (hr : s.cfg (rootV R (next R g)) = .root d cw .free) :
    EpochShape R (view R (ghostStep2 R s (rootV R g))) g ∧
      C3At R (ghostStep2 R s (rootV R g)) g := by
  let e := rootV R g
  let t := ghostStep2 R s e
  let q := s.k g
  let C := resolveInit c
  let D := resolveResp d
  change EpochShape R (view R t) g ∧ C3At R t g
  have hrn : rn R e = rootV R (next R g) := rn_of_last R _ (by change ¬0+1<R.h; omega)
  have hgen := direct_generations R (view R s) hs.coherent g
    (by change (s.cfg (rootV R g)).cwPort = _; rw [hl]; rfl)
    (by change (s.cfg (rootV R (next R g))).ccwPort = _; rw [hr]; rfl)
  change s.k g = s.k (next R g) at hgen
  have hraw : rawEpochs R (curView R s) e g = .delivered q C D := by
    rw [rawEpochs,if_pos rfl]
    change rowEpoch (s.k g) (s.epoch g).cur (s.cfg (rootV R g)) (s.cfg (rn R e)) = _
    rw [hl,hrn,hr]; rfl
  have hpay := raw_delivered_payloads R s hs e g q C D hraw
  change t.hist g q = some C ∧ t.hist (next R g) q = some D at hpay
  have hcur : (t.epoch g).cur = if fires R (physical2 R s) e g then .idle else .delivered q C D := by
    change (epochStep2 R s e g).cur = _
    rw [epochStep2_cur,hraw]
  have hprev : (t.epoch g).prev = if fires R (physical2 R s) e (next R g) then .idle
      else if fires R (physical2 R s) e g then .delivered q C D else .idle := by
    change (epochStep2 R s e g).prev = _
    have hl' : s.cfg e = .root c .toSend ccw := hl
    cases hO : fires R (physical2 R s) e g <;> cases hR : fires R (physical2 R s) e (next R g) <;>
      simp [epochStep2,hl',hrn,hr,compares,hraw,hO,hR,if_pos (show g = e.1 from rfl)]
  have hkO : t.k g = q + if fires R (physical2 R s) e g then 1 else 0 := ghostStep2_k R s e g
  have hkR : t.k (next R g) = q + if fires R (physical2 R s) e (next R g) then 1 else 0 := by
    change (ghostStep2 R s e).k (next R g) = _
    rw [ghostStep2_k,← hgen]
  have hv : (view R t).epoch g = .delivered q C D := by
    cases hO : fires R (physical2 R s) e g <;> cases hR : fires R (physical2 R s) e (next R g) <;>
      simp [view,prefixView,combinedView,hcur,hprev,hO,hR,hkO,hpay.1,hpay.2]
  have hw : (t.cfg (rootV R (next R g))).ccwPort = some
      (if fires R (physical2 R s) e (next R g) then .free else resCcw C D) := by
    cases hf : fires R (physical2 R s) e (next R g) with
    | true => rw [root_cfg_join R s e (next R g) hf]; rfl
    | false =>
      rw [root_cfg_no_join R s e (next R g) hf]
      have hn : rootV R (next R g) ≠ e := by rw [← hrn]; exact rn_ne_self R e
      have hl' : s.cfg e = .root c .toSend ccw := hl
      rw [rawAt,if_neg hn,if_pos hrn.symm,hl',hrn,hr]; rfl
  constructor
  · rw [EpochShape,hv]
    refine ⟨?_,?_,hpay.1,hpay.2,?_⟩
    · change t.k g = q ∨ t.k g = q+1
      rw [hkO]
      split
      · exact Or.inr rfl
      · exact Or.inl (Nat.add_zero _)
    · change t.k (next R g) = q ∨ t.k (next R g) = q+1
      rw [hkR]
      split
      · exact Or.inr rfl
      · exact Or.inl (Nat.add_zero _)
    · intro a ha
      have hb := a.isLt
      omega
  · have hheld : CcwHeld (some (resCcw C D)) := by
      dsimp only [C,D]
      cases c <;> cases d <;> trivial
    unfold C3At
    rw [hv,hcur,hprev,hkR,hw]
    cases hO : fires R (physical2 R s) e g <;> cases hR : fires R (physical2 R s) e (next R g)
    all_goals simp only [Bool.false_eq_true,if_false,if_true,Nat.add_zero]
    all_goals first |
      (exact ⟨⟨fun _ => Nat.le_refl _,fun _ => hheld⟩,
        fun _ => ⟨C,D,hpay.1,hpay.2,rfl⟩,
        ⟨fun _ => Or.inl rfl,fun _ => hheld⟩⟩) |
      (exact ⟨⟨fun _ => Nat.le_refl _,fun _ => hheld⟩,
        fun _ => ⟨C,D,hpay.1,hpay.2,rfl⟩,
        ⟨fun _ => Or.inr rfl,fun _ => hheld⟩⟩) |
      (simp [ComparedAt,CurrentResult,PreviousResult,CcwHeld]; intro h; omega)

/-- If the receiver has caught up with the owner, prev cannot represent
the receiver's current round. This uses exactly the retained tag clause. -/
theorem previous_not_current (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (hk : s.k g ≤ s.k (next R g)) :
    ¬ PreviousResult (s.epoch g).prev (s.k (next R g)) := by
  have hp := hs.previous g
  cases he : (s.epoch g).prev with
  | idle => exact id
  | outbound q c => simp only [PrevShape,he] at hp
  | returning q c d => simp only [PrevShape,he] at hp
  | delivered q c d =>
    simp only [PrevShape,he] at hp
    change ¬ q = s.k (next R g)
    omega

/-- V1's selected gap satisfies full C1 and C3 after either owner JOIN
outcome. The receiver is not incident, so its generation and receipt
remain unchanged; a transferred delivery occupies prev when cur resets. -/
theorem C1_C3_step_V1 (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (q : Nat) (c d : Choice) (hh : 1 < R.h)
    (he : (s.epoch g).cur = .returning q c d)
    (hslots : ∀ x : Fin R.h, 0 < x.val →
      s.cfg (g,x) = .interior (if x.val = 1 then .reply d else .empty)) :
    EpochShape R (view R (ghostStep2 R s (rootV R g))) g ∧
      C3At R (ghostStep2 R s (rootV R g)) g := by
  let e := rootV R g
  let t := ghostStep2 R s e
  change EpochShape R (view R t) g ∧ C3At R t g
  have htag := hs.current g
  have hq : q = s.k g := by simpa only [he,CurrentTag] using htag
  have hshape := hs.coherent.shape g
  simp only [prefixView,combinedView,he,EpochShape] at hshape
  have hbound : s.k (next R g) = q ∨ s.k (next R g) = q+1 := hshape.2.1
  obtain ⟨x,ccw,hroot⟩ := waiting_root R s hs g (by rw [he]; trivial)
  have hx := owner_choice_of_current R s hs g q c (Or.inr ⟨d,Or.inl he⟩)
  rw [hroot] at hx
  have hxc : x = c := Option.some.inj hx
  subst x
  have hrn : rn R e = (g,⟨1,hh⟩) := ShortGapTwoEpochLaws.rn_root_first R g hh
  have hrslot : s.cfg (g,⟨1,hh⟩) = .interior (.reply d) := by simpa using hslots ⟨1,hh⟩ (Nat.zero_lt_succ 0)
  have hraw : rawEpochs R (curView R s) e g = .delivered q c d := by
    rw [rawEpochs,if_pos rfl]
    change rowEpoch (s.k g) (s.epoch g).cur (s.cfg (rootV R g)) (s.cfg (rn R e)) = _
    rw [he,hroot,hrn,hrslot]; rfl
  have hpay := raw_delivered_payloads R s hs e g q c d hraw
  change t.hist g q = some c ∧ t.hist (next R g) q = some d at hpay
  have hnotR : ¬ incident R e (rootV R (next R g)) := by
    rintro (h | h)
    · exact next_ne_self R g (congrArg Prod.fst h)
    · rw [hrn] at h
      have hv := congrArg (fun v : Vtx R => v.2.val) h
      change 0 = 1 at hv
      omega
  have hR : fires R (physical2 R s) e (next R g) = false := by simp [fires,hnotR]
  have hkR : t.k (next R g) = s.k (next R g) := by simp [t,ghostStep2_k,hR]
  have hcfgR : t.cfg (rootV R (next R g)) = s.cfg (rootV R (next R g)) := by
    rw [ghostStep2_physical]
    exact if_neg hnotR
  have hkO : t.k g = q + if fires R (physical2 R s) e g then 1 else 0 := by
    change (ghostStep2 R s e).k g = _
    rw [ghostStep2_k,← hq]
  have hcur : (t.epoch g).cur = if fires R (physical2 R s) e g then .idle else .delivered q c d := by
    change (epochStep2 R s e g).cur = _
    rw [epochStep2_cur,hraw]
  have hprev : (t.epoch g).prev = if fires R (physical2 R s) e g then .delivered q c d else (s.epoch g).prev := by
    change (epochStep2 R s e g).prev = _
    have hl : s.cfg e = .root c .waiting ccw := hroot
    cases hO : fires R (physical2 R s) e g <;>
      simp [epochStep2,hR,hO,hraw,hl,hrn,hrslot,compares]
  have hv : (view R t).epoch g = .delivered q c d := by
    cases hO : fires R (physical2 R s) e g <;> simp [view,prefixView,combinedView,hcur,hprev,hO]
  have hempty : EmptyGap R (view R t) g := by
    intro a ha
    change (ghostStep2 R s e).cfg (g,a) = .interior .empty
    rw [ShortGapTwoEpochLaws.cfg_step_pair]
    have hn : (g,a) ≠ e := by
      intro h
      have hz := congrArg (fun v : Vtx R => v.2.val) h
      change a.val = 0 at hz
      omega
    rw [if_neg hn]
    by_cases har : (g,a) = rn R e
    · rw [if_pos har]
      change ShortGapLiteralRingRows.joinA (row (s.cfg (rootV R g)) (s.cfg (rn R e))).2 = _
      rw [hroot,hrn,hrslot]; rfl
    · have ha1 : a.val ≠ 1 := by
        intro h
        apply har
        rw [hrn]
        exact congrArg (g,·) (Fin.ext h)
      rw [if_neg har,hslots a ha,if_neg ha1]
  have hprevN := previous_not_current R s hs g (by omega)
  have hheld : CcwHeld (s.cfg (rootV R (next R g))).ccwPort ↔ q = s.k (next R g) := by
    have h := hs.incoming g
    simpa only [he,CurrentResult,or_false,iff_false,not_false_eq_true,hprevN] using h
  constructor
  · rw [EpochShape,hv]
    refine ⟨?_,?_,hpay.1,hpay.2,hempty⟩
    · change t.k g = q ∨ t.k g = q+1
      rw [hkO]
      split
      · exact Or.inr rfl
      · exact Or.inl (Nat.add_zero _)
    · change t.k (next R g) = q ∨ t.k (next R g) = q+1
      rw [hkR]
      exact hbound
  · unfold C3At
    rw [hv,hcfgR,hkR,hcur,hprev]
    refine ⟨?_,?_,?_⟩
    · have h := hs.coherent.incoming g
      simpa only [prefixView,combinedView,he,ComparedAt] using h
    · intro h
      have hpre : ComparedAt ((view R s).epoch g) (s.k (next R g)) := by
        simpa only [view,prefixView,combinedView,he,ComparedAt] using h
      obtain ⟨x,y,hx,hy,hw⟩ := hs.coherent.incomingValue g hpre
      exact ⟨x,y,history2_monotone R s e g _ x hx,history2_monotone R s e (next R g) _ y hy,hw⟩
    · cases hO : fires R (physical2 R s) e g with
      | false => simpa only [Bool.false_eq_true,if_false,CurrentResult,hprevN,or_false] using hheld
      | true => simpa only [if_true,CurrentResult,PreviousResult,false_or] using hheld

private theorem identity_annotations (k : Nat) (E : GapEpoch) (a b : Agent)
    (h : row a b = (a,b)) : rowEpoch k E a b = E ∧ compares a b = false := by
  cases a with
  | interior t =>
    cases b with
    | interior u => cases t <;> cases u <;> exact ⟨rfl,rfl⟩
    | root d cw ccw =>
      cases t <;> cases ccw
      all_goals first | exact ⟨rfl,rfl⟩ | (simp [row] at h)
  | root c cw ccw =>
    cases b with
    | interior t =>
      cases cw <;> cases t
      all_goals first | exact ⟨rfl,rfl⟩ | (simp [row] at h)
    | root d dw dd =>
      cases cw <;> cases dd
      all_goals first | exact ⟨rfl,rfl⟩ |
        (cases c <;> cases d <;> simp [row,resolveInit,resolveResp,resCw,res,Verdict.cw] at h)

private theorem record_of_saved (H : Nat → Option Choice) (k : Nat) (d : Choice)
    (hh : H k = some d) : record H k d = H := by
  funext r
  by_cases hr : r = k
  · subst r; simp [record,hh]
  · simp [record,hr]

private theorem ghost2_ext {R : RFrame} {s t : GhostRing2 R}
    (hc : ∀ v, s.cfg v = t.cfg v) (hk : ∀ i, s.k i = t.k i)
    (hh : ∀ i r, s.hist i r = t.hist i r) (he : ∀ g, s.epoch g = t.epoch g) : s = t := by
  have hc' := funext hc
  have hk' := funext hk
  have hh' := funext (fun i => funext (hh i))
  have he' := funext he
  cases s
  cases t
  cases hc'
  cases hk'
  cases hh'
  cases he'
  rfl

/-- A literal pair identity is an identity of the full two-epoch state
on Lineage2, including history and both retained annotations. -/
theorem ghostStep2_noop (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (hrow : row (s.cfg e) (s.cfg (rn R e)) = (s.cfg e,s.cfg (rn R e))) :
    ghostStep2 R s e = s := by
  have hraw : ∀ v, rawAt R s.cfg e v = s.cfg v := by
    intro v
    by_cases h0 : v = e
    · simp [rawAt,hrow,h0]
    · by_cases h1 : v = rn R e
      · simp [rawAt,hrow,h1,rn_ne_self]
      · simp [rawAt,h0,h1]
  have hfire : ∀ i, fires R (physical2 R s) e i = false := by
    intro i
    have hn := hs.coherent.normalized i
    change joinReady (s.cfg (rootV R i)) = false at hn
    simp [fires,physical2,hraw,hn]
  have hjoin : ∀ v, ShortGapLiteralRingRows.joinA (s.cfg v) = s.cfg v := by
    intro v
    by_cases hp : 0 < v.2.val
    · obtain ⟨t,ht⟩ := interior_roles R _ hs.coherent v.1 v.2 hp
      change s.cfg v = .interior t at ht
      rw [ht]; rfl
    · have hv : v = rootV R v.1 := by
        apply Prod.ext
        · rfl
        · apply Fin.ext; change v.2.val = 0; omega
      rw [hv]
      exact joinA_eq_of_not_ready _ (hs.coherent.normalized v.1)
  have hE : ∀ g, rawEpochs R (curView R s) e g = (s.epoch g).cur := by
    intro g
    by_cases hg : g = e.1
    · rw [rawEpochs,if_pos hg]
      exact (identity_annotations _ _ _ _ hrow).1
    · exact if_neg hg
  have hcomp : compares (s.cfg e) (s.cfg (rn R e)) = false := (identity_annotations 0 .idle _ _ hrow).2
  apply ghost2_ext
  · intro v
    rw [ghostStep2_physical]
    simp [ShortGapOwnerRoundSlice.ringStepU,joinTick,hraw,hjoin]
  · intro i; simp [ghostStep2_k,hfire]
  · intro i r
    by_cases hi : incident R e (rootV R i)
    · obtain ⟨d,cw,ccw,hr,hd,_⟩ := raw_root_resolved R s hs e i hi
      have hroot : s.cfg (rootV R i) = .root d cw ccw := (hraw _).symm.trans hr
      have hh := hs.coherent.histNow i d cw ccw hroot
      change s.hist i (s.k i) = resolvedOpt d at hh
      have hh' : s.hist i (s.k i) = some d := by cases d <;> simp_all [resolvedOpt]
      rw [history_step_record R s e i hi d cw ccw hr hd,record_of_saved _ _ _ hh']
    · change (if incident R e (rootV R i) then
        updateHistory (rawAt R s.cfg e (rootV R i)) (s.k i) (s.hist i) else s.hist i) r = s.hist i r
      rw [if_neg hi]
  · intro g
    change epochStep2 R s e g = s.epoch g
    simp [epochStep2,hfire,hE,hcomp]

/-- Full closure for every actual no-op pair, including K3 and clean
waiting/stationary rows; all eight clauses are preserved together. -/
theorem lineage2_step_noop (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (e : Vtx R) (hrow : row (s.cfg e) (s.cfg (rn R e)) = (s.cfg e,s.cfg (rn R e))) :
    Lineage2 R (ghostStep2 R s e) := by
  rw [ghostStep2_noop R s hs e hrow]
  exact hs

/-! Consumers with the corrected stopping horizon. The five global
clause laws above leave C1, C3 and C7 as explicit assembly obligations. -/

theorem lineage2_step_of_remaining_clauses (R : RFrame) (s : GhostRing2 R)
    (hs : Lineage2 R s) (e : Vtx R)
    (h1 : C1 R (ghostStep2 R s e)) (h3 : C3 R (ghostStep2 R s e)) (h7 : C7 R (ghostStep2 R s e)) :
    Lineage2 R (ghostStep2 R s e) :=
  (lineage2_iff_clauses R _).mpr ⟨C0_step R s hs e,h1,C2_step R s hs e,h3,
    C4_step R s hs e,C5_step R s hs e,C6_step R s hs e,h7⟩

/-- The candidate bound only needs history's future-domain clause.
It therefore applies to post-states before full lineage closure is known. -/
theorem candidate_round_le_maxGen_of_C4 (R : RFrame) (s : GhostRing2 R)
    (hs : C4 R s) (q : Nat) (hc : VirtualCandidate2 R q s) : q ≤ maxGen R s := by
  obtain ⟨g,hg⟩ := hc
  have hh : s.hist g q = some .out1 := by
    have h := hg.1
    change choiceToWord ((s.hist g q).getD .race) = .out1 at h
    cases he : s.hist g q with
    | none => simp [he,choiceToWord] at h
    | some c => cases c <;> simp_all [choiceToWord]
  have hq : q ≤ s.k g := by
    by_cases h : s.k g < q
    · rw [hs.future g q h] at hh; cases hh
    · omega
  exact Nat.le_trans hq (le_generationMax s.k g)

theorem accounting_success_implies_success_step (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Lineage2 R s) (e : Vtx R)
    (hv : ShortGapTwoEpochLaws.VirtualSuccess R r (ghostStep2 R s e)) :
    VirtualSuccess R r (ghostStep2 R s e) := by
  obtain ⟨q,_,hc⟩ := hv
  exact ⟨q,candidate_round_le_maxGen_of_C4 R _ (C4_step R s hs e) q hc,hc⟩

theorem genPipelined2_childSum (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Dom R r s) (hr : PeriodHIncidenceChoice.HasRace (word2 R r s)) :
    1 + (List.ofFn (fun e : Fin R.n => roundDebt2 R r (ghostStep2 R s (edgeVtx R e)))).sum ≤
      R.n * roundDebt2 R r s :=
  ShortGapTwoEpochLaws.genPipelined2_childSum R r s (dom_accounting R r s hs) hr

def RoundFailure (R : RFrame) (r : Nat) (s : GhostRing2 R) : Prop :=
  PeriodHIncidenceChoice.Frozen (word2 R r s) ∧ ¬ VirtualSuccess R r s

theorem roundFailure_uniform (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (h4 : C4 R s) (hf : RoundFailure R r s) : PeriodHIncidenceChoice.Constant (word2 R r s) := by
  apply PeriodHIncidenceChoice.frozen_noCandidate_constant (ring R) _ hf.1
  intro g hg
  exact hf.2 ⟨r,candidate_round_le_maxGen_of_C4 R s h4 r ⟨g,hg⟩,⟨g,hg⟩⟩

noncomputable def successEdgeCount (R : RFrame) (r : Nat) (s : GhostRing2 R) : Nat := by
  classical
  exact (List.ofFn (fun e : Fin R.n => if VirtualSuccess R r (ghostStep2 R s (edgeVtx R e)) then 1 else 0)).sum

noncomputable def failureEdgeCount (R : RFrame) (r : Nat) (s : GhostRing2 R) : Nat := by
  classical
  exact (List.ofFn (fun e : Fin R.n => if RoundFailure R r (ghostStep2 R s (edgeVtx R e)) then 1 else 0)).sum

/-- Enlarging success to maxGen preserves local balance. C4_step bounds
post-step candidates without presupposing the remaining closure clauses. -/
theorem genPipelined2_localBalance (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Dom R r s) (hr : PeriodHIncidenceChoice.HasRace (word2 R r s)) :
    failureEdgeCount R r s ≤ successEdgeCount R r s := by
  classical
  have hb : failureEdgeCount R r s ≤ ShortGapTwoEpochLaws.failureEdgeCount R r s := by
    apply ofFn_sum_le
    intro e
    by_cases hf : RoundFailure R r (ghostStep2 R s (edgeVtx R e))
    · have ho : ShortGapTwoEpochLaws.RoundFailure R r (ghostStep2 R s (edgeVtx R e)) :=
        ⟨hf.1,fun h => hf.2 (accounting_success_implies_success_step R r s hs.1 _ h)⟩
      simp only [if_pos hf,if_pos ho]
      exact Nat.le_refl _
    · simp only [if_neg hf]
      exact Nat.zero_le _
  have hg : ShortGapTwoEpochLaws.successEdgeCount R r s ≤ successEdgeCount R r s := by
    apply ofFn_sum_le
    intro e
    by_cases ho : ShortGapTwoEpochLaws.VirtualSuccess R r (ghostStep2 R s (edgeVtx R e))
    · have hn := accounting_success_implies_success_step R r s hs.1 _ ho
      simp only [if_pos ho,if_pos hn]
      exact Nat.le_refl _
    · simp only [if_neg ho]
      exact Nat.zero_le _
  exact Nat.le_trans hb (Nat.le_trans
    (ShortGapTwoEpochLaws.genPipelined2_localBalance R r s (dom_accounting R r s hs) hr) hg)

theorem dom_step_or_success_of_lineage (R : RFrame) (r : Nat) (s : GhostRing2 R)
    (hs : Dom R r s) (e : Vtx R) (hl : Lineage2 R (ghostStep2 R s e)) :
    Dom R r (ghostStep2 R s e) ∨ VirtualSuccess R r (ghostStep2 R s e) := by
  classical
  by_cases hv : VirtualSuccess R r (ghostStep2 R s e)
  · exact Or.inr hv
  · exact Or.inl ⟨hl,cohortEntered2_step R r s e hs.2.1,hv⟩

/-- Active states exclude both terminal ports of the corrected process. -/
def Active (R : RFrame) (r : Nat) :=
  {s : GhostRing2 R // Dom R r s ∧ PeriodHIncidenceChoice.HasRace (word2 R r s)}

noncomputable def stoppedStepOfClosure (R : RFrame) (r : Nat)
    (hclose : ∀ s, Dom R r s → ∀ e, Lineage2 R (ghostStep2 R s e))
    (s : Active R r) (e : Fin R.n) : StopNode (Active R r) := by
  classical
  let t := ghostStep2 R s.val (edgeVtx R e)
  exact if hv : VirtualSuccess R r t then .success
    else if hr : PeriodHIncidenceChoice.HasRace (word2 R r t) then
      .active ⟨t,⟨hclose s.val s.property.1 _,cohortEntered2_step R r s.val _ s.property.1.2.1,hv⟩,hr⟩
    else .failure

def stoppedPotential (R : RFrame) (r : Nat) : StopNode (Active R r) → Nat
  | .active s => R.n * roundDebt2 R r s.val
  | .success | .failure => 0

theorem stoppedStep_success_iff (R : RFrame) (r : Nat)
    (hclose : ∀ s, Dom R r s → ∀ e, Lineage2 R (ghostStep2 R s e))
    (s : Active R r) (e : Fin R.n) :
    stoppedStepOfClosure R r hclose s e = .success ↔
      VirtualSuccess R r (ghostStep2 R s.val (edgeVtx R e)) := by
  classical
  unfold stoppedStepOfClosure
  dsimp only
  split <;> simp_all
  split <;> simp_all

theorem stoppedStep_failure_iff (R : RFrame) (r : Nat)
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

theorem stoppedStep_failure_uniform (R : RFrame) (r : Nat)
    (hclose : ∀ s, Dom R r s → ∀ e, Lineage2 R (ghostStep2 R s e))
    (s : Active R r) (e : Fin R.n) (hf : stoppedStepOfClosure R r hclose s e = .failure) :
    PeriodHIncidenceChoice.Constant (word2 R r (ghostStep2 R s.val (edgeVtx R e))) :=
  roundFailure_uniform R r _ (C4_step R s.val s.property.1.1 _)
    ((stoppedStep_failure_iff R r hclose s e).mp hf)

/-- The stopped process uses the corrected success predicate; its remaining
closure hypothesis is displayed explicitly and is separate from Dom. -/
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

def startActive (R : RFrame) : Active R 1 :=
  ⟨ghostStart2 R,dom_start R,⟨⟨0,by have := R.hm; omega⟩,rfl⟩⟩

theorem stoppedPotential_start (R : RFrame) :
    stoppedPotential R 1 (.active (startActive R)) = 2 * R.n * R.m * R.h := by
  change R.n * roundDebt2 R 1 (ghostStart2 R) = _
  rw [potential2_start]
  ac_rfl

/-!
STALL REPORT:

Global C0, C2, C4, C5 and C6 preservation is proved for every physical
edge, with Lineage2 as the sole precondition. The selected gap's full
C1/C3 package is proved for K1/K2 comparison, direct P1 (all four JOIN
combinations), and V1 delivery (both owner JOIN outcomes). Literal no-op
rows preserve the full state and hence all eight clauses.

General C1, C3 and C7 preservation is still unassembled: selected-gap
launch/interior movement and adjacent-gap JOIN effects must be combined,
and the newly joined round must be added to C7.joined in both directions.
The comparison payload-prefix and strict-prefix-denial pieces are proved;
they do not by themselves establish the global joined-denial clause.
No clause is claimed false and no new reachable counterexample is claimed.

Thus lineage2_step, unconditional dom_step_or_success and unconditional
genPipelined2_natBellmanSuperSolution are not declared. Their explicitly
conditional reductions retain the unresolved premises in their types.
The maxGen correction is proved and used throughout the new stopped
process, child sum and local balance; accounting r no longer limits success.
-/

#print axioms lineage2_iff_clauses
#print axioms candidate_round_le_maxGen
#print axioms virtualSuccess_iff_any_candidate
#print axioms virtualSuccess_persists
#print axioms dom_start
#print axioms C0_step
#print axioms C2_step
#print axioms C4_step
#print axioms C5_step
#print axioms C6_step
#print axioms owner_join_raw_delivered
#print axioms raw_delivered_payloads
#print axioms C1_C3_step_comparison
#print axioms prefix_step_comparison
#print axioms C1_C3_step_P1
#print axioms C1_C3_step_V1
#print axioms lineage2_step_noop
#print axioms lineage2_step_of_remaining_clauses
#print axioms genPipelined2_childSum
#print axioms genPipelined2_localBalance
#print axioms dom_step_or_success_of_lineage
#print axioms genPipelined2_natBellmanSuperSolution_of_lineage2_step
#print axioms stoppedStep_success_iff
#print axioms stoppedStep_failure_iff
#print axioms stoppedStep_failure_uniform
#print axioms stoppedPotential_start

end ShortGapLineage2Closure
