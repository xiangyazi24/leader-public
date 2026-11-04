import Leader.L3.StageM.EntryPin

/-!
# The strict cohort's tail export at a boundary reference: run indexing and the source sweep

Width ports of the run indexing of `L3.DigitEntryBridge` (BankRepairDigitEntryBridge) along a
coupled run `widthDigitAuditNext` from a state `q0` with the run invariant `WidthRunInv` and a
frameless audit at clock `0` (the clean start of a first-zero run):

* `wRunAt` (prefix states), `wRunFrames`, `wFrameTime`, `wFramesUpTo` (frames persist);
* `wInvAt` (the run invariant at every prefix), `wLaneStep` (the lane trace moves by the lane
  letters), `wClock`, `wStepAt`, `wRecExport`, `wExportUnique`;
* `wTailRun`: the tail sweep of the strict tail sample, from its sample letter to its recorded
  export (port of `tailRun`);
* `YoungTail`, `youngTailStep`, `wSweepAtExport`: the source cells behind the strict tail carry
  samples read at their own cell (`SPin`); at the export letter the tail has left the source, every
  source cell is a younger slot, target cell `R` is occupied, and every source atom is pinned at its
  own cell (`ChosenInv` at `lam = 0`). This is half F2 and the chosen half of F1 of the 2026-11-02
  11:17 handover (research/lean-l3/ledgers/stage-m-notes.md).
-/

namespace L3.StageMEntryRun

set_option autoImplicit false
set_option linter.unusedSectionVars false

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.WidthWave
open L3.WidthPacketMoment
open L3.WidthPacketMomentCutEntry
open L3.WidthPacketMomentCompare
open L3.WidthPacketMomentGroupCompletion
open L3.CohortDomination
open L3.CohortTail
open L3.CohortSites
open L3.CohortEntry
open L3.PacketClass
open L3.CohortStages
open L3.Rearm
open L3.Recording
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.CohortWindow
open L3.CohortClose
open L3.ValueLedger
open L3.UseRows
open L3.UseCells
open L3.UseTrack
open L3.SitePin
open L3.DigitEntryPhase

/-! ### Prefix states of a coupled run -/

section Runs

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)


/-- The state after the first `t` letters of `word`. -/
def wRunAt (q : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (word : List (Fin n)) (t : Nat) :
    ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n :=
  (word.take t).foldl (widthDigitAuditNext ref) q

/-- The frame that the audit letter `e` prepends at the state `x`. -/
def wFrameAt (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n) : DigitFrame (compileAdvice (ceilLogTwo n)) n :=
  ⟨x.2.clock + 1, e, piD (ref.phys x.1), x.2.current, svcAt ring (piD (ref.phys x.1)) x.2 e⟩

/-- One more letter. Consumer: `laneAtStep` and the group 6 assembly. -/
theorem wRunAtSucc : ∀ (word : List (Fin n))
    (q : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (t : Nat) (e : Fin n), word[t]? = some e →
    wRunAt ref q word (t + 1) =
      widthDigitAuditNext ref (wRunAt ref q word t) e := by
  intro word
  induction word with
  | nil => intro q t e h; simp at h
  | cons a rest ih =>
    intro q t e h
    cases t with
    | zero =>
      simp at h
      subst h
      rfl
    | succ t =>
      have h' : rest[t]? = some e := by simpa using h
      exact ih _ t e h'

/-- The clock counts the letters. Consumer: `frameTime`. -/
theorem wRunAtClock : ∀ (word : List (Fin n))
    (q : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (t : Nat), t ≤ word.length → (wRunAt ref q word t).2.clock = q.2.clock + t := by
  intro word
  induction word with
  | nil =>
    intro q t h
    have : t = 0 := by simp at h; omega
    subst this
    rfl
  | cons a rest ih =>
    intro q t h
    cases t with
    | zero => rfl
    | succ t =>
      have := ih (widthDigitAuditNext ref q a) t (by simp at h; omega)
      show (wRunAt ref (widthDigitAuditNext ref q a) rest t).2.clock = _
      rw [this]
      show q.2.clock + 1 + t = q.2.clock + (t + 1)
      omega

/-- Past the end of the word the prefix state is the final state. Consumer: `laneAtStep`,
`exportUnique`, `strictCompletionCyc`. -/
theorem wRunAtLen (word : List (Fin n))
    (q : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (t : Nat) (h : word.length ≤ t) :
    wRunAt ref q word t = word.foldl (widthDigitAuditNext ref) q := by
  unfold wRunAt
  rw [List.take_of_length_le h]

/-- **Fold lemma (step 4a).** Every frame of the final audit is an initial frame or the
one-step frame of the letter `t` at the prefix state `t`. Consumer: `frameTime` and the group 6
assembly (recorded samples, exports and terminals become letters of the run). -/
theorem wRunFrames : ∀ (word : List (Fin n))
    (q : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (f : DigitFrame (compileAdvice (ceilLogTwo n)) n),
    f ∈ (word.foldl (widthDigitAuditNext ref) q).2.frames →
    f ∈ q.2.frames ∨ ∃ t e, word[t]? = some e ∧ f = wFrameAt ref (wRunAt ref q word t) e := by
  intro word
  induction word with
  | nil => intro q f hf; exact Or.inl hf
  | cons a rest ih =>
    intro q f hf
    rcases ih (widthDigitAuditNext ref q a) f hf with h | ⟨t, e, h1, h2⟩
    · rcases auditFrameMemStepCases ring (piD (ref.phys q.1)) q.2 a f h with h3 | h3
      · exact Or.inl h3
      · exact Or.inr ⟨0, a, rfl, h3⟩
    · exact Or.inr ⟨t + 1, e, by simpa using h1, h2⟩

/-- Frames are never dropped. Consumer: `runFramesAtEnd`. -/
theorem wFramesMono : ∀ (word : List (Fin n))
    (q : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (f : DigitFrame (compileAdvice (ceilLogTwo n)) n), f ∈ q.2.frames →
    f ∈ (word.foldl (widthDigitAuditNext ref) q).2.frames := by
  intro word
  induction word with
  | nil => intro q f h; exact h
  | cons a rest ih =>
    intro q f h
    exact ih _ f (auditFrameMemStep ring (piD (ref.phys q.1)) q.2 a f h)

/-- Frames of a prefix state survive to the final audit. Consumer: the group 6 assembly
(provenance of a tracked atom read in the final audit). -/
theorem wRunFramesAtEnd (word : List (Fin n))
    (q : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (t : Nat) (f : DigitFrame (compileAdvice (ceilLogTwo n)) n)
    (h : f ∈ (wRunAt ref q word t).2.frames) :
    f ∈ (word.foldl (widthDigitAuditNext ref) q).2.frames := by
  have e : (word.drop t).foldl (widthDigitAuditNext ref)
      (wRunAt ref q word t) = word.foldl (widthDigitAuditNext ref) q := by
    unfold wRunAt
    rw [← List.foldl_append, List.take_append_drop]
  rw [← e]
  exact wFramesMono ref _ _ f h

/-- A recorded frame of a run from a frameless start at clock `0` is the one-step frame of
letter `time - 1`. Consumer: the group 6 assembly. -/
theorem wFrameTime (word : List (Fin n))
    (q : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h0 : q.2.frames = []) (hc : q.2.clock = 0) (f : DigitFrame (compileAdvice (ceilLogTwo n)) n)
    (hf : f ∈ (word.foldl (widthDigitAuditNext ref) q).2.frames) :
    ∃ t e, word[t]? = some e ∧ f.time = t + 1 ∧
      f = wFrameAt ref (wRunAt ref q word t) e := by
  rcases wRunFrames ref word q f hf with h | ⟨t, e, h1, h2⟩
  · rw [h0] at h
    exact absurd h List.not_mem_nil
  · refine ⟨t, e, h1, ?_, h2⟩
    have ht : t < word.length := by
      rcases Nat.lt_or_ge t word.length with h | h
      · exact h
      · rw [List.getElem?_eq_none_iff.mpr h] at h1
        cases h1
    rw [h2]
    show (wRunAt ref q word t).2.clock + 1 = t + 1
    rw [wRunAtClock ref word q t (by omega), hc]
    omega

end Runs

section Mono

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)

/-- Frames of an earlier prefix state are frames of every later prefix state. Consumer:
`L3.StageMEntryCarryRows` (a recorded export stays recorded). -/
theorem wFramesUpTo (word : List (Fin n))
    (q : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (t1 t2 : Nat) (h12 : t1 ≤ t2)
    (f : DigitFrame (compileAdvice (ceilLogTwo n)) n)
    (hf : f ∈ (wRunAt ref q word t1).2.frames) : f ∈ (wRunAt ref q word t2).2.frames := by
  have e : ((word.take t2).drop t1).foldl (widthDigitAuditNext ref) (wRunAt ref q word t1) =
      wRunAt ref q word t2 := by
    unfold wRunAt
    have ht : (word.take t2).take t1 = word.take t1 := by
      rw [List.take_take, Nat.min_eq_left h12]
    rw [← ht, ← List.foldl_append, List.take_append_drop]
  rw [← e]
  exact wFramesMono ref _ _ f hf

/-- The prefix state after `t2` letters is the run of the letters `t1 .. t2` from the prefix
state after `t1`. Consumer: `L3.StageMEntryCyc` (the pinned state precedes the strict cut). -/
theorem wRunAtSplit (word : List (Fin n))
    (q : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (t : Nat) :
    (word.drop t).foldl (widthDigitAuditNext ref) (wRunAt ref q word t) =
      word.foldl (widthDigitAuditNext ref) q := by
  unfold wRunAt
  rw [← List.foldl_append, List.take_append_drop]

end Mono

/-! ### The coupled run of one interior pair from a run-invariant start -/

section Coupled

variable {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
  (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src)
  (hend : src + 2 * R < n)
  (q0 : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
  (hq0 : WidthRunInv ring ref root lane src R q0) (hc0 : q0.2.clock = 0)
  (W : List (Fin n))

/-- The masked lane of the pair at prefix `t`. -/
def wLane (t : Nat) : CohortLane :=
  cohortProj ring root lane src R (piD (ref.phys (wRunAt ref.toWidthDigitReference q0 W t).1))

/-- The lane letter of letter `t` (`none` past the end of the word). -/
def wKe (t : Nat) : Option Nat :=
  (W[t]?).bind (cohortEdgeOf root src R)

include hn hR hsrc hend hq0 in
/-- The run invariant at every prefix. Consumer: every row of this module and of
`L3.StageMEntryCarryRows`. -/
theorem wInvAt (t : Nat) :
    WidthRunInv ring ref root lane src R (wRunAt ref.toWidthDigitReference q0 W t) :=
  widthRunInvFold ring ref hn root lane src R hR hsrc hend (W.take t) q0 hq0

include hc0 in
/-- The clock of a prefix state is its length. Consumer: every row of the assembly. -/
theorem wClock (t : Nat) (ht : t ≤ W.length) :
    (wRunAt ref.toWidthDigitReference q0 W t).2.clock = t := by
  rw [wRunAtClock ref.toWidthDigitReference W q0 t ht, hc0]
  omega

/-- The letter at an index inside the word. Consumer: every row of the assembly. -/
theorem wStepAt (t : Nat) (ht : t < W.length) :
    ∃ e, W[t]? = some e ∧
      wRunAt ref.toWidthDigitReference q0 W (t + 1) =
        widthDigitAuditNext ref.toWidthDigitReference
          (wRunAt ref.toWidthDigitReference q0 W t) e ∧
      wKe root src R W t = cohortEdgeOf root src R e := by
  refine ⟨W[t], List.getElem?_eq_getElem ht,
    wRunAtSucc ref.toWidthDigitReference W _ t _ (List.getElem?_eq_getElem ht), ?_⟩
  unfold wKe
  rw [List.getElem?_eq_getElem ht]
  rfl

/-- The lane letter of a known letter. Consumer: `wTailRun`. -/
theorem wKeOf {t : Nat} {e : Fin n} (h : W[t]? = some e) :
    wKe root src R W t = cohortEdgeOf root src R e := by
  unfold wKe
  rw [h]
  rfl

include hn hR hsrc hend hq0 in
/-- The lane trace moves by the lane letters. Consumer: `wTailRun`, `wSweepAtExport`. -/
theorem wLaneStep (t : Nat) :
    wLane ref root lane src R q0 W (t + 1) =
      cohortLaneStep R (wLane ref root lane src R q0 W t) (wKe root src R W t) := by
  cases h : W[t]? with
  | none =>
    have hl : W.length ≤ t := List.getElem?_eq_none_iff.mp h
    have e1 : wRunAt ref.toWidthDigitReference q0 W (t + 1) =
        wRunAt ref.toWidthDigitReference q0 W t := by
      rw [wRunAtLen ref.toWidthDigitReference _ _ (t + 1) (by omega),
        wRunAtLen ref.toWidthDigitReference _ _ t hl]
    unfold wLane wKe
    rw [e1, h]
    rfl
  | some e =>
    unfold wLane wKe
    rw [wRunAtSucc ref.toWidthDigitReference W _ t e h, h]
    exact (widthLaneStep ref.toWidthDigitReference ref.singletonFixed hn root lane src R hR hsrc
      hend _ (wInvAt ref hn root lane src R hR hsrc hend q0 hq0 W t).1.1 e).2

include hn hR hsrc hend hq0 in
/-- The lane letter moves the lane trace by its edge. Consumer: `wTailRun`. -/
theorem wLaneEdge (t k : Nat) (hk : wKe root src R W t = some k) :
    wLane ref root lane src R q0 W (t + 1) = cohortEdge R (wLane ref root lane src R q0 W t) k := by
  rw [wLaneStep ref hn root lane src R hR hsrc hend q0 hq0 W t, hk]
  rfl

include hc0 in
/-- An export of the receipt of letter `t` is recorded at every later prefix. Consumer:
`wTailRun`, `L3.StageMEntryCarryRows`. -/
theorem wRecExportAt (t : Nat) (ht : t < W.length) (e : Fin n) (he : W[t]? = some e)
    (x : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hx : (digitReceiptLane x.lane
      (svcAt ring (piD (ref.phys (wRunAt ref.toWidthDigitReference q0 W t).1))
        (wRunAt ref.toWidthDigitReference q0 W t).2 e)).exported = some x)
    (htime : x.time = t + 1) (hs : x.source = e) (t' : Nat) (ht' : t + 1 ≤ t') :
    DigitRecordedExport (wRunAt ref.toWidthDigitReference q0 W t').2 x := by
  refine ⟨wFrameAt ref.toWidthDigitReference (wRunAt ref.toWidthDigitReference q0 W t) e,
    wFramesUpTo ref.toWidthDigitReference W _ (t + 1) t' ht' _ ?_, ?_, hs.symm, hx⟩
  · rw [wRunAtSucc ref.toWidthDigitReference W _ t e he]
    exact List.mem_cons.mpr (Or.inl rfl)
  · show (wRunAt ref.toWidthDigitReference q0 W t).2.clock + 1 = x.time
    rw [wClock ref q0 hc0 W t (by omega), htime]

include hn hR hsrc hend hq0 in
/-- Exports on the delimiter edge carrying the same sample are equal (at any prefix). Consumer:
`wTailRun`, `L3.StageMEntryCarryRows`. -/
theorem wExportUnique (t : Nat) (x y : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (sid : DigitStamp n)
    (hx : DigitRecordedExport (wRunAt ref.toWidthDigitReference q0 W t).2 x)
    (hy : DigitRecordedExport (wRunAt ref.toWidthDigitReference q0 W t).2 y)
    (hox : OnEdge ring root lane src R x) (hoy : OnEdge ring root lane src R y)
    (h1 : x.operand = some (.sampled sid)) (h2 : y.operand = some (.sampled sid)) : x = y :=
  (wInvAt ref hn root lane src R hR hsrc hend q0 hq0 W t).1.2.2.2.2.2.2.2.2.2 x y sid hx hy hox
    hoy h1 h2

end Coupled

/-! ### Rows of one coupled letter on the layout class -/

section Letter

variable {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
  (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src)
  (hend : src + 2 * R < n)

include hn hR hsrc hend in
/-- Source rows on the coupled chain (port of `srcRowsBank`). Consumer: `wTailRun`,
`wSampleStep`. -/
theorem wSrcRows
    (z : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hz : WidthCohortLayout ref.toWidthDigitReference root src R z.1) (e : Fin n) :
    L3.DigitEntryBridge.OutH R (cohortProj ring root lane src R (piD (ref.phys z.1)))
      (cohortEdgeOf root src R e)
      (DigitStamp.mk (z.2.clock + 1) e lane)
      (fun q => (laneCells ring root lane src z.2.current q).out)
      (fun q => (laneCells ring root lane src
        (widthDigitAuditNext ref.toWidthDigitReference z e).2.current q).out) := by
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hz
  obtain ⟨-, hroot, hbX, hbY⟩ := widthLeadEdge ref.toWidthDigitReference ref.singletonFixed hn
    root z.1 hL e
  obtain ⟨jx, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  exact L3.DigitEntryBridge.srcRows ring (by omega) root (piD (ref.phys z.1)) R src hR hsrc hend
    hroot hb0 hbR hbF lane z.2 jx hj hbX hbY

include hn hR hsrc hend in
/-- The tracked step of one coupled letter with the drawn cell explicit (`trackedPinStep` on the
layout class). Consumer: `wYoungStep`, `L3.StageMEntryCarryRows`. -/
theorem wTrackedStep
    (z : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hz : WidthCohortLayout ref.toWidthDigitReference root src R z.1) (e : Fin n) :
    ∃ k, (∀ q, q ≠ k → q ≠ k + 1 →
        tracked ring root lane src R (widthDigitAuditNext ref.toWidthDigitReference z e).2 q =
        tracked ring root lane src R z.2 q) ∧
      MoveOk (tracked ring root lane src R z.2 k) (tracked ring root lane src R z.2 (k + 1))
        (tracked ring root lane src R (widthDigitAuditNext ref.toWidthDigitReference z e).2 k)
        (tracked ring root lane src R (widthDigitAuditNext ref.toWidthDigitReference z e).2
          (k + 1))
        (some (.sampled (stampAt ring root lane src z.2.clock k))) ∧
      (k < R → tracked ring root lane src R (widthDigitAuditNext ref.toWidthDigitReference z e).2
          k = some (.sampled (stampAt ring root lane src z.2.clock k)) →
        (cohortProj ring root lane src R (piD (ref.phys z.1))).out k = .U ∨
          tracked ring root lane src R z.2 k =
            some (.sampled (stampAt ring root lane src z.2.clock k))) ∧
      (k + 1 < R → (cohortProj ring root lane src R (piD (ref.phys z.1))).out (k + 1) ≠ .E →
        tracked ring root lane src R (widthDigitAuditNext ref.toWidthDigitReference z e).2
          (k + 1) = tracked ring root lane src R z.2 (k + 1)) ∧
      (k < R → ∀ T, (cohortProj ring root lane src R (piD (ref.phys z.1))).out k = .D T →
        cohortTok R (cohortProj ring root lane src R (piD (ref.phys z.1))) (k + 1) = .empty →
        tracked ring root lane src R (widthDigitAuditNext ref.toWidthDigitReference z e).2 k =
          none) ∧
      (∀ k', cohortEdgeOf root src R e = some k' → k' = k) ∧
      (k < R → (cohortProj ring root lane src R (piD (ref.phys z.1))).out k = .U →
        SPin ring root lane src (widthDigitAuditNext ref.toWidthDigitReference z e).2 k
          (.sampled (stampAt ring root lane src z.2.clock k))) := by
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hz
  obtain ⟨-, hroot, hbX, hbY⟩ := widthLeadEdge ref.toWidthDigitReference ref.singletonFixed hn
    root z.1 hL e
  obtain ⟨jx, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  obtain ⟨k, hfr, hm, hF, hM, hH, hK, hJ⟩ := trackedPinStep ring (by omega) root
    (piD (ref.phys z.1)) R src hR hsrc hend hroot hb0 hbR hb2R hbF lane z.2 jx hj hbX hbY
  refine ⟨k, hfr, hm, hF, hM, hH, hK, fun hk hU => ?_⟩
  have hjk := hJ hk
  subst hjk
  exact freshSPin ring root (piD (ref.phys z.1)) R src hsrc hend hroot hb0 hbF lane z.2 k hk hbX hU

include hn hR hsrc hend in
/-- The delimiter-edge export of one coupled letter (port of `delExport`). Consumer:
`wTailRun`. -/
theorem wDelExport
    (z : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hz : WidthCohortLayout ref.toWidthDigitReference root src R z.1) (e : Fin n)
    (hke : cohortEdgeOf root src R e = some (R - 1)) (T : Bool)
    (hD : (cohortProj ring root lane src R (piD (ref.phys z.1))).out (R - 1) = .D T)
    (hE : (cohortProj ring root lane src R (piD (ref.phys z.1))).inp R = .E)
    (hL : (cohortProj ring root lane src R (piD (ref.phys z.1))).live R = false) :
    ∃ ex : DigitExport (compileAdvice (ceilLogTwo n)) n,
      (digitReceiptLane lane (svcAt ring (piD (ref.phys z.1)) z.2 e)).exported = some ex ∧
      ex.operand = (laneCells ring root lane src z.2.current (R - 1)).out.atom ∧
      ex.time = z.2.clock + 1 ∧ ex.lane = lane ∧
      ex.source = digitSite ring root (src + (R - 1)) := by
  obtain ⟨hL', hb0, hbR, hb2R, hbF⟩ := hz
  obtain ⟨-, hroot, hbX, hbY⟩ := widthLeadEdge ref.toWidthDigitReference ref.singletonFixed hn
    root z.1 hL' e
  have he := L3.DigitEntryBridge.edgeSite ring root src R e (R - 1) hke
  subst he
  obtain ⟨ex, hex, hl, hs, ht⟩ :=
    (delEdgeFacts ring root (piD (ref.phys z.1)) R src hR hend hroot hbR hbF lane z.2 hbX hbY).2 T
      hD hE hL
  exact ⟨ex, hex, delOperand ring root (piD (ref.phys z.1)) R src hR hend hroot hbR hbF lane z.2
    hbX hbY ex hex, ht, hl, hs⟩

include hn hR hsrc hend in
/-- The delimiter-edge export of a coupled letter: its operand is the delimiter cell's output
atom, and the edge accepted a data packet into an empty carry-free input (port of `delRecv`).
Consumer: `wTailRun`. -/
theorem wDelRecv (z : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hzl : WidthCohortLayout ref.toWidthDigitReference root src R z.1) (e : Fin n)
    (hke : cohortEdgeOf root src R e = some (R - 1))
    (x : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hx : (digitReceiptLane lane (svcAt ring (piD (ref.phys z.1)) z.2 e)).exported = some x) :
    x.operand = (laneCells ring root lane src z.2.current (R - 1)).out.atom ∧
      ∃ T, (cohortProj ring root lane src R (piD (ref.phys z.1))).out (R - 1) = .D T ∧
        (cohortProj ring root lane src R (piD (ref.phys z.1))).inp R = .E ∧
        (cohortProj ring root lane src R (piD (ref.phys z.1))).live R = false := by
  obtain ⟨hL', hb0, hbR, hb2R, hbF⟩ := hzl
  obtain ⟨-, hroot, hbX, hbY⟩ := widthLeadEdge ref.toWidthDigitReference ref.singletonFixed hn
    root z.1 hL' e
  have he := L3.DigitEntryBridge.edgeSite ring root src R e (R - 1) hke
  subst he
  have hdel := delEdgeFacts ring root (piD (ref.phys z.1)) R src hR hend hroot hbR hbF lane z.2
    hbX hbY
  exact ⟨delOperand ring root (piD (ref.phys z.1)) R src hR hend hroot hbR hbF lane z.2 hbX hbY x
    hx, hdel.1 x hx⟩

include hn hR hsrc hend in
/-- A recorded sample at the source border: the read slot becomes the tail packet carrying the
fresh sampled atom (port of `sampleStep`). Consumer: `wTailRun`. -/
theorem wSampleStep
    (z : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hz : WidthCohortLayout ref.toWidthDigitReference root src R z.1) (e : Fin n)
    (hke : cohortEdgeOf root src R e = some 0)
    (s : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (hs : (digitReceiptLane lane (svcAt ring (piD (ref.phys z.1)) z.2 e)).sample = some s) :
    (laneCells ring root lane src (widthDigitAuditNext ref.toWidthDigitReference z e).2.current
        0).out = .packet (some (.sampled ⟨z.2.clock + 1, e, lane⟩)) ∧
      (cohortProj ring root lane src R
        (piD (ref.phys (widthDigitAuditNext ref.toWidthDigitReference z e).1))).out 0 =
          .D true := by
  have hU := L3.DigitEntryBridge.sampleU ring (piD (ref.phys z.1)) z.2 e lane s hs
  have he := L3.DigitEntryBridge.edgeSite ring root src R e 0 hke
  have h0 : (cohortProj ring root lane src R (piD (ref.phys z.1))).out 0 = .U := by
    rw [projOut ring root lane src R _ 0 (by omega), ← he]
    exact hU
  have hpipe := (wSrcRows ref hn root lane src R hR hsrc hend z hz e).2.1 0 hke (by omega)
  rw [h0] at hpipe
  refine ⟨(Prod.mk.inj hpipe).1, ?_⟩
  have hst := (widthCohortStep ref.toWidthDigitReference ref.singletonFixed hn root lane src R hR
    hsrc hend z.1 hz e).2
  show (cohortProj ring root lane src R
    (piD (ref.phys (ref.toWidthDigitReference.next z.1 e)))).out 0 = _
  rw [hst, hke]
  show (cohortEdge R _ 0).out 0 = _
  unfold cohortEdge
  rw [if_pos (by omega)]
  simp [cohortUpd, h0, bankRepairDigitPipeStep]

end Letter

/-! ### The tail sweep -/

section Assembly

variable {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
  (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src)
  (hend : src + 2 * R < n)
  (q0 : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
  (hq0 : WidthRunInv ring ref root lane src R q0) (hc0 : q0.2.clock = 0)
  (W : List (Fin n))

include hn hR hsrc hend hq0 in
/-- A source cell whose output ghost is a recorded tail sample holds the physical tail packet
(port of `physTail`). Consumer: `wTailRun`. -/
theorem wPhysTail (t' : Nat) (s0 : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (hs0 : DigitRecordedSample (wRunAt ref.toWidthDigitReference q0 W t').2 s0)
    (htl : s0.tail = true) (t p : Nat) (hp : p < R)
    (ho : (laneCells ring root lane src (wRunAt ref.toWidthDigitReference q0 W t).2.current
      p).out = .packet (some (.sampled s0.id))) (htt : t ≤ t') :
    (wLane ref root lane src R q0 W t).out p = .D true := by
  have hc := (wInvAt ref hn root lane src R hR hsrc hend q0 hq0 W t).1.2.2.2.2.1
  obtain ⟨T, hT, hok⟩ := L3.DigitEntryBridge.outPacketD (hc.1 p hp) ho
  have hfo := (wInvAt ref hn root lane src R hR hsrc hend q0 hq0 W t').1.2.1
  have := L3.DigitEntryBridge.tailBit ring root lane _ _
    (fun f hf => wFramesUpTo ref.toWidthDigitReference W q0 t t' htt f hf) hfo s0 hs0 htl T hok
  subst this
  exact hT

include hn hR hsrc hend hq0 hc0 in
/-- **The tail sweep (step 4b).** From the sample letter of the tail atom `a₀` to its export
letter, the tracked cell of the lane trace started at the sample (`p₀ = 0`) holds the output
ghost `a₀` and stays below `R` (a delimiter export of `a₀` before its recorded one would be a
second export of the same sample); at the export letter the tracked cell is the delimiter cell
and moves to `R`. Consumer: `strictCompletionCyc`. -/
theorem wTailRun (st : Nat → CohortLane) (ts : Nat)
    (hst : ∀ r, st r = wLane ref root lane src R q0 W (ts + 1 + r))
    (s0 : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (hs0 : DigitRecordedSample
      (wRunAt ref.toWidthDigitReference q0 W W.length).2 s0)
    (htl : s0.tail = true) (hsl : s0.id.lane = lane) (es : Fin n) (hes : W[ts]? = some es)
    (hσ : s0.id.time = ts + 1) (hsite : es = digitSite ring root (src + 0))
    (hsamp : (digitReceiptLane lane
      (svcAt ring (piD (ref.phys (wRunAt ref.toWidthDigitReference q0 W ts).1))
        (wRunAt ref.toWidthDigitReference q0 W ts).2 es)).sample = some s0)
    (hsite' : s0.id.site = es) (x0 : DigitExport (compileAdvice (ceilLogTwo n)) n) (tx : Nat)
    (ex : Fin n) (hexw : W[tx]? = some ex) (hx0t : x0.time = tx + 1)
    (hexe : ex = digitSite ring root (src + (R - 1)))
    (hxr : (digitReceiptLane lane
      (svcAt ring (piD (ref.phys (wRunAt ref.toWidthDigitReference q0 W tx).1))
        (wRunAt ref.toWidthDigitReference q0 W tx).2 ex)).exported = some x0)
    (hxo : x0.operand = some (.sampled s0.id))
    (huniq : ∀ x : DigitExport (compileAdvice (ceilLogTwo n)) n,
      DigitRecordedExport
        (wRunAt ref.toWidthDigitReference q0 W W.length).2 x →
      OnEdge ring root lane src R x → x.operand = some (.sampled s0.id) → x.time = x0.time)
    (hlt : ts < tx) (htx : tx < W.length) :
    cohortTok R (st 0) 0 = .pkt true ∧ (∀ r, ts + 1 + r ≤ tx → strictTrack R st 0 r < R) ∧
      strictTrack R st 0 (tx - ts) = R := by
  have hzs := (wInvAt ref hn root lane src R hR hsrc hend q0 hq0 W ts).1.1
  have hke0 : cohortEdgeOf root src R es = some 0 := by
    rw [hsite]
    exact cohortEdgeOfSite ring root src R hend 0 (by omega)
  obtain ⟨hg0, hp0⟩ := wSampleStep ref hn root lane src R hR hsrc hend _ hzs es hke0 s0 hsamp
  have hstep0 := wRunAtSucc ref.toWidthDigitReference W q0 ts es hes
  have hid : s0.id = ⟨ts + 1, es, lane⟩ := by rw [← hσ, ← hsite', ← hsl]
  rw [wClock ref q0 hc0 W ts (by omega), ← hid, ← hstep0] at hg0
  rw [← hstep0] at hp0
  have htok0 : cohortTok R (st 0) 0 = .pkt true := by
    rw [hst, cohortTokSrc _ (by omega : 0 < R)]
    show cohortTokOut ((cohortProj ring root lane src R
      (piD (ref.phys (wRunAt ref.toWidthDigitReference q0 W (ts + 1)).1))).out 0) = _
    rw [hp0]
    rfl
  have J : ∀ r, ts + 1 + r ≤ tx → strictTrack R st 0 r < R ∧
      (laneCells ring root lane src (wRunAt ref.toWidthDigitReference q0 W (ts + 1 + r)).2.current
        (strictTrack R st 0 r)).out = .packet (some (.sampled s0.id)) := by
    intro r
    induction r with
    | zero => intro _; exact ⟨by show 0 < R; omega, hg0⟩
    | succ r ih =>
      intro hr
      obtain ⟨hp, ho⟩ := ih (by omega)
      have ht : ts + 1 + r < W.length := by omega
      obtain ⟨e, he, hstep, hke⟩ := wStepAt ref root src R q0 W (ts + 1 + r) ht
      have hzt := (wInvAt ref hn root lane src R hR hsrc hend q0 hq0 W (ts + 1 + r)).1.1
      have hph := wPhysTail ref hn root lane src R hR hsrc hend q0 hq0 W W.length s0 hs0 htl
        (ts + 1 + r) _ hp ho (by omega)
      have hrows := wSrcRows ref hn root lane src R hR hsrc hend _ hzt e
      rw [← hstep] at hrows
      have hst1 : st (r + 1) = cohortLaneStep R (st r) (cohortEdgeOf root src R e) := by
        rw [hst, hst, ← hke]
        exact wLaneStep ref hn root lane src R hR hsrc hend q0 hq0 W (ts + 1 + r)
      have htr : strictTrack R st 0 (r + 1) = strictNext R (st (r + 1)) (strictTrack R st 0 r) :=
        rfl
      rcases L3.DigitEntryBridge.srcStep hrows hp ho hph with ⟨ho', htok⟩ | ⟨hp1, ho', htok⟩ | ⟨hp1, hkR, hE, hL⟩
      · have htok' : cohortTok R (st (r + 1)) (strictTrack R st 0 r) = .pkt true := by
          rw [hst1, hst]
          exact htok
        have e1 : strictTrack R st 0 (r + 1) = strictTrack R st 0 r := by
          rw [htr]
          unfold strictNext
          rw [if_pos hp, if_pos htok']
        rw [e1]
        exact ⟨hp, ho'⟩
      · have htok' : cohortTok R (st (r + 1)) (strictTrack R st 0 r) = .other := by
          rw [hst1, hst]
          exact htok
        have e1 : strictTrack R st 0 (r + 1) = strictTrack R st 0 r + 1 := by
          rw [htr]
          unfold strictNext
          rw [if_pos hp, if_neg (by rw [htok']; intro h; cases h)]
        rw [e1]
        exact ⟨hp1, ho'⟩
      · exfalso
        have hD : (cohortProj ring root lane src R
            (piD (ref.phys (wRunAt ref.toWidthDigitReference q0 W (ts + 1 + r)).1))).out (R - 1) =
              .D true := by
          rw [show R - 1 = strictTrack R st 0 r by omega]
          exact hph
        obtain ⟨x, hx, hxo', hxt, hxl, hxs⟩ :=
          wDelExport ref hn root lane src R hR hsrc hend _ hzt e hkR true hD hE hL
        have hrec := wRecExportAt ref q0 hc0 W (ts + 1 + r) ht e he x (by rw [hxl]; exact hx)
          (by rw [hxt, wClock ref q0 hc0 W (ts + 1 + r) (by omega)])
          (by rw [hxs]; exact (L3.DigitEntryBridge.edgeSite ring root src R e (R - 1) hkR).symm)
          W.length (by omega)
        have hop : x.operand = some (.sampled s0.id) := by
          rw [hxo', show R - 1 = strictTrack R st 0 r by omega, ho]
          rfl
        have := huniq x hrec ⟨hxl, hxs⟩ hop
        rw [hxt, wClock ref q0 hc0 W (ts + 1 + r) (by omega), hx0t] at this
        omega
  refine ⟨htok0, fun r hr => (J r hr).1, ?_⟩
  obtain ⟨hp, ho⟩ := J (tx - ts - 1) (by omega)
  rw [show ts + 1 + (tx - ts - 1) = tx by omega] at ho
  have hzx := wInvAt ref hn root lane src R hR hsrc hend q0 hq0 W tx
  have hkx : cohortEdgeOf root src R ex = some (R - 1) := by
    rw [hexe]
    exact cohortEdgeOfSite ring root src R hend (R - 1) (by omega)
  obtain ⟨hxo', T, hD, hE, hL⟩ :=
    wDelRecv ref hn root lane src R hR hsrc hend _ hzx.1.1 ex hkx x0 hxr
  have hpR : strictTrack R st 0 (tx - ts - 1) = R - 1 := by
    apply hzx.1.2.2.2.2.2.1 _ _ s0.id
    · rw [L3.DigitEntryBridge.trackedSrc ring root lane src R _ _ hp, ho]
      rfl
    · rw [L3.DigitEntryBridge.trackedSrc ring root lane src R _ _ (by omega), ← hxo', hxo]
  rw [show tx - ts = tx - ts - 1 + 1 by omega]
  show strictNext R (st (tx - ts - 1 + 1)) (strictTrack R st 0 (tx - ts - 1)) = R
  have hst2 : st (tx - ts - 1 + 1) =
      cohortEdge R (wLane ref root lane src R q0 W tx) (R - 1) := by
    rw [hst, show ts + 1 + (tx - ts - 1 + 1) = tx + 1 by omega]
    exact wLaneEdge ref hn root lane src R hR hsrc hend q0 hq0 W tx (R - 1)
      (by rw [wKeOf root src R W hexw]; exact hkx)
  have hv : cohortTok R (cohortEdge R (wLane ref root lane src R q0 W tx) (R - 1)) (R - 1) ≠
      .pkt true := L3.DigitEntryBridge.delVacate (show R - 1 + 1 = R by omega) hD hE hL
  unfold strictNext
  rw [hpR, if_pos (by omega : R - 1 < R), hst2, if_neg hv]
  omega

end Assembly

/-! ### The younger cells behind the strict tail -/

section Young

variable {n : Nat}

/-- The source cells strictly behind the tracked cell `p` carry atoms of class `P q` (`P = SPin`:
read at their own cell). Consumer: `youngTailStep`, `wSweepAtExport`. -/
def YoungTail (R : Nat) (P : Nat → DigitAtom n → Prop) (tr : Nat → Option (DigitAtom n))
    (p : Nat) : Prop :=
  ∀ q, q < p → q < R → ∀ a, tr q = some a → P q a

variable {R : Nat}

/-- Under one lane letter the strict tail stays, or its own edge is drawn with an empty cell
ahead. Consumer: `youngTailStep`. -/
theorem tailStayOrHop {s : CohortLane} {p : Nat} (h : TailSweep R s p)
    (ke : Option Nat) :
    cohortTok R (cohortLaneStep R s ke) p = .pkt true ∨
      (ke = some p ∧ cohortTok R s (p + 1) = .empty) := by
  obtain ⟨hp, ht, hY⟩ := h
  have hocc : cohortTok R s p ≠ .empty := by rw [ht]; intro hc; cases hc
  have hx : cohortTokOut (s.out p) = .pkt true := by rw [← cohortTokSrc s hp]; exact ht
  cases ke with
  | none => exact Or.inl ht
  | some k =>
    show cohortTok R (cohortEdge R s k) p = .pkt true ∨ _
    by_cases hk : k = p
    · subst hk
      by_cases he : cohortTok R s (k + 1) = .empty
      · exact Or.inr ⟨rfl, he⟩
      · left
        by_cases h1 : k + 1 < R
        · obtain ⟨e1, -⟩ := cohortTokPipe R k s h1
          have hy : cohortTokOut (s.out (k + 1)) ≠ .empty := by
            rw [← cohortTokSrc s h1]; exact he
          rw [e1, tailPipeStay _ _ _ true hx hy]
        · have hkR : k + 1 = R := by omega
          obtain ⟨e1, -⟩ := cohortTokDel R k s hkR
          have hy : cohortTokIn (s.inp (k + 1)) (s.live (k + 1)) ≠ .empty := by
            rw [← cohortTokTgt s (by omega : R ≤ k + 1)]; exact he
          rw [e1, tailDelStay _ _ _ true hx hy]
    · left
      by_cases hk1 : p = k + 1
      · have h1 : k + 1 < R := by omega
        obtain ⟨-, e2⟩ := cohortTokPipe R k s h1
        have hxk := hY k (by omega) (by omega)
        rw [cohortTokSrc s (by omega : k < R)] at hxk
        have hy : cohortTokOut (s.out (k + 1)) ≠ .empty := by
          rw [← cohortTokSrc s h1, ← hk1]; exact hocc
        rw [hk1, e2, (rearmPipeKeep (decide (k = 0)) _ _ hxk hy).2, ← cohortTokSrc s h1, ← hk1]
        exact ht
      · rw [cohortTokFrame R k p s (fun h => hk h.symm) hk1]
        exact ht

/-- The sweep continues while the tracked cell stays in the source. Consumer:
`wSweepAtExport`. -/
theorem tailSweepNext (hR : 2 ≤ R) {s : CohortLane} {p : Nat} (h : TailSweep R s p)
    (ke : Option Nat) (hlt : strictNext R (cohortLaneStep R s ke) p < R) :
    TailSweep R (cohortLaneStep R s ke) (strictNext R (cohortLaneStep R s ke) p) := by
  have hp := h.1
  unfold strictNext at hlt ⊢
  rw [if_pos hp] at hlt ⊢
  cases ke with
  | none =>
    change TailSweep R s (if cohortTok R s p = .pkt true then p else p + 1)
    rw [if_pos h.2.1]
    exact h
  | some k =>
    show TailSweep R (cohortEdge R s k)
      (if cohortTok R (cohortEdge R s k) p = .pkt true then p else p + 1)
    change (if cohortTok R (cohortEdge R s k) p = .pkt true then p else p + 1) < R at hlt
    rcases tailSweepEdge hR h k with ⟨h1, h2⟩ | ⟨h1, ⟨-, h4⟩ | ⟨h3, -, -⟩⟩
    · rw [if_pos h1]
      exact h2
    · rw [if_neg (by rw [h1]; intro hc; cases hc)]
      exact h4
    · rw [if_neg (by rw [h1]; intro hc; cases hc)] at hlt
      omega

/-- When the tracked cell leaves the source the tail was exported: every source cell is a younger
slot and target cell `R` is occupied. Consumer: `wSweepAtExport`. -/
theorem tailSweepExit (hR : 2 ≤ R) {s : CohortLane} {p : Nat} (h : TailSweep R s p)
    (ke : Option Nat) (heq : strictNext R (cohortLaneStep R s ke) p = R) :
    CohortYounger R (cohortLaneStep R s ke) R ∧
      cohortTok R (cohortLaneStep R s ke) R ≠ .empty := by
  have hp := h.1
  unfold strictNext at heq
  rw [if_pos hp] at heq
  cases ke with
  | none =>
    change (if cohortTok R s p = .pkt true then p else p + 1) = R at heq
    rw [if_pos h.2.1] at heq
    omega
  | some k =>
    change (if cohortTok R (cohortEdge R s k) p = .pkt true then p else p + 1) = R at heq
    rcases tailSweepEdge hR h k with ⟨h1, -⟩ | ⟨h1, ⟨h3, -⟩ | ⟨-, h4, h5⟩⟩
    · rw [if_pos h1] at heq
      omega
    · rw [if_neg (by rw [h1]; intro hc; cases hc)] at heq
      omega
    · refine ⟨h4, ?_⟩
      show cohortTok R (cohortEdge R s k) R ≠ .empty
      rw [h5]
      intro hc
      cases hc

/-- **One letter on the younger cells behind the strict tail**: an atom behind the tail never
moves (the cell ahead is occupied), the tail's hop leaves no atom, and a fresh read at cell `q`
is of class `P' q`. Consumer: `wSweepAtExport`. -/
theorem youngTailStep {t k p : Nat} {s : CohortLane} {ke : Option Nat}
    {tr tr' : Nat → Option (DigitAtom n)} {f : DigitStamp n} {P P' : Nat → DigitAtom n → Prop}
    (hR : 2 ≤ R) (hT : TailSweep R s p) (hTB : TimeBound tr t) (hft : f.time = t + 1)
    (hfr : ∀ q, q ≠ k → q ≠ k + 1 → tr' q = tr q)
    (hm : MoveOk (tr k) (tr (k + 1)) (tr' k) (tr' (k + 1)) (some (.sampled f)))
    (hF : k < R → tr' k = some (.sampled f) → s.out k = .U ∨ tr k = some (.sampled f))
    (hM : k + 1 < R → s.out (k + 1) ≠ .E → tr' (k + 1) = tr (k + 1))
    (hH : k < R → ∀ T, s.out k = .D T → cohortTok R s (k + 1) = .empty → tr' k = none)
    (hK : ∀ k', ke = some k' → k' = k)
    (hPP : ∀ q a, P q a → P' q a) (hfresh : k < R → s.out k = .U → P' k (.sampled f))
    (h : YoungTail R P tr p) :
    YoungTail R P' tr' (strictNext R (cohortLaneStep R s ke) p) := by
  intro q hq hqR a ha
  have hT' := hT
  obtain ⟨hp, ht, hY⟩ := hT
  have hnext : strictNext R (cohortLaneStep R s ke) p =
      if cohortTok R (cohortLaneStep R s ke) p = .pkt true then p else p + 1 := by
    unfold strictNext
    rw [if_pos hp]
  have hmove : q = p → ke = some p ∧ cohortTok R s (p + 1) = .empty := by
    intro hqp
    rcases tailStayOrHop hT' ke with h1 | h1
    · rw [hnext, if_pos h1] at hq
      omega
    · exact h1
  have hqle : q ≤ p := by
    rw [hnext] at hq
    split at hq <;> omega
  have hnE : ∀ r, r ≤ p → s.out r ≠ .E := by
    intro r hr hE
    by_cases hrp : r = p
    · subst hrp
      rw [cohortTokSrc s hp, hE] at ht
      cases ht
    · rcases hY r (by omega) (by omega) with h1 | h1 <;>
        rw [cohortTokSrc s (by omega), hE] at h1 <;> cases h1
  have hold : tr q = some a → tr' q = some a → P' q a := by
    intro h0 h0'
    by_cases hqp : q < p
    · exact hPP _ _ (h q hqp hqR a h0)
    · exfalso
      have hqp' : q = p := by omega
      obtain ⟨hke, he⟩ := hmove hqp'
      have hkp := hK p hke
      subst hkp hqp'
      have hD : s.out q = .D true := by
        rw [cohortTokSrc s hp] at ht
        exact outPktOf ht
      rw [hH hp true hD he] at h0'
      cases h0'
  by_cases hq1 : q = k
  · subst hq1
    rcases (hm a).1 ha with h0 | h0
    · exact hold h0 ha
    · have hf : a = .sampled f := (Option.some.inj h0).symm
      subst hf
      rcases hF hqR ha with hU | hold'
      · exact hfresh hqR hU
      · exact absurd hold' (freshNot hTB hft q)
  · by_cases hq2 : q = k + 1
    · have h1 := hM (by omega) (by rw [← hq2]; exact hnE q hqle)
      rw [← hq2] at h1
      rw [h1] at ha
      exact hold ha (by rw [h1]; exact ha)
    · have h1 := hfr q hq1 hq2
      rw [h1] at ha
      exact hold ha (by rw [h1]; exact ha)

/-- `YoungTail` at threshold `R` is `ChosenInv` at the cycle start `lam = 0`. Consumer:
`L3.StageMEntryCyc`. -/
theorem chosenOfYoungTail {P : Nat → DigitAtom n → Prop} {tr : Nat → Option (DigitAtom n)}
    (h : YoungTail R P tr R) : ChosenInv R P tr (fun _ => 0) := by
  intro i hi hpos a ha
  rw [cohortPosZero] at hpos ha
  exact h (R - 1 - i) (by omega) hpos a ha

end Young

/-! ### The sweep on the coupled run, up to the tail export -/

section Sweep

variable {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
  (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src)
  (hend : src + 2 * R < n)
  (q0 : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
  (hq0 : WidthRunInv ring ref root lane src R q0) (hc0 : q0.2.clock = 0)
  (W : List (Fin n))

include hn hR hsrc hend hq0 in
/-- One coupled letter on the sweep: the younger cells keep their pin. Consumer:
`wSweepAtExport`. -/
theorem wYoungStep (t p : Nat) (ht : t < W.length)
    (hT : TailSweep R (wLane ref root lane src R q0 W t) p)
    (hY : YoungTail R (SPin ring root lane src (wRunAt ref.toWidthDigitReference q0 W t).2)
      (tracked ring root lane src R (wRunAt ref.toWidthDigitReference q0 W t).2) p) :
    YoungTail R (SPin ring root lane src (wRunAt ref.toWidthDigitReference q0 W (t + 1)).2)
      (tracked ring root lane src R (wRunAt ref.toWidthDigitReference q0 W (t + 1)).2)
      (strictNext R (wLane ref root lane src R q0 W (t + 1)) p) := by
  obtain ⟨e, -, hstep, hke⟩ := wStepAt ref root src R q0 W t ht
  have hinv := wInvAt ref hn root lane src R hR hsrc hend q0 hq0 W t
  have hlane := wLaneStep ref hn root lane src R hR hsrc hend q0 hq0 W t
  rw [hke] at hlane
  rw [hlane, hstep]
  obtain ⟨k, hfr, hm, hF, hM, hH, hK, hfresh⟩ :=
    wTrackedStep ref hn root lane src R hR hsrc hend _ hinv.1.1 e
  exact youngTailStep hR hT hinv.1.2.2.2.2.2.2.1 rfl hfr hm hF hM hH hK
    (sPinStep ring root lane src _ _ e) hfresh hY

include hn hR hsrc hend hq0 in
/-- **The source at the tail export.** Along the strict tail's sweep (the lane trace `st` from the
sample letter `ts`, tracked cell `strictTrack`, as produced by `wTailRun`), right after the export
letter `tx` every source cell is a younger slot, target cell `R` is occupied, and every source atom
was read at its own cell. Consumer: `L3.StageMEntryCyc` (F1 chosen half, F2). -/
theorem wSweepAtExport (st : Nat → CohortLane) (ts tx : Nat)
    (hst : ∀ r, st r = wLane ref root lane src R q0 W (ts + 1 + r))
    (hlt : ts < tx) (htx : tx < W.length)
    (htok0 : cohortTok R (st 0) 0 = .pkt true)
    (hbefore : ∀ r, ts + 1 + r ≤ tx → strictTrack R st 0 r < R)
    (hV0 : strictTrack R st 0 (tx - ts) = R) :
    CohortYounger R (wLane ref root lane src R q0 W (tx + 1)) R ∧
      cohortTok R (wLane ref root lane src R q0 W (tx + 1)) R ≠ .empty ∧
      YoungTail R (SPin ring root lane src (wRunAt ref.toWidthDigitReference q0 W (tx + 1)).2)
        (tracked ring root lane src R (wRunAt ref.toWidthDigitReference q0 W (tx + 1)).2) R := by
  have hstep : ∀ r, st (r + 1) = cohortLaneStep R (st r) (wKe root src R W (ts + 1 + r)) := by
    intro r
    rw [hst, hst, show ts + 1 + (r + 1) = ts + 1 + r + 1 by omega]
    exact wLaneStep ref hn root lane src R hR hsrc hend q0 hq0 W (ts + 1 + r)
  have claim : ∀ r, ts + 1 + r ≤ tx → TailSweep R (st r) (strictTrack R st 0 r) ∧
      YoungTail R (SPin ring root lane src (wRunAt ref.toWidthDigitReference q0 W (ts + 1 + r)).2)
        (tracked ring root lane src R (wRunAt ref.toWidthDigitReference q0 W (ts + 1 + r)).2)
        (strictTrack R st 0 r) := by
    intro r
    induction r with
    | zero =>
      intro _
      exact ⟨tailSampleStart hR htok0, fun q hq => absurd hq (Nat.not_lt_zero q)⟩
    | succ r ih =>
      intro hr
      obtain ⟨hT, hY⟩ := ih (by omega)
      have htr : strictTrack R st 0 (r + 1) = strictNext R (st (r + 1)) (strictTrack R st 0 r) :=
        rfl
      refine ⟨?_, ?_⟩
      · rw [htr, hstep r]
        rw [hstep r] at htr
        have hb := hbefore (r + 1) hr
        rw [htr] at hb
        exact tailSweepNext hR hT _ hb
      · rw [htr, show ts + 1 + (r + 1) = ts + 1 + r + 1 by omega, hst (r + 1),
          show ts + 1 + (r + 1) = ts + 1 + r + 1 by omega]
        rw [hst r] at hT
        exact wYoungStep ref hn root lane src R hR hsrc hend q0 hq0 W (ts + 1 + r) _ (by omega) hT hY
  obtain ⟨hT, hY⟩ := claim (tx - ts - 1) (by omega)
  have hTx : TailSweep R (wLane ref root lane src R q0 W tx) (strictTrack R st 0 (tx - ts - 1)) := by
    rw [hst, show ts + 1 + (tx - ts - 1) = tx by omega] at hT
    exact hT
  have hYx := hY
  rw [show ts + 1 + (tx - ts - 1) = tx by omega] at hYx
  have heq : strictNext R (wLane ref root lane src R q0 W (tx + 1))
      (strictTrack R st 0 (tx - ts - 1)) = R := by
    have h : strictTrack R st 0 (tx - ts - 1 + 1) =
        strictNext R (st (tx - ts - 1 + 1)) (strictTrack R st 0 (tx - ts - 1)) := rfl
    rw [hst (tx - ts - 1 + 1), show ts + 1 + (tx - ts - 1 + 1) = tx + 1 by omega,
      show tx - ts - 1 + 1 = tx - ts by omega, hV0] at h
    exact h.symm
  have hY' := wYoungStep ref hn root lane src R hR hsrc hend q0 hq0 W tx _ htx hTx hYx
  rw [heq] at hY'
  have hlane := wLaneStep ref hn root lane src R hR hsrc hend q0 hq0 W tx
  rw [hlane] at heq
  obtain ⟨h1, h2⟩ := tailSweepExit hR hTx _ heq
  rw [← hlane] at h1 h2
  exact ⟨h1, h2, hY'⟩

end Sweep

end L3.StageMEntryRun

#print axioms L3.StageMEntryRun.wRunFrames
#print axioms L3.StageMEntryRun.wFrameTime
#print axioms L3.StageMEntryRun.wFramesUpTo
#print axioms L3.StageMEntryRun.wTrackedStep
#print axioms L3.StageMEntryRun.wTailRun
#print axioms L3.StageMEntryRun.youngTailStep
#print axioms L3.StageMEntryRun.wSweepAtExport
