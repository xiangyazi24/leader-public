import Leader.L3.StageM.EntryCarryRows

/-!
# The strict cohort packed at its targets at the tail export: assembly

`wPackedAtExport`: right after the export of the strict tail sample, target cell `R + m` holds the
strict atom `a_m` as a pending or settled input with tail bit `m = 0`, and the settled cells form a
top run (`CohortArrived`, `CohortSettledTop`). The route is the one of `L3.StageMEntryCarryRows`; this
module tracks the strict atoms along the coupled run (`wBackRange`, `wPassStep`,
`wSettledGhost`, `wOtherRun`, `wSettledTopRun`) and assembles the three clauses.
-/

namespace L3.StageMEntryPack

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
open L3.StageMEntryRun
open L3.StageMEntryCarryRows

section Generic

variable {c : Compiled} {n : Nat}

/-- On a target cell the tracked atom is the input atom. Consumer: the tracking lemmas. -/
theorem trackedTgt (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (A : DigitAudit c n) (q : Nat) (h1 : R ≤ q) (h2 : q < 2 * R) :
    tracked ring root lane src R A q = inA ring root lane src A q := by
  unfold tracked trackedAt inA
  rw [if_neg (by omega), if_pos h2]

/-- A tracked sampled atom carries the tail bit of its recorded sample. Consumer:
`wPackedAtExport`. -/
theorem tailBitEq {R src : Nat} (ring : DirectedRing n) (root : Fin n) (lane : DigitLane)
    (A Af : DigitAudit c n) (hfin : ∀ f, f ∈ A.frames → f ∈ Af.frames)
    (hfo : AuditFrameOrder Af) (s0 : DigitSample c n) (hs0 : DigitRecordedSample Af s0)
    (T : Bool) (hok : GhostOk ring root lane src R (InheritedOk lane) A T (.sampled s0.id)) :
    T = s0.tail := by
  rcases hok with ⟨site, slot, h⟩ | ⟨s, hs, hrec, htail, -⟩
  · cases h
  · obtain ⟨f, hf, h1⟩ := hrec
    have hs' : s = s0 := sampleUnique Af hfo s s0 ⟨f, hfin f hf, h1⟩ hs0
      (DigitAtom.sampled.inj hs).symm
    rw [← htail, hs']

/-- An input cell holding an atom, not live or tombstone, is pending or settled with the
provenance of its tail bit. Consumer: `wPackedAtExport`. -/
theorem inTokOfSome {Ok : Bool → DigitAtom n → Prop} (i : BankRepairDigitInSh) (l : Bool)
    (o : Option (DigitAtom n)) (a : DigitAtom n) (hc : InCorr Ok i o) (ho : o = some a)
    (hne : cohortTokIn i l ≠ .other) :
    ∃ T, (cohortTokIn i l = .pkt T ∨ cohortTokIn i l = .settled T) ∧ Ok T a := by
  subst ho
  cases i with
  | E => simp [InCorr] at hc
  | X => cases l <;> exact absurd rfl hne
  | P T =>
    cases l
    · exact ⟨T, Or.inl rfl, hc⟩
    · exact absurd rfl hne
  | S T =>
    cases l
    · exact ⟨T, Or.inr rfl, hc⟩
    · exact absurd rfl hne

/-- The last change of a property before a time where it holds: it held all along since `a`, or
it failed at some `f ≥ a` and held at every later time up to `b`. Consumer: `wPackedAtExport`
(the letter at which a settled target cell formed). -/
theorem lastChange (P : Nat → Prop) (a b : Nat) (hab : a ≤ b) (hb : P b) :
    (∀ t, a ≤ t → t ≤ b → P t) ∨ ∃ f, a ≤ f ∧ f < b ∧ ¬ P f ∧ ∀ t, f < t → t ≤ b → P t := by
  have key : ∀ d, P (a + d) → (∀ t, a ≤ t → t ≤ a + d → P t) ∨
      ∃ f, a ≤ f ∧ f < a + d ∧ ¬ P f ∧ ∀ t, f < t → t ≤ a + d → P t := by
    intro d
    induction d with
    | zero =>
      intro h
      left
      intro t h1 h2
      rw [show t = a + 0 by omega]
      exact h
    | succ d ih =>
      intro h
      rcases Classical.em (P (a + d)) with hd | hd
      · rcases ih hd with hall | ⟨f, h1, h2, h3, h4⟩
        · left
          intro t h1 h2
          rcases Nat.lt_or_ge (a + d) t with h' | h'
          · rw [show t = a + (d + 1) by omega]
            exact h
          · exact hall t h1 h'
        · right
          refine ⟨f, h1, by omega, h3, fun t h5 h6 => ?_⟩
          rcases Nat.lt_or_ge (a + d) t with h' | h'
          · rw [show t = a + (d + 1) by omega]
            exact h
          · exact h4 t h5 h'
      · right
        refine ⟨a + d, by omega, by omega, hd, fun t h5 h6 => ?_⟩
        rw [show t = a + (d + 1) by omega]
        exact h
  have := key (b - a) (by rw [show a + (b - a) = b by omega]; exact hb)
  rw [show a + (b - a) = b by omega] at this
  exact this

end Generic

section Track

variable {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
  (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src)
  (hend : src + 2 * R < n)
  (q0 : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
  (hq0 : WidthRunInv ring ref root lane src R q0)
  (hi0 : q0.2 = digitAuditInitial (piD (ref.phys q0.1))) (hc0 : q0.2.clock = 0)
  (W : List (Fin n))

include hi0 hc0 in
/-- A recorded export of the final audit, with its letter. Consumer: `wRecordedAt`,
`L3.StageMEntryCyc`. -/
theorem wExportLetter (x : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hx : DigitRecordedExport (wRunAt ref.toWidthDigitReference q0 W W.length).2 x) :
    ∃ t e, W[t]? = some e ∧ x.time = t + 1 ∧ e = x.source ∧
      (digitReceiptLane x.lane (svcAt ring (piD (ref.phys (wRunAt ref.toWidthDigitReference q0 W t).1))
        (wRunAt ref.toWidthDigitReference q0 W t).2 e)).exported = some x := by
  obtain ⟨f, hf, h1, h2, h3⟩ := hx
  rw [wRunAtLen ref.toWidthDigitReference W q0 W.length (Nat.le_refl _)] at hf
  obtain ⟨t, e, he, hft, rfl⟩ := wFrameTime ref.toWidthDigitReference W q0 (by rw [hi0]; rfl) hc0 f hf
  exact ⟨t, e, he, h1.symm.trans hft, h2, h3⟩

include hi0 hc0 in
/-- A recorded export of the final audit is recorded from its own time on. Consumer:
`wBackRange`. -/
theorem wRecordedAt (x : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hx : DigitRecordedExport (wRunAt ref.toWidthDigitReference q0 W W.length).2 x) (t : Nat)
    (ht : x.time ≤ t) : DigitRecordedExport (wRunAt ref.toWidthDigitReference q0 W t).2 x := by
  obtain ⟨t0, e, he, htime, hs, hexp⟩ := wExportLetter ref q0 hi0 hc0 W x hx
  have ht0 : t0 < W.length := by
    rcases Nat.lt_or_ge t0 W.length with h | h
    · exact h
    · rw [List.getElem?_eq_none_iff.mpr h] at he
      cases he
  exact wRecExportAt ref q0 hc0 W t0 ht0 e he x hexp htime hs.symm t (by omega)

include hn hR hsrc hend hq0 hc0 in
/-- **One letter back**: a sampled atom whose delimiter export is recorded sits, one letter
earlier, at the same target cell or at the cell below (it never re-enters the source). Consumer:
`wBackRange`. -/
theorem wBackStep (t : Nat) (ht : t < W.length) (sid : DigitStamp n)
    (x : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hx : DigitRecordedExport (wRunAt ref.toWidthDigitReference q0 W t).2 x)
    (hon : OnEdge ring root lane src R x) (hop : x.operand = some (.sampled sid))
    (htime : sid.time ≤ t) (q : Nat)
    (h : tracked ring root lane src R (wRunAt ref.toWidthDigitReference q0 W (t + 1)).2 q =
      some (.sampled sid)) :
    ∃ p, R ≤ p ∧ p ≤ q ∧
      tracked ring root lane src R (wRunAt ref.toWidthDigitReference q0 W t).2 p =
        some (.sampled sid) := by
  obtain ⟨e, -, hstep, -⟩ := wStepAt ref root src R q0 W t ht
  rw [hstep] at h
  have hinv := wInvAt ref hn root lane src R hR hsrc hend q0 hq0 W t
  obtain ⟨k, hfr, hm, -⟩ := wTrackedStep ref hn root lane src R hR hsrc hend _ hinv.1.1 e
  rcases moveOrigin hfr hm q _ h with ⟨p, hpq, hp, -⟩ | ⟨-, hf⟩
  · refine ⟨p, ?_, hpq, hp⟩
    by_cases hp' : p < R
    · exact absurd hop (hinv.1.2.2.2.2.2.2.2.2.1 p sid x hp' hp hx hon)
    · omega
  · exfalso
    have hs := DigitAtom.sampled.inj (Option.some.inj hf)
    have h1 : (wRunAt ref.toWidthDigitReference q0 W t).2.clock + 1 = sid.time :=
      congrArg DigitStamp.time hs
    rw [wClock ref q0 hc0 W t (by omega)] at h1
    omega

include hn hR hsrc hend hq0 hi0 hc0 in
/-- **Back along the run**: from a later prefix to an earlier one after the atom's export, the
atom sits at a target cell no higher. Consumer: `wPackedAtExport`. -/
theorem wBackRange (t1 t2 : Nat) (h12 : t1 ≤ t2) (ht2 : t2 ≤ W.length) (sid : DigitStamp n)
    (x : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hx : DigitRecordedExport (wRunAt ref.toWidthDigitReference q0 W W.length).2 x)
    (hxt : x.time ≤ t1) (hon : OnEdge ring root lane src R x)
    (hop : x.operand = some (.sampled sid)) (htime : sid.time ≤ t1) (q : Nat) (hRq : R ≤ q)
    (h : tracked ring root lane src R (wRunAt ref.toWidthDigitReference q0 W t2).2 q =
      some (.sampled sid)) :
    ∃ p, R ≤ p ∧ p ≤ q ∧
      tracked ring root lane src R (wRunAt ref.toWidthDigitReference q0 W t1).2 p =
        some (.sampled sid) := by
  have key : ∀ d, ∀ q, R ≤ q → t1 + d ≤ W.length →
      tracked ring root lane src R (wRunAt ref.toWidthDigitReference q0 W (t1 + d)).2 q =
        some (.sampled sid) →
      ∃ p, R ≤ p ∧ p ≤ q ∧
        tracked ring root lane src R (wRunAt ref.toWidthDigitReference q0 W t1).2 p =
          some (.sampled sid) := by
    intro d
    induction d with
    | zero => intro q hq _ hh; exact ⟨q, hq, Nat.le_refl q, hh⟩
    | succ d ih =>
      intro q hq hd hh
      rw [show t1 + (d + 1) = t1 + d + 1 by omega] at hh
      obtain ⟨p, hp1, hp2, hp⟩ := wBackStep ref hn root lane src R hR hsrc hend q0 hq0 hc0 W
        (t1 + d) (by omega) sid x (wRecordedAt ref q0 hi0 hc0 W x hx (t1 + d) (by omega)) hon hop
        (by omega) q hh
      obtain ⟨p', h1, h2, h3⟩ := ih p hp1 (by omega) hp
      exact ⟨p', h1, by omega, h3⟩
  have h' := h
  rw [show t2 = t1 + (t2 - t1) by omega] at h'
  exact key (t2 - t1) q hRq (by omega) h'

include hn hR hsrc hend hq0 hc0 in
/-- **One letter back on the cell above**: an atom at `q + 1` was at `q + 1` one letter earlier,
unless it hopped from `q`. Consumer: `wPackedAtExport` (the cell above a forming settled cell). -/
theorem wPassStep (t : Nat) (ht : t < W.length) (sid : DigitStamp n) (htime : sid.time ≤ t)
    (q : Nat)
    (h : tracked ring root lane src R (wRunAt ref.toWidthDigitReference q0 W (t + 1)).2 (q + 1) =
      some (.sampled sid))
    (hne : tracked ring root lane src R (wRunAt ref.toWidthDigitReference q0 W t).2 q ≠
      some (.sampled sid)) :
    tracked ring root lane src R (wRunAt ref.toWidthDigitReference q0 W t).2 (q + 1) =
      some (.sampled sid) := by
  obtain ⟨e, -, hstep, -⟩ := wStepAt ref root src R q0 W t ht
  rw [hstep] at h
  have hinv := wInvAt ref hn root lane src R hR hsrc hend q0 hq0 W t
  obtain ⟨k, hfr, hm, -⟩ := wTrackedStep ref hn root lane src R hR hsrc hend _ hinv.1.1 e
  rcases moveOrigin hfr hm (q + 1) _ h with ⟨p, hpq, hp, hne'⟩ | ⟨-, hf⟩
  · by_cases hpe : p = q + 1
    · rw [← hpe]
      exact hp
    · obtain ⟨h1, h2, -⟩ := hne' hpe
      exfalso
      apply hne
      rw [show q = p by omega]
      exact hp
  · exfalso
    have hs := DigitAtom.sampled.inj (Option.some.inj hf)
    have h1 : (wRunAt ref.toWidthDigitReference q0 W t).2.clock + 1 = sid.time :=
      congrArg DigitStamp.time hs
    rw [wClock ref q0 hc0 W t (by omega)] at h1
    omega

include hn hR hsrc hend hq0 in
/-- A target cell settled before and after a letter keeps its tracked atom. Consumer:
`wPackedAtExport`. -/
theorem wSettledGhost (t : Nat) (ht : t < W.length) (q : Nat) (h1 : R ≤ q) (h2 : q < 2 * R)
    (T T' : Bool) (hT : cohortTok R (wLane ref root lane src R q0 W t) q = .settled T)
    (hT' : cohortTok R (wLane ref root lane src R q0 W (t + 1)) q = .settled T') :
    tracked ring root lane src R (wRunAt ref.toWidthDigitReference q0 W (t + 1)).2 q =
      tracked ring root lane src R (wRunAt ref.toWidthDigitReference q0 W t).2 q := by
  rw [trackedTgt ring root lane src R _ q h1 h2, trackedTgt ring root lane src R _ q h1 h2]
  obtain ⟨e, -, hstep, hke⟩ := wStepAt ref root src R q0 W t ht
  have hm := wMoveH ref hn root lane src R hR hsrc hend _
    (wInvAt ref hn root lane src R hR hsrc hend q0 hq0 W t).1.1 e
  have hl := wLaneStep ref hn root lane src R hR hsrc hend q0 hq0 W t
  rw [hke] at hl
  rw [hl] at hT'
  rw [hstep]
  exact tgtSettledKeep hm q h1 h2 T T' hT hT'

include hn hR hsrc hend hq0 in
/-- A live or tombstone target cell that keeps a tracked atom stays live or tombstone along the
run. Consumer: `wPackedAtExport`. -/
theorem wOtherRun (t1 t2 : Nat) (h12 : t1 ≤ t2) (ht2 : t2 ≤ W.length) (q : Nat) (h1 : R ≤ q)
    (h2 : q < 2 * R) (hT : cohortTok R (wLane ref root lane src R q0 W t1) q = .other)
    (hg : ∀ t, t1 ≤ t → t ≤ t2 → ∃ b,
      tracked ring root lane src R (wRunAt ref.toWidthDigitReference q0 W t).2 q = some b) :
    cohortTok R (wLane ref root lane src R q0 W t2) q = .other := by
  have key : ∀ d, t1 + d ≤ t2 → cohortTok R (wLane ref root lane src R q0 W (t1 + d)) q = .other := by
    intro d
    induction d with
    | zero => intro _; exact hT
    | succ d ih =>
      intro hd
      have h0 := ih (by omega)
      rw [show t1 + (d + 1) = t1 + d + 1 by omega]
      obtain ⟨e, -, hstep, hke⟩ := wStepAt ref root src R q0 W (t1 + d) (by omega)
      have hm := wMoveH ref hn root lane src R hR hsrc hend _
        (wInvAt ref hn root lane src R hR hsrc hend q0 hq0 W (t1 + d)).1.1 e
      have hl := wLaneStep ref hn root lane src R hR hsrc hend q0 hq0 W (t1 + d)
      rw [hke] at hl
      rw [hl]
      obtain ⟨b, hb⟩ := hg (t1 + d + 1) (by omega) (by omega)
      rw [trackedTgt ring root lane src R _ q h1 h2, hstep] at hb
      exact tgtOtherKeep hR hm q h1 h2 h0 b hb
  have := key (t2 - t1) (by omega)
  rwa [show t1 + (t2 - t1) = t2 by omega] at this

include hn hR hsrc hend hq0 in
/-- While a cell stays settled, a settled tail-free cell above it stays settled. Consumer:
`wPackedAtExport`. -/
theorem wSettledTopRun (t1 t2 : Nat) (h12 : t1 ≤ t2) (q : Nat)
    (h1 : R < q) (h2 : q + 1 < 2 * R)
    (hx : ∀ t, t1 ≤ t → t ≤ t2 → ∃ T, cohortTok R (wLane ref root lane src R q0 W t) q = .settled T)
    (hy : cohortTok R (wLane ref root lane src R q0 W t1) (q + 1) = .settled false) :
    cohortTok R (wLane ref root lane src R q0 W t2) (q + 1) = .settled false := by
  have key : ∀ d, t1 + d ≤ t2 →
      cohortTok R (wLane ref root lane src R q0 W (t1 + d)) (q + 1) = .settled false := by
    intro d
    induction d with
    | zero => intro _; exact hy
    | succ d ih =>
      intro hd
      have h0 := ih (by omega)
      rw [show t1 + (d + 1) = t1 + d + 1 by omega,
        wLaneStep ref hn root lane src R hR hsrc hend q0 hq0 W (t1 + d)]
      obtain ⟨T, hT⟩ := hx (t1 + d) (by omega) (by omega)
      exact tgtSettledTopKeep q h1 h2 T hT h0
  have := key (t2 - t1) (by omega)
  rwa [show t1 + (t2 - t1) = t2 by omega] at this

include hn hR hsrc hend hq0 in
/-- A target cell settled along a stretch of the run keeps its tracked atom. Consumer:
`wPackedAtExport`. -/
theorem wSettledRun (q : Nat) (h1 : R ≤ q) (h2 : q < 2 * R) (t1 t2 : Nat) (h12 : t1 ≤ t2)
    (ht2 : t2 ≤ W.length)
    (hs : ∀ t, t1 ≤ t → t ≤ t2 → ∃ T, cohortTok R (wLane ref root lane src R q0 W t) q = .settled T) :
    tracked ring root lane src R (wRunAt ref.toWidthDigitReference q0 W t1).2 q =
      tracked ring root lane src R (wRunAt ref.toWidthDigitReference q0 W t2).2 q := by
  have key : ∀ d, t1 + d ≤ t2 →
      tracked ring root lane src R (wRunAt ref.toWidthDigitReference q0 W (t1 + d)).2 q =
        tracked ring root lane src R (wRunAt ref.toWidthDigitReference q0 W t1).2 q := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro hd
      obtain ⟨T, hT⟩ := hs (t1 + d) (by omega) (by omega)
      obtain ⟨T', hT'⟩ := hs (t1 + d + 1) (by omega) (by omega)
      rw [show t1 + (d + 1) = t1 + d + 1 by omega,
        wSettledGhost ref hn root lane src R hR hsrc hend q0 hq0 W (t1 + d) (by omega) q h1 h2 T T'
          hT hT']
      exact ih (by omega)
  have := key (t2 - t1) (by omega)
  rw [show t1 + (t2 - t1) = t2 by omega] at this
  exact this.symm

include hn hR hsrc hend hq0 hc0 in
/-- Back along a stretch where cell `q` does not hold the atom, the atom stays at `q + 1`.
Consumer: `wPackedAtExport` (the cell above a forming settled cell). -/
theorem wPassRun (sid : DigitStamp n) (q t1 t2 : Nat) (h12 : t1 ≤ t2) (ht2 : t2 ≤ W.length)
    (htime : sid.time ≤ t1)
    (hne : ∀ t, t1 ≤ t → t < t2 →
      tracked ring root lane src R (wRunAt ref.toWidthDigitReference q0 W t).2 q ≠
        some (.sampled sid))
    (h : tracked ring root lane src R (wRunAt ref.toWidthDigitReference q0 W t2).2 (q + 1) =
      some (.sampled sid)) :
    tracked ring root lane src R (wRunAt ref.toWidthDigitReference q0 W t1).2 (q + 1) =
      some (.sampled sid) := by
  have key : ∀ d, t1 + d ≤ t2 →
      tracked ring root lane src R (wRunAt ref.toWidthDigitReference q0 W (t2 - d)).2 (q + 1) =
        some (.sampled sid) := by
    intro d
    induction d with
    | zero => intro _; rw [Nat.sub_zero]; exact h
    | succ d ih =>
      intro hd
      have h0 := ih (by omega)
      rw [show t2 - d = t2 - (d + 1) + 1 by omega] at h0
      exact wPassStep ref hn root lane src R hR hsrc hend q0 hq0 hc0 W (t2 - (d + 1)) (by omega)
        sid (by omega) q h0 (hne _ (by omega) (by omega))
  have := key (t2 - t1) (by omega)
  rwa [show t2 - (t2 - t1) = t1 by omega] at this

include hn hR hsrc hend hq0 hi0 hc0 in
/-- **The strict cohort packed at its targets at the tail export (F1, old half).** Let the strict
samples `a_m = sm m` (read at source cell `m`, tail bit `m = 0`) be exported by `xm m` on the
delimiter edge in the order `m = R - 1, …, 0`, the tail `a_0` at letter `tx`, and let `a_m` be
read at target cell `R + m` at a letter `ut m` after the tail export, the cell settled there for
`m > 0` (the strict ledger's use reads, `wCarryChain`). Then right after the tail export the
cohort has arrived (`CohortArrived`) and its settled cells form a top run (`CohortSettledTop`).
Consumer: `L3.StageMEntryCyc` (the old half of `CohortCycIn R 0` at the pinned cycle start). -/
theorem wPackedAtExport (sm : Nat → DigitSample (compileAdvice (ceilLogTwo n)) n)
    (hsm : ∀ m, m < R →
      DigitRecordedSample (wRunAt ref.toWidthDigitReference q0 W W.length).2 (sm m))
    (htl : ∀ m, m < R → (sm m).tail = decide (m = 0))
    (xm : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hxm : ∀ m, m < R →
      DigitRecordedExport (wRunAt ref.toWidthDigitReference q0 W W.length).2 (xm m))
    (hxon : ∀ m, m < R → OnEdge ring root lane src R (xm m))
    (hxop : ∀ m, m < R → (xm m).operand = some (.sampled (sm m).id))
    (hxord : ∀ i j, i < j → j < R → (xm j).time < (xm i).time)
    (tx : Nat) (hx0 : (xm 0).time = tx + 1) (htx : tx < W.length) (ut : Nat → Nat)
    (hut : ∀ m, m < R → tx + 1 ≤ ut m ∧ ut m ≤ W.length)
    (huse : ∀ m, m < R → inA ring root lane src
      (wRunAt ref.toWidthDigitReference q0 W (ut m)).2 (R + m) = some (.sampled (sm m).id))
    (hset : ∀ m, 0 < m → m < R →
      ∃ T, cohortTok R (wLane ref root lane src R q0 W (ut m)) (R + m) = .settled T) :
    CohortArrived R (wLane ref root lane src R q0 W (tx + 1)) ∧
      CohortSettledTop R (wLane ref root lane src R q0 W (tx + 1)) := by
  have hgdEnd := (wInvAt ref hn root lane src R hR hsrc hend q0 hq0 W W.length).1.2.2.2.2
  have hfoEnd := (wInvAt ref hn root lane src R hR hsrc hend q0 hq0 W W.length).1.2.1
  have hSD : ∀ t, SampDistinct
      (tracked ring root lane src R (wRunAt ref.toWidthDigitReference q0 W t).2) :=
    fun t => (wInvAt ref hn root lane src R hR hsrc hend q0 hq0 W t).1.2.2.2.2.2.1
  have hsx : ∀ m, m < R → (sm m).id.time < (xm m).time := fun m hm =>
    (hgdEnd.2.2.2.1 (xm m) (sm m).id (hxm m hm) (hxon m hm) (hxop m hm)).1
  have hxle : ∀ m, m < R → (xm m).time ≤ tx + 1 := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, hx0]
      exact Nat.le_refl _
    · have := hxord 0 m h hm
      omega
  have huseT : ∀ m, m < R → tracked ring root lane src R
      (wRunAt ref.toWidthDigitReference q0 W (ut m)).2 (R + m) = some (.sampled (sm m).id) := by
    intro m hm
    rw [trackedTgt ring root lane src R _ (R + m) (by omega) (by omega)]
    exact huse m hm
  -- the strict atoms are distinct (one recorded export per atom, at distinct times)
  have hdist : ∀ i j, i < R → j < R → (sm i).id = (sm j).id → i = j := by
    intro i j hi hj h
    have hx := wExportUnique ref hn root lane src R hR hsrc hend q0 hq0 W W.length (xm i) (xm j)
      (sm i).id (hxm i hi) (hxm j hj) (hxon i hi) (hxon j hj) (hxop i hi) (by rw [hxop j hj, h])
    rcases Nat.lt_trichotomy i j with h' | h' | h'
    · have := hxord i j h' hj
      rw [hx] at this
      omega
    · exact h'
    · have := hxord j i h' hi
      rw [hx] at this
      omega
  -- positions at the tail export: `a_m` at `R + m`
  have hback : ∀ m, m < R → ∃ p, R ≤ p ∧ p ≤ R + m ∧ tracked ring root lane src R
      (wRunAt ref.toWidthDigitReference q0 W (tx + 1)).2 p = some (.sampled (sm m).id) := by
    intro m hm
    have h1 := hsx m hm
    have h2 := hxle m hm
    exact wBackRange ref hn root lane src R hR hsrc hend q0 hq0 hi0 hc0 W (tx + 1) (ut m)
      (hut m hm).1 (hut m hm).2 (sm m).id (xm m) (hxm m hm) h2 (hxon m hm) (hxop m hm)
      (by omega) (R + m) (by omega) (huseT m hm)
  have P1 : ∀ m, m < R → tracked ring root lane src R
      (wRunAt ref.toWidthDigitReference q0 W (tx + 1)).2 (R + m) = some (.sampled (sm m).id) := by
    have key : ∀ k m, m < k → m < R → tracked ring root lane src R
        (wRunAt ref.toWidthDigitReference q0 W (tx + 1)).2 (R + m) =
          some (.sampled (sm m).id) := by
      intro k
      induction k with
      | zero => intro m hm; exact absurd hm (Nat.not_lt_zero m)
      | succ k ih =>
        intro m hm hmR
        rcases Nat.lt_or_ge m k with h | h
        · exact ih m h hmR
        · obtain ⟨p, hp1, hp2, hp⟩ := hback m hmR
          rcases Nat.lt_or_ge p (R + m) with hlt | hge
          · exfalso
            have h' := ih (p - R) (by omega) (by omega)
            rw [show R + (p - R) = p by omega, hp] at h'
            have := hdist m (p - R) hmR (by omega) (DigitAtom.sampled.inj (Option.some.inj h'))
            omega
          · rw [show R + m = p by omega]
            exact hp
    exact fun m hm => key (m + 1) m (by omega) hm
  -- `a_m` stays at `R + m` from the tail export to its use read
  have hpos : ∀ m, m < R → ∀ t, tx + 1 ≤ t → t ≤ ut m → tracked ring root lane src R
      (wRunAt ref.toWidthDigitReference q0 W t).2 (R + m) = some (.sampled (sm m).id) := by
    intro m hm t h1 h2
    have e1 := hsx m hm
    have e2 := hxle m hm
    have e3 := (hut m hm).2
    obtain ⟨p, hp1, hp2, hp⟩ := wBackRange ref hn root lane src R hR hsrc hend q0 hq0 hi0 hc0 W
      t (ut m) h2 (hut m hm).2 (sm m).id (xm m) (hxm m hm) (by omega) (hxon m hm) (hxop m hm)
      (by omega) (R + m) (by omega) (huseT m hm)
    obtain ⟨p', hq1, hq2, hq⟩ := wBackRange ref hn root lane src R hR hsrc hend q0 hq0 hi0 hc0 W
      (tx + 1) t h1 (by omega) (sm m).id (xm m) (hxm m hm) e2 (hxon m hm) (hxop m hm)
      (by omega) p hp1 hp
    have := hSD (tx + 1) p' (R + m) (sm m).id hq (P1 m hm)
    rw [show R + m = p by omega]
    exact hp
  -- delivery of the tail at its export letter: cell `R` is a pending input
  obtain ⟨t0, e0, he0, ht0, hs0, hr0⟩ :=
    wExportLetter ref q0 hi0 hc0 W (xm 0) (hxm 0 (by omega))
  have ht0x : t0 = tx := by omega
  rw [ht0x] at he0 hr0
  rw [(hxon 0 (by omega)).1] at hr0
  have hke0 : cohortEdgeOf root src R e0 = some (R - 1) := by
    rw [hs0, (hxon 0 (by omega)).2]
    exact cohortEdgeOfSite ring root src R hend (R - 1) (by omega)
  obtain ⟨-, T0, hD, hE, hL⟩ := wDelRecv ref hn root lane src R hR hsrc hend _
    (wInvAt ref hn root lane src R hR hsrc hend q0 hq0 W tx).1.1 e0 hke0 (xm 0) hr0
  have hR0 : cohortTok R (wLane ref root lane src R q0 W (tx + 1)) R = .pkt T0 := by
    rw [wLaneStep ref hn root lane src R hR hsrc hend q0 hq0 W tx, wKeOf root src R W he0, hke0]
    show cohortTok R (cohortEdge R (wLane ref root lane src R q0 W tx) (R - 1)) R = .pkt T0
    have e := (cohortTokDel R (R - 1) (wLane ref root lane src R q0 W tx) (by omega)).2
    rw [show R - 1 + 1 = R by omega] at e
    rw [e]
    have hD' : (wLane ref root lane src R q0 W tx).out (R - 1) = .D T0 := hD
    have hE' : (wLane ref root lane src R q0 W tx).inp R = .E := hE
    have hL' : (wLane ref root lane src R q0 W tx).live R = false := hL
    rw [hD', hE', hL']
    simp [bankRepairDigitDelStep, cohortTokIn]
  -- shapes at the tail export
  have hcorT := (wInvAt ref hn root lane src R hR hsrc hend q0 hq0 W (tx + 1)).1.2.2.2.2.1
  have hshape : ∀ m, m < R → cohortTok R (wLane ref root lane src R q0 W (tx + 1)) (R + m) ≠ .other →
      cohortTok R (wLane ref root lane src R q0 W (tx + 1)) (R + m) = .pkt (decide (m = 0)) ∨
        cohortTok R (wLane ref root lane src R q0 W (tx + 1)) (R + m) = .settled (decide (m = 0)) := by
    intro m hm hne
    have hc := (hcorT.2 (R + m) (by omega) (by omega)).1
    rw [cohortTokTgt _ (by omega : R ≤ R + m)] at hne ⊢
    obtain ⟨T, hT, hok⟩ := inTokOfSome _ _ _ _ hc
      (by have := P1 m hm; rw [trackedTgt ring root lane src R _ (R + m) (by omega) (by omega)] at this; exact this)
      hne
    have hTt := tailBitEq ring root lane _ _
      (fun f hf => wFramesUpTo ref.toWidthDigitReference W q0 (tx + 1) W.length (by omega) f hf)
      hfoEnd (sm m) (hsm m hm) T hok
    rw [hTt, htl m hm] at hT
    exact hT
  have hnot : ∀ m, m < R →
      cohortTok R (wLane ref root lane src R q0 W (tx + 1)) (R + m) ≠ .other := by
    intro m hm hO
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · have hz : cohortTok R (wLane ref root lane src R q0 W (tx + 1)) (R + m) = .pkt T0 := by
        rw [h0]
        exact hR0
      rw [hz] at hO
      cases hO
    · have h' := wOtherRun ref hn root lane src R hR hsrc hend q0 hq0 W (tx + 1) (ut m)
        (hut m hm).1 (hut m hm).2 (R + m) (by omega) (by omega) hO
        (fun t h1 h2 => ⟨_, hpos m hm t h1 h2⟩)
      obtain ⟨T, hT⟩ := hset m h0 hm
      rw [h'] at hT
      cases hT
  refine ⟨fun i hi => ?_, ?_⟩
  · -- arrived
    have hm : R - 1 - i < R := by omega
    have htail : cohortTail R i = decide (R - 1 - i = 0) := by
      unfold cohortTail
      by_cases h : i + 1 = R
      · rw [decide_eq_true h, decide_eq_true (by omega : R - 1 - i = 0)]
      · rw [decide_eq_false h, decide_eq_false (by omega : ¬ R - 1 - i = 0)]
    rw [show 2 * R - 1 - i = R + (R - 1 - i) by omega, htail]
    exact hshape _ hm (hnot _ hm)
  · -- settled top
    intro q h1 h2 hq
    obtain ⟨T, hT⟩ := hq
    obtain ⟨m, rfl⟩ : ∃ m, q = R + m := ⟨q - R, by omega⟩
    have hm1 : m + 1 < R := by omega
    have hm : m < R := by omega
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · have hz : cohortTok R (wLane ref root lane src R q0 W (tx + 1)) (R + m) = .pkt T0 := by
        rw [h0]
        exact hR0
      rw [hz] at hT
      cases hT
    · -- the export letter of `a_m`: `a_m` sits at the delimiter cell `R - 1`
      obtain ⟨tm, em, hem, htm, hsem, hrm⟩ := wExportLetter ref q0 hi0 hc0 W (xm m) (hxm m hm)
      have hkem : cohortEdgeOf root src R em = some (R - 1) := by
        rw [hsem, (hxon m hm).2]
        exact cohortEdgeOfSite ring root src R hend (R - 1) (by omega)
      rw [(hxon m hm).1] at hrm
      obtain ⟨hop, -⟩ := wDelRecv ref hn root lane src R hR hsrc hend _
        (wInvAt ref hn root lane src R hR hsrc hend q0 hq0 W tm).1.1 em hkem (xm m) hrm
      have hsrcT : tracked ring root lane src R (wRunAt ref.toWidthDigitReference q0 W tm).2
          (R - 1) = some (.sampled (sm m).id) := by
        rw [← hxop m hm, hop]
        unfold tracked trackedAt
        rw [if_pos (by omega : R - 1 < R)]
      have htme := hxle m hm
      rcases lastChange (fun t => ∃ T, cohortTok R (wLane ref root lane src R q0 W t) (R + m) =
          .settled T) tm (tx + 1) (by omega) ⟨T, hT⟩ with hall | ⟨f, hf1, hf2, hfn, hfa⟩
      · exfalso
        have hg := wSettledRun ref hn root lane src R hR hsrc hend q0 hq0 W (R + m) (by omega)
          (by omega) tm (tx + 1) (by omega) (by omega) hall
        rw [P1 m hm] at hg
        have := hSD tm (R + m) (R - 1) (sm m).id hg hsrcT
        omega
      · have hfn' : ∀ T, cohortTok R (wLane ref root lane src R q0 W f) (R + m) ≠ .settled T :=
          fun T hh => hfn ⟨T, hh⟩
        have hfa' : ∀ t, f < t → t ≤ tx + 1 →
            ∃ T, cohortTok R (wLane ref root lane src R q0 W t) (R + m) = .settled T := hfa
        -- the cell above was settled when `R + m` formed
        have hT' : ∃ T', cohortTok R (wLane ref root lane src R q0 W (f + 1)) (R + m + 1) =
            .settled T' := by
          obtain ⟨Tn, hTn⟩ := hfa' (f + 1) (by omega) (by omega)
          rw [wLaneStep ref hn root lane src R hR hsrc hend q0 hq0 W f] at hTn ⊢
          exact tgtSettledForm (R + m) (by omega) (by omega) hfn' Tn hTn
        -- `R + m` holds `a_m` from its formation to the tail export
        have hgm : ∀ t, f + 1 ≤ t → t ≤ tx + 1 → tracked ring root lane src R
            (wRunAt ref.toWidthDigitReference q0 W t).2 (R + m) = some (.sampled (sm m).id) := by
          intro t h1 h2
          rw [wSettledRun ref hn root lane src R hR hsrc hend q0 hq0 W (R + m) (by omega)
            (by omega) t (tx + 1) h2 (by omega) (fun t' h1' h2' => hfa' t' (by omega) h2')]
          exact P1 m hm
        -- so the cell above holds `a_{m+1}` at the formation
        have hup : tracked ring root lane src R (wRunAt ref.toWidthDigitReference q0 W (f + 1)).2
            (R + m + 1) = some (.sampled (sm (m + 1)).id) := by
          have h := P1 (m + 1) hm1
          rw [show R + (m + 1) = R + m + 1 by omega] at h
          have e1 := hsx (m + 1) hm1
          have e2 := hxord m (m + 1) (by omega) hm1
          exact wPassRun ref hn root lane src R hR hsrc hend q0 hq0 hc0 W (sm (m + 1)).id (R + m)
            (f + 1) (tx + 1) (by omega) (by omega) (by omega)
            (fun t h1 h2 hh => by
              rw [hgm t h1 (by omega)] at hh
              have := hdist m (m + 1) hm hm1 (DigitAtom.sampled.inj (Option.some.inj hh))
              omega) h
        -- its tail bit is that of `a_{m+1}`: false
        obtain ⟨T', hT'⟩ := hT'
        have hcorF := (wInvAt ref hn root lane src R hR hsrc hend q0 hq0 W (f + 1)).1.2.2.2.2.1
        have hc := (hcorF.2 (R + m + 1) (by omega) (by omega)).1
        have hT'' := hT'
        rw [cohortTokTgt _ (by omega : R ≤ R + m + 1)] at hT''
        obtain ⟨T2, hT2, hok⟩ := inTokOfSome _ _ _ _ hc
          (by rw [trackedTgt ring root lane src R _ (R + m + 1) (by omega) (by omega)] at hup; exact hup)
          (fun h => by have h3 := hT''.symm.trans h; cases h3)
        have hTT := tailBitEq ring root lane _ _
          (fun f' hf' => wFramesUpTo ref.toWidthDigitReference W q0 (f + 1) W.length (by omega) f' hf')
          hfoEnd (sm (m + 1)) (hsm (m + 1) hm1) T2 hok
        rw [htl (m + 1) hm1, decide_eq_false (by omega : ¬ m + 1 = 0)] at hTT
        have hTf : T' = false := by
          rcases hT2 with h | h
          · have h3 := h.symm.trans hT''
            cases h3
          · have h3 := h.symm.trans hT''
            injection h3 with h4
            rw [← h4, hTT]
        rw [hTf] at hT'
        exact ⟨false, wSettledTopRun ref hn root lane src R hR hsrc hend q0 hq0 W (f + 1) (tx + 1)
          (by omega) (R + m) (by omega) (by omega) (fun t h1 h2 => hfa' t (by omega) h2) hT'⟩

end Track

end L3.StageMEntryPack

#print axioms L3.StageMEntryPack.tailBitEq
#print axioms L3.StageMEntryPack.wRecordedAt
#print axioms L3.StageMEntryPack.wBackRange
#print axioms L3.StageMEntryPack.wPassStep
#print axioms L3.StageMEntryPack.wSettledGhost
#print axioms L3.StageMEntryPack.wOtherRun
#print axioms L3.StageMEntryPack.wSettledTopRun
#print axioms L3.StageMEntryPack.lastChange
#print axioms L3.StageMEntryPack.wSettledRun
#print axioms L3.StageMEntryPack.wPassRun
#print axioms L3.StageMEntryPack.wPackedAtExport
