import Leader.L4.ReportFastAcqDriver

namespace L4.ReportFastAcqPrefix
open AllSizeProtocol PhysicalCustody ShortResetCycle
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportOwnerAcquireProvenance
open ReportOwnerForwardLocations ReportOwnerReverseShape
open ReportFastAcqTrack ReportFastAcqAllowed ReportFastAcqDriver
open ReportFastNominationBridge ReportAdaptiveFibre

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

theorem on_not_done_no_consume (d : Sheet) (C : Chart h) (x : Raw s n)
    (c : Cursor) (e : Fin n) (A : On d C x c)
    (N : ReportFastAcqTrack.next C e c≠.done) :
    NoConsume d C x e := by
  cases c with
  | done => exact (N rfl).elim
  | fwd k =>
    obtain ⟨q,R,_,_⟩ := A
    right
    rw [R.shape.2.2 0 C.positive]
    unfold frontTag
    split <;> try decide
    split <;> decide
  | rev k =>
    obtain ⟨q,R,_⟩ := A
    cases k with
    | zero =>
      left
      intro E
      subst e
      exact N (by simp [ReportFastAcqTrack.next])
    | succ j =>
      right
      rw [R.shape.2.2 0 C.positive]
      simp [backTag]

abbrev Z (s n : Nat) := Track (Trace s n) n

noncomputable def driven (d : Sheet) (B : Fin 5→Chart h) (D : Fin 5→Bool) :
    Z s n→Fin n→Z s n :=
  driver (B 2) (ReportFastAcqDriver.step (B 2)) (bans d B D Trace.raw) Trace.cur

noncomputable def run (d : Sheet) (B : Fin 5→Chart h) (D : Fin 5→Bool)
    (z : Z s n) (w : List (Fin n)) : Z s n :=
  SequentialMarkClock.run (driven d B D) z w

noncomputable def actual (d : Sheet) (B : Fin 5→Chart h) (D : Fin 5→Bool) :
    Z s n→List (Fin n)→List (Fin n)
  | _, [] => []
  | z,e::w => mergeSide (bans d B D Trace.raw z.base) e ::
      actual d B D (driven d B D z e) w

theorem run_raw (d : Sheet) (B : Fin 5→Chart h) (D : Fin 5→Bool)
    (z : Z s n) (w : List (Fin n)) :
    (run d B D z w).base.raw=rawRun z.base.raw (actual d B D z w) := by
  induction w generalizing z with
  | nil => rfl
  | cons e w IH =>
    change (run d B D (driven d B D z e) w).base.raw=
      rawRun (rawNext s z.base.raw _) (actual d B D (driven d B D z e) w)
    rw [IH]
    unfold driven driver
    rw [next_base]
    rfl

theorem run_snoc (d : Sheet) (B : Fin 5→Chart h) (D : Fin 5→Bool)
    (z : Z s n) (w : List (Fin n)) (e : Fin n) :
    run d B D z (w++[e])=driven d B D (run d B D z w) e :=
  MonitorRawBridge.run_snoc _ _ _ _

theorem actual_snoc (d : Sheet) (B : Fin 5→Chart h) (D : Fin 5→Bool)
    (z : Z s n) (w : List (Fin n)) (e : Fin n) :
    actual d B D z (w++[e])=actual d B D z w++
      [mergeSide (bans d B D Trace.raw (run d B D z w).base) e] := by
  induction w generalizing z with
  | nil => rfl
  | cons a w IH =>
    change _ :: actual d B D (driven d B D z a) (w++[e]) =
      _ :: (actual d B D (driven d B D z a) w ++ [_])
    rw [IH]
    rfl

theorem driven_cursor (d : Sheet) (B : Fin 5→Chart h) (D : Fin 5→Bool)
    (z : Z s n) (e : Fin n) :
    (driven d B D z e).base.cur =
      ReportFastAcqTrack.next (B 2) (mergeSide (bans d B D Trace.raw z.base) e) z.base.cur := by
  unfold driven driver
  rw [next_base]
  rfl

private theorem snoc_ind {P : List (Fin n) → Prop}
    (base : P []) (step : ∀ w e, P w → P (w++[e])) (w : List (Fin n)) : P w := by
  have R : ∀ v : List (Fin n), P v.reverse := by
    intro v
    induction v with
    | nil => exact base
    | cons e v ih => rw [List.reverse_cons]; exact step _ e ih
  simpa only [List.reverse_reverse] using R w.reverse

/-- The actual physical word of a pre-hit prefix, not a filtered
subset of its marks. Final live and cursor stickiness exclude any
earlier successful consume. -/
theorem before_on_live_run (d : Sheet) (B : Fin 5→Chart h) (D : Fin 5→Bool)
    (z : Z s n) (w : List (Fin n))
    (H : ∀ u v,w=u++v →
      On d (B 2) (run d B D z u).base.raw (run d B D z u).base.cur)
    (L : (run d B D z w).base.cur≠.done) :
    BeforeConsume d (B 2) z.base.raw (actual d B D z w) := by
  induction w using snoc_ind with
  | base => exact .nil
  | step u e IH =>
    have L0 : (run d B D z u).base.cur≠.done := by
      intro H0
      apply L
      rw [run_snoc,driven_cursor,H0]
      rfl
    have A := IH (fun a b E=>H a (b++[e]) (by rw [E,List.append_assoc])) L0
    have N0 := H u [e] rfl
    have N1 : ReportFastAcqTrack.next (B 2)
        (mergeSide (bans d B D Trace.raw (run d B D z u).base) e)
        (run d B D z u).base.cur≠.done := by rwa [run_snoc,driven_cursor] at L
    have NC := on_not_done_no_consume d (B 2) _ _ _ N0 N1
    rw [run_raw] at NC
    rw [actual_snoc]
    exact .snoc _ A NC


theorem run_good (d : Sheet) (B : Fin 5→Chart h) (D : Fin 5→Bool)
    (Env : Trace s n→Prop)
    (Rows : ReportFastAllowedCredit.Rows (ReportFastAcqDriver.step (B 2))
      (fun z=>Env z ∧ On d (B 2) z.raw z.cur) (fun z=>z.cur=.done)
      (fun z=>ReportFastAcqTrack.debt (B 2) z.cur) (bans d B D Trace.raw)
      (fun z q=>ReportFastAcqTrack.label (B 2) z.cur=some q) (fun z q=>Spent d B z.raw q))
    (z : Z s n) (w : List (Fin n))
    (H : GoodTrack (fun z=>Env z ∧ On d (B 2) z.raw z.cur) (fun z=>z.cur=.done)
      (fun z q=>ReportFastAcqTrack.label (B 2) z.cur=some q) (fun z q=>Spent d B z.raw q) z) :
    GoodTrack (fun z=>Env z ∧ On d (B 2) z.raw z.cur) (fun z=>z.cur=.done)
      (fun z q=>ReportFastAcqTrack.label (B 2) z.cur=some q) (fun z q=>Spent d B z.raw q)
      (run d B D z w) := by
  induction w generalizing z with
  | nil => exact H
  | cons e w IH =>
    exact IH (driven d B D z e) (ReportFastAllowedCredit.track_step _ _ _ _ _ _ _ Rows z _
      H (ReportFastRawRelift.allowed_after_merge _ (Rows.pairs _ H.1) e))

theorem first_done_inputs (d : Sheet) (B : Fin 5→Chart h) (D : Fin 5→Bool)
    (z : Z s n) (w : List (Fin n)) (e : Fin n)
    (H : ∀ u v,w=u++v →
      On d (B 2) (run d B D z u).base.raw (run d B D z u).base.cur)
    (L : (run d B D z w).base.cur≠.done)
    (End : (run d B D z (w++[e])).base.cur=.done) :
    let old := rawRun z.base.raw (actual d B D z w)
    BeforeConsume d (B 2) z.base.raw (actual d B D z w) ∧
      mergeSide (bans d B D Trace.raw (run d B D z w).base) e=door (B 2) ∧
      (tok d (B 2) old 0).tag=3 ∧ (tok d (B 2) old 0).fault=false ∧
      (tok d (B 2) old 0).outcome≠1 := by
  dsimp only
  have R := H w [] (by simp)
  have E := (finish_iff (B 2) _ _ L).mp (by rwa [run_snoc,driven_cursor] at End)
  rw [E.1] at R
  obtain ⟨q,State,Success⟩ := R
  have T : (tok d (B 2) (run d B D z w).base.raw 0).tag=3 := by
    rw [State.shape.2.2 0 (B 2).positive]
    rfl
  have F : (tok d (B 2) (run d B D z w).base.raw 0).fault=false := by
    rw [State.packet]
    exact ReportByteRows.acqFlightD_live _ _
  have S : (tok d (B 2) (run d B D z w).base.raw 0).outcome≠1 := by
    rw [State.packet]
    simp [ReportByteRows.acqFlightD,Success]
  rw [run_raw] at T F S
  exact ⟨before_on_live_run d B D z w H L,E.2,T,F,S⟩

#print axioms on_not_done_no_consume
#print axioms before_on_live_run
#print axioms run_good
#print axioms first_done_inputs
end L4.ReportFastAcqPrefix
