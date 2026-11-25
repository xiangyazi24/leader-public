import Leader.L4.ReportOwnerResetDrain
import Leader.L4.ReportResetCovers

namespace L4.ReportOwnerReceiptClock

open AllSizeProtocol PhysicalCustody ReportResetRawHooks ReportOwnerResetDrain
open ReportResetBarrier ShortResetCycle ShortResetChart ReportResetEventClock

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

abbrev State (Q : Raw s n → Prop) := {x : Raw s n // Q x} × Option Stage

/-- A fresh monitor cannot credit an inherited WAIT0 or D0, and never
freezes the raw part, including after completion. -/
def next (sheet : Sheet) (C : Chart h) (F : Fibre (h:=h) sheet Q)
    (z : State Q) (e : Fin n) : State Q :=
  (advance sheet F z.1 e,
    match z.2 with
    | none => if ownerPC sheet C z.1.val = .issue0 ∧ e = door C then some (.fwd 0) else none
    | some st => some (nextStage C e st))

def launchHit (sheet : Sheet) (C : Chart h) (F : Fibre (h:=h) sheet Q)
    (z : State Q) : Prop :=
  z.2=some (.fwd 0) ∧
    ∃ y : {x : Raw s n // Q x}, ownerPC sheet C y.val=.issue0 ∧
      z.1=advance sheet F y (door C)

def done (z : State Q) : Prop := z.2=some .done

theorem raw_project (sheet : Sheet) (C : Chart h) (F : Fibre (h:=h) sheet Q)
    (z : State Q) (e : Fin n) : (next sheet C F z e).1.val=rawNext s z.1.val e :=
  rfl

theorem initial_not_hit (sheet : Sheet) (C : Chart h) (F : Fibre (h:=h) sheet Q)
    (z : {x : Raw s n // Q x}) : ¬launchHit sheet C F (z,none) :=
  by intro H; have K := H.1; contradiction

theorem initial_not_done (z : {x : Raw s n // Q x}) : ¬done (z,none) :=
  by simp [done]

/-- The first transition that turns the monitor on is exactly the
literal ISSUE0 door mark on the old raw configuration. -/
theorem fresh_launch_iff (sheet : Sheet) (C : Chart h) (F : Fibre (h:=h) sheet Q)
    (z : {x : Raw s n // Q x}) (e : Fin n) :
    launchHit sheet C F (next sheet C F (z,none) e) ↔
      ownerPC sheet C z.val=.issue0 ∧ e=door C := by
  unfold next launchHit
  dsimp only
  by_cases H : ownerPC sheet C z.val=.issue0 ∧ e=door C
  · rcases H with ⟨P,rfl⟩
    simp only [P,true_and,if_true]
    exact ⟨fun _=>trivial,fun _=>⟨z,P,rfl⟩⟩
  · simp [H]

private theorem active_cost (sheet : Sheet) (C : Chart h)
    (F : Fibre (h:=h) sheet Q) (t : Nat)
    (z : {x : Raw s n // Q x} × Stage) :
    Height.iidHitCost (next sheet C F) done t (z.1,some z.2) =
      Height.iidHitCost (ReportResetBarrier.monitor C (advance sheet F))
        (fun y=>y.2=.done) t z := by
  induction t generalizing z with
  | zero => rfl
  | succ t ih =>
    rcases z with ⟨x,st⟩
    by_cases D : st=.done
    · simp [Height.iidHitCost,done,D]
    · have I : ∀ e : Fin n,
          Height.iidHitCost (next sheet C F) done t
            (next sheet C F (x,some st) e) =
          Height.iidHitCost (ReportResetBarrier.monitor C (advance sheet F))
            (fun y=>y.2=.done) t
            (ReportResetBarrier.monitor C (advance sheet F) (x,st) e) :=
        fun e => ih (ReportResetBarrier.monitor C (advance sheet F) (x,st) e)
      simp [Height.iidHitCost,done,D,I]

/-- A freshly credited launch has the checked physical drain mean. -/
theorem after_hit (sheet : Sheet) (C : Chart h) (F : Fibre (h:=h) sheet Q)
    (N : 1<n) (z : State Q) (H : launchHit sheet C F z) :
    Height.IIDExpectedHittingTimeAtMost (next sheet C F) done z (2*C.L*n) := by
  rcases z with ⟨x,st⟩
  obtain ⟨S,y,P,E⟩ := H
  dsimp only at S E
  subst st
  subst x
  intro t
  rw [active_cost sheet C F t (advance sheet F y (door C),.fwd 0)]
  exact completed_mean sheet C F y.val y.property N P t

/-- Exact per-owner receipt bound reduced to a history-uniform,
same-tape first real launch clock. No all-owner closure is asserted. -/
theorem owner_receipt_mean_of_prelaunch (sheet : Sheet) (C : Chart h)
    (F : Fibre (h:=h) sheet Q) (N : 1<n) (z : {x : Raw s n // Q x})
    (B : Nat) (L : C.L≤B)
    (before : Height.IIDExpectedHittingTimeAtMost (next sheet C F)
      (launchHit sheet C F) (z,none) (n*(Cpre C.L (params sheet s).digits+1))) :
    Height.IIDExpectedHittingTimeAtMost (next sheet C F) done (z,none)
      (n*resetCoefficient B (params sheet s).digits) := by
  apply (MonitorRawBridge.height_iff_row _ _ _ _).mpr
  apply after_launch (t := (params sheet s).digits) (next sheet C F) (launchHit sheet C F) done L (z,none)
  · exact (MonitorRawBridge.height_iff_row _ _ _ _).mp before
  · intro y Y
    exact (MonitorRawBridge.height_iff_row _ _ _ _).mp (after_hit sheet C F N y Y)

/-- The polynomial-priced version accepts the scalar potential
bound; it does not require a stronger event counter with coefficient Cpre. -/
theorem owner_receipt_mean_of_polynomial (sheet : Sheet) (C : Chart h)
    (F : Fibre (h:=h) sheet Q) (N : 1<n) (z : {x : Raw s n // Q x})
    (B : Nat) (L : C.L≤B)
    (before : Height.IIDExpectedHittingTimeAtMost (next sheet C F)
      (launchHit sheet C F) (z,none) (n*(10*(B+4*(params sheet s).digits+7)^2+1))) :
    Height.IIDExpectedHittingTimeAtMost (next sheet C F) done (z,none)
      (n*resetCoefficient B (params sheet s).digits) := by
  let P := 10*(B+4*(params sheet s).digits+7)^2
  have V := AllSizeComposition.additive_stage (next sheet C F) (launchHit sheet C F)
    done (n*(P+1)) (2*C.L*n) (z,none)
    ((MonitorRawBridge.height_iff_row _ _ _ _).mp before)
    (fun y Y => (MonitorRawBridge.height_iff_row _ _ _ _).mp (after_hit sheet C F N y Y))
  have W : n*(P+1)+2*C.L*n ≤ n*resetCoefficient B (params sheet s).digits := by
    unfold resetCoefficient
    have H : P+1+2*C.L≤10*(B+4*(params sheet s).digits+7)^2+2*B+1 := by unfold P; omega
    calc
      _ = n*(P+1+2*C.L) := by rw [Nat.mul_comm (2*C.L) n, ← Nat.mul_add]
      _ ≤ _ := Nat.mul_le_mul_left _ H
  apply (MonitorRawBridge.height_iff_row _ _ _ _).mpr
  intro t
  exact Nat.le_trans (V t) (Nat.mul_le_mul_right _ W)

/-- Separate before-launch clock freezes its latch, never the physical bytes. -/
def preNext (sheet : Sheet) (C : Chart h) (F : Fibre (h:=h) sheet Q)
    (z : {x : Raw s n // Q x} × Bool) (e : Fin n) :
    {x : Raw s n // Q x} × Bool :=
  (advance sheet F z.1 e,
    z.2 || decide (ownerPC sheet C z.1.val=.issue0 ∧ e=door C))

/-- Conservation and nomination on the literal prelaunch marks.
A coalition count on a different scheduler cannot instantiate this contract. -/
structure PrelaunchEvents (sheet : Sheet) (C : Chart h) (F : Fibre (h:=h) sheet Q) : Type where
  progress : {x : Raw s n // Q x} → Fin n → Bool
  nominate : ∀ x, ∃ e, (ownerPC sheet C x.val=.issue0 ∧ e=door C) ∨ progress x e=true
  budget : ∀ x w, events (preNext sheet C F) (fun z=>z.2=true)
    (fun z=>progress z.1) (x,false) w ≤ Cpre C.L (params sheet s).digits

theorem pre_cost (sheet : Sheet) (C : Chart h) (F : Fibre (h:=h) sheet Q)
    (t : Nat) (x : {x : Raw s n // Q x}) :
    Height.iidHitCost (next sheet C F) (launchHit sheet C F) t (x,none) =
      Height.iidHitCost (preNext sheet C F) (fun z=>z.2=true) t (x,false) := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    have I : ∀ e : Fin n,
        Height.iidHitCost (next sheet C F) (launchHit sheet C F) t (next sheet C F (x,none) e) =
        Height.iidHitCost (preNext sheet C F) (fun z=>z.2=true) t (preNext sheet C F (x,false) e) := by
      intro e
      by_cases H : ownerPC sheet C x.val=.issue0 ∧ e=door C
      · have A := (fresh_launch_iff sheet C F x e).mpr H
        cases t with
        | zero => rfl
        | succ t =>
          rw [Height.iidHitCost, if_pos A]
          simp [Height.iidHitCost,preNext,H]
      · rw [show next sheet C F (x,none) e=(advance sheet F x e,none) by simp [next,H]]
        rw [show preNext sheet C F (x,false) e=(advance sheet F x e,false) by simp [preNext,H]]
        exact ih _
    simp [Height.iidHitCost,initial_not_hit sheet C F x,I]

theorem owner_receipt_mean_of_events (sheet : Sheet) (C : Chart h)
    (F : Fibre (h:=h) sheet Q) (N : 1<n) (x : {x : Raw s n // Q x})
    (B : Nat) (L : C.L≤B) (P : PrelaunchEvents sheet C F) :
    Height.IIDExpectedHittingTimeAtMost (next sheet C F) done (x,none)
      (n*resetCoefficient B (params sheet s).digits) := by
  apply owner_receipt_mean_of_prelaunch sheet C F N x B L
  have pre := expected_of_counted_events (preNext sheet C F) (fun z=>z.2=true)
     (fun _=>True) (fun z=>P.progress z.1) (fun _ _ _=>trivial) (by
       intro z _ _
       obtain ⟨e,E⟩ := P.nominate z.1
       exact ⟨e,E.imp (fun H=>by simp [preNext,H]) id⟩)
     (x,false) trivial _ (P.budget x)
  intro t
  rw [pre_cost sheet C F t x]
  exact pre t

private theorem snoc_ind {P : List (Fin n) → Prop}
    (base : P []) (step : ∀ w e, P w → P (w++[e])) (w : List (Fin n)) : P w := by
  have R : ∀ v : List (Fin n), P v.reverse := by
    intro v
    induction v with
    | nil => exact base
    | cons e v ih => rw [List.reverse_cons]; exact step _ e ih
  simpa only [List.reverse_reverse] using R w.reverse

private theorem run_raw (sheet : Sheet) (C : Chart h) (F : Fibre (h:=h) sheet Q)
    (z : State Q) (w : List (Fin n)) :
    (SequentialMarkClock.run (next sheet C F) z w).1.val = rawRun z.1.val w := by
  induction w generalizing z with
  | nil => rfl
  | cons e w ih =>
    change (SequentialMarkClock.run (next sheet C F) (next sheet C F z e) w).1.val =
      rawRun (rawNext s z.1.val e) w
    rw [ih,raw_project]

private def Trace (sheet : Sheet) (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (a : Option Stage) : Prop :=
  match a with
  | none => True
  | some st => ∃ pre u post : List (Fin n),
      w=pre++u++post ∧ (st≠.done → post=[]) ∧
      Generated sheet C (rawRun x pre) u st

private theorem trace_run (sheet : Sheet) (C : Chart h) (F : Fibre (h:=h) sheet Q)
    (x : {x : Raw s n // Q x}) (w : List (Fin n)) :
    Trace sheet C x.val w (SequentialMarkClock.run (next sheet C F) (x,none) w).2 := by
  induction w using snoc_ind with
  | base => trivial
  | step w e ih =>
    rw [MonitorRawBridge.run_snoc]
    let z := SequentialMarkClock.run (next sheet C F) (x,none) w
    have xr : z.1.val=rawRun x.val w := run_raw sheet C F (x,none) w
    change Trace sheet C x.val w z.2 at ih
    change Trace sheet C x.val (w++[e]) (next sheet C F z e).2
    cases S : z.2 with
    | none =>
      by_cases E : ownerPC sheet C z.1.val=.issue0 ∧ e=door C
      · obtain ⟨P,rfl⟩ := E
        simp only [next,S,P,true_and,if_true,Trace]
        exact ⟨w,[door C],[],by simp,fun _=>rfl,.issue (by rwa [←xr])⟩
      · simp [next,S,E,Trace]
    | some st =>
      simp only [next,S,Trace] at ih ⊢
      obtain ⟨pre,u,post,W,K,G⟩ := ih
      by_cases D : st=.done
      · subst st
        change ∃ a b c, w++[e]=a++b++c ∧ (.done≠Stage.done → c=[]) ∧
          Generated sheet C (rawRun x.val a) b .done
        exact ⟨pre,u,post++[e],by rw [W,List.append_assoc],fun H=>(H rfl).elim,G⟩
      · have P : post=[] := K D
        subst post
        exact ⟨pre,u++[e],[],by simp [W,List.append_assoc],fun _=>rfl,.snoc e G D⟩

/-- A checked hit credits a real completed cut on the ORIGINAL tape;
any residual suffix is not claimed to preserve the Parked predicate. -/
theorem done_has_genuine_cut (sheet : Sheet) (C : Chart h) (F : Fibre (h:=h) sheet Q)
    (N : 1<n) (x : {x : Raw s n // Q x}) (w : List (Fin n))
    (hit : done (SequentialMarkClock.run (next sheet C F) (x,none) w)) :
    ∃ pre u post : List (Fin n), w=pre++u++post ∧
      Generated sheet C (rawRun x.val pre) u .done ∧
      FullParked sheet C (rawRun x.val (pre++u)) := by
  have T := trace_run sheet C F x w
  have D : (SequentialMarkClock.run (next sheet C F) (x,none) w).2=some .done := hit
  rw [D] at T
  obtain ⟨pre,u,post,W,_,G⟩ := T
  have Qpre : Q (rawRun x.val pre) := by
    rw [←run_raw sheet C F (x,none) pre]
    exact (SequentialMarkClock.run (next sheet C F) (x,none) pre).1.property
  refine ⟨pre,u,post,W,G,?_⟩
  rw [ShortOwnerEpochJS.raw_append]
  exact genuine_full_parked sheet C F _ Qpre N u G

end L4.ReportOwnerReceiptClock
