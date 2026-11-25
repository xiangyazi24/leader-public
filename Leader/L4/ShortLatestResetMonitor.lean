import Leader.L4.ShortOwnerEpochJS
import Leader.L4.ShortEpochResetOrigin
import Leader.L4.ShortPublishChart

namespace L4.ShortLatestResetMonitor

open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring
open ShortResetChart ShortResetCycle ShortResetForwardH2 ShortResetFlow
open ShortOwnerEpochJS ShortSequentialClean
open ShortObservedResetRelease (BeforeGoal)

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

variable {s n : Nat} {h : Fin n → Bool}

/-- A genuine RESET0 completed exactly at the end of this prefix.
    The launch may begin with dirty inherited slots. BeforeConsume
    stops the tracked reset at its actual first consume. -/
def GenuineAt (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) : Prop :=
  ∃ a t : List (Fin n),
    w=a++door C::t ∧
    ShortActualIssueClock.Issuable C (rawRun x a) ∧
    ShortResetReleased.BeforeConsume C (.fwd 0) t ∧
    ShortResetReleased.stageRun C (.fwd 0) t=.done

/-- The current letter takes the genuine own-reset cursor from
    .rev 0 to .done. A merely planted old D0 does not qualify. -/
def GenuineConsumeAt (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (e : Fin n) : Prop :=
  ∃ a t : List (Fin n),
    w=a++door C::t ∧
    ShortActualIssueClock.Issuable C (rawRun x a) ∧
    ShortResetReleased.BeforeConsume C (.fwd 0) t ∧
    ShortResetReleased.stageRun C (.fwd 0) t=.rev 0 ∧
    rightNeighbor e=C.root

private theorem stage_append (C : Chart h) (st : Stage)
    (u v : List (Fin n)) :
    ShortResetReleased.stageRun C st (u++v)=
      ShortResetReleased.stageRun C
        (ShortResetReleased.stageRun C st u) v := by
  induction u generalizing st with
  | nil => rfl
  | cons e u ih => exact ih (nextStage C e st)

private theorem before_append (C : Chart h) (st : Stage)
    (u v : List (Fin n)) :
    ShortResetReleased.BeforeConsume C st (u++v) ↔
      ShortResetReleased.BeforeConsume C st u ∧
      ShortResetReleased.BeforeConsume C
        (ShortResetReleased.stageRun C st u) v := by
  induction u generalizing st with
  | nil =>
    simp [ShortResetReleased.BeforeConsume,ShortResetReleased.stageRun]
  | cons e u ih =>
    change (st≠.done ∧ ShortResetReleased.BeforeConsume C
        (nextStage C e st) (u++v)) ↔
      (st≠.done ∧ ShortResetReleased.BeforeConsume C
        (nextStage C e st) u) ∧
      ShortResetReleased.BeforeConsume C
        (ShortResetReleased.stageRun C (nextStage C e st) u) v
    rw [ih]
    exact and_assoc.symm

private theorem next_done_iff (C : Chart h) (e : Fin n)
    (st : Stage) (L : st≠.done) :
    nextStage C e st=.done ↔ st=.rev 0 ∧ rightNeighbor e=C.root := by
  cases st with
  | done => exact False.elim (L rfl)
  | fwd i =>
    by_cases E : e=nextAt C.root i
    · by_cases J : i+1<C.L <;> simp [nextStage,E,J]
    · simp [nextStage,E]
  | rev i =>
    cases i with
    | zero =>
      by_cases E : rightNeighbor e=C.root <;> simp [nextStage,E]
    | succ i =>
      by_cases E : e=nextAt C.root i <;> simp [nextStage,E]

private theorem nil_or_snoc {A : Type} (w : List A) :
    w=[] ∨ ∃ v e, w=v++[e] := by
  induction w with
  | nil => exact .inl rfl
  | cons a w ih =>
    rcases ih with H|⟨v,e,H⟩
    · subst w
      exact .inr ⟨[],a,rfl⟩
    · exact .inr ⟨a::v,e,congrArg (List.cons a) H⟩

private theorem snoc_inj {A : Type} (u v : List A) (e f : A)
    (W : u++[e]=v++[f]) : u=v ∧ e=f := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil =>
      have H : [e]=[f] := W
      exact ⟨rfl,(List.cons.inj H).1⟩
    | cons b v =>
      have H := congrArg List.length W
      simp only [List.length_append,List.length_cons,List.length_nil] at H
      omega
  | cons a u ih =>
    cases v with
    | nil =>
      have H := congrArg List.length W
      simp only [List.length_append,List.length_cons,List.length_nil] at H
      omega
    | cons b v =>
      change a::(u++[e])=b::(v++[f]) at W
      obtain ⟨P,Q⟩ := List.cons.inj W
      obtain ⟨R,S⟩ := ih v Q
      exact ⟨by rw [P,R],S⟩

/-- Exactly the reset.done branch, on the current actual letter. -/
theorem genuine_snoc_iff (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (e : Fin n) :
    GenuineAt C x (w++[e]) ↔ GenuineConsumeAt C x w e := by
  constructor
  · rintro ⟨a,t,W,I,B,D⟩
    rcases nil_or_snoc t with Z|⟨u,f,T⟩
    · subst t
      change Stage.fwd 0=Stage.done at D
      contradiction
    · subst t
      have S : w++[e]=(a++door C::u)++[f] := by
        calc
          _ = a++door C::(u++[f]) := W
          _ = _ := by simp [List.append_assoc]
      obtain ⟨Q,F⟩ := snoc_inj w (a++door C::u) e f S
      subst f
      have M := (before_append C (.fwd 0) u [e]).mp B
      have L : ShortResetReleased.stageRun C (.fwd 0) u≠.done :=
        M.2.1
      rw [stage_append] at D
      change nextStage C e
        (ShortResetReleased.stageRun C (.fwd 0) u)=.done at D
      obtain ⟨R,E⟩ := (next_done_iff C e _ L).mp D
      exact ⟨a,u,Q,I,M.1,R,E⟩
  · rintro ⟨a,u,W,I,B,R,E⟩
    refine ⟨a,u++[e],?_,I,?_,?_⟩
    · rw [W]
      simp [List.append_assoc]
    · apply (before_append C (.fwd 0) u [e]).mpr
      refine ⟨B,?_⟩
      rw [R]
      exact ⟨by decide,trivial⟩
    · rw [stage_append,R]
      simp [ShortResetReleased.stageRun,nextStage,E]

theorem genuine_at_nil (C : Chart h) (x : Raw s n) :
    ¬ GenuineAt C x [] := by
  rintro ⟨a,t,W,_,_,_⟩
  have H := congrArg List.length W
  simp only [List.length_append,List.length_cons,List.length_nil] at H
  omega

theorem genuine_prepend (C : Chart h) (x : Raw s n)
    (a u : List (Fin n)) (R : GenuineAt C (rawRun x a) u) :
    GenuineAt C x (a++u) := by
  obtain ⟨b,t,W,I,B,D⟩ := R
  refine ⟨a++b,t,?_,?_,B,D⟩
  · rw [W,List.append_assoc]
  · rw [raw_append]
    exact I

/-- Convert the true-bit first-goal segment after a real launch
    into the existing stopped RESET cursor. -/
theorem goal_to_stage (C : Chart h) (N : 5≤n)
    (x : Raw s n) (G : Geom C x) (st : Stage)
    (A : ShortResetCycle.Active C x st) (w : List (Fin n))
    (B : BeforeGoal C (x,true) w)
    (H : ShortActualIssueClock.Goal C
      (ShortObservedResetRelease.run C (x,true) w)) :
    ShortResetReleased.BeforeConsume C st w ∧
      ShortResetReleased.stageRun C st w=.done := by
  induction w generalizing x st with
  | nil =>
    refine ⟨trivial,?_⟩
    change ShortActualIssueClock.Goal C (x,true) at H
    change st=.done
    cases st with
    | done => rfl
    | fwd i =>
      have F : get (x C.root).mis1 81 2 (by decide)=2 := A.2.1.1
      have P : get (x C.root).mis1 81 2 (by decide)=1 := H.2.2.1
      omega
    | rev i =>
      have F : get (x C.root).mis1 81 2 (by decide)=2 := A.2.1.1
      have P : get (x C.root).mis1 81 2 (by decide)=1 := H.2.2.1
      omega
  | cons e w ih =>
    -- CHECK: the identical ClearBefore reductions are used in
    -- ShortObservedResetRelease.lean:49-64.
    change ¬ShortActualIssueClock.Goal C (x,true) ∧
      BeforeGoal C (ShortActualIssueClock.step C (x,true) e) w at B
    change ShortActualIssueClock.Goal C
      (ShortObservedResetRelease.run C
        (ShortActualIssueClock.step C (x,true) e) w) at H
    have L : st≠.done := by
      intro D
      subst st
      exact B.1 ⟨rfl,A⟩
    have S : ShortActualIssueClock.step C (x,true) e=
        (rawNext s x e,true) := rfl
    rw [S] at B H
    have A' := ShortResetCycle.active_step C x e (by omega) G.2 st L A
    have K := ih (rawNext s x e) (geom_step C x N G e)
      (nextStage C e st) A' B.2 H
    exact ⟨⟨L,K.1⟩,K.2⟩

theorem first_goal_genuine (C : Chart h) (N : 5≤n)
    (x : Raw s n) (G : Geom C x) (w : List (Fin n))
    (B : BeforeGoal C (x,false) w)
    (H : ShortActualIssueClock.Goal C
      (ShortObservedResetRelease.run C (x,false) w)) :
    ShortResetHelloSplice.Parked C (rawRun x w) ∧ GenuineAt C x w := by
  obtain ⟨P,a,t,W,I,A,F,K⟩ :=
    ShortEpochResetOrigin.genuine_reset_seed N C x G.1 G.2 w B H
  let z := rawNext s (rawRun x a) (door C)
  have Gz : Geom C z :=
    geom_step C (rawRun x a) N (geom_run C x N G a) (door C)
  have Q := goal_to_stage C N z Gz (.fwd 0) A t F K
  exact ⟨P,a,t,W,I,Q.1,Q.2⟩

/-- Every detected completion gives a genuine Parked seed,
    independently of which receipt was first credited. -/
theorem genuine_parked (C : Chart h) (N : 5≤n)
    (x : Raw s n) (G : Geom C x) (w : List (Fin n))
    (H : GenuineAt C x w) :
    ShortResetHelloSplice.Parked C (rawRun x w) := by
  obtain ⟨a,t,W,I,B,D⟩ := H
  have G0 := geom_run C x N G a
  have R := ShortResetReleased.released_from_actual_issue
    C N (rawRun x a) G0.1 G0.2 I t B D
  rw [W,raw_append]
  exact ShortResetHelloSplice.parked_after_consume C _ R.1 R.2

/-- Actual old physical return snapshot for the counted mark. -/
theorem genuine_consume_old (C : Chart h) (N : 5≤n)
    (x : Raw s n) (G : Geom C x)
    (w : List (Fin n)) (e : Fin n)
    (H : GenuineConsumeAt C x w e) :
    rightNeighbor e=C.root ∧
      ShortResetCycle.Active C (rawRun x w) (.rev 0) ∧
      ShortResetReleased.Released C (rawRun x w) (.rev 0) := by
  obtain ⟨a,t,W,I,B,D,E⟩ := H
  let z := rawNext s (rawRun x a) (door C)
  have G0 := geom_run C x N G a
  have Gz : Geom C z := geom_step C (rawRun x a) N G0 (door C)
  have A : ShortResetCycle.Active C z (.fwd 0) :=
    (ShortActualIssueClock.actual_issue C N (rawRun x a) G0.2 I).2
  have R := ShortResetReleased.raw_run_released C N t z (.fwd 0)
    Gz.1 Gz.2 A (ShortResetReleased.released_at_issue C z) B
  rw [D] at R
  refine ⟨E,?_⟩
  rw [W,raw_append]
  exact R

theorem genuine_consume_wire (C : Chart h) (N : 5≤n)
    (x : Raw s n) (G : Geom C x)
    (w : List (Fin n)) (e : Fin n)
    (H : GenuineConsumeAt C x w e) :
    rightNeighbor e=C.root ∧
      Wait0 (rawRun x w) C.root ∧
      (kField 0).read (rawRun x w C.root).mis1=encode resetReply ∧
      ShortResetHelloSplice.Parked C (rawNext s (rawRun x w) e) := by
  obtain ⟨E,A,_⟩ := genuine_consume_old C N x G w e H
  have W := A.2.2 0 C.positive
  -- CHECK: Rev's literal field projection,
  -- ShortResetReverseChart.lean:11-16, ShortResetCycle.lean:158-163.
  change (kField (lane C.a C.b 0)).read (rawRun x w C.root).mis1 =
      encode (ShortResetReverseChart.trailAt 0 0) at W
  rw [C.rootPort] at W
  have W' : (kField 0).read (rawRun x w C.root).mis1=encode resetReply := by
    simpa [ShortResetReverseChart.trailAt] using W
  have P := genuine_parked C N x G (w++[e])
    ((genuine_snoc_iff C x w e).mpr H)
  rw [raw_snoc] at P
  exact ⟨E,A.2.1,W',P⟩

/-! Latest-index update. The index is an attained maximum,
    not merely an upper bound or a historically credited receipt. -/

private theorem prefix_snoc {A : Type} (w : List A) (e : A)
    (p t : List A) (W : w++[e]=p++t) :
    p=w++[e] ∨ ∃ v, w=p++v := by
  induction w generalizing p with
  | nil =>
    cases p with
    | nil => exact .inr ⟨[],rfl⟩
    | cons a p =>
      cases p with
      | nil =>
        have E : e=a := (List.cons.inj W).1
        subst a
        exact .inl rfl
      | cons b p =>
        change [e]=a::b::(p++t) at W
        simp at W
  | cons a w ih =>
    cases p with
    | nil => exact .inr ⟨a::w,rfl⟩
    | cons b p =>
      change a::(w++[e])=b::(p++t) at W
      obtain ⟨E,F⟩ := List.cons.inj W
      subst b
      rcases ih p F with R|⟨v,R⟩
      · exact .inl (congrArg (List.cons a) R)
      · exact .inr ⟨v,congrArg (List.cons a) R⟩

def Latest (C : Chart h) (x : Raw s n) (w : List (Fin n)) :
    Option Nat → Prop
  | none =>
      ∀ p t : List (Fin n), w=p++t → ¬GenuineAt C x p
  | some k =>
      (∃ p t : List (Fin n),
        w=p++t ∧ p.length=k ∧ GenuineAt C x p) ∧
      (∀ p t : List (Fin n),
        w=p++t → GenuineAt C x p → p.length≤k)

theorem latest_start (C : Chart h) (x : Raw s n) :
    Latest C x [] none := by
  intro p t W H
  have L := congrArg List.length W
  simp only [List.length_nil,List.length_append] at L
  cases p with
  | nil => exact genuine_at_nil C x H
  | cons a p =>
    simp only [List.length_cons] at L
    omega

noncomputable def advanceIndex (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (k : Option Nat) (e : Fin n) : Option Nat := by
  classical
  exact if GenuineConsumeAt C x w e then some (w.length+1) else k

theorem advanceIndex_hit (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (k : Option Nat) (e : Fin n)
    (H : GenuineConsumeAt C x w e) :
    advanceIndex C x w k e=some (w.length+1) := by
  classical
  simp only [advanceIndex,if_pos H]

theorem advanceIndex_miss (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (k : Option Nat) (e : Fin n)
    (H : ¬GenuineConsumeAt C x w e) :
    advanceIndex C x w k e=k := by
  classical
  simp only [advanceIndex,if_neg H]

theorem latest_step (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (k : Option Nat) (e : Fin n)
    (A : Latest C x w k) :
    Latest C x (w++[e]) (advanceIndex C x w k e) := by
  classical
  by_cases H : GenuineConsumeAt C x w e
  · rw [advanceIndex_hit C x w k e H]
    change (∃ p t : List (Fin n), w++[e]=p++t ∧
        p.length=w.length+1 ∧ GenuineAt C x p) ∧
      (∀ p t : List (Fin n), w++[e]=p++t →
        GenuineAt C x p → p.length≤w.length+1)
    refine ⟨⟨w++[e],[],by simp,by simp,
      (genuine_snoc_iff C x w e).mpr H⟩,?_⟩
    intro p t W _
    have L := congrArg List.length W
    simp only [List.length_append,List.length_cons,List.length_nil] at L
    omega
  · rw [advanceIndex_miss C x w k e H]
    have absent : ¬GenuineAt C x (w++[e]) :=
      fun K => H ((genuine_snoc_iff C x w e).mp K)
    cases k with
    | none =>
      intro p t W R
      rcases prefix_snoc w e p t W with P|⟨v,V⟩
      · exact absent (P ▸ R)
      · exact A p v V R
    | some j =>
      obtain ⟨⟨p,t,W,L,R⟩,M⟩ := A
      refine ⟨⟨p,t++[e],?_,L,R⟩,?_⟩
      · rw [W,List.append_assoc]
      · intro q r V F
        rcases prefix_snoc w e q r V with P|⟨v,V'⟩
        · exact False.elim (absent (P ▸ F))
        · exact M q v V' F

theorem latest_some (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (i : Option Nat)
    (A : Latest C x w i) (p t : List (Fin n))
    (W : w=p++t) (H : GenuineAt C x p) :
    ∃ k, i=some k := by
  cases i with
  | none => exact False.elim (A p t W H)
  | some k => exact ⟨k,rfl⟩

/-! Enriched monitor, still driven by the original sequential
    clock's exact raw transition on every original mark. -/

structure State (s n : Nat) (h : Fin n → Bool) where
  clock : SequentialMarkClock.State (Raw s n) Bool (Certified s n h)
  tape : List (Fin n)
  latest : Chart h → Option Nat

def monitorStart (x : Raw s n) (cs : List (Certified s n h)) :
    State s n h :=
  ⟨SequentialMarkClock.start false cs x,[],fun _=>none⟩

noncomputable def monitorNext (x : Raw s n) (z : State s n h)
    (e : Fin n) : State s n h :=
  ⟨ShortSequentialClean.next z.clock e,
    z.tape++[e],
    fun C=>advanceIndex C x z.tape (z.latest C) e⟩

def finished (z : State s n h) : Prop :=
  SequentialMarkClock.finished z.clock

theorem monitor_raw_step (x : Raw s n) (z : State s n h)
    (e : Fin n) :
    (monitorNext x z e).clock.raw=rawNext s z.clock.raw e :=
  ShortSequentialClean.actual_raw_step z.clock e

theorem monitor_index_hit (x : Raw s n) (z : State s n h)
    (C : Chart h) (e : Fin n)
    (H : GenuineConsumeAt C x z.tape e) :
    (monitorNext x z e).latest C=some (z.tape.length+1) :=
  advanceIndex_hit C x z.tape (z.latest C) e H

theorem monitor_index_miss (x : Raw s n) (z : State s n h)
    (C : Chart h) (e : Fin n)
    (H : ¬GenuineConsumeAt C x z.tape e) :
    (monitorNext x z e).latest C=z.latest C :=
  advanceIndex_miss C x z.tape (z.latest C) e H

private theorem run_snoc {Z : Type} (step : Z→Fin n→Z)
    (z : Z) (w : List (Fin n)) (e : Fin n) :
    SequentialMarkClock.run step z (w++[e])=
      step (SequentialMarkClock.run step z w) e := by
  induction w generalizing z with
  | nil => rfl
  | cons f w ih => exact ih (step z f)

/-- No fabricated empty todo monitor or unanchored latest index. -/
def Correct (x : Raw s n) (cs : List (Certified s n h))
    (z : State s n h) : Prop :=
  z.clock=SequentialMarkClock.run ShortSequentialClean.next
    (SequentialMarkClock.start false cs x) z.tape ∧
  ∀ C : Chart h, Latest C x z.tape (z.latest C)

theorem correct_start (x : Raw s n) (cs : List (Certified s n h)) :
    Correct x cs (monitorStart x cs) :=
  ⟨rfl,fun C=>latest_start C x⟩

theorem correct_step (x : Raw s n) (cs : List (Certified s n h))
    (z : State s n h) (e : Fin n) (A : Correct x cs z) :
    Correct x cs (monitorNext x z e) := by
  constructor
  · -- CHECK: original next/state alias, ShortSequentialClean.lean:25-34.
    change ShortSequentialClean.next z.clock e =
      SequentialMarkClock.run ShortSequentialClean.next
        (SequentialMarkClock.start false cs x) (z.tape++[e])
    rw [run_snoc,A.1]
  · intro C
    exact latest_step C x z.tape (z.latest C) e (A.2 C)

theorem correct_run (x : Raw s n) (cs : List (Certified s n h))
    (z : State s n h) (A : Correct x cs z) (w : List (Fin n)) :
    Correct x cs (SequentialMarkClock.run (monitorNext x) z w) := by
  induction w generalizing z with
  | nil => exact A
  | cons e w ih =>
    exact ih (monitorNext x z e) (correct_step x cs z e A)

theorem tape_run (x : Raw s n) (z : State s n h)
    (w : List (Fin n)) :
    (SequentialMarkClock.run (monitorNext x) z w).tape=z.tape++w := by
  induction w generalizing z with
  | nil => simp [SequentialMarkClock.run]
  | cons e w ih =>
    change (SequentialMarkClock.run (monitorNext x)
      (monitorNext x z e) w).tape=z.tape++e::w
    rw [ih]
    change (z.tape++[e])++w=z.tape++e::w
    simp only [List.append_assoc,List.cons_append,List.nil_append]

theorem clock_run (x : Raw s n) (z : State s n h)
    (w : List (Fin n)) :
    (SequentialMarkClock.run (monitorNext x) z w).clock =
      SequentialMarkClock.run ShortSequentialClean.next z.clock w := by
  induction w generalizing z with
  | nil => rfl
  | cons e w ih => exact ih (monitorNext x z e)

theorem physical_run (x : Raw s n) (z : State s n h)
    (w : List (Fin n)) :
    (SequentialMarkClock.run (monitorNext x) z w).clock.raw =
      rawRun z.clock.raw w := by
  induction w generalizing z with
  | nil => rfl
  | cons e w ih =>
    change (SequentialMarkClock.run (monitorNext x)
      (monitorNext x z e) w).clock.raw=rawRun (rawNext s z.clock.raw e) w
    rw [ih,monitor_raw_step]

/-! E4+: construct the actual current owner epoch from its own
    latest attained prefix, including its fixed ADMIT gate. -/

theorem fixed_gate_for_chart (x : Raw s n) (X : H2Ready x)
    (N : 9<n) (C : Chart (header x)) :
    0<C.a ∧ C.a+1<C.L ∧
      ShortAdmitFlight.FixedGate (s:=s) C C.a := by
  have F := ShortReadCaptureGeometry.capture_chart_fields x X.1 C N
  have pos : 0<C.a := by rcases F.1 with R|R <;> omega
  have room := (ShortPublishChart.stage_seal_centre x x X X
    C N (fun _=>rfl)).1
  refine ⟨pos,room,?_⟩
  intro y Y heads k K
  -- CHECK: gated and slotGate are the same definition,
  -- ShortAdmitForward.lean:13-14, ShortGateChart.lean:7-8,
  -- ShortAdmitFlight.lean:114-116.
  change ShortGateChart.slotGate C y k=true ↔ k=C.a
  exact (ShortPublishChart.stage_seal_centre x y X Y C N heads).2.2.1 k K

theorem first_hit_has_genuine_prefix (x : Raw s n) (X : H2Ready x)
    (N : 9<n) (cs : List (Certified s n (header x)))
    (w : List (Fin n))
    (R : SequentialMarkClock.FirstHitReceipts
      phase goal false cs (x,false) w)
    (c : Certified s n (header x)) (M : c∈cs) :
    ∃ p t : List (Fin n), w=p++t ∧ GenuineAt c.chart x p := by
  obtain ⟨a,u,v,W,_,B,H⟩ :=
    ShortEpochFirstHit.first_goal_prefix cs x w R c M
  have G := geom_run c.chart x (by omega) ⟨X,fun _=>rfl⟩ a
  have K := first_goal_genuine c.chart (by omega) (rawRun x a) G u B H
  exact ⟨a++u,v,W,genuine_prepend c.chart x a u K.2⟩

/-- The actual latest post-consume cut, the identical suffix,
    and the owner epoch replay from THAT cut. -/
def AtLatest (x : Raw s n) (C : Chart (header x))
    (w : List (Fin n)) (y : Raw s n) (k : Nat) : Prop :=
  ∃ p t : List (Fin n),
    w=p++t ∧ p.length=k ∧ GenuineAt C x p ∧
    (∀ a b : List (Fin n),
      w=a++b → GenuineAt C x a → a.length≤k) ∧
    ShortResetHelloSplice.Parked C (rawRun x p) ∧
    y=rawRun (rawRun x p) t ∧
    OwnerEpoch C (rawRun x p) t C.a

theorem at_latest_ownerInv (x : Raw s n) (C : Chart (header x))
    (w : List (Fin n)) (y : Raw s n) (k : Nat)
    (A : AtLatest x C w y k) :
    OwnerInv C y C.a := by
  obtain ⟨p,t,_,_,_,_,_,Y,E⟩ := A
  rw [Y]
  exact E

theorem at_latest_of_some (x : Raw s n) (X : H2Ready x)
    (N : 9<n) (C : Chart (header x))
    (w : List (Fin n)) (k : Nat)
    (A : Latest C x w (some k)) :
    AtLatest x C w (rawRun x w) k := by
  obtain ⟨⟨p,t,W,L,R⟩,Max⟩ := A
  have G : Geom C x := ⟨X,fun _=>rfl⟩
  have P := genuine_parked C (by omega) x G p R
  have Y := geom_run C x (by omega) G p
  obtain ⟨gp,gL,gates⟩ := fixed_gate_for_chart x X N C
  have E := epoch_from_parked C (rawRun x p) N Y P
    C.a gp gL gates t
  refine ⟨p,t,W,L,R,Max,P,?_,E⟩
  rw [W,raw_append]

/-- All later resets can supersede the first credited receipt.
    This returns the attained maximum, rather than that initial
    receipt's index. -/
theorem latest_from_first_hits (x : Raw s n) (X : H2Ready x)
    (N : 9<n) (cs : List (Certified s n (header x)))
    (w : List (Fin n))
    (R : SequentialMarkClock.FirstHitReceipts
      phase goal false cs (x,false) w)
    (c : Certified s n (header x)) (M : c∈cs)
    (i : Option Nat) (A : Latest c.chart x w i) :
    ∃ k, i=some k ∧ AtLatest x c.chart w (rawRun x w) k := by
  obtain ⟨p,t,W,H⟩ := first_hit_has_genuine_prefix x X N cs w R c M
  obtain ⟨k,E⟩ := latest_some c.chart x w i A p t W H
  rw [E] at A
  exact ⟨k,E,at_latest_of_some x X N c.chart w k A⟩

/-- HistoricalOn must refer to the actual observed word. It yields
    a latest anchored replay for every selected root, on a single
    common endpoint, with no simultaneous Parked assertion. -/
theorem latest_from_history (x : Raw s n) (X : H2Ready x)
    (N : 9<n) (w : List (Fin n)) (y : Raw s n)
    (H : ShortAllOwnerSound.HistoricalOn x w y)
    (idx : Chart (header x)→Option Nat)
    (A : ∀ C, Latest C x w (idx C)) :
    ∀ r : Fin n, header x r=true →
      ∃ C : Chart (header x), C.root=r ∧
        ∃ k, idx C=some k ∧ AtLatest x C w y k := by
  obtain ⟨Y,cs,_,cover,R⟩ := H
  subst y
  intro r hr
  obtain ⟨c,M,E⟩ := (cover r).mp hr
  exact ⟨c.chart,E,
    latest_from_first_hits x X N cs w R c M (idx c.chart) (A c.chart)⟩

/-- Exact same-tape E4+ consumer at the enriched monitor endpoint.
    Includes each roster member's own index and the selected-root
    coverage, not just an existential alternative raw history. -/
theorem latest_at_finished (x : Raw s n) (X : H2Ready x)
    (N : 9<n) (cs : List (Certified s n (header x)))
    (w : List (Fin n))
    (E : cs.map (fun c=>c.chart.root)=ShortAllOwnerClock.roots (header x))
    (D : finished (SequentialMarkClock.run (monitorNext x)
      (monitorStart x cs) w)) :
    let z := SequentialMarkClock.run (monitorNext x) (monitorStart x cs) w
    z.tape=w ∧ z.clock.raw=rawRun x w ∧
      (∀ c∈cs, ∃ k, z.latest c.chart=some k ∧
        AtLatest x c.chart w z.clock.raw k) ∧
      (∀ r : Fin n, header x r=true →
        ∃ C : Chart (header x), C.root=r ∧
          ∃ k, z.latest C=some k ∧ AtLatest x C w z.clock.raw k) := by
  let z := SequentialMarkClock.run (monitorNext x) (monitorStart x cs) w
  have T : z.tape=w := by
    have K := tape_run x (monitorStart x cs) w
    change z.tape = [] ++ w at K
    simpa only [List.nil_append] using K
  have A : Correct x cs z :=
    correct_run x cs (monitorStart x cs) (correct_start x cs) w
  have C := A.1
  have idx := A.2
  rw [T] at C idx
  have D' : SequentialMarkClock.finished
      (SequentialMarkClock.run ShortSequentialClean.next
        (SequentialMarkClock.start false cs x) w) := by
    rw [←C]
    exact D
  -- CHECK: ShortAllOwnerSound.lean:18-30 and
  -- ShortAllOwnerClock.lean:130-145 use the same next alias.
  have H := ShortAllOwnerSound.history_on_actual_tape x cs w E D'
  rw [←C] at H
  obtain ⟨cover,R⟩ := ShortAllOwnerClock.all_owner_first_hit_receipts x cs w E D'
  refine ⟨T,H.1,?_,latest_from_history x X N w z.clock.raw H z.latest idx⟩
  intro c M
  obtain ⟨k,K,P⟩ :=
    latest_from_first_hits x X N cs w R c M (z.latest c.chart) (idx c.chart)
  exact ⟨k,K,H.1.symm ▸ P⟩

/-- History-free raw predicate for the next E5 consumer. It is
    weaker than the indexed endpoint statement, but is forward
    closed and now has a genuine ReceiptSound proof. -/
def CurrentOwners (x y : Raw s n) : Prop :=
  ∀ r : Fin n, header x r=true →
    ∃ C : Chart (header x), C.root=r ∧ OwnerInv C y C.a

theorem current_owners_closed (x y : Raw s n) (X : H2Ready x)
    (N : 9<n) (e : Fin n) (A : CurrentOwners x y) :
    CurrentOwners x (rawNext s y e) := by
  intro r hr
  obtain ⟨C,R,P⟩ := A r hr
  obtain ⟨gp,gL,gates⟩ := fixed_gate_for_chart x X N C
  exact ⟨C,R,owner_raw_step C y N C.a gp gL gates e P⟩

theorem current_owners_receipt_sound (x : Raw s n) (X : H2Ready x)
    (N : 9<n) :
    ShortAllOwnerSound.ReceiptSound x (CurrentOwners x) := by
  intro w y H
  obtain ⟨Y,cs,E,cover,R⟩ := H
  have H' : ShortAllOwnerSound.HistoricalOn x w y :=
    ⟨Y,cs,E,cover,R⟩
  let z := SequentialMarkClock.run (monitorNext x) (monitorStart x cs) w
  have T : z.tape=w := by
    have K := tape_run x (monitorStart x cs) w
    change z.tape = [] ++ w at K
    simpa only [List.nil_append] using K
  have A : Correct x cs z :=
    correct_run x cs (monitorStart x cs) (correct_start x cs) w
  have idx := A.2
  rw [T] at idx
  intro r hr
  obtain ⟨C,K,k,_,P⟩ :=
    latest_from_history x X N w y H' z.latest idx r hr
  exact ⟨C,K,at_latest_ownerInv x C w y k P⟩

set_option exponentiation.threshold 8100 in
theorem current_owners_expected (x : Raw s n) (X : H2Ready x)
    (N : 9<n) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (CurrentOwners x) x
      ((10^8095+19)*n^2) :=
  ShortAllOwnerSound.raw_expected_of_receipts N x X (CurrentOwners x)
    (current_owners_receipt_sound x X N)

end L4.ShortLatestResetMonitor
