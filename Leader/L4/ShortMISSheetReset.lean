import Leader.L4.ShortMISSheetParked
import Leader.L4.ShortResetReleased
import Leader.L4.ResetReturnIID

namespace L4.ShortMISSheetReset
open AllSizeProtocol PhysicalCustody ShortMISEngine MISByteCodec
open ShortResetChart ShortResetCycle ShortResetMIS1Ring
open ShortMISSheetParked ShortResetReleased ShortResetFlow
open ShortMISLift (Issuable resetStep resetGoal)

variable {s n : Nat}

private theorem active_congr {h : Fin n → Bool} (C : Chart h)
    (x y : Raw s n) (H : ∀ q,(x q).mis1=(y q).mis1) (st : Stage) :
    Active C x st ↔ Active C y st := by
  cases st <;> simp only [Active,Wait0,Complete,
    ShortResetForwardH2.TrailPrefix,ShortResetForwardH2.bits,ShortResetReverseChart.Rev,H]

private theorem released_congr {h : Fin n → Bool} (C : Chart h)
    (x y : Raw s n) (H : ∀ q,(x q).mis1=(y q).mis1) (st : Stage) :
    Released C x st ↔ Released C y st := by
  simp only [Released,H]

theorem actual_issue (P : Params s n) (C : Chart P.h) (x : Raw s n)
    (X : Cached P x) (I : Issuable P C x) (e : Fin n)
    (E : e=RearTrace.predecessor C.root) :
    Active C (view P (rawNext s x e)) (.fwd 0) := by
  have N : 1<n := by have := C.positive; have := C.length_lt; omega
  let z := view P x
  obtain ⟨F,O⟩ := ShortActualIssueClock.issuable_fields C z I
  have R : rightNeighbor e=C.root := E ▸ RearTrace.right_predecessor C.root
  obtain ⟨W,B⟩ := begin_reset C z e (edge_sep N e) R
    ((view_header P x _).trans C.rootHeader) F O
  apply (active_congr C _ _ (view_next P x X e) _).mp
  exact ⟨C.positive,W,fun _ H=>False.elim (Nat.not_lt_zero _ H),B⟩

theorem actual_step (P : Params s n) (C : Chart P.h) (x : Raw s n)
    (X : Cached P x) (e : Fin n) (st : Stage) (D : st≠.done)
    (A : Active C (view P x) st) (R : Released C (view P x) st) :
    Active C (view P (rawNext s x e)) (nextStage C e st) ∧
      Released C (view P (rawNext s x e)) (nextStage C e st) := by
  have N : 1<n := by have := C.positive; have := C.length_lt; omega
  exact ⟨(active_congr C _ _ (view_next P x X e) _).mp
      (active_step C (view P x) e N (view_header P x) st D A),
    (released_congr C _ _ (view_next P x X e) _).mp
      (step_released C (view P x) e N (view_header P x) st D A R)⟩

private theorem issue_hold (P : Params s n) (C : Chart P.h) (x : Raw s n)
    (X : Cached P x) (I : Issuable P C x) (e : Fin n)
    (E : e≠RearTrace.predecessor C.root) : Issuable P C (rawNext s x e) := by
  have H := ShortActualIssueClock.issuable_nondoor C (view P x)
    ((view_header P x _).trans C.rootHeader) I e E
  unfold ShortActualIssueClock.Issuable at H
  rwa [view_next P x X e] at H

private theorem live_lt {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (st : Stage) (D : st≠.done) (A : Active C x st) :
    match st with | .fwd k | .rev k => k<C.L | .done => False := by
  cases st
  · exact A.1
  · exact A.1
  · exact D rfl

private theorem positive {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (st : Stage) (D : st≠.done) (A : Active C x st) : 0<debt C.L st := by
  have H := live_lt C x st D A
  cases st
  · simp only [debt]; omega
  · simp [debt]
  · contradiction

private def Seen (P : Params s n) (C : Chart P.h)
    (y : Raw s n × Bool) (r : Nat) : Prop :=
  Cached P y.1 ∧
    ((y.2=false ∧ Issuable P C y.1 ∧ r=2*C.L+1) ∨
    (y.2=true ∧ ∃ st, st≠.done ∧ Active C (view P y.1) st ∧ r=debt C.L st))

theorem clean (P : Params s n) (C : Chart P.h) (x : Raw s n)
    (X : Cached P x) (I : Issuable P C x) :
    Height.IIDExpectedHittingTimeAtMost (resetStep P C) (resetGoal P C)
      (x,false) ((2*C.L+1)*n) := by
  rw [Nat.mul_comm]
  refine ResetReturnIID.iid_of_relational_rank _ _ (Seen P C) ?_ ?_ _ _
    (.inr ⟨X,.inl ⟨rfl,I,rfl⟩⟩)
  · rintro ⟨x,b⟩ r ⟨_,⟨_,_,rfl⟩|⟨_,st,D,A,rfl⟩⟩
    · omega
    · exact positive C _ st D A
  · rintro ⟨x,b⟩ r ⟨X,⟨rfl,I,rfl⟩|⟨rfl,st,D,A,rfl⟩⟩
    · refine ⟨RearTrace.predecessor C.root,fun e=>?_⟩
      by_cases H : e=RearTrace.predecessor C.root
      · have step : resetStep P C (x,false) e=(rawNext s x e,true) := by
          simp [resetStep,I,H]
        rw [step]
        exact .inr ⟨2*C.L,⟨P.cached_closed x e X,
          .inr ⟨rfl,.fwd 0,by decide,actual_issue P C x X I e H,by simp [debt]⟩⟩,
          by omega,fun _=>by omega⟩
      · have step : resetStep P C (x,false) e=(rawNext s x e,false) := by
          simp [resetStep,H]
        rw [step]
        exact .inr ⟨2*C.L+1,⟨P.cached_closed x e X,
          .inl ⟨rfl,issue_hold P C x X I e H,rfl⟩⟩,Nat.le_refl _,fun hx=>False.elim (H hx)⟩
    · obtain ⟨weak,e0,strong⟩ := debt_step C st (by cases st; exact A.1; exact A.1; exact D rfl)
      refine ⟨e0,fun e=>?_⟩
      have step : resetStep P C (x,true) e=(rawNext s x e,true) := rfl
      rw [step]
      have N : 1<n := by have := C.positive; have := C.length_lt; omega
      have A' : Active C (view P (rawNext s x e)) (nextStage C e st) :=
        (active_congr C _ (view P (rawNext s x e)) (view_next P x X e) _).mp
        (active_step C (view P x) e N (view_header P x) st D A)
      by_cases H : nextStage C e st=.done
      · rw [H] at A'
        exact .inl ⟨rfl,A'⟩
      · exact .inr ⟨_,⟨P.cached_closed x e X,.inr ⟨rfl,_,H,A',rfl⟩⟩,weak e,
          fun hx=>hx.symm ▸ strong⟩

private abbrev Before (P : Params s n) (C : Chart P.h) :=
  SequentialMarkClock.ClearBefore (resetStep P C) (resetGoal P C)

private abbrev run (P : Params s n) (C : Chart P.h) :=
  SequentialMarkClock.run (resetStep P C)

private def LastConsume (P : Params s n) (C : Chart P.h)
    (x : Raw s n) (w : List (Fin n)) : Prop :=
  ∃ v : List (Fin n), ∃ e : Fin n, w=v++[e] ∧ rightNeighbor e=C.root ∧
      MISByteCodec.get (P.byte (rawRun x v) C.root) 81 2 (by decide)=2 ∧
      MISByteCodec.get (P.byte (rawRun x v) C.root) 78 3 (by decide)=0 ∧
      (MISByteCodec.kField 0).read (P.byte (rawRun x v) C.root)=encode resetReply

private theorem last_mark (P : Params s n) (C : Chart P.h) (x : Raw s n)
    (e : Fin n) (st : Stage) (A : Active C (view P x) st) (D : st≠.done)
    (H : nextStage C e st=.done) :
    LastConsume P C x [e] := by
  cases st with
  | done => exact False.elim (D rfl)
  | fwd k => simp only [nextStage] at H; split at H <;> (try split at H) <;> contradiction
  | rev k =>
    cases k with
    | succ k => simp only [nextStage] at H; split at H <;> contradiction
    | zero =>
      have E : rightNeighbor e=C.root := by
        by_cases F : rightNeighbor e=C.root
        · exact F
        · simp [nextStage,F] at H
      have W : Wait0 (view P x) C.root := A.2.1
      have B := A.2.2 0 C.positive
      change (kField (lane C.a C.b 0)).read (P.byte x C.root)=_ at B
      rw [C.rootPort] at B
      exact ⟨[],e,rfl,E,W.1,W.2,B⟩

private theorem active_not_goal (P : Params s n) (C : Chart P.h)
    (x : Raw s n) (st : Stage) (D : st≠.done) (A : Active C (view P x) st) :
    ¬resetGoal P C (x,true) := by
  intro H
  have W : Wait0 (view P x) C.root := by
    cases st
    · exact A.2.1
    · exact A.2.1
    · exact False.elim (D rfl)
  have F := W.1.symm.trans H.2.2.1
  contradiction

private theorem active_receipt (P : Params s n) (C : Chart P.h) (x : Raw s n)
    (X : Cached P x) (st : Stage) (D : st≠.done)
    (A : Active C (view P x) st) (R : Released C (view P x) st)
    (w : List (Fin n)) (F : Before P C (x,true) w)
    (H : resetGoal P C (run P C (x,true) w)) :
    BeforeConsume C st w ∧ stageRun C st w=.done ∧
    ShortMISLift.Parked P C (rawRun x w) ∧ LastConsume P C x w := by
  induction w generalizing x st with
  | nil => exact False.elim (active_not_goal P C x st D A H)
  | cons e t ih =>
    let y := rawNext s x e
    let st' := nextStage C e st
    change ¬resetGoal P C (x,true) ∧ Before P C (y,true) t at F
    change resetGoal P C (run P C (y,true) t) at H
    have Y := P.cached_closed x e X
    obtain ⟨A',R'⟩ := actual_step P C x X e st D A R
    by_cases J : st'=.done
    · change st'=.done at J
      change Active C (view P y) st' at A'
      change Released C (view P y) st' at R'
      rw [J] at A' R'
      cases t with
      | nil =>
        refine ⟨⟨D,trivial⟩,J,⟨A',?_⟩,last_mark P C x e st A D J⟩
        exact fun k K HH => R' k K HH trivial
      | cons i t =>
        exact False.elim (F.2.1 ⟨rfl,A'⟩)
    · obtain ⟨B,S,Cut,v,m,E,L⟩ := ih y Y st' J A' R' F.2 H
      refine ⟨⟨D,B⟩,S,Cut,e::v,m,?_,L⟩
      rw [E]
      rfl

/-- Genuine own RESET receipt on the original tape. A sticky issue bit
alone is insufficient: every proper prefix misses the observer target. -/
theorem firstHit (P : Params s n) (C : Chart P.h) (x : Raw s n)
    (X : Cached P x) (w : List (Fin n))
    (F : Before P C (x,false) w)
    (H : resetGoal P C (run P C (x,false) w)) :
    ShortMISLift.Receipt P C x w := by
  induction w generalizing x with
  | nil => exact False.elim (Bool.false_ne_true H.1)
  | cons e t ih =>
    let y := rawNext s x e
    change ¬resetGoal P C (x,false) ∧ Before P C (resetStep P C (x,false) e) t at F
    change resetGoal P C (run P C (resetStep P C (x,false) e) t) at H
    have Y := P.cached_closed x e X
    by_cases E : Issuable P C x ∧ e=RearTrace.predecessor C.root
    · have J : resetStep P C (x,false) e=(y,true) := by simp [resetStep,E,y]
      rw [J] at F H
      have A := actual_issue P C x X E.1 e E.2
      obtain ⟨B,S,Cut,v,m,W,L⟩ :=
        active_receipt P C y Y (.fwd 0) (by decide) A (released_at_issue C _) t F.2 H
      refine ⟨⟨[],t,?_,E.1,B,S⟩,Cut,e::v,m,?_,L⟩
      · rw [E.2]
        rfl
      · rw [W]
        rfl
    · have J : resetStep P C (x,false) e=(y,false) := by simp [resetStep,E,y]
      rw [J] at F H
      obtain ⟨⟨u,v,W,I,B,S⟩,Cut,a,m,V,L⟩ := ih y Y F.2 H
      refine ⟨⟨e::u,v,?_,I,B,S⟩,Cut,e::a,m,?_,L⟩
      · rw [W]
        rfl
      · rw [V]
        rfl

end L4.ShortMISSheetReset
