import Leader.L4.DirtyReplyOrigin
import Leader.L4.BStarClearanceRingDT

namespace L4.DirtyTrailSuffix
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarAcquireLiteralChain BStarAcquireVisitOrder BStarH6WordChart BStarAcquireForwardTrace
open BStarResetChartTouch BStarLongFixedRouting BStarClearanceIndexedSum BStarClearanceIndexedWait
open BStarClearanceSource BStarClearanceReplyService BStarClearanceRingDT BStarClearanceOffset
open BStarClearanceCommandFrame BStarClearanceCommandSum BStarClearanceAggregate
open DirtyReplyOrigin DirtyLeastForward

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => BStarClearanceOffset.X k₁ k₂ t₂ J₁ J₂ r c p c₁ n
local notation "step" => AllSizeS1Geometry.step (n:=n) B

private theorem total_one {A : Type} (l : List A) : total (fun _=>1) l=l.length := by
  induction l with
  | nil => rfl
  | cons a w ih => change 1+total (fun _=>1) w=w.length+1; rw [ih,Nat.add_comm]

private theorem total_zero {A : Type} {f : A→Nat} (l : List A) (h : ∀ a∈l,f a=0) :
    total f l=0 := by
  induction l with
  | nil => rfl
  | cons a w ih =>
    change f a+total f w=0
    rw [h a List.mem_cons_self,ih (fun z H=>h z (List.mem_cons_of_mem _ H))]

theorem physicalRank_zero {base y : X} {S : List (Pos n)}
    (NF : ∀ u∈S, ¬ringF y u) : total (physicalRank B base y (distance S)) S=0 := by
  apply total_zero
  intro u um
  let g := longGeometry B (base u.1)
  let raw : Pair (BitVec LW) := ((y u.1).long,(y u.1).long)
  exact no_forward_zero (g,g) (L u.2) (distance S u) (BStarLongRouting.readRaw raw (L u.2))
    (fun h=>NF u um ((isForward_iff _ _ _).mp h))

theorem replySum_zero {y : X} {S : List (Pos n)}
    (ND : ∀ u∈S, ¬ringD y u) : total (physicalDT y true (replyDistance S)) S=0 := by
  apply total_zero
  intro u U
  have h := ND u U
  change returnCount (atSite (y u.1).long u.2)≠1 at h
  change replyDistance S u*returnCount (atSite (y u.1).long u.2)=0
  cases z : atSite (y u.1).long u.2 <;> simp_all [returnCount]

/-- On the literal chart with no forward or reply, each nominated
trail-consuming mark pays one unit; the rank is just trail count. -/
theorem trail_suffix_expected {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (head : ∀ i,let g:=longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i,let g:=oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q x)
    (layout : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    (cb : correct (oldH6 B base) hh 5 base) (cy : ∀ y,Q y→correct (oldH6 B base) hh 5 y)
    (noF : ∀ u∈S, ¬ringF x u) (noD : ∀ u∈S, ¬ringD x u) :
    let root := (endpoint (oldH6 B base) hh o 0).1
    Height.IIDExpectedHittingTimeAtMost step (fun y=>¬Held (y root).long) x (n*S.length) := by
  classical
  dsimp only
  let root := (endpoint (oldH6 B base) hh o 0).1
  let stop := fun y : X=>¬Held (y root).long
  let Φ := fun y : X=>total (physicalDT y false (fun _=>1)) S
  let Live := fun y a=>Q y ∧ (∀ u∈S, ¬ringF y u) ∧ (∀ u∈S, ¬ringD y u) ∧
    Held (y root).long ∧ Φ y≤a
  have lenS := chart.length
  have root_mem : endpoint (oldH6 B base) hh o 0∈S := by
    rw [←chart.root,←List.getElem_eq_getD (h:=by omega) fall]
    exact List.getElem_mem _
  have rootTrail (y : X) (a : Nat) (Y : Live y a) : atSite (y root).long 0=.trail := by
    rcases Y.2.2.2.1.2.2 with T|⟨p,P⟩
    · exact T
    · exfalso
      apply Y.2.1 _ root_mem
      change forwardCount (atSite (y root).long 0)=1
      rw [P]
      rfl
  have pos (y : X) (a : Nat) (Y : Live y a) : 0<a := by
    obtain ⟨l,r,E⟩ := List.mem_iff_append.mp root_mem
    have b := Y.2.2.2.2
    change total (physicalDT y false (fun _=>1)) S≤a at b
    rw [E,total_append] at b
    change _ + (1*trail (atSite (y root).long 0) + _ )≤a at b
    rw [rootTrail y a Y] at b
    simp only [trail,Nat.mul_one] at b
    omega
  have advance (y : X) (a : Nat) (Y : Live y a) : ∃ d : Fin n,∀ e : Fin n,
      stop (step y e) ∨ ∃ a',Live (step y e) a' ∧ a'≤a ∧ (e=d→a'<a) := by
    have wait (e : Fin n) := held_before hp y root e Y.2.2.2.1
    have NF (e : Fin n) (u : Pos n) (U : u∈S) : ¬ringF (step y e) u := by
      intro F
      rcases ring_origin hp chart (layout _ Y.1) e (sep e) (wait e) u U F with same|⟨v,V,old,_⟩
      · exact Y.2.1 u U same
      · exact Y.2.1 v V old
    have ND (e : Fin n) (u : Pos n) (U : u∈S) : ¬ringD (step y e) u := by
      intro D
      rcases ring_reply_origin hp chart (layout _ Y.1) e (sep e) (wait e) Y.2.1 u U D with same|⟨v,V,old,_⟩
      · exact Y.2.2.1 u U same
      · exact Y.2.2.1 v V old
    have pay (e : Fin n) := ((indexed_DT_paying hp chart (layout _ Y.1) cb (cy y Y.1) e (sep e)
      (wait e) ((physicalRank_zero hp (NF e)).trans (physicalRank_zero hp Y.2.1).symm)).2.2
      ((replySum_zero (ND e)).trans (replySum_zero Y.2.2.1).symm))
    have mem (j : Nat) (J : j≤len) : S.getD j fall∈S := by
      rw [←List.getElem_eq_getD (h:=by omega) fall]
      exact List.getElem_mem _
    have quiet (j : Nat) (J : j≤len) :
        atCursor y (S.getD j fall)=.empty ∨ atCursor y (S.getD j fall)=.trail := by
      have F := Y.2.1 _ (mem j J)
      have D := Y.2.2.1 _ (mem j J)
      change forwardCount (atCursor y (S.getD j fall))≠1 at F
      change returnCount (atCursor y (S.getD j fall))≠1 at D
      cases z : atCursor y (S.getD j fall) <;> simp_all [forwardCount,returnCount]
    have source : atCursor y (S.getD 0 fall)=.trail := by
      rw [chart.root]
      exact rootTrail y a Y
    obtain ⟨d,C,K,⟨j,J,U⟩,A⟩ :=
      nominate_trail hp chart head cont (layout _ Y.1) quiet ⟨0,by omega,source⟩
    have dPays : Φ (step y d)<Φ y :=
      (pay d).2 ⟨C,K,U ▸ mem j J,trail_footprint_payment hp y d (sep d) C K A⟩
    refine ⟨d,fun e=>?_⟩
    by_cases Z : stop (step y e)
    · exact .inl Z
    have E := (pay e).1
    refine .inr ⟨Φ (step y e),⟨closed _ _ Y.1,NF e,ND e,Classical.not_not.mp Z,Nat.le_refl _⟩,
      Nat.le_trans E Y.2.2.2.2,fun h=>?_⟩
    subst e
    exact Nat.lt_of_lt_of_le dPays Y.2.2.2.2
  apply ResetReturnIID.iid_of_relational_rank step stop Live pos advance
  by_cases Z : stop x
  · exact .inl Z
  refine .inr ⟨I,noF,noD,Classical.not_not.mp Z,?_⟩
  have H : Φ x≤total (fun _=>1) S := by
    apply sum_mono
    intro u _
    change 1*trail (atSite (x u.1).long u.2)≤1
    cases atSite (x u.1).long u.2 <;> simp [trail]
  rwa [total_one] at H

#print axioms trail_suffix_expected
end L4.DirtyTrailSuffix

namespace L4.DirtyTrailSuffix
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarH6WordChart
open BStarAcquireLiteralChain BStarAcquireVisitOrder BStarResetChartTouch BStarLongFixedRouting
open BStarClearanceSource BStarClearanceOffset DirtyReplyOrigin DirtyLeastForward
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => BStarClearanceOffset.X k₁ k₂ t₂ J₁ J₂ r c p c₁ n
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- Sequential raw IID reply and trail clearance from the first
forward-free held state. The stopping state needs no generated owner. -/
theorem forward_free_exit_expected {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (head : ∀ i,let g:=longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i,let g:=oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q x)
    (layout : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    (cb : correct (oldH6 B base) hh 5 base) (cy : ∀ y,Q y→correct (oldH6 B base) hh 5 y)
    (noF : ∀ u∈S, ¬ringF x u) :
    let root := (endpoint (oldH6 B base) hh o 0).1
    Height.IIDExpectedHittingTimeAtMost step (fun y=>¬Held (y root).long) x (n*S.length+n*S.length) := by
  classical
  dsimp only
  let root := (endpoint (oldH6 B base) hh o 0).1
  let NF := fun y : X=>∀ u∈S,¬ringF y u
  let ND := fun y : X=>∀ u∈S,¬ringD y u
  let stop := fun y : X=>¬Held (y root).long
  let P := fun y=>stop y ∨ ND y
  let A := fun y=>Q y ∧ NF y ∧ ND y
  let T := fun y=>A y ∨ stop y
  have equal (t : Nat) (y : X) (Y : Q y) (F : NF y) :
      Height.iidHitCost step T t y=Height.iidHitCost step P t y := by
    induction t generalizing y with
    | zero => rfl
    | succ t ih =>
      by_cases h : P y
      · have hr : T y := h.elim Or.inr (fun d=>.inl ⟨Y,F,d⟩)
        rw [Height.iidHitCost_of_target _ _ _ hr,Height.iidHitCost_of_target _ _ _ h]
      · have noT : ¬T y := fun H=>h (H.elim (fun d=>.inr d.2.2) Or.inl)
        have held : Held (y root).long := Classical.not_not.mp (fun H=>h (.inl H))
        have keep (e : Fin n) : NF (step y e) := by
          intro u U New
          rcases ring_origin hp chart (layout y Y) e (sep e) (held_before hp y root e held) u U New with old|⟨v,V,old,_⟩
          · exact F u U old
          · exact F v V old
        simp only [Height.iidHitCost,if_neg noT,if_neg h]
        rw [show (fun e : Fin n => Height.iidHitCost step T t (step y e)) =
          (fun e => Height.iidHitCost step P t (step y e)) from
          funext (fun e=>ih _ (closed y e Y) (keep e))]
  have hn : 0<n := by obtain ⟨e,_⟩ := hh; exact Nat.zero_lt_of_lt e.isLt
  apply Height.iid_stage_le step hn x A stop (n*S.length) (n*S.length)
  · intro t
    rw [show (fun z=>A z ∨ stop z)=T from rfl,equal t x I noF]
    exact reply_suffix_expected hp chart head cont sep Q I layout closed noF t
  · intro y hy
    exact trail_suffix_expected hp chart head cont sep Q hy.1 layout closed cb cy hy.2.1 hy.2.2

#print axioms forward_free_exit_expected
end L4.DirtyTrailSuffix
