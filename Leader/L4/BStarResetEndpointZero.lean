import Leader.L4.BStarResetNoAcquire

namespace L4.BStarResetEndpointZero
open AllSizeProtocol BStarTrace BStarLongToken BStarAcquireAnchors BStarResetChartTouch
open BStarH6WordChart BStarAcquireVisitOrder BStarLongFixedRouting BStarLongFiberOwner
open BStarLongWork BStarLongTransport BStarLongCommandData BStarLongCommand BStarResetHealthyService
open BStarAcquireRailCoverage BStarAcquireLiteralChain BStarResetMarkAdapter BStarResetChartService
open BStarResetSchedule BStarSeparatingRail BStarResetTaggedRows
open BStarResetIssueClean BStarResetNoAcquire BStarGrantBirth

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run (AllSizeS1Geometry.step (n:=n) B)

private theorem end_good {Y : Type} {n : Nat} {nextMark : Y → Fin n → Y}
    {track : Y → BStarSeparatingRail.Rail} {tag : Tag} {len : Nat}
    {x : Y} {u v : Cursor} {w : List (Fin n)}
    (T : Seen nextMark track tag len x u w v) (G : Good tag len (track x) u) :
    Good tag len (track (BStarResetSchedule.run nextMark x w)) v := by
  induction T with
  | nil => exact G
  | cons _ _ _ g _ ih => exact ih g

private theorem split_last {α : Type} {mid pre tail : List α} {door e : α}
    (h : mid++[door]=pre++e::tail) :
    (pre=mid ∧ e=door ∧ tail=[]) ∨
      ∃ post, mid=pre++e::post ∧ tail=post++[door] := by
  induction pre generalizing mid with
  | nil =>
    cases mid with
    | nil => simp_all
    | cons a rest =>
      have H := List.cons.inj h
      exact .inr ⟨rest,by simp [H.1],H.2.symm⟩
  | cons a before ih =>
    cases mid with
    | nil => simp at h
    | cons b mid =>
      have H := List.cons.inj h
      rcases ih H.2 with ⟨E,O,T⟩|⟨post,E,T⟩
      · exact .inl ⟨by simp [H.1,E],O,T⟩
      · exact .inr ⟨post,by simp [H.1,E],T⟩

/-- On a healthy RREL Stage entered from the all-empty owner chart, none
of its literal marks can create a grant at an owned incidence. -/
theorem stage_no_win {base x y : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X → Prop) (good : Q x)
    (fiber : ∀ x,Q x → ∀ i, Layout B base i=Layout B x i)
    (closed : ∀ x e,Q x → Q (step x e))
    (clean : ∀ j≤len, project (fun j => S.getD j fall) x j=.empty)
    (w : List (Fin n))
    (st : BStarResetHealthyCycle.Stage hp (fun j => S.getD j fall) len 2 x w y)
    (i : Fin n) (j : Fin 3) (own : commandOwner (oldH6 B base) i (slot j)=o.val)
    (pre : List (Fin n)) (e : Fin n) (tail : List (Fin n)) (W : w=pre++e::tail) :
    ¬WonAt hp (run x pre) e i j := by
  let adr := fun j => S.getD j fall
  let door := RearTrace.predecessor (adr 0).1
  obtain ⟨mid,E,Y,P,O,T,R⟩ := st
  obtain ⟨mid',E',cleanMid⟩ := stage_clean_prefix hp C sep Q good fiber closed 2 (by decide) clean w
    ⟨mid,E,Y,P,O,T,R⟩
  have M : mid'=mid := by
    have := List.cons.inj (E'.symm.trans E)
    exact (List.append_cancel_right this.2)
  subst mid'
  refine no_win_at hp _ _ _ _ ?_
  cases pre with
  | nil =>
    refine quiet_no_acquire _ _ _ (.inl ?_)
    have act : BStarAcquireRailCoverage.active (longGeometry B (base i)) (slot j)=true := by
      have b := j.isLt
      unfold BStarAcquireRailCoverage.active slot
      simp [show j.val≠8 by omega,show j.val≠9 by omega]
    obtain ⟨k,hk,H⟩ := List.getElem_of_mem (C.cover (i,slot j) act own)
    have ix : adr k=(i,slot j) := (List.getElem_eq_getD _).symm.trans H
    have L := C.length
    change BStarAcquireForwardTrace.atCursor x (i,slot j)=.empty
    rw [←ix]
    exact clean k (by omega)
  | cons d pre =>
    have eq := List.cons.inj (E.symm.trans W)
    change door=d ∧ _ at eq
    rcases eq with ⟨D,F⟩
    subst d
    rcases split_last F with ⟨ep,_,_⟩|⟨post,H,_⟩
    · subst pre
      have nonNil : mid≠[] := by
        intro N
        rw [N] at T
        cases T
      have G : Good (healthyTag 2) len (project adr (run (step x door) mid)) (.back 0) := by
        cases mid with
        | nil => exact (nonNil rfl).elim
        | cons m ms =>
          cases T with
          | cons _ _ _ g t =>
            rw [BStarResetSchedule.run.eq_2]
            exact end_good t g
      exact good_no_acquire hp C (.back 0) G trivial i j own
    · obtain ⟨z,_,_,G,Clean⟩ := cleanMid pre post e H
      exact good_no_acquire hp C z G Clean i j own

/-- Actual RREL release plus no marked reacquisition yields zero grants
at every physical owned incidence after the actual consumption. -/
theorem stage_grant_zero {base x y : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X → Prop) (good : Q x)
    (fiber : ∀ x,Q x → ∀ i, Layout B base i=Layout B x i)
    (closed : ∀ x e,Q x → Q (step x e))
    (clean : ∀ j≤len, project (fun j => S.getD j fall) x j=.empty)
    (w : List (Fin n))
    (st : BStarResetHealthyCycle.Stage hp (fun j => S.getD j fall) len 2 x w y)
    (i : Fin n) (j : Fin 3) (own : commandOwner (oldH6 B base) i (slot j)=o.val) :
    bit y i j=0 := by
  obtain ⟨pre,e,tail,W,Z⟩ := BStarResetReleaseHistory.stage_release hp C sep Q good fiber closed w st i j own
  have Y : y=run x w := st.choose_spec.2.1
  rw [Y,W,BStarResetSchedule.run_append]
  apply zero_along hp sep (step (run x pre) e) i j tail Z
  intro a m b E
  have W' : w=(pre++e::a)++m::b := by rw [W,E,List.append_assoc]; rfl
  have N := stage_no_win hp C sep Q good fiber closed clean w st i j own _ _ _ W'
  rwa [BStarResetSchedule.run_append] at N

end L4.BStarResetEndpointZero
