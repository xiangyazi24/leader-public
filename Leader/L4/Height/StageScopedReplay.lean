import Leader.L4.Height.StageHealthyIdle
import Leader.L4.BStarResetChartNomination

namespace L4.Height.StageScopedReplay
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongTransport BStarLongEvents
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter
open BStarSeparatingRail BStarGeneratedOwner BStarOwnerLaunchOrigin
open BStarLongDoor BStarLongLayout StageHealthyIdle
open BStarResetRailRing

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- Every earlier physical mark either stutters or advances one slot,
retaining the exact well-formed STAGE. No scheduler premise. -/
theorem arbitrary_stage_step {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (source : BitVec LW) (d : BStarLongPublication.Descriptor)
    (D : BStarLongPublication.decode (sourceDescriptor.read source)=some d)
    (j : Nat) (J : j<len) (qx : Q x) (e : Fin n)
    (cur : Current hp base (fun k=>S.getD k fall) len x (.busy stageOp (.out j)))
    (old : project (fun k=>S.getD k fall) x j=.forward (BStarStageIssue.payload source))
    (auth : ∀ (K : CommandClaim), S.getD j fall=address e K.source →
      (K,.advance (BStarStageIssue.payload source))∈actualOffers (oldPair B x e)
        ((x e).long,(x (rightNeighbor e)).long) →
      (geometry (oldPair B x e) K.source.side).axes.h6=true → K.source.occurrence.val=1 →
      BStarLongOutgoing.actual (atOld ((x e).long,(x (rightNeighbor e)).long) K.source) d=true) :
    ∃ k, j≤k ∧ k≤j+1 ∧
      Event hp (fun t=>S.getD t fall) len x e (.busy stageOp (.out j)) (.busy stageOp (.out k)) ∧
      Current hp base (fun t=>S.getD t fall) len (step x e) (.busy stageOp (.out k)) ∧
      project (fun t=>S.getD t fall) (step x e) k=.forward (BStarStageIssue.payload source) ∧
      (linkAt hp x e (fun t=>S.getD t fall) len j → k=j+1) := by
  by_cases link : linkAt hp x e (fun t=>S.getD t fall) len j
  · obtain ⟨jLen,K,a,mem,dest,src,dst⟩ := link
    have R := (old_read x e K.source).trans ((congrArg (atCursor x) src).symm.trans old)
    have selected : (K,.advance (BStarStageIssue.payload source))∈actualOffers (oldPair B x e)
        ((x e).long,(x (rightNeighbor e)).long) := by
      apply StageHealthyHop.bound_stage_selected _ _ K _ mem
        (by rw [(BStarAcquireReturn.link_shape _ K a mem dest).2.1]; decide) _ rfl
      unfold bound
      rw [R]
      exact BStarStageIssue.bound_forward_exact _ _ source d D
    have out := StageHealthyHop.joined_stage k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e))
      K a source d mem dest D (auth K src selected) R
    have post := (congrArg (atCursor (step x e)) dst).trans ((new_read B x e (sep e) a).symm.trans out)
    obtain ⟨m,ev,nxt⟩ := current_step hp C Q fiber closed sep qx e (.busy stageOp (.out j)) cur
    cases ev with
    | transit _ _ d live seen =>
      cases seen with
      | cons M go adv gd tail =>
        cases tail
        cases adv with
        | stay =>
          have empty := nxt.2.2 (j+1) (by omega) jLen
          exact Token.noConfusion (empty.symm.trans post)
        | forward =>
          exact ⟨j+1,by omega,Nat.le_refl _,.transit _ _ _ live (.cons M go (.forward j) gd (.nil _ _)),
            nxt,post,fun _ => rfl⟩
        | turn => omega
  · obtain ⟨m,ev,nxt⟩ := current_step hp C Q fiber closed sep qx e (.busy stageOp (.out j)) cur
    have K : j<len := by omega
    have silent := (silent_at_stage hp C e (sep e) stageOp j cur.1 _
      cur.2.1 old (canonical source d D) link (fun E => (Nat.ne_of_lt K E).elim)).2
    have F : project (fun t=>S.getD t fall) (step x e) j=.forward (BStarStageIssue.payload source) := silent.trans old
    cases ev with
    | transit _ _ d live seen =>
      cases seen with
      | cons M go adv gd tail =>
        cases tail
        cases adv with
        | stay => exact ⟨j,Nat.le_refl _,by omega,.transit _ _ _ live (.cons M go (.stay _) gd (.nil _ _)),nxt,F,
            fun H => (link H).elim⟩
        | forward =>
          have E := (BStarOwnerControlHistory.pointed_unique_forward _ len (j+1) nxt.2.1 nxt.2.2 j (by omega)).mp ⟨_,F⟩
          omega
        | turn => omega

#print axioms arbitrary_stage_step


/-- Authorization is required only on the reached same-word busy prefix,
and only for the actual selected canonical offer at its current slot. -/
def PrefixAuth (base x : X) (addr : Nat→Pos n) (len j : Nat)
    (source : BitVec LW) (d : BStarLongPublication.Descriptor) (w : List (Fin n)) : Prop :=
  ∀ u e v,w=u++e::v → ∀ k,
    BusyOnly hp base addr len stageOp x (.out j) u (.out k) →
    ∀ K : CommandClaim,addr k=address e K.source →
    let y := play x u
    (K,.advance (BStarStageIssue.payload source))∈actualOffers (oldPair B y e)
      ((y e).long,(y (rightNeighbor e)).long) →
    (geometry (oldPair B y e) K.source.side).axes.h6=true → K.source.occurrence.val=1 →
    BStarLongOutgoing.actual (atOld ((y e).long,(y (rightNeighbor e)).long) K.source) d=true

theorem PrefixAuth.tail {base x : X} {addr : Nat→Pos n} {len j k : Nat} {w : List (Fin n)}
    {source : BitVec LW} {d : BStarLongPublication.Descriptor} {e : Fin n}
    (H : PrefixAuth hp base x addr len j source d (e::w))
    (I : Current hp base addr len x (.busy stageOp (.out j)))
    (E : Event hp addr len x e (.busy stageOp (.out j)) (.busy stageOp (.out k))) :
    PrefixAuth hp base (step x e) addr len k source d w := by
  intro u f v W l T
  exact H (e::u) f v (congrArg (List.cons e) W) l (.cons I E T)

theorem PrefixAuth.take {base x : X} {addr : Nat→Pos n} {len j : Nat} {w : List (Fin n)}
    {source : BitVec LW} {d : BStarLongPublication.Descriptor}
    (H : PrefixAuth hp base x addr len j source d w)
    (u v : List (Fin n)) (split : w=u++v) :
    PrefixAuth hp base x addr len j source d u := by
  intro q e t E k T
  exact H q e (t++v) (by rw [split,E,List.append_assoc,List.cons_append]) k T

/-- A replay with the nominated ordered subsequence reaches the terminal
on some prefix. Intervening marks may help but cannot undo progress or
change the well-formed STAGE before that first terminal cut. -/
theorem reaches_terminal_of_sublist {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (source : BitVec LW) (d : BStarLongPublication.Descriptor)
    (D : BStarLongPublication.decode (sourceDescriptor.read source)=some d)
    {ls w : List (Fin n)} (sub : ls.Sublist w) :
    ∀ (x : X) (a j : Nat), a+ls.length=len → a≤j → j≤len → Q x →
      PrefixAuth hp base x (fun t=>S.getD t fall) len j source d w →
      Current hp base (fun t=>S.getD t fall) len x (.busy stageOp (.out j)) →
      project (fun t=>S.getD t fall) x j=.forward (BStarStageIssue.payload source) →
      (∀ k (hk : k<ls.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
        linkAt hp y ls[k] (fun t=>S.getD t fall) len (a+k)) →
      ∃ pre post, w=pre++post ∧
        BusyOnly hp base (fun t=>S.getD t fall) len stageOp x (.out j) pre (.out len) ∧
        project (fun t=>S.getD t fall) (play x pre) len=.forward (BStarStageIssue.payload source) := by
  induction sub with
  | slnil =>
    intro state a j J A U _ _ I F _
    have eq : j=len := by simp at J; omega
    subst j
    exact ⟨[],[],rfl,.nil I,F⟩
  | @cons ls w e sub ih =>
    intro state a j J A U q auth I F nominate
    by_cases eqa : j=len
    · subst j
      exact ⟨[],e::w,rfl,.nil I,F⟩
    have jl : j<len := by omega
    obtain ⟨k,jk,K,E,now,new,_⟩ := arbitrary_stage_step hp C Q fiber closed sep source d D j jl q e I F (auth [] e w rfl j (.nil I))
    obtain ⟨pre,post,W,T,P⟩ := ih (step state e) a k J (by omega) (by omega) (closed _ q e) (auth.tail hp I E)
      now new nominate
    exact ⟨e::pre,post,congrArg (List.cons e) W,.cons I E T,P⟩
  | @cons_cons ls w e sub ih =>
    intro state a j J A U q auth I F nominate
    by_cases eqa : j=len
    · subst j
      exact ⟨[],e::w,rfl,.nil I,F⟩
    have jl : j<len := by omega
    obtain ⟨k,jk,K,E,now,new,served⟩ := arbitrary_stage_step hp C Q fiber closed sep source d D j jl q e I F (auth [] e w rfl j (.nil I))
    have kA : a+1≤k := by
      by_cases same : a=j
      · subst a
        have link := nominate 0 (by simp) state (fiber state q)
        have eq := served (by simpa using link)
        omega
      · omega
    have nom' (t : Nat) (ht : t<ls.length) (y : X) (H : ∀ i,Layout B base i=Layout B y i) :
        linkAt hp y ls[t] (fun t=>S.getD t fall) len ((a+1)+t) := by
      have link := nominate (t+1) (by simp; omega) y H
      have eq : a+(t+1)=(a+1)+t := by omega
      simpa only [List.getElem_cons_succ,eq] using link
    obtain ⟨pre,post,W,T,P⟩ := ih (step state e) (a+1) k (by simp at J; omega) kA (by omega)
      (closed _ q e) (auth.tail hp I E) now new nom'
    exact ⟨e::pre,post,congrArg (List.cons e) W,.cons I E T,P⟩

#print axioms reaches_terminal_of_sublist
end L4.Height.StageScopedReplay
