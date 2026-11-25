import Leader.L4.BStarSeparatorQuiet
import Leader.L4.BStarSeparatorParked
import Leader.L4.BStarSeparatorJoinedTags

/-! Pointed separator on the real fixed lower chart for an arbitrary
genuine opcode. Every actual raw mark lifts until receipt at K0,
including holds and canonical faults. This module does not force a
schedule to service the parked front. -/
namespace L4.BStarSeparatorRing
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing
open BStarSeparatingRail BStarSeparatorControl BStarSeparatorQuiet BStarSeparatorParked
open BStarSeparatorJoinedTags BStarResetSchedule BStarAcquireWaitControl
open BStarLongDoor BStarResetChartService

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "XX" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

def mark_at {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (e : Fin n) (he : e≠rightNeighbor e) (op : Nat)
    (wait : Waiting hp base (S.getD 0 fallback).1 op x)
    (z : Cursor) (live : z≠.back 0)
    (G : Good anyTag len (project (fun j => S.getD j fallback) x) z) :
    Mark anyTag len (project (fun j => S.getD j fallback) x)
      (project (fun j => S.getD j fallback) (AllSizeS1Geometry.step B x e)) := by
  let adr := fun j => S.getD j fallback
  let U := project adr x
  let y := AllSizeS1Geometry.step B x e
  let W := project adr y
  have MF := frames_any hp C wait.1 e z live G wait.2.1 wait.2.2.1
  change Mark anyTag len U W
  have old (j : Nat) (q : At (Fin 11)) (E : adr j=address e q) :
      BStarLongTransport.readK ((x e).long,(x (rightNeighbor e)).long) q=U j :=
    (old_read x e q).trans ((congrArg (atCursor x) E).symm)
  have new (j : Nat) (q : At (Fin 11)) (E : adr j=address e q) :
      BStarLongTransport.readK (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) q=W j :=
    (new_read B x e he q).trans ((congrArg (atCursor y) E).symm)
  apply parked_mark (link:=linkAt hp x e adr len) (term:=onTerminal hp x e adr len)
    (fun _ J => J.1) (link_disjoint hp x e he adr len)
    (terminal_disjoint hp x e he adr len) (quiet_any hp x e he adr len MF)
  · intro j l F
    obtain ⟨J,K,a,M,hd,S,D⟩ := l
    have O := forward_link_joined k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e)) K a hd M
      (MF.safe j (by omega) K.source S).1 ((old j _ S).symm ▸ F)
    have A := new j K.source S
    have E := new (j+1) a D
    rw [A,E] at O
    exact O
  · intro j l T D'
    obtain ⟨_,K,a,M,hd,S,D⟩ := l
    have O := trail_reply_joined k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e)) K a hd M
      ((old j _ S).trans T) ((old (j+1) _ D).symm ▸ D')
    rw [new j K.source S,new (j+1) a D] at O
    exact O
  · intro l F
    obtain ⟨K,M,hk,hd,k,S⟩ := l
    have O := forward_terminal_joined k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e)) K hk hd k M
      (MF.safe len (Nat.le_refl _) K.source S).1 ((old len _ S).symm ▸ F)
    rw [new len K.source S] at O
    exact O

/-- Same physical prefix, with the original controller opcode unchanged
through the arrival mark itself. The next mark may consume the reply. -/
theorem lift_word {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (Q : XX → Prop)
    (fiber : ∀ x, Q x → ∀ i, Layout B base i=Layout B x i)
    (closed : ∀ x, Q x → ∀ e, Q (AllSizeS1Geometry.step B x e))
    (distinct : ∀ e : Fin n,e≠rightNeighbor e)
    (op : Nat) (w : List (Fin n)) (z : Cursor) :
    let root := (S.getD 0 fallback).1
    let track := project (fun j => S.getD j fallback)
    let step := AllSizeS1Geometry.step (n:=n) B
    Q x → Waiting hp base root op x → Good anyTag len (track x) z →
    ∃ pre post d, w=pre++post ∧
      Seen step track anyTag len x z pre d ∧
      Q (BStarResetSchedule.run step x pre) ∧ Waiting hp base root op (BStarResetSchedule.run step x pre) ∧
      Good anyTag len (track (BStarResetSchedule.run step x pre)) d ∧
      (d=.back 0 → Clean track anyTag len (BStarResetSchedule.run step x pre)) ∧
      (d=.back 0 ∨ post=[]) := by
  dsimp only
  let adr := fun j => S.getD j fallback
  let root := (adr 0).1
  let step := AllSizeS1Geometry.step (n:=n) B
  let track : XX → BStarSeparatingRail.Rail := project adr
  have cl {a : XX} (G : Good anyTag len (track a) (.back 0)) : Clean track anyTag len a :=
    ⟨G.2.1,G.2.2.2⟩
  induction w generalizing x z with
  | nil =>
    intro q W G
    exact ⟨[],[],z,rfl,.nil _ _,q,W,G,fun e => cl (e ▸ G),.inr rfl⟩
  | cons e w ih =>
    intro q W G
    by_cases Z : z=.back 0
    · subst z
      exact ⟨[],e::w,.back 0,rfl,.nil _ _,q,W,G,fun _ => cl G,.inl rfl⟩
    · have M := mark_at hp C e (distinct e) op W z Z G
      obtain ⟨d,D,G'⟩ := lift_mark M z Z G
      let y := step x e
      have q' : Q y := closed x q e
      obtain ⟨h,k⟩ := root_header hp C W.1
      have F : track x 0=atSite (x root).long 0 := by
        change atSite (x root).long (adr 0).2=_
        rw [k]
      have ctrl := step_wait k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x e root h W.2.1 W.2.2.1
        (F ▸ before_receipt G Z)
      have P := congrArg (fun q : BitVec 2 × BitVec 9 => q.1.toNat) ctrl
      have O := congrArg (fun q : BitVec 2 × BitVec 9 => q.2.toNat) ctrl
      have W' : Waiting hp base root op y :=
        ⟨fiber y q',(BStarResetWaitRing.valid_of_control_eq _ _ ctrl).trans W.2.1,
          P.trans W.2.2.1,O.trans W.2.2.2⟩
      obtain ⟨pre,post,z',E,T,U,V,H,A,B'⟩ := ih (x:=y) d q' W' G'
      exact ⟨e::pre,post,z',congrArg (List.cons e) E,.cons Z M D G' T,U,V,H,A,B'⟩

#print axioms mark_at
#print axioms lift_word
end L4.BStarSeparatorRing
