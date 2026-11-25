import Leader.L4.BStarCommitIssue

namespace L4.BStarDoorUnique
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongCommand
open BStarLongEvents BStarCommitIssue BStarLongCommandData

def isDoor : Offer → Bool
  | .door _ => true
  | _ => false

def doorAction (o : CommandClaim × Offer) : Bool := isDoor o.2
def doorKind (c : CommandClaim) : Bool := c.kind==.door

private theorem update_isDoor (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (O : BStarLongGrant.Offers) (o : CommandClaim × Offer) :
    doorAction (BStarLongGrant.update g x O o)=doorAction o := by
  obtain ⟨c,q⟩ := o
  cases q <;> try (unfold BStarLongGrant.update; dsimp only; split <;> rfl)
  unfold BStarLongGrant.update
  dsimp only
  split
  · split <;> rfl
  · rfl

private theorem cancel_isDoor (f : List (At (Fin 11))) (o : CommandClaim × Offer) :
    doorAction (cancel f o)=doorAction o := by
  obtain ⟨c,q⟩ := o
  cases q <;> try rfl
  unfold cancel
  dsimp only
  split <;> rfl

private theorem check_isDoor (g : Pair LongGeometry) (old : At Sheet → BStarLongPackets.Lane)
    (o : CommandClaim × Offer) :
    doorAction (o.1,checkOffer g old o)=doorAction o := by
  obtain ⟨c,q⟩ := o
  cases q <;> try rfl
  unfold checkOffer
  dsimp only
  split <;> rfl

private theorem classify_isDoor (c : CommandClaim) (g : LongGeometry) (s t : Token) :
    isDoor (classify c g s t)=doorKind c := by
  unfold classify doorKind
  split
  · simp_all [isDoor]
  · rename_i H
    have H' : (c.kind==.door)=false := by cases E : c.kind==.door <;> simp_all
    rw [H']
    repeat' first | rfl | split

private theorem classify_action (c : CommandClaim) (g : LongGeometry) (s t : Token) :
    doorAction (c,classify c g s t)=doorKind c := classify_isDoor c g s t

theorem claim_door_singleton (g : Pair LongGeometry) (h : g.2.axes.h6=true) :
    (orderedCommands g).filter doorKind=[doorClaim] := by
  obtain ⟨x,y⟩ := g
  change y.axes.h6=true at h
  cases a : (x.inside && x.last) <;> cases b : y.inside <;>
    simp only [orderedCommands,commandClaims,ends,h,a,b,if_true] <;> decide +kernel

theorem actual_door_singleton (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (h : g.2.axes.h6=true) :
    (actualOffers g x).filter doorAction=
      [(doorClaim,.door (bind g.2 0 (atSite x.2 0)))] := by
  unfold actualOffers BStarLongGrant.run BStarLongCommandData.round gated offersOn
  simp only [List.filter_map,Function.comp_def,update_isDoor,cancel_isDoor,
    check_isDoor,classify_action]
  rw [claim_door_singleton g h]
  rfl

theorem actual_door_split (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (h : g.2.axes.h6=true) :
    let target : CommandClaim × Offer := (doorClaim,.door (bind g.2 0 (atSite x.2 0)))
    ∃ pre post, actualOffers g x=pre++target::post ∧
      (∀ o∈pre, ∀ t : Token, o.2≠.door t) ∧
      (∀ o∈post, ∀ t : Token, o.2≠.door t) := by
  let target : CommandClaim × Offer := (doorClaim,.door (bind g.2 0 (atSite x.2 0)))
  obtain ⟨pre,post,E⟩ := List.mem_iff_append.mp (actual_door g x h)
  have H := actual_door_singleton g x h
  rw [E] at H
  change (_ ++ target :: _).filter doorAction=[target] at H
  have T : doorAction target=true := rfl
  simp only [List.filter_append,List.filter_cons,T,if_true] at H
  have L := congrArg List.length H
  simp only [List.length_append,List.length_cons,List.length_nil] at L
  have A : (pre.filter doorAction).length=0 := by omega
  have B : (post.filter doorAction).length=0 := by omega
  have empty_imp (xs : List (CommandClaim × Offer)) (K : (xs.filter doorAction).length=0) :
      ∀ o∈xs, ∀ t : Token, o.2≠.door t := by
    intro o ho t hf
    have Q : o∈xs.filter doorAction := List.mem_filter.mpr ⟨ho,by simp [doorAction,hf,isDoor]⟩
    rw [List.length_eq_zero_iff.mp K] at Q
    exact (List.not_mem_nil Q)
  exact ⟨pre,post,E,empty_imp pre A,empty_imp post B⟩

end L4.BStarDoorUnique
