import Leader.L4.BStarLongLiteral

/-! Project the selected-work fold (distinct from K transport, COPY,
grant and nonheader clearing) onto the actual publication endpoint. -/
namespace L4.BStarLongLandingCore
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongWork
open BStarLongCommand BStarLongEvents BStarLongLiteral BStarLongArithmetic

def rightDoor (c : CommandClaim) : Bool := c.kind != .door || c.source.side==.right

private theorem all_right_doors (g : Pair LongGeometry) :
    (orderedCommands g).all rightDoor=true := by
  obtain ⟨x,y⟩ := g
  unfold orderedCommands commandClaims ends
  simp only
  generalize x.inside=ix
  generalize x.last=lx
  generalize y.axes.h6=hy
  generalize y.inside=iy
  cases ix <;> cases lx <;> cases hy <;> cases iy <;> decide +kernel

private theorem door_kind (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (t : Token) (H : (c,.door t)∈actualOffers g x) : c.kind=.door := by
  let d := BStarLongCommandData.round g x
  obtain ⟨⟨a,q⟩,ha,eq⟩ := List.mem_map.mp H
  have ac : a=c := (update_claim g x d.offered (a,q)).symm.trans (congrArg Prod.fst eq)
  subst a
  have E : q=.door t := by
    by_cases h3 : c.source.occurrence.val < 3
    · cases q <;> simp [BStarLongGrant.update,h3] at eq ⊢ <;> try assumption
      split at eq <;> simp at eq
    · simpa [BStarLongGrant.update,h3] using congrArg Prod.snd eq
  subst q
  obtain ⟨⟨b,v⟩,hb,be⟩ := List.mem_map.mp ha
  have nv : b=c ∧ v=.door t := by
    cases v <;> simp [BStarLongCommandData.cancel] at be
    · exact ⟨be.1,congrArg Offer.door be.2⟩
    · split at be <;> simp_all
  obtain ⟨bc,vc⟩ := nv
  subst b
  subst v
  have he := ((gated_mem g x c (.door t)).mp hb).2.symm
  unfold gatedAt at he
  have CE : classifyOld g x c=.door t := by
    cases m : classifyOld g x c <;>
      simp [m,BStarLongCommandData.checkOffer] at he ⊢ <;> try assumption
    split at he <;> contradiction
  unfold classifyOld at CE
  simp only [classify] at CE
  split at CE
  · exact beq_iff_eq.mp ‹_›
  · split at CE
    · split at CE <;> contradiction
    · split at CE
      · split at CE <;> contradiction
      · split at CE
        · contradiction
        · split at CE <;> contradiction

theorem actual_door_right (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (t : Token) (H : (c,.door t)∈actualOffers g x) : c.source.side=.right := by
  have cm : c∈(actualOffers g x).map Prod.fst := List.mem_map.mpr ⟨(c,.door t),H,rfl⟩
  rw [actualOffers_claims] at cm
  have K := door_kind g x c t H
  have D := List.all_eq_true.mp (all_right_doors g) c cm
  simpa [rightDoor,K] using D

def noLeftEffect (ys : List (Bool × Patch LW)) : Prop :=
    ∀ y, (ys.foldl runWrite y).1=y.1

private theorem empty_left (x : BitVec LW) : (Patch.empty LW).apply x=x := by
  simp [Patch.empty,Patch.apply]

theorem selected_offcenter (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (o : CmdOffer) (ho : o∈actualOffers g x) (hc : centerClaim o.1=false) :
    noLeftEffect (selected g x o).work := by
  obtain ⟨c,t⟩ := o
  intro y
  cases t with
  | advance p =>
    have h : c.source.occurrence.val≠1 := by simpa [centerClaim] using hc
    have av : visit (geometry g c.source.side) c.source.occurrence (atOld x c.source) p =
        (.empty _,p) := by simp [visit,h]
    simp [selected,av,BStarLongOutgoing.noncenter_hold _ _ _ _ h,
      BStarLongOutgoing.hold,runWrite,empty_left]
  | door t =>
    have h := actual_door_right g x c t ho
    unfold selected
    dsimp only
    split <;> simp [runWrite,h]
  | _ => rfl

theorem selected_lands (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (p : Payload) (b : Fin 3) (H : LiteralCommit g.1 (L 1) x.1 p b) (y : Pair (BitVec LW)) :
    (((selected g x (centerLink g,.advance p)).work).foldl runWrite y).1=
      (BStarLongPublication.setter b).apply y.1 := by
  obtain ⟨_,hh,hf,hop,d,hd,hb,hc⟩ := H
  have N : nodeOf commitOp=none := by decide +kernel
  have av : visit g.1 1 x.1 p=(.empty _,p) := by
    unfold visit
    split
    · rfl
    · rw [hop,N]
  have C := BStarLongOutgoing.center_commit g.1 x.1 p d b hh hf hop hd hb hc
  change (([(false,(visit g.1 1 x.1 p).1),
    (false,(BStarLongOutgoing.execute g.1 1 x.1 (visit g.1 1 x.1 p).2).row)] :
      List (Bool × Patch LW)).foldl runWrite y).1=_
  rw [av,C]
  simp [runWrite,empty_left]

end L4.BStarLongLandingCore
