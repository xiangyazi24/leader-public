import Leader.L4.BStarJoinedPublic
import Leader.L4.BStarLapTransfer

/-! The two independent interpreters (ordinary public plus H5 lap)
jointly refine the actual bStar product on every old byte pair. -/
namespace L4.BStarJoinedLap
open AllSizeProtocol BStarTrace BStarPublicCodec BStarLapTransfer

theorem joined_lap_public {a : LargeParams} (b : LargeRows a) (hp : 0<a.p)
    (bind : b.shared.ordinaryPublic=BStarPublic.publicWork (c₁:=a.c1) hp)
    (x : Pair (LargeSite a)) :
    let raw := Pair.map LargeSite.guard x
    let old := Pair.map (fun s => readPub hp s.publicRow) x
    let ord := pairStep old.1 old.2
    let y := largePair b x
    let o := Pair.map (reference b) x
    let n := Pair.map (reference b) y
    let plan := oldPlan raw o n (Pair.map Site.mark old) (Pair.map Site.mark ord)
    Pair.map (fun s => decode (get s.guard)) y =
      (plan.1.1.site (decode (get raw.1)),plan.1.2.site (decode (get raw.2))) ∧
    Pair.map (fun s => readPub hp s.publicRow) y =
      ({ord.1 with mark:=ord.1.mark || plan.2},ord.2) := by
  let raw := Pair.map LargeSite.guard x
  let old := Pair.map (fun (s : LargeSite a) => readPub hp s.publicRow) x
  let ord := pairStep old.1 old.2
  let y := largePair b x
  let pub := Pair.map LargeSite.publicRow x
  let pub1 := patchPair (b.shared.ordinaryPublic pub) pub
  let bit := fun t : BitVec (publicWidth a.p a.c1) => t.getLsbD (publicMarkOffset a.c1)
  let o := Pair.map (reference b) x
  let n := Pair.map (reference b) y
  let m := Pair.map Site.mark old
  let m1 := Pair.map Site.mark ord
  let r := H5.row raw o n m m1
  have yd : Pair.map LargeSite.guard y =
      patchPair (H5.row raw o n (Pair.map bit pub) (Pair.map bit pub1)).slots raw := rfl
  have M : Pair.map bit pub=m := Prod.ext
    (BStarJoinedPublic.read_mark_bit hp pub.1).symm
    (BStarJoinedPublic.read_mark_bit hp pub.2).symm
  have A : Pair.map (readPub hp) pub1=ord := by
    change Pair.map (readPub hp) (patchPair (b.shared.ordinaryPublic pub) pub)=_
    rw [bind]
    exact BStarPublicPatrol.public_transfer hp pub
  have M1 : Pair.map bit pub1=m1 := by
    change Pair.map bit pub1=Pair.map Site.mark ord
    rw [←A]
    exact Prod.ext (BStarJoinedPublic.read_mark_bit hp pub1.1).symm
      (BStarJoinedPublic.read_mark_bit hp pub1.2).symm
  rw [M,M1] at yd
  have H := decoded_transfer raw o n m m1
  have G := congrArg (fun t => (t.1,t.2.1)) H
  have S := congrArg (fun t => t.2.2) H
  let plan := oldPlan raw o n m m1
  change Pair.map (fun s => decode (get s.guard)) y =
      (plan.1.1.site (decode (get raw.1)),plan.1.2.site (decode (get raw.2))) ∧
    Pair.map (fun s => readPub hp s.publicRow) y =
      ({ord.1 with mark:=ord.1.mark || plan.2},ord.2)
  constructor
  · change Pair.map (fun z => decode (get z)) (Pair.map LargeSite.guard y)=_
    rw [yd]
    exact G
  · have P := BStarJoinedPublic.joined_public b hp bind x
    change Pair.map (fun s => readPub hp s.publicRow) y =
      ({ord.1 with mark := ord.1.mark || r.seed.1},
       {ord.2 with mark := ord.2.mark || r.seed.2}) at P
    change r.seed=(plan.2,false) at S
    rw [S] at P
    simpa only [Bool.or_false] using P

theorem bStar_joined_lap_public (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) :
    let b := BStarLongWork.bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let raw := Pair.map LargeSite.guard x
    let old := Pair.map (fun s => readPub hp s.publicRow) x
    let ord := pairStep old.1 old.2
    let y := largePair b x
    let plan := oldPlan raw (Pair.map (reference b) x) (Pair.map (reference b) y)
      (Pair.map Site.mark old) (Pair.map Site.mark ord)
    Pair.map (fun s => decode (get s.guard)) y =
      (plan.1.1.site (decode (get raw.1)),plan.1.2.site (decode (get raw.2))) ∧
    Pair.map (fun s => readPub hp s.publicRow) y =
      ({ord.1 with mark:=ord.1.mark || plan.2},ord.2) :=
  joined_lap_public _ hp rfl x

#print axioms bStar_joined_lap_public
end L4.BStarJoinedLap

