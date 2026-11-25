import Leader.L4.BStarLongCommandData

namespace L4.BStarLongCopyFence
open AllSizeProtocol BStarLongClaims BStarLongPackets BStarLongPrep BStarLongCommandData

private theorem fold_away (A : List (At Sheet × Leaf)) (old : At Sheet → Lane)
    (s : At Sheet) (ha : ∀ a, (s,a)∉A) :
    (A.foldl update old) s=old s := by
  induction A generalizing old with
  | nil => rfl
  | cons a A ih =>
    have ne : s≠a.1 := fun H => ha a.2 (by cases a; simp_all)
    rw [List.foldl_cons,ih (update old a) (fun a h => ha a (List.mem_cons_of_mem _ h))]
    simp [update,ne]

private theorem fold_at (s : At Sheet) (A : List Leaf) (old : At Sheet → Lane) :
    ((A.map (s,·)).foldl update old) s=typedLeaves (old s) A := by
  induction A generalizing old with
  | nil => rfl
  | cons a t ih =>
    rw [List.map_cons,List.foldl_cons,ih]
    simp [typedLeaves,update]

/-- A chosen hop's receiver is written by exactly that claim, not by
prep or another data claim. This equality is for the actual COPY patch
emitted by the command-data round, on either side of an arbitrary pair. -/
theorem receiver_exact (g : Pair LongGeometry) (x : Pair (BitVec BStarTrace.LW))
    (u v : At Sheet) (c : DataClaim)
    (hs : c.source=u) (hd : c.destination=some v) (hh : c.kind=.hop)
    (hsel : c∈orderedData g (reserved (round g x).prep)) (hne : u≠v) :
    let read := view x
    let post := view (patchPair (patch g x) x)
    post v=typedLeaves (read v) (hopEffects (read u) (read v) (retains g v)).2 := by
  let P := (round g x).prep
  let old := view x
  let L := orderedData g (reserved P)
  have hV : v∈c.slots := by simp [Claim.slots,hd]
  have K := data_reservations g (reserved P)
  have notPre (a : Leaf) : (v,a)∉prepAssignments old P :=
    fun h => K.2 c hsel v hV (prep_lane_reserved old P v a h)
  obtain ⟨l,r,E⟩ := List.mem_iff_append.mp hsel
  change L=l++c::r at E
  have H : L.Pairwise (fun a b => ∀ s∈b.slots, s∉a.slots) := K.1
  rw [E] at H
  have awayL (a : Leaf) : (v,a)∉l.flatMap (dataEffects g old) := by
    intro h
    obtain ⟨b,hb,hB⟩ := List.mem_flatMap.mp h
    exact (H.rel_of_mem_append hb (by simp : c∈c::r)) v hV (data_lane_claim g old b v a hB)
  have awayR (a : Leaf) : (v,a)∉r.flatMap (dataEffects g old) := by
    intro h
    obtain ⟨b,hb,hB⟩ := List.mem_flatMap.mp h
    have H' := (List.pairwise_cons.mp (List.pairwise_append.mp H).2.1).1 b hb
    exact H' v (data_lane_claim g old b v a hB) hV
  have C : dataEffects g old c=
      ((hopEffects (old u) (old v) (retains g v)).1.map (u,·)) ++
      ((hopEffects (old u) (old v) (retains g v)).2.map (v,·)) := by
    simp [dataEffects,hs,hd,hh]
  have awaySender (a : Leaf) :
      (v,a)∉(hopEffects (old u) (old v) (retains g v)).1.map (u,·) := by
    intro H
    obtain ⟨b,_,hb⟩ := List.mem_map.mp H
    exact hne (congrArg Prod.fst hb)
  dsimp only
  rw [BStarLongCommandData.round_transfer]
  change ((prepAssignments old P ++ L.flatMap (dataEffects g old)).foldl update old) v=_
  rw [E,List.flatMap_append,List.flatMap_cons,C]
  simp only [List.foldl_append]
  rw [fold_away _ _ _ awayR,fold_at,fold_away _ _ _ awaySender,fold_away _ _ _ awayL,
    fold_away _ _ _ notPre]

/-- A successful retained receiver is the literal two-place shift
register: incoming mobile is retained, previous retained becomes
mobile, and gate/frozen are unchanged. The former retained value
also contributes to the sticky error. -/
theorem retained_shift (g : Pair LongGeometry) (x : Pair (BitVec BStarTrace.LW))
    (u v : At Sheet) (c : DataClaim)
    (hs : c.source=u) (hd : c.destination=some v) (hh : c.kind=.hop)
    (hsel : c∈orderedData g (reserved (round g x).prep)) (hne : u≠v)
    (ret : retains g v=true) (openBoth : ((view x u).gate && (view x v).gate)=true)
    (occupied : (view x u).mobile≠.empty) (empty : (view x v).mobile=.empty) :
    let rx := view x u
    let ry := view x v
    view (patchPair (patch g x) x) v =
      {ry with retained := rx.mobile, mobile := ry.retained, error :=
        (ry.error || rx.mobile.isBad || ry.retained.isBad)} := by
  rw [receiver_exact g x u v c hs hd hh hsel hne]
  simp [hopEffects,ret,openBoth,occupied,empty,typedLeaves,Leaf.put]

/-- FENCE samples the old empty mobile and valid OLD retained operand.
If the very same mark performs the retained receive, a subsequent
test of that lane cannot advance: the old retained operand is now
mobile. This statement does not invent a re-test in the first mark. -/
theorem fence_old_then_hold (g : Pair LongGeometry) (x : Pair (BitVec BStarTrace.LW))
    (u v : At Sheet) (c : DataClaim)
    (hs : c.source=u) (hd : c.destination=some v) (hh : c.kind=.hop)
    (hsel : c∈orderedData g (reserved (round g x).prep)) (hne : u≠v)
    (ret : retains g v=true) (gu : (view x u).gate=true) (gv : (view x v).gate=true)
    (clean : (view x v).error=false) (empty : (view x v).mobile=.empty)
    (a b : BitVec 36) (inc : (view x u).mobile=.data a)
    (oldRet : (view x v).retained=.data b) :
    fence (view x v) true=.advance ∧
      fence (view (patchPair (patch g x) x) v) true=.hold := by
  have H := retained_shift g x u v c hs hd hh hsel hne ret (by simp [gu,gv])
    (by simp [inc]) empty
  exact ⟨by simp [fence,gv,clean,empty,oldRet,validPayload],
    by simp [H,fence,gv,clean,inc,oldRet,Digit9.isBad]⟩

#print axioms receiver_exact
#print axioms retained_shift
#print axioms fence_old_then_hold
end L4.BStarLongCopyFence
