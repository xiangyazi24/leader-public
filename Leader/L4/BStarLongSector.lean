import Leader.L4.BStarLongWork
import Leader.L4.BStarPhysicalDigitSem

/-! Physical long scratch under the literal join, and the saturated
coordinate chart used by the digit operators. -/
namespace L4.BStarLongSector
open AllSizeProtocol BStarTrace BStarLongWork

private theorem door_preserves_off (z : BitVec LW) :
    offField.read ((LongDoorGuard.repair manifest).apply z) = offField.read z := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
  apply LongDoorGuard.repair_holds_outside
  · right
    change 1764 ≤ 2364+i
    omega
  · right
    change 2206 ≤ 2364+i
    omega

/-- The actual joined bStar mark refreshes the clockwise predecessor's
successor header/END and the responder's clipped offset, from the
immutable old geometry. Even an invalid right-door repair leaves the
just-written offset intact. -/
theorem joined_cache (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let y := largePair b x
    shField.read y.1.long=BitVec.ofBool g.2.axes.h6 ∧
    seField.read y.1.long=BitVec.ofBool (g.2.inside && g.2.last) ∧
    offField.read y.2.long=BitVec.ofNat 3 (nextOffset g) := by
  dsimp only
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let old : Pair (BitVec LW) := Pair.map LargeSite.long x
  let w := longWork g old
  let q := longScratch g old
  let post := patchPair q (patchPair w old)
  have E : offField.read (largePair b x).2.long = offField.read post.2 := by
    change offField.read ((LongDoorGuard.guard manifest g.2.axes.h6 old.2
      (w.2.compose q.2)).apply old.2) = _
    unfold LongDoorGuard.guard
    split
    · rw [Patch.compose_apply,door_preserves_off]
      exact congrArg offField.read (Patch.compose_apply _ _ _)
    · exact congrArg offField.read (Patch.compose_apply _ _ _)
  rw [E]
  have L : (largePair b x).1.long=post.1 := Patch.compose_apply _ _ _
  rw [L]
  exact longScratch_values g (patchPair w old)

/-- The responder's next effective raw offset through the real joined
mark, and the initiator's freshly sampled successor-END bit. -/
theorem joined_offsets (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let y := largePair b x
    endL y.1.long = (g.2.inside && g.2.last) ∧ offsetL y.2.long=nextOffset g := by
  dsimp only
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let y := largePair b x
  obtain ⟨_,A,B⟩ := joined_cache k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x
  change endL y.1.long = (g.2.inside && g.2.last) ∧ offsetL y.2.long=nextOffset g
  constructor
  · let z : BitVec LW := y.1.long
    have E := congrArg (fun u : BitVec 1 => u.getLsbD 0) A
    change z.getLsbD 2362 = _
    change (z.extractLsb' 2362 1).getLsbD 0 =
      (BitVec.ofBool (g.2.inside && g.2.last)).getLsbD 0 at E
    simpa only [BitVec.getLsbD_extractLsb',Nat.zero_lt_succ,decide_true,
      Bool.true_and,Nat.add_zero,BitVec.getLsbD_ofBool] using E
  · let z : BitVec LW := y.2.long
    change z.extractLsb' 2364 3=BitVec.ofNat 3 (nextOffset g) at B
    change min 5 (z.extractLsb' 2364 3).toNat=nextOffset g
    have h : nextOffset g≤5 := by
      unfold nextOffset
      dsimp only
      split
      · decide
      · exact Nat.min_le_left _ _
    rw [B,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : nextOffset g<2^3),
      Nat.min_eq_right h]

/-- Repeated nonseam refreshes add one to the physical ordinal and
then apply the same cap, never wrap a truncated cache. -/
theorem offset_increment (g : Pair LongGeometry) (j : Nat)
    (old : (if g.1.axes.h6 then 0 else min 5 g.1.offset)=min 5 j)
    (body : g.2.axes.h6=false) : nextOffset g=min 5 (j+1) := by
  unfold nextOffset
  simp only [body,Bool.false_eq_true,if_false,old]
  omega


/-- A sector chart records saturation and the true current/successor
END positions; it does not infer them from stale packed scratch. -/
structure DigitAt (g : LongGeometry) (r j : Nat) : Prop where
  index : j<r
  offset : BStarPhysicalDigitSem.off g=min 5 j
  endNow : (g.inside && g.last)=decide (j+1=r)
  endNext : g.successorEnd=decide (j+2=r)

/-- CONST and MASK consume only these three tests. In particular
ordinal 6 and larger work even though packed offset remains 5. -/
theorem constants_of_chart (g : LongGeometry) (r j : Nat) (h : DigitAt g r j) :
    BStarPhysicalDigitSem.ConstantsPosition g r j := by
  refine ⟨⟨?_,?_⟩,h.endNow,?_⟩
  · rw [h.offset]
    omega
  · rw [h.offset]
    omega
  · rw [h.endNow,h.endNext]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true,decide_eq_true_eq]
    have := h.index
    omega

/-- If the actual old left site is at ordinal j and its successor is
not a new header, one physical mark writes the successor's saturated
j+1 offset. This does not assert that arbitrary old geometry is settled. -/
theorem joined_offset_increment (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (j : Nat) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    BStarPhysicalDigitSem.off g.1=min 5 j →
    g.2.axes.h6=false →
    offsetL (largePair b x).2.long=min 5 (j+1) := by
  dsimp only
  intro O H
  rw [(joined_offsets k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x).2]
  exact offset_increment _ j O H

/-- An actual mark with an old right header anchors its raw offset
at zero; this reset does not use the previous raw offset on either end. -/
theorem joined_offset_reset (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (oldHeaders b x.2).h6=true →
    offsetL (largePair b x).2.long=0 := by
  dsimp only
  intro H
  rw [(joined_offsets k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x).2]
  unfold nextOffset
  dsimp only
  exact if_pos (show (Pair.map (longGeometry (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp)) x).2.axes.h6=true from H)

/-- A mark that samples the true right END gives the exact left
successor-END test in the new joined long geometry. The width
provider's old END readout is the only layout input. -/
theorem joined_end_transfer (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (j : Nat) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    (g.2.inside && g.2.last)=decide (j+2=r) →
    (longGeometry b (largePair b x).1).successorEnd=decide (j+2=r) := by
  dsimp only
  intro H
  exact (joined_offsets k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x).1.trans H

#print axioms joined_cache
#print axioms joined_offsets
#print axioms constants_of_chart
#print axioms joined_offset_increment
#print axioms joined_offset_reset
#print axioms joined_end_transfer
end L4.BStarLongSector
