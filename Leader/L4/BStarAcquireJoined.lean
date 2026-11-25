import Leader.L4.BStarAcquireSource
import Leader.L4.BStarAcquireFrame

/-! The capture-file frame extends to actual bStar, provided this
endpoint remains a source header and its old guard does not repair. -/
namespace L4.BStarAcquireJoined
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongWork BStarLongDoor
open BStarAcquireFrame BStarLongClaims BStarLongToken

def snapshot (x : BitVec LW) : BitVec 27 × BitVec 6 :=
  (capturedHeaders.read x,captures.read x)

theorem scratch_frame (g : Pair LongGeometry) (old : Pair (BitVec LW)) (s : Bool) :
    Frame (lane s (longScratch g old)) := by
  cases s
  · change Frame ((shField.assign _).compose (seField.assign _))
    exact compose (assign _ _ (.inr (by decide))) (assign _ _ (.inr (by decide)))
  · change Frame (offField.assign _)
    exact assign _ _ (.inr (by decide))

/-- No additional effect of the other layers can erase the capture file.
On the right the outer invalid-door guard is the only extra repair path. -/
theorem joined_retains (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (s : Bool) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    (lane s g).axes.h6=true →
    (s=true → LongDoorGuard.valid manifest raw.2=true) →
    (∀ cl tok, (cl,.door tok)∈BStarLongEvents.actualOffers g raw →
      (cl.source.side==.right)=s →
      Normal (BStarLongWork.atOld raw cl.source) (oldDoor (BStarLongWork.atOld raw cl.source) tok)) →
    snapshot (lane s (Pair.map LargeSite.long (largePair b x)))=snapshot (lane s raw) := by
  dsimp only
  intro hh valid normal
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let w := longWork g raw
  let q := longScratch g raw
  let mid := patchPair w raw
  have ⟨H,K⟩ := long_work_preserves g raw s hh normal
  have SH := captures_hold (lane s q) (lane s mid) (scratch_frame g raw s)
  have middle : snapshot (lane s mid)=snapshot (lane s raw) := Prod.ext H K
  have finish : snapshot ((lane s q).apply (lane s mid))=snapshot (lane s mid) :=
    Prod.ext SH.1 SH.2
  suffices E : lane s (Pair.map LargeSite.long (largePair b x)) =
      (lane s q).apply (lane s mid) by
    exact (congrArg snapshot E).trans (finish.trans middle)
  cases s
  · change (w.1.compose q.1).apply raw.1=q.1.apply (w.1.apply raw.1)
    exact Patch.compose_apply _ _ _
  · change (LongDoorGuard.guard manifest g.2.axes.h6 raw.2 (w.2.compose q.2)).apply raw.2=
      q.2.apply (w.2.apply raw.2)
    rw [show g.2.axes.h6=true from hh]
    rw [LongDoorGuard.valid_no_override _ _ _ (valid rfl)]
    exact Patch.compose_apply _ _ _

#print axioms scratch_frame
#print axioms joined_retains
end L4.BStarAcquireJoined
