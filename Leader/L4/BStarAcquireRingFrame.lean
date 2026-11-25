import Leader.L4.BStarAcquireJoinedHop
import Leader.L4.BStarK0Frame
import Leader.L4.AllSizeS1Geometry

/-! Raw K0 frames through scratch, the outer guard, and a literal
selected clockwise ring step. The routing absence conditions refer to
the actual old pair, not a separate synthesized geometry. -/
namespace L4.BStarAcquireRingFrame
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken
open BStarLongWork BStarLongClaims BStarLongRouting BStarLongCommand BStarLongDoor

abbrev W (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) :=
  LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

def k0 {a : LargeParams} (x : LargeSite a) : BitVec 52 := x.long.extractLsb' 1712 52

private theorem scratch_hold (g : Pair LongGeometry) (x : Pair (BitVec LW)) (s : Bool)
    (w : BitVec LW) :
    (kField 0).read ((lane s (longScratch g x)).apply w)=(kField 0).read w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
  exact Patch.hold _ _ _ (BStarAcquireJoinedHop.scratch_kframe g x s _ (by change 1192≤1712+i; omega) (by change 1712+i<1764; omega))

def InFlightWait (g : LongGeometry) (w : BitVec LW) : Prop :=
  LongDoorGuard.valid manifest w=true ∧ (ctrlPhase.read w).toNat=2 ∧
    (bind g 0 (atSite w 0)=.trail ∨ ∃ v, bind g 0 (atSite w 0)=.forward v)

theorem joined_left (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (W k₁ k₂ t₂ J₁ J₂ r c p c₁)) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    (∀ w∈routing g raw, w.1≠L 0) →
    k0 (largePair b x).1=k0 x.1 := by
  dsimp only
  intro h
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let work := longWork g raw
  let scratch := longScratch g raw
  change (kField 0).read ((work.1.compose scratch.1).apply raw.1)=_
  rw [Patch.compose_apply]
  refine (scratch_hold g raw false _).trans ?_
  exact BStarK0Frame.left_k0 g raw h

theorem joined_right (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (W k₁ k₂ t₂ J₁ J₂ r c p c₁)) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    InFlightWait g.2 raw.2 →
    (∀ w∈routing g raw, w.1≠R 0) →
    k0 (largePair b x).2=k0 x.2 := by
  dsimp only
  rintro ⟨valid,wait,bound⟩ h
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let work := longWork g raw
  let scratch := longScratch g raw
  change (kField 0).read ((LongDoorGuard.guard manifest g.2.axes.h6 raw.2
    (work.2.compose scratch.2)).apply raw.2)=_
  have E : LongDoorGuard.guard manifest g.2.axes.h6 raw.2
      (work.2.compose scratch.2)=work.2.compose scratch.2 := by
    cases g.2.axes.h6
    · exact LongDoorGuard.no_authority _ _ _
    · exact LongDoorGuard.valid_no_override _ _ _ valid
  rw [E,Patch.compose_apply]
  refine (scratch_hold g raw true _).trans ?_
  exact BStarK0Frame.right_wait_k0 g raw valid wait bound h

/-- One exact raw K0 idle-frame for every selected ring mark: if the
tracked site is the left or right selected endpoint, inspect only the
respective actual routing target. The right-only door holds on valid
WAIT with a literal occurrence-bound trail/forward. An unselected
tracked site is bit-exact without any old guard or routing condition.
Left wins in the one-site overlapping-endpoint convention. -/
theorem step_idle_k0 (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    {n : Nat} (x : Fin n → W k₁ k₂ t₂ J₁ J₂ r c p c₁) (e i : Fin n) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let j := rightNeighbor e
    let a := (x e,x j)
    let g := Pair.map (longGeometry b) a
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long a
    (i=e → ∀ w∈routing g raw, w.1≠L 0) →
    (i≠e → i=j → InFlightWait g.2 raw.2 ∧ ∀ w∈routing g raw, w.1≠R 0) →
    k0 (AllSizeS1Geometry.step b x e i)=k0 (x i) := by
  dsimp only
  intro left right
  by_cases E : i=e
  · subst i
    simpa only [AllSizeS1Geometry.step,if_true] using
      joined_left k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e)) (left rfl)
  · by_cases J : i=rightNeighbor e
    · subst i
      simpa only [AllSizeS1Geometry.step,if_neg E,if_true] using
        joined_right k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e))
          (right E rfl).1 (right E rfl).2
    · simp only [AllSizeS1Geometry.step,if_neg E,if_neg J]

/-- All private state, including valid WAIT and the raw token, is
unchanged when neither endpoint is the tracked site. -/
theorem unselected {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x : Fin n→LargeSite a) (e i : Fin n) (hl : i≠e) (hr : i≠rightNeighbor e) :
    AllSizeS1Geometry.step b x e i=x i := by
  simp only [AllSizeS1Geometry.step,if_neg hl,if_neg hr]

end L4.BStarAcquireRingFrame
