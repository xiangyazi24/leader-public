import Leader.L4.DirtyPrepDrainStable
import Leader.L4.DirtyPrepWeak
import Leader.L4.DirtyPrepStrict

namespace L4.DirtyPrepPaidMean
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongPackets
open BStarAcquireAnchors BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarH6WordChart BStarH6Ordinal BStarClearanceDataChart BStarResetChartTouch
open BStarFenceShadow BStarFencePorts BStarFenceLineGeometry BStarFenceSweepClock
open BStarFenceLeftShadow (leftOcc)
open BStarFenceRightShadow (rightOcc)
open BStarClearanceSource (Held held_before)
open BStarClearanceIndexedSum (distance distance_idx)
open DirtyLeastForward (ringF ring_origin)
open L4.Height
open BStarClearanceOffset (correct)

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

theorem expected_through_prep_and_stable_drain
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q x)
    (layout : ∀ q,Q q→∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B q i)
    (closed : ∀ q,Q q→∀ e,Q (step q e))
    {l d r' : Nat} (LF : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 l r')
    (RF : RightFrame B base (S.getD len fall).1 d r') (dp : 0<d)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r') ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r'))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → r'≤oldOrdinal B base hh i+1)
    (hn : 0<n) (hl : 0<l+r') (lc : l+r'≤n) (rc : d+r'≤n)
    (head : ∀ i,let g:=longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i,let g:=oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2=true)
    (cb : correct (oldH6 B base) hh 5 base)
    (cx : ∀ q,Q q→correct (oldH6 B base) hh 5 q)
    {j : Nat} (J : j≤len) (high : 6≤(S.getD j fall).2.val)
    (low : ∀ i,i<j→(S.getD i fall).2.val≤5) :
    let root := (S.getD 0 fall).1
    let A (q : X) := Held (q root).long
    let F (q : X) (i : Nat) := ringF q (S.getD i fall)
    let phys := fun q : X => (⟨leftOcc q root l r', rightOcc q (S.getD len fall).1 d r'⟩ :
      Two (l:=l+r') (r:=d+r'))
    Height.IIDExpectedHittingTimeAtMost step (fun q=>¬A q ∨ (∀ i,i<j→¬F q i) ∧ Empty (phys q)) x
      (n*(3*j+2)+92*n*max (l+r') (d+r')) := by
  dsimp only
  apply DirtyPrepDrainStable.expected_through_prep_and_stable_drain_of_local hp
    chart sep Q I layout closed LF RF dp flags notShort hn hl lc rc head cont J high
  · intro q i Qq H L e live
    obtain ⟨ij,F,least⟩ := L
    have prep := low i ij
    exact DirtyPrepWeak.weak_held_least hp chart sep (layout q Qq) cb (cx q Qq) H
      (by omega) prep F least e live
  · intro q i Qq _ L
    obtain ⟨ij,F,least⟩ := L
    have prep := low i ij
    exact DirtyPrepStrict.prep_least_pays hp chart sep (layout q Qq) head cont
      cb (cx q Qq) i (by omega) prep F least

theorem expected_through_first_high_and_stable_drain
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q x)
    (layout : ∀ q,Q q→∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B q i)
    (closed : ∀ q,Q q→∀ e,Q (step q e))
    {l d r' : Nat} (LF : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 l r')
    (RF : RightFrame B base (S.getD len fall).1 d r') (dp : 0<d)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r') ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r'))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → r'≤oldOrdinal B base hh i+1)
    (hn : 0<n) (hl : 0<l+r') (lc : l+r'≤n) (rc : d+r'≤n)
    (head : ∀ i,let g:=longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i,let g:=oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2=true)
    (cb : correct (oldH6 B base) hh 5 base)
    (cx : ∀ q,Q q→correct (oldH6 B base) hh 5 q)
    (W : Nat) (Wchart : len≤W) (Wlines : max (l+r') (d+r')≤W) :
    let root := (S.getD 0 fall).1
    let A (q : X) := Held (q root).long
    let F (q : X) (i : Nat) := ringF q (S.getD i fall)
    let phys := fun q : X => (⟨leftOcc q root l r', rightOcc q (S.getD len fall).1 d r'⟩ :
      Two (l:=l+r') (r:=d+r'))
    ∃ j, j≤len ∧ 6≤(S.getD j fall).2.val ∧ (∀ i,i<j→(S.getD i fall).2.val≤5) ∧
      Height.IIDExpectedHittingTimeAtMost step
        (fun q=>¬A q ∨ (∀ i,i<j→¬F q i) ∧ Empty (phys q)) x
        (n*(3*W+2)+92*n*W) := by
  dsimp only
  obtain ⟨j,J,high,low⟩ := DirtyFenceFixedCut.exists_first_high hp chart
  refine ⟨j,J,high,low,?_⟩
  have P := expected_through_prep_and_stable_drain hp chart sep Q I layout closed
    LF RF dp flags notShort hn hl lc rc head cont cb cx J high low
  intro t
  refine Nat.le_trans (P t) (Nat.mul_le_mul_right _ ?_)
  have JW : j≤W := Nat.le_trans J Wchart
  exact Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) (Nat.mul_le_mul_left _ Wlines)

end L4.DirtyPrepPaidMean
