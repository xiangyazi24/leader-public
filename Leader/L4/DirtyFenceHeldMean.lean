import Leader.L4.DirtyFenceShadow
import Leader.L4.DirtyFenceIdentityMean
import Leader.L4.BStarClearanceSource

namespace L4.DirtyFenceHeldMean
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongPackets
open BStarAcquireAnchors BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarH6WordChart BStarH6Ordinal BStarClearanceDataChart BStarResetChartTouch
open BStarFenceShadow BStarFencePorts BStarFenceLineGeometry BStarFenceSweepClock
open BStarFenceLeftShadow (leftOcc)
open BStarFenceRightShadow (rightOcc)
open BStarClearanceSource (Held held_before)
open BStarClearanceIndexedSum (distance)
open DirtyLeastForward (ringF ring_origin)
open L4.Height

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- Once every field-preparation-capable chart address is in the
forward-free cutoff, a dirty held owner either leaves Held or clears
both physical mobile lines in the same raw IID clock as open exclusion.
The phase does not require a generated owner, PC11, or clean retained
state. The statement does not assert that the cutoff is already reached. -/
theorem expected_until_nonheld_or_empty
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
    (cutoff : Nat)
    (onPrep : ∀ u∈S, (∃ sh op,sh∈prepSites (longGeometry B (base u.1)) u.2 op) →
      cutoff<distance S u)
    (clear : ∀ u∈S, cutoff<distance S u → ¬ringF x u) :
    let Lroot := (S.getD 0 fall).1
    let Rroot := (S.getD len fall).1
    let phys := fun q : X => (⟨leftOcc q Lroot l r', rightOcc q Rroot d r'⟩ :
      Two (l:=l+r') (r:=d+r'))
    Height.IIDExpectedHittingTimeAtMost step (fun q=>¬Held (q Lroot).long ∨ Empty (phys q)) x
      (92*n*max (l+r') (d+r')) := by
  classical
  dsimp only
  let Lroot := (S.getD 0 fall).1
  let Rroot := (S.getD len fall).1
  let phys := fun q : X => (⟨leftOcc q Lroot l r', rightOcc q Rroot d r'⟩ :
    Two (l:=l+r') (r:=d+r'))
  let active := fun q : X => decide (Held (q Lroot).long)
  let P := fun q : X => Q q ∧ ∀ u∈S, cutoff<distance S u → ¬ringF q u
  have rootEq : Lroot=(endpoint (oldH6 B base) hh o 0).1 := congrArg Prod.fst chart.root
  have pclosed (q : X) (e : Fin n) (K : P q) (A : active q=true) : P (step q e) := by
    have H : Held (q Lroot).long := of_decide_eq_true A
    have W := held_before hp q Lroot e H
    rw [rootEq] at W
    refine ⟨closed q K.1 e,?_⟩
    intro u U cut F
    rcases ring_origin hp chart (layout q K.1) e (sep e) W u U F with old|⟨v,V,old,far⟩
    · exact K.2 u U cut old
    · exact K.2 v V (by omega) old
  have one (q : X) (e : Fin n) (K : P q) (_ : active q=true) :
      Mark (leftPort Lroot) e (phys q).left (phys (step q e)).left ∧
      Mark (rightPort Rroot) e (phys q).right (phys (step q e)).right := by
    exact DirtyFenceShadow.both_marks hp chart sep (layout q K.1)
      (DirtyFenceShadow.owner_reservation_free_of_cutoff hp chart (layout q K.1) cutoff onPrep K.2)
      LF RF dp flags notShort e
  have E : Done active phys = (fun q=>¬Held (q Lroot).long ∨ Empty (phys q)) := by
    funext q
    apply propext
    simp [Done,active]
  rw [←E]
  exact DirtyFenceIdentityMean.identity_stopped_expected hn (leftPort Lroot) (rightPort Rroot)
    hl (by omega) (fun _ _=>left_labels_injective Lroot lc) (fun _ _=>right_labels_injective Rroot rc)
    step active P phys pclosed one x ⟨I,clear⟩

end L4.DirtyFenceHeldMean
