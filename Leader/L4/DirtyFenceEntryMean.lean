import Leader.L4.DirtyFenceHeldMean
import Leader.L4.DirtyFenceOccurrence

namespace L4.DirtyFenceEntryMean
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongPackets
open BStarAcquireAnchors BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarH6WordChart BStarH6Ordinal BStarClearanceDataChart BStarResetChartTouch
open BStarFenceShadow BStarFencePorts BStarFenceLineGeometry BStarFenceSweepClock
open BStarFenceLeftShadow (leftOcc)
open BStarFenceRightShadow (rightOcc)
open BStarClearanceSource (Held held_before)
open BStarClearanceIndexedSum (distance distance_idx)
open BStarLongCommandData (fenceSheet)
open DirtyLeastForward (ringF ring_origin)
open L4.Height

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- At a FENCE address with a forward-free strict prefix, the geometric
order excludes preparation at all owner lanes during Held. The stop
bound needs no assumption about a clean data or retained token. -/
theorem expected_from_least_fence_address
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
    {j : Nat} (J : j≤len) {sh : Sheet}
    (F : fenceSheet (longGeometry B (base (S.getD j fall).1)) (S.getD j fall).2=some sh)
    (clearBefore : ∀ i,i<j → ¬ringF x (S.getD i fall)) :
    let Lroot := (S.getD 0 fall).1
    let Rroot := (S.getD len fall).1
    let phys := fun q : X => (⟨leftOcc q Lroot l r', rightOcc q Rroot d r'⟩ :
      Two (l:=l+r') (r:=d+r'))
    Height.IIDExpectedHittingTimeAtMost step (fun q=>¬Held (q Lroot).long ∨ Empty (phys q)) x
      (92*n*max (l+r') (d+r')) := by
  let cutoff := distance S (S.getD j fall)
  have onPrep (u : Pos n) (U : u∈S)
      (P : ∃ sh op,sh∈prepSites (longGeometry B (base u.1)) u.2 op) :
      cutoff<distance S u := by
    obtain ⟨_,_,H⟩ := P
    exact DirtyFenceOccurrence.prep_before_fence hp chart head cont J F U H
  have clear (u : Pos n) (U : u∈S) (far : cutoff<distance S u) : ¬ringF x u := by
    obtain ⟨i,hi,E⟩ := List.mem_iff_getElem.mp U
    have JS : j<S.length := by have := chart.length; omega
    have iS : S.getD i fall=u := (List.getElem_eq_getD (h:=hi) fall).symm.trans E
    change distance S (S.getD j fall)<distance S u at far
    rw [←iS,←List.getElem_eq_getD (h:=JS) fall,←List.getElem_eq_getD (h:=hi) fall,
      distance_idx chart.nodup JS,distance_idx chart.nodup hi] at far
    rw [←iS]
    exact clearBefore i (by omega)
  exact DirtyFenceHeldMean.expected_until_nonheld_or_empty hp chart sep Q I layout closed LF RF dp
    flags notShort hn hl lc rc cutoff onPrep clear

#print axioms expected_from_least_fence_address
end L4.DirtyFenceEntryMean
