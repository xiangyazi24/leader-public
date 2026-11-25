import Leader.L4.Height.FenceEmbedding
import Leader.L4.BStarFenceCoverage

namespace L4.Height.FenceCoverage
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarH6WordChart BStarH6Ordinal
open BStarLongFiberOwner BStarAcquireAnchors BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetChartTouch BStarClearanceDataChart BStarCopyRightStrip FenceEmbedding

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

def InLines {n : Nat} (root mid : Fin n) (u v width : Nat) (i : Fin n) (sh : Sheet) : Prop :=
  (∃ k,0<k ∧ k≤u+width ∧ (addr root (k-1),BStarCopyLeftStrip.rail u (k-1))=(i,sh)) ∨
  (∃ k,0<k ∧ k≤v+width ∧ (addr mid (v+width-k),returnRail v (v+width-k))=(i,sh))

theorem cover {base : X} {hh : ∃ i,oldH6 B base i=true} {o : Owners (oldH6 B base)}
    {S : List (Pos n)} {len : Nat} {fall : Pos n} (C : Chart hp base hh o S len fall)
    {u v w : Nat} (L : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 u w)
    (R : BStarCopyLeftStrip.Strip B base (S.getD len fall).1 v w)
    (seam : addr (S.getD 0 fall).1 u=(S.getD len fall).1)
    (inside : ∀ j,(longGeometry B (base j)).inside=decide (oldOrdinal B base hh j<w))
    (i : Fin n) (sh : Sheet) (active : activeSheet (longGeometry B (base i)) sh=true)
    (own : dataOwner (oldH6 B base) i sh=o.val) :
    InLines (S.getD 0 fall).1 (S.getD len fall).1 u v w i sh := by
  let dest := (S.getD len fall).1
  have frame : BStarFenceLineGeometry.RightFrame B base dest v w :=
    ⟨R.seam_le,R.width_le,R.width_pos,R.source_header,R.dest_header,R.ls_body,
      fun j hj=>(strip_bond R j hj).2⟩
  have small (keep : sh=.ld ∨ sh=.rs) : oldOrdinal B base hh i<w := by
    have lt : (longGeometry B (base i)).inside=true := by rcases keep with rfl|rfl <;> exact active
    exact of_decide_eq_true ((inside i).symm.trans lt)
  rcases BStarFenceCoverage.all_sheets hp C R.seam_pos L frame seam i sh own small with
    ⟨j,loc,sheet⟩|⟨j,loc,sheet⟩
  · refine .inl ⟨j.val+1,by omega,by have := j.isLt; omega,?_⟩
    simp only [Nat.add_sub_cancel]
    exact Prod.ext loc.symm sheet.symm
  · refine .inr ⟨j.val+1,by omega,by have := j.isLt; omega,?_⟩
    change (_,returnRail v (v+w-(j.val+1)))=(i,sh)
    have coord : v+w-(j.val+1)=BStarFencePorts.rightCoord j := by
      unfold BStarFencePorts.rightCoord
      omega
    rw [coord]
    exact Prod.ext loc.symm sheet.symm

#print axioms cover
end L4.Height.FenceCoverage
