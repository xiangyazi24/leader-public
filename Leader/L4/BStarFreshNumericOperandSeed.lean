import Leader.L4.BStarFreshNumericOperandPrefix
import Leader.L4.BStarFenceCoverage

/-! Projection of a physical two-line completed FENCE cut to the
drained mobile and retained-data seed required by the numeric phase. -/
namespace L4.BStarFreshNumericOperandSeed
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongPackets
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetChartTouch BStarLongFixedRouting BStarClearanceDataChart
open BStarFenceLineGeometry BStarFenceNominatedClear BStarFenceCoverage
open BStarFreshNumericOperands
open BStarCopyRightStrip (addr)

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

/-- Every active physical lane of an owned chart is on one of the two
actual FENCE lines, including the padding carried by LS or RD. -/
theorem active_on_lines {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    {l d w : Nat} (dp : 0<d)
    (LF : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 l w)
    (RF : RightFrame B base (S.getD len fall).1 d w)
    (seam : addr (S.getD 0 fall).1 l=(S.getD len fall).1)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<w))
    (i : Fin n) (sh : Sheet) (owner : ActiveOwner hp base o.val i sh) :
    OnLines (S.getD 0 fall).1 (S.getD len fall).1 l d w i sh := by
  apply all_sheets hp C dp LF RF seam i sh owner.1
  intro E
  have I := owner.2
  have inside : (longGeometry B (base i)).inside=true := by
    rcases E with rfl|rfl <;> exact I
  rw [flags] at inside
  exact of_decide_eq_true inside

theorem numeric_seed {base y : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    {l d w : Nat} (dp : 0<d)
    (LF : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 l w)
    (RF : RightFrame B base (S.getD len fall).1 d w)
    (seam : addr (S.getD 0 fall).1 l=(S.getD len fall).1)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<w))
    (mobile : ∀ i sh,OnLines (S.getD 0 fall).1 (S.getD len fall).1 l d w i sh →
      (readLane (Sheet.index sh) (y i).long).mobile=.empty)
    (retained : ∀ i sh,OnLines (S.getD 0 fall).1 (S.getD len fall).1 l d w i sh →
      ActiveOwner hp base o.val i sh → (sh=.ld ∨ sh=.rd) →
      ∃ a,(readLane (Sheet.index sh) (y i).long).retained=.data a) :
    (∀ i sh,ActiveOwner hp base o.val i sh → (readLane (Sheet.index sh) (y i).long).mobile=.empty) ∧
    (∀ i sh,ActiveOwner hp base o.val i sh → (sh=.ld ∨ sh=.rd) →
      ∃ a,(readLane (Sheet.index sh) (y i).long).retained=.data a) :=
  ⟨fun i sh own => mobile i sh (active_on_lines hp C dp LF RF seam flags i sh own),
    fun i sh own => retained i sh (active_on_lines hp C dp LF RF seam flags i sh own) own⟩

end L4.BStarFreshNumericOperandSeed
