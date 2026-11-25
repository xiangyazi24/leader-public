import Leader.L4.Height.FreshNumericInputs
import Leader.L4.Height.ProductionWidths
import Leader.L4.Height.FenceEmbedding
import Leader.L4.BStarFreshNumericOperandSeed

namespace L4.Height.FreshFenceSeed
open AllSizeProtocol PhysicalCustody ProductionCustody BStarTrace BStarLongWork BStarLongClaims BStarLongPackets
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarFreshNumeric BStarFreshNumericOperands BStarFreshNumericOperandSeed
open BStarCopyFenceSaturation
open BStarCopyRightStrip (addr rail)
open BStarCopyLeftFence (ldRead)
open BStarCopyRightFence (rdRead)
open BStarCopyLeftPending (pending)
open BStarCopyRightMixed (planOf)

variable {s n : Nat} {x : Raw s n} {g : CustodyWitness x}
local notation "hp" => (show 0<2 by decide)
local notation "B" => rows s
local notation "r" => radWidth s
local notation "h" => oldH6 B g.base

/-- Both drained physical FENCE lines and their two exact packed images
supply all mobile guards and every retained read performed by the native
scan. A right-hand OUT padding site requires only a mobile guard. -/
theorem from_images (P : Production g) {o : Owners h} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp g.base g.hh o S len fall) (y : Raw s n)
    (l rs top : Nat) (a : Fin n) (left right : Nat→BitVec 36) :
    let src := (S.getD 0 fall).1
    let dst := (S.getD len fall).1
    BStarCopyLeftStrip.Strip B g.base src l r → addr src l=dst →
    BStarCopyRightRetained.Dest B g.base dst r →
    BStarCopyRightWrappedGeometry.WrappedStrip B g.base a rs top →
    addr a 0=addr dst (r-1) → top+1=rs+r →
    (∀ i sh,BStarCopyLeftFenceHold.Region src l r i sh →
      (readLane (Sheet.index sh) (y i).long).mobile=.empty) →
    (∀ i sh,BStarCopyRightWrappedFenceHold.Region dst a r rs top i sh →
      (readLane (Sheet.index sh) (y i).long).mobile=.empty) →
    laneRead (ldRead y dst) 0 r=(pending id r).reverse.map (Digit9.data ∘ left) →
    laneRead (rdRead y dst r) 0 r=(planOf (fun i=>i-rs) rs top).reverse.map (Digit9.data ∘ right) →
    (∀ i sh,ActiveOwner hp g.base o.val i sh → (readLane (Sheet.index sh) (y i).long).mobile=.empty) ∧
    (∀ k≤len,(S.getD k fall).2.val=1 → (longGeometry B (g.base (S.getD k fall).1)).inside=true →
      operands (y (S.getD k fall).1).long) := by
  dsimp only
  let dst := (S.getD len fall).1
  intro L join D R atBase size drainL drainR leftImage rightImage
  constructor
  · obtain ⟨_,d,_,other,_,_,_⟩ := FenceEmbedding.two_strips hp C r (width g)
      (radius_pos P) g.flags g.notShort (terminal_le_width g) g.charts
    have frame : BStarFenceLineGeometry.RightFrame B g.base dst d r :=
      ⟨other.seam_le,other.width_le,other.width_pos,other.source_header,other.dest_header,other.ls_body,
        fun j hj=>(FenceEmbedding.strip_bond other j hj).2⟩
    have offset : a=addr dst (r-1) :=
      (Fin.ext (Nat.mod_eq_of_lt a.isLt) : addr a 0=a).symm.trans atBase
    have rotate (j : Nat) : addr a j=addr dst ((r-1)+j) := by
      rw [offset,BStarCopyLeftFenceHold.address_add]
    let gap := r-1+rs
    have gapHead : h (addr dst gap)=true := (rotate rs) ▸ R.rs_header
    have gapPos : 0<gap := by dsimp [gap]; have := R.seam_pos; omega
    have dPos := other.seam_pos
    have gapBody (j : Nat) (pos : 0<j) (small : j<gap) : h (addr dst j)=false := by
      by_cases inside : j<r
      · exact D.body j pos inside
      · let t := j-(r-1)
        have rp := D.pos
        have shift : r-1+t=j := by dsimp [t]; omega
        rw [←shift,←rotate]
        apply R.rd_noheader <;> dsimp [t,gap] at * <;> omega
    have widthEq : d=gap := by
      rcases Nat.lt_trichotomy d gap with less|eq|more
      · exact False.elim (Bool.noConfusion ((gapBody d dPos less).symm.trans other.dest_header))
      · exact eq
      · exact False.elim (Bool.noConfusion ((other.ls_body gap gapPos more).symm.trans gapHead))
    intro i sh own
    rcases active_on_lines hp C dPos L frame join (fun j=>(g.flags j).1) i sh own with
      ⟨k,loc,sheet⟩|⟨k,loc,sheet⟩
    · exact drainL _ _ ⟨k.val,k.isLt,loc.symm,sheet.symm⟩
    · let c := BStarFencePorts.rightCoord k
      have cn : c<d+r := by dsimp [c,BStarFencePorts.rightCoord]; have := k.isLt; omega
      have lo : r≤d := by rw [widthEq]; dsimp [gap]; have := R.seam_pos; omega
      by_cases inside : c<r
      · apply drainR _ _ (.inl ⟨c,inside,loc.symm,?_⟩)
        change sh=BStarFenceLineGeometry.rightRail d c at sheet
        simpa only [BStarFenceLineGeometry.rightRail,if_pos (Nat.lt_of_lt_of_le inside lo)] using sheet
      · let t := c-(r-1)
        have rp := D.pos
        have shift : r-1+t=c := by dsimp [t]; omega
        apply drainR _ _ (.inr ⟨t,by dsimp [t]; omega,by dsimp [t,gap] at *; omega,
          (rotate t).trans ((congrArg (addr dst) shift).trans loc.symm),?_⟩)
        change sh=BStarFenceLineGeometry.rightRail d c at sheet
        rw [sheet]
        unfold BStarFenceLineGeometry.rightRail rail
        have cmp : c<d ↔ t<rs := by dsimp [gap,t] at *; omega
        by_cases less : c<d
        · simp [less,cmp.mp less]
        · have notT : ¬t<rs := fun q=>less (cmp.mpr q)
          simp [less,notT]
  · intro k hk one inside
    obtain ⟨j,eq⟩ := FreshNumericInputs.digit_at hp C (fun i=>(g.flags i).1) g.notShort
      (fun _=>rfl) k hk one inside
    obtain ⟨A,B'⟩ := BStarNativeCopyReadback.both_at_digit y dst rs top left right size leftImage rightImage j
    rw [eq]
    exact ⟨⟨_,A⟩,_,B'⟩

#print axioms from_images
end L4.Height.FreshFenceSeed
