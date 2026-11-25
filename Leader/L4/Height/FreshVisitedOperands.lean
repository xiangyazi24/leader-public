import Leader.L4.Height.FreshFenceContinuation

namespace L4.Height.FreshVisitedOperands
open AllSizeProtocol BStarTrace BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetChartTouch BStarLongWork BStarLongClaims BStarLongPackets
open BStarCopyFIFO BStarCopyMarkedLedger BStarCopyFenceSaturation FreshFenceContinuation
open BStarCopyLeftDeposit (headFirst)
open BStarCopyRightMark (stripWord)
open BStarCopyRightStrip (addr rail)
open BStarCopyLeftFence (ldRead)
open BStarCopyRightFence (rdRead)

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

private theorem retained_at {T : Type} {plan : List T} {s : Ledger T} {up : List T}
    (digits : T→BitVec 36) (ord : OrderedPrefix plan s up) (done : s.release.pending=[])
    (nilUp : up=[]) (lanes : Nat→Lane) (j : Nat) (bound : j<plan.length)
    (matchLane : ∀ t,t<plan.length → Compatible digits (s.cells t) (lanes t))
    (passed : ∀ t,t<j → (lanes t).mobile=.empty) : ∃ d,(lanes j).retained=.data d := by
  obtain ⟨trace,boundary⟩ := ordered_prefix ord
  have earlier (t : Nat) (small : t<j) : (s.cells t).mobile=none := by
    have read := (passed t small).symm.trans (matchLane t (by omega)).1
    cases state : (s.cells t).mobile with
    | none => rfl
    | some v => rw [state] at read; contradiction
  obtain ⟨_,tag,atJ⟩ := FreshFenceOperand.inspections_receive trace done (nilUp ▸ boundary)
    j bound earlier
  exact ⟨digits tag,by rw [(matchLane j bound).2,atJ]; rfl⟩

/-- At *each* retaining FENCE inspection on the literal chart, all upstream
cells and the proper prefix of retaining cells have already been visited.
The ordered stream therefore supplies the inspected old operand itself,
even at index zero, at the last digit, and on the wrapped right line. -/
theorem on_retaining_visit {L R : Type} {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (width ls rs top : Nat) (pos : 0<width)
    (left dest other : Fin n) (atDest : dest=(S.getD len fall).1)
    (seam : addr left ls=dest) (head : addr other 0=addr dest (width-1))
    (leftLine : BStarCopyLeftStrip.Strip B base left ls width)
    (rd : BStarCopyRightRetained.Dest B base dest width)
    (rightLine : BStarCopyRightWrappedGeometry.WrappedStrip B base other rs top)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (BStarH6Ordinal.oldOrdinal B base hh i<width))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → width≤BStarH6Ordinal.oldOrdinal B base hh j+1)
    (k : Nat) (K : k≤len)
    (empty : ∀ i sh,Visited hp base S fall k i sh → (readLane (Sheet.index sh) (x i).long).mobile=.empty)
    (ld : L→BitVec 36) (rr : R→BitVec 36) (lp : List L) (rp : List R)
    (lc : Ledger L) (rc : Ledger R) (lu : Nat→Option L) (ru : Nat→Option R)
    (sizeL : lp.length=width) (sizeR : rp.length=width)
    (lo : OrderedPrefix lp lc (headFirst ls lu)) (ro : OrderedPrefix rp rc (stripWord top ru))
    (doneL : lc.release.pending=[]) (doneR : rc.release.pending=[])
    (lmatch : BStarCopyLeftMark.UpstreamMatches ld x left ls lu)
    (rmatch : BStarCopyRightMark.MobileMatches rr x other rs top ru)
    (lkeep : BStarCopyLeftRetained.RetainedMatches ld x dest width lc)
    (rkeep : BStarCopyRightRetained.RetainedMatches rr x dest width rc) :
    (∀ j,j<width → S.getD k fall=(addr dest j,fencePort .ld) → ∃ d,(ldRead x dest j).retained=.data d) ∧
    (∀ j,j<width → S.getD k fall=(addr dest (width-1-j),fencePort .rd) →
      ∃ d,(rdRead x dest width j).retained=.data d) := by
  obtain ⟨last,A,leftPos,destPos,upPos⟩ := strip_ranks hp chart width ls rs top pos left dest other
    atDest seam head leftLine rd rightLine flags notShort
  have length := chart.length
  constructor
  · intro j J here
    have ray : addr dest j=addr left (ls+j) := by
      rw [←seam]
      exact BStarCopyLeftFenceHold.address_add left ls j
    obtain ⟨index,place,mark,_⟩ := leftPos (ls+j) (by omega)
    have ldSheet : BStarCopyLeftStrip.rail ls (ls+j)=.ld := if_neg (by omega)
    rw [ldSheet,←ray] at mark
    have eq := (List.getD_inj (show index<S.length by omega) (show k<S.length by omega) chart.nodup).mp
      (mark.trans here.symm)
    subst index
    have before (t : Nat) (less : t<ls+j) :
        (readLane (Sheet.index (BStarCopyLeftStrip.rail ls t)) (x (addr left t)).long).mobile=.empty := by
      obtain ⟨q,rnk,loc,mapped⟩ := leftPos t (by omega)
      exact empty _ _ ⟨⟨q,by omega,loc⟩,mapped⟩
    have nop := left_empty_labels ld x left ls lu lmatch (fun t T=>before t (by omega))
    apply retained_at ld lo doneL nop (ldRead x dest) j (by omega)
    · intro t T; exact lkeep t (by omega)
    · intro t T
      have was := before (ls+t) (by omega)
      rw [show BStarCopyLeftStrip.rail ls (ls+t)=.ld from if_neg (by omega),
        ←BStarCopyLeftFenceHold.address_add,seam] at was
      exact was
  · intro j J here
    obtain ⟨index,place,mark,_⟩ := destPos (width-1-j) (by omega)
    have eq := (List.getD_inj (show index<S.length by omega) (show k<S.length by omega) chart.nodup).mp
      (mark.trans here.symm)
    subst index
    have nop := right_empty_labels rr x other rs top ru rmatch (by
      intro t positive bounded
      obtain ⟨q,rnk,loc,mapped⟩ := upPos t bounded
      exact empty _ _ ⟨⟨q,by omega,loc⟩,mapped⟩)
    apply retained_at rr ro doneR nop (rdRead x dest width) j (by omega)
    · intro t T; exact right_image rr x dest width rc rkeep t (by omega)
    · intro t T
      obtain ⟨q,rnk,loc,mapped⟩ := destPos (width-1-t) (by omega)
      exact empty _ _ ⟨⟨q,by omega,loc⟩,mapped⟩

end L4.Height.FreshVisitedOperands
