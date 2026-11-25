import Leader.L4.PhysicalReceiptCut
import Leader.L4.PhysicalRaceCutAdapters
import Leader.L4.ScoredTapeCertificates
import Leader.L4.PhysicalRawClockTape

namespace L4.PhysicalSeparatorRace
open AllSizeProtocol BStarTrace PhysicalCustody BStarLongWork BStarLongClaims
open BStarH6WordChart BStarAcquireLiteralChain BStarLongFixedRouting BStarFenceLineGeometry BStarH6Ordinal
open BStarLongDoor BStarSeparatingRail BStarClearanceResidual BStarClearanceOffset
open BStarAcquireVisitOrder BStarResetChartTouch BStarResetChartService BStarAcquireAnchors
open BStarResetSchedule BStarResetMarkAdapter BStarResetHealthyService BStarAcquireRailCoverage
open PhysicalEligibleReply PhysicalReceiptCut PhysicalRaceExactCut PhysicalRaceCutAdapters
open ScoredTapeSerial ScoredTapeCertificates
local notation "hp" => (show 0<2 by decide)

def Zero {s n : Nat} (base : Raw s n) (hh : ∃ i,oldH6 (rows s) base i=true)
    (Q : Raw s n→Prop) (addr : Nat→Pos n) (len : Nat) (y : Raw s n) : Prop :=
  Boundary Q (oldH6 (rows s) base) hh addr len y ∧ (ctrlOp.read (y (addr 0).1).long).toNat=0

def SeparatorPaid {s n : Nat} (base x : Raw s n) (hh : ∃ i,oldH6 (rows s) base i=true)
    (Q : Raw s n→Prop) (addr : Nat→Pos n) (len : Nat) (w : Word n) : Prop :=
  let d := RearTrace.predecessor (addr 0).1
  ∃ receive gap, w=receive++(gap++[d]) ∧
    SeparatorReceiptCut base x Q addr len receive ∧ (∀ e∈gap,DisjointMarks e d) ∧
    Boundary Q (oldH6 (rows s) base) hh addr len (rawRun x w)

private theorem rawApp {s n : Nat} (x : Raw s n) (a b : Word n) :
    rawRun x (a++b)=rawRun (rawRun x a) b := BStarResetSchedule.run_append _ _ _ _

private theorem qRun {s n : Nat} (Q : Raw s n→Prop)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (w : Word n) (y : Raw s n) :
    Q y→Q (rawRun y w) := by
  induction w generalizing y with
  | nil => exact id
  | cons e w ih => intro I; exact ih _ (closed _ e I)

theorem separator_paid_of_race {s n : Nat} {base x : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : Raw s n→Prop) (layout : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (cx : ∀ y,Q y→correct (oldH6 (rows s) base) hh 5 y) (w : Word n) :
    let addr := fun j=>S.getD j fall
    let d := RearTrace.predecessor (addr 0).1
    RaceOutcome (SeparatorReceiptCut base x Q addr len) d 1 w →
      SeparatorPaid base x hh Q addr len w := by
  dsimp only
  intro H
  let addr := fun j=>S.getD j fall
  let d := RearTrace.predecessor (addr 0).1
  obtain ⟨receive,raced,W,h,R⟩ := H
  have h0 := h
  obtain ⟨_,_,_,_,_,qy,wait,clean⟩ := h
  obtain ⟨g,tail,E,D,_,_,pc,range,_,ReadyEnd⟩ :=
    accepted_separator_cut C Q layout closed sep qy wait clean raced R.1
  have noTail := single_tail_nil R E D
  subst tail
  have Eq : w=receive++(g++[d]) := by rw [W,E]
  have qe := qRun Q closed (g++[d]) (rawRun x receive) qy
  have lt : pc<413 := range.elim (fun eq=>eq.symm ▸ (by decide : (0 : Nat)<413)) And.right
  refine ⟨receive,g,Eq,h0,D,?_⟩
  rw [Eq,rawApp]
  exact ⟨qe,cx _ qe,legal_issue _ ReadyEnd.2.1 (ReadyEnd.2.2.symm ▸ lt),ReadyEnd.1⟩

/-- Scored physical separator: wait for the actual clean receipt,
then charge exactly one incident win, not an ordinary consume. -/
noncomputable def separator_reader {s n : Nat} {base x : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (hn : 4≤n)
    (Q : Raw s n→Prop) (layout : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (cx : ∀ y,Q y→correct (oldH6 (rows s) base) hh 5 y) (K : Nat)
    (H : Height.IIDExpectedHittingTimeAtMost ResetReturnIID.appendTape
      (SeparatorReceiptCut base x Q (fun j=>S.getD j fall) len) [] K) :
    Certificate n 1 3 (K+n) (SeparatorPaid base x hh Q (fun j=>S.getD j fall) len) := by
  simpa only [Nat.mul_one, StoppedDoorRaceIID.score, AdaptiveDoorCredit.score, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow] using (race hn _ (RearTrace.predecessor (S.getD 0 fall).1) 5 1 (by decide) (by decide) K H).map
    (separator_paid_of_race C Q layout closed sep cx)

#print axioms separator_paid_of_race
#print axioms separator_reader
/-- From arbitrary old upper bytes on the settled chart, use the genuine
launch from the released controller. Its legal opcode need not be zero;
the separator only needs an authenticated outward and return traversal. -/
noncomputable def separator_from_arbitrary_reader {s n : Nat} {base x : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : Raw s n→Prop) (I : Q x)
    (layout : ∀ q,Q q→∀ i,Layout (rows s) base i=Layout (rows s) q i)
    (closed : ∀ q,Q q→∀ e,Q (rawNext s q e))
    {l d w : Nat} (LF : BStarCopyLeftStrip.Strip (rows s) base (S.getD 0 fall).1 l w)
    (RF : RightFrame (rows s) base (S.getD len fall).1 d w) (dp : 0<d)
    (seam : BStarCopyRightStrip.addr (S.getD 0 fall).1 l=(S.getD len fall).1)
    (flags : ∀ i,(longGeometry (rows s) (base i)).inside=decide (oldOrdinal (rows s) base hh i<w) ∧
      (longGeometry (rows s) (base i)).last=decide (oldOrdinal (rows s) base hh i+1=w))
    (notShort : ∀ i,oldH6 (rows s) base (rightNeighbor i)=true → w≤oldOrdinal (rows s) base hh i+1)
    (hn : 0<n) (hl : 0<l+w) (lc : l+w≤n) (rc : d+w≤n)
    (head : ∀ i,let g:=longGeometry (rows s) (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i,let g:=oldPair (rows s) base i; BStarAcquireRailCoverage.continuation g.1 g.2=true)
    (cb : correct (oldH6 (rows s) base) hh 5 base) (cx : ∀ q,Q q→correct (oldH6 (rows s) base) hh 5 q)
    (W : Nat) (wW : w≤W)
    (width : ∀ i,oldH6 (rows s) base (rightNeighbor i)=true → oldOrdinal (rows s) base hh i+1≤W)
    (four : 4≤n) :
    Certificate n 1 3 (((252*n*W+3*n)+252*n*W)+n)
      (SeparatorPaid base x hh Q (fun j=>S.getD j fall) len) := by
  have A := DirtyOwnerRelease.genuine_launch_expected_linear hp chart sep Q I layout closed
    LF RF dp seam flags notShort hn hl lc rc head cont cb cx W wW width
  have H := separator_receipt_after_observer chart sep Q I layout closed LF RF dp seam flags
    notShort hn hl lc rc head cont cb cx W wW width _ A
  exact separator_reader chart four Q layout (fun q e U=>closed q U e) sep cx _ H

/-- Ordinary residual navigation earns no race credit and may stop
immediately if the actual consume already scheduled zero. -/
def residual_to_zero_reader {s n : Nat} {base x : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : Raw s n→Prop)
    (layout : ∀ q,Q q→∀ i,Layout (rows s) base i=Layout (rows s) q i)
    (closed : ∀ q,Q q→∀ e,Q (rawNext s q e))
    {l d w : Nat} (LF : BStarCopyLeftStrip.Strip (rows s) base (S.getD 0 fall).1 l w)
    (RF : RightFrame (rows s) base (S.getD len fall).1 d w) (dp : 0<d)
    (seam : BStarCopyRightStrip.addr (S.getD 0 fall).1 l=(S.getD len fall).1)
    (flags : ∀ i,(longGeometry (rows s) (base i)).inside=decide (oldOrdinal (rows s) base hh i<w) ∧
      (longGeometry (rows s) (base i)).last=decide (oldOrdinal (rows s) base hh i+1=w))
    (notShort : ∀ i,oldH6 (rows s) base (rightNeighbor i)=true → w≤oldOrdinal (rows s) base hh i+1)
    (hn : 0<n) (hl : 0<l+w) (lc : l+w≤n) (rc : d+w≤n)
    (head : ∀ i,let g:=longGeometry (rows s) (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i,let g:=oldPair (rows s) base i; BStarAcquireRailCoverage.continuation g.1 g.2=true)
    (cb : correct (oldH6 (rows s) base) hh 5 base) (cx : ∀ q,Q q→correct (oldH6 (rows s) base) hh 5 q)
    (W : Nat) (wW : w≤W)
    (width : ∀ i,oldH6 (rows s) base (rightNeighbor i)=true → oldOrdinal (rows s) base hh i+1≤W)
    (I : Boundary Q (oldH6 (rows s) base) hh (fun j=>S.getD j fall) len x) :
    Certificate n 3 3 (412*(n+(252*n*W+n)))
      (fun w=>Zero base hh Q (fun j=>S.getD j fall) len (rawRun x w)) := by
  have R := ResidualControllerIID.to_issue_zero_expected_linear hp chart sep Q layout closed
    LF RF dp seam flags notShort hn hl lc rc head cont cb cx W wW width I
  exact Certificate.idle _ 3 _ (by decide)
    (PhysicalRawClockTape.raw_endpoint_expected (rawNext s) x _ _ R)

#print axioms separator_from_arbitrary_reader
#print axioms residual_to_zero_reader
end L4.PhysicalSeparatorRace
