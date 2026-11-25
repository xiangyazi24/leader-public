import Leader.L4.ControllerTapeIID
import Leader.L4.ResidualControllerIID
import Leader.L4.PhysicalEligibleReply
import Leader.L4.SeparatorReturnLinear

namespace L4.PhysicalReceiptCut
open BStarResetSchedule BStarSeparatingRail
open ControllerTapeIID (expected_of_prefix expected_after_prefix)
local notation "append" => ResetReturnIID.appendTape

/-- Forget the unused suffix of a stopped observer without forgetting
the exact scheduler history of its first successful cut. -/
theorem exact_prefix_expected {n : Nat}
    (A P : List (Fin n)→Prop) (K : Nat)
    (prefixCut : ∀ w,A w→∃ pre tail,w=pre++tail ∧ P pre)
    (H : Height.IIDExpectedHittingTimeAtMost append A [] K) :
    Height.IIDExpectedHittingTimeAtMost append P [] K := by
  have runTape (a b : List (Fin n)) : BStarResetSchedule.run append a b=a++b := by
    induction b generalizing a with
    | nil => simp [BStarResetSchedule.run]
    | cons e t ih =>
      simpa only [BStarResetSchedule.run,ResetReturnIID.appendTape,List.append_assoc,List.singleton_append] using ih (a++[e])
  apply expected_of_prefix append [] P A K _ H
  intro w W
  obtain ⟨pre,tail,E,T⟩ := prefixCut w W
  exact ⟨pre,tail,E,by simpa only [runTape,List.nil_append] using T⟩

theorem stopped_exact_receipt {X : Type} {n : Nat} {step : X→Fin n→X}
    {track : X→BStarResetSchedule.Track} {tag : Tag} {len : Nat} {Inv : X→Prop} {x : X} {c : Cursor} {K : Nat}
    (H : Height.IIDExpectedHittingTimeAtMost append (Stopped step track tag len Inv x c) [] K) :
    Height.IIDExpectedHittingTimeAtMost append
      (fun w=>Seen step track tag len x c w (.back 0) ∧
        Inv (BStarResetSchedule.run step x w) ∧ Clean track tag len (BStarResetSchedule.run step x w)) [] K := by
  apply exact_prefix_expected _ _ K _ H
  intro w W
  obtain ⟨pre,post,E,S,I,C⟩ := W
  exact ⟨pre,post,E,S,I,C⟩

open AllSizeProtocol BStarTrace BStarLongDoor BStarLongWork BStarLongClaims BStarClearanceSource
open PhysicalCustody BStarLongToken BStarSeparatorControl BStarAcquireWaitControl
local notation "hp" => (show 0<2 by decide)

def LaunchCut {s n : Nat} (x : Raw s n) (root : Fin n) (w : List (Fin n)) : Prop :=
  let d := RearTrace.predecessor root
  ∃ pre,w=pre++[d] ∧ let y:=rawRun x pre
    Launch (y root).long (rawNext s y d root).long

/-- The sticky launch bit bounds the first actual mark carrying a
certified transition. The cut's tape ends precisely at that mark. -/
theorem exact_launch_of_observer {s n : Nat} (x : Raw s n) (root : Fin n) (K : Nat)
    (H : Height.IIDExpectedHittingTimeAtMost (IssueLaunchIID.observe hp root)
      (fun q=>q.2=true) (x,false) K) :
    Height.IIDExpectedHittingTimeAtMost append (LaunchCut x root) [] K := by
  apply exact_prefix_expected _ _ K _ (ResidualControllerIID.launch_tape_of_observer hp x root K H)
  intro w W
  obtain ⟨pre,tail,E,L⟩ := W
  exact ⟨pre++[RearTrace.predecessor root],tail,
    by simpa only [List.append_assoc,List.singleton_append] using E,pre,rfl,L⟩

open PhysicalEligibleReply BStarResetHealthyService BStarH6WordChart
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarLongFixedRouting
open BStarResetChartTouch BStarResetChartService BStarFenceLineGeometry BStarH6Ordinal
open BStarClearanceOffset BStarResetMarkAdapter

theorem eligible_of_waiting_clean {s n : Nat} {base y : Raw s n}
    {addr : Nat→Pos n} {op len : Nat}
    (W : Waiting hp base (addr 0).1 op y)
    (C : Clean (project addr) (healthyTag op) len y) :
    Eligible base addr len op y :=
  ⟨W,C,C.1⟩

def SeparatorReceiptCut {s n : Nat} (base x : Raw s n)
    (Q : Raw s n→Prop) (addr : Nat→Pos n) (len : Nat) (w : List (Fin n)) : Prop :=
  let root := (addr 0).1
  let door := RearTrace.predecessor root
  ∃ pre tour,w=pre++door::tour ∧
    let old := rawRun x pre
    let seed := rawNext s old door
    let op := (ctrlOp.read (old root).long).toNat
    Launch (old root).long (seed root).long ∧
    Seen (rawNext s) (project addr) anyTag len seed (.out 0) tour (.back 0) ∧
    Q (rawRun x w) ∧ Waiting hp base root op (rawRun x w) ∧
    Clean (project addr) anyTag len (rawRun x w)

/-- Compose the real launch clock and arbitrary-opcode return clock.
The cut contains no post-receipt gap or consume mark. -/
theorem separator_receipt_after_observer {s n : Nat} {base x : Raw s n}
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
    (K : Nat)
    (observed : Height.IIDExpectedHittingTimeAtMost
      (IssueLaunchIID.observe hp (S.getD 0 fall).1) (fun z=>z.2=true) (x,false) K) :
    Height.IIDExpectedHittingTimeAtMost append
      (SeparatorReceiptCut base x Q (fun j=>S.getD j fall) len) [] (K+252*n*W) := by
  let addr := fun j=>S.getD j fall
  let root := (addr 0).1
  let door := RearTrace.predecessor root
  let A := LaunchCut x root
  let P := SeparatorReceiptCut base x Q addr len
  have Qrun (y : Raw s n) (u : List (Fin n)) (q : Q y) : Q (rawRun y u) := by
    induction u generalizing y with
    | nil => exact q
    | cons e t ih => exact ih _ (closed y q e)
  have Aclock := exact_launch_of_observer x root K observed
  apply Height.iid_stage_le append hn [] A P K (252*n*W)
    (expected_after_prefix _ _ [] _ (fun _ h=>.inl h) Aclock)
  intro tape found
  obtain ⟨pre,E,launched⟩ := found
  let old := rawRun x pre
  let seed := rawNext s old door
  have clocks := SeparatorReturnLinear.separator_after_launch_expected_linear hp chart sep Q
    (Qrun x pre I) layout closed LF RF dp seam flags notShort hn hl lc rc head cont cb cx W wW width launched
  rw [E]
  apply expected_after_prefix _ P (pre++[door]) _ _ (stopped_exact_receipt clocks)
  intro tour T
  obtain ⟨S0,⟨⟨Q0,_⟩,W0⟩,C0⟩ := T
  have split : (pre++[door])++tour=pre++door::tour := by simp [List.append_assoc]
  have playback : rawRun x ((pre++[door])++tour)=rawRun seed tour := by
    change BStarResetSchedule.run (rawNext s) x ((pre++[door])++tour)=_
    rw [split,BStarResetSchedule.run_append]
    rfl
  exact ⟨pre,tour,split,launched,S0,by rwa [playback],by rwa [playback],by rwa [playback]⟩

#print axioms eligible_of_waiting_clean
#print axioms separator_receipt_after_observer
#print axioms exact_prefix_expected
#print axioms stopped_exact_receipt
#print axioms exact_launch_of_observer
end L4.PhysicalReceiptCut
