import Leader.L4.BStarReceiptRecoveredTour
import Leader.L4.BStarPostCutAttempt
import Leader.L4.BStarPostCutCommitTour
import Leader.L4.BStarAttemptCuts
import Leader.L4.BStarCommitOwnerOrigin

namespace L4.BStarReceiptRecoveredAttempt
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarLongFiberOwner BStarLongFixedRouting BStarResetChartTouch
open BStarGeneratedOwner BStarGeneratedTapeCuts BStarCommitGeneratedTail
open BStarLongDoor BStarClearanceSource BStarLongCommand BStarOwnerLaunchOrigin
open BStarCustodyCuts BStarPostCutCommitTour BStarCommitTailScan
open BStarLongEvents BStarLongPublication BStarGrantWriterHistory
open BStarLongLayout BStarCommitIssue BStarCommitPayload

open BStarPostCutAttempt BStarOwnerRecoveryPass

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step
local notation "pc" => BStarGeneratedBandScan.pc


theorem actual_attempt {base x : X} (u v tail : List (Fin n))
    (facts : CutFacts hp base x u v) (hh : ∃ j,oldH6 B base j=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X → Prop) (I : Q x)
    (fiber : ∀ y,Q y → ∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y → Q (step y e))
    (mark i : Fin n) (pub : ¬NoPublication hp (run x ((u++v)++tail)) mark i) :
    ∃ (o : Owners (oldH6 B base)) (S : List (Pos n)) (len : Nat) (fall : Pos n)
      (pre reset lead flight : List (Fin n)) (door : Fin n) (k : Nat)
      (desc : Descriptor) (bank : Fin 3),
      (u++v)++tail=(pre++reset)++lead++door::flight ∧
      Recovered hp base hh o (run x pre) reset ∧
      u.length≤pre.length ∧ 0<reset.length ∧ (pre++reset).length≤(u++v).length ∧
      commandOwner (oldH6 B base) i 1=o.val ∧
      Chart hp base hh o S len fall ∧ k≤len ∧ S.getD k fall=(i,1) ∧
      let addr := fun j => S.getD j fall
      let origin := run x (pre++reset)
      let issue := run origin lead
      let bytes := (issue (addr 0).1).long
      door=RearTrace.predecessor (addr 0).1 ∧
      Launch bytes (step issue door (addr 0).1).long ∧
      (ctrlOp.read bytes).toNat=commitOp ∧
      decode (sourceDescriptor.read bytes)=some desc ∧ Allows bytes desc=true ∧
      (choice.read bytes).toNat=bank.val ∧
      GeneratedOwner hp base addr len origin .idle lead .idle ∧
      AttemptPrefix hp base origin addr len lead ∧
      BusyOnly hp base addr len commitOp (step issue door) (.out 0) flight (.out k) ∧
      BeforePublication hp (step issue door) i flight ∧
      (∃ K payload,
        let y := run x ((u++v)++tail)
        let g := oldPair B y mark
        let raw : Pair (BitVec LW) := ((y mark).long,(y (rightNeighbor mark)).long)
        (K,.advance payload)∈actualOffers g raw ∧
        LiteralCommit (geometry g K.source.side) K.source (BStarLongWork.atOld raw K.source) payload bank ∧
        decode (descriptorBits payload)=some desc) := by
  classical
  obtain ⟨hh0,o,pre,reset,rest,S,len,fall,k,W,Rcredit,A,B0,C0,own,C,kl,idx,pc3,initial,G,_,_⟩ :=
    BStarReceiptRecoveredTour.actual_tour hp u v tail facts hh sep Q I fiber closed mark i pub
  let origin := run x (pre++reset)
  have old : run origin rest=run x ((u++v)++tail) :=
    (BStarResetSchedule.run_append step x (pre++reset) rest).symm.trans
      (congrArg (run x) (by simpa only [List.append_assoc] using W.symm))
  obtain ⟨s,K,q,bank,loc,side,selected,literal⟩ := stopping_commit hp _ mark i pub
  let y := run x ((u++v)++tail)
  let g := oldPair B y mark
  let raw : Pair (BitVec LW) := ((y mark).long,(y (rightNeighbor mark)).long)
  let ev : Publication := ⟨s,bank⟩
  have hw : BStarLongWork.atOld raw K.source=(y i).long := by
    change lane (K.source.side==.right) raw=(y i).long
    rw [side,loc]
    cases s <;> rfl
  have li : LiteralCommit (geometry g K.source.side) K.source (BStarLongWork.atOld raw K.source) q bank := by
    rw [side,hw]
    exact literal
  have evMem : ev∈(longTrace g raw).publications :=
    (literal_event_iff g raw ev).mpr ⟨K,q,selected,side.symm,li⟩
  have L : s=.left := literal_endpoint_left g raw ev evMem
  have im : i=mark := by rw [loc,L]; rfl
  have idxMark : S.getD k fall=(mark,1) := im ▸ idx
  have evMem' : ev∈(longTrace (oldPair B (run origin rest) mark)
      (((run origin rest) mark).long,((run origin rest) (rightNeighbor mark)).long)).publications := by
    rw [old]; exact evMem
  obtain ⟨_,lead,flight,door,desc,R,doorLoc,launch,PC,Desc,allow,bankEq,busy,before,offer⟩ :=
    BStarCommitOwnerOrigin.publication_from_generated hp C sep G (at_end hp G) k kl mark idxMark ev evMem'
  obtain ⟨mode,Ge,_⟩ := split hp lead (door::flight) (R ▸ G)
  have modeEq : mode=.idle := idle_of_issue hp (at_end hp Ge) launch.1
  subst mode
  have keep (z : X) (w : List (Fin n)) (J : Q z) : Q (run z w) := by
    induction w generalizing z with
    | nil => exact J
    | cons e w ih => exact ih _ (closed z e J)
  have attempt : AttemptPrefix hp base origin (fun j => S.getD j fall) len lead :=
    BStarAttemptCuts.attempt_cuts hp C Q (keep x (pre++reset) I) fiber closed sep Ge
      (by change pc origin (S.getD 0 fall).1<6; rw [show pc origin (S.getD 0 fall).1=3 from pc3]; decide) PC
  refine ⟨o,S,len,fall,pre,reset,lead,flight,door,k,desc,bank,?_,Rcredit,A,B0,C0,own,C,kl,idx,
    doorLoc,launch,PC,Desc,allow,bankEq,Ge,attempt,busy,im.symm ▸ before,?_⟩
  · rw [W,R]; simp only [List.append_assoc]
  · have stateEq : run (run x (pre++reset)) rest=run x ((u++v)++tail) := old
    obtain ⟨K,p,S0,L0,D0⟩ := offer
    refine ⟨K,p,?_,?_,?_⟩
    · exact stateEq ▸ S0
    · exact stateEq ▸ L0
    · exact D0
end L4.BStarReceiptRecoveredAttempt
