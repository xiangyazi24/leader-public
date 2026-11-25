import Leader.L4.Height.ReleaseGrantReceipt
import Leader.L4.Height.StageSealPreserve
import Leader.L4.BStarStageWriterAuth
import Leader.L4.BStarStageIssue

namespace L4.Height.FreshStageAuthority
open AllSizeProtocol BStarTrace PhysicalCustody ProductionCustody ProductionCycles
open BStarLongWork BStarLongClaims BStarLongToken BStarLongCommand BStarLongDoor
open BStarLongLayout BStarLongPublication BStarLongLiteral BStarLongEvents BStarBankTrace
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireAnchors
open BStarResetChartTouch BStarGeneratedOwner BStarGeneratedBandScan BStarSteeredLikelihood
open BStarStageProvenance BStarStageDescriptorHistory BStarResetMarkAdapter

variable {s n : Nat} {x : Raw s n} {g : CustodyWitness x}
local notation "hp" => (show 0<2 by decide)
local notation "h" => oldH6 (rows s) g.base

/-- At every idle ISSUE408 on the released owner's actual word the
source descriptor decodes and names its captured center. -/
theorem idle_stage (P : Production g) (o : Owners h) (a : Word n) (rrel : Fin n)
    (paid : accepted g o a rrel) {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp g.base g.hh o S len fall) (w : Word n) :
    let z := rawNext s (rawRun x a) rrel
    let slot := fun j=>S.getD j fall
    let root := (slot 0).1
    let y := rawRun z w
    GeneratedOwner hp g.base slot len z .idle w .idle → pc y root=408 →
      ∃ d,BStarLongPublication.decode (sourceDescriptor.read (y root).long)=some d ∧
        d.old.val=((capturedSelector 1).read (y root).long).toNat ∧
        initial stageOp (y root).long=some (BStarStageIssue.argument (y root).long) := by
  dsimp only
  let z := rawNext s (rawRun x a) rrel
  let root := (S.getD 0 fall).1
  intro G currentPC
  have lower : pc z root<6 := by
    have E := congrArg Prod.fst C.root
    have start : pc z root=3 := by rw [show root=(endpoint h g.hh o 0).1 from E]; exact paid.2.2
    omega
  obtain ⟨_,_,_,_,d,_,_,_,dec,_,sel⟩ := BStarStageCaptureOrigin.idle_desc_from_capture hp C g.Q
    (g.closed _ rrel (ready_run P a).1) g.fiber g.closed (separation P) G lower currentPC
  let v : BitVec LW := (rawRun z w root).long
  have decoded' : BStarLongPublication.decode (sourceDescriptor.read v)=some d := dec
  refine ⟨d,dec,sel,?_⟩
  change initial stageOp v=some (BStarStageIssue.argument v)
  rw [BStarStageIssue.stage_initial,decoded']
  rfl

/-- A real healthy center STAGE offer determines its own writer authority
from the released history, then writes the exact literal latch on that mark.
The caller supplies the old offer and its decoded bytes. -/
theorem stage_writes_from_history (P : Production g) (o : Owners h) (a : Word n) (rrel : Fin n)
    (paid : accepted g o a rrel) {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp g.base g.hh o S len fall) (w : Word n) (m : Mode)
    (j : Nat) (J : j≤len) (i : Fin n) (pos : S.getD j fall=(i,1))
    (head : oldH6 (rows s) g.base i=true) (d : Descriptor) (p : Payload) :
    let z := rawNext s (rawRun x a) rrel
    let y := rawRun z w
    GeneratedOwner hp g.base (fun k=>S.getD k fall) len z .idle w m →
    (centerLink (oldPair (rows s) y i),BStarLongCommand.Offer.advance p)∈
      actualOffers (oldPair (rows s) y i) ((y i).long,(y (rightNeighbor i)).long) →
    p.fault=0 → p.opcode.toNat=stageOp →
    descOfStage p=some d →
    BStarLongOutgoing.actual (y i).long d=true ∧
      stage.read (rawNext s y i i).long=packOptional (some d) := by
  dsimp only
  let z := rawNext s (rawRun x a) rrel
  let y := rawRun z w
  let root := (S.getD 0 fall).1
  let geom := oldPair (rows s) y i
  let raw := ((y i).long,(y (rightNeighbor i)).long)
  let K := centerLink geom
  intro G offered healthy op decoded
  have q := g.closed _ rrel (ready_run P a).1
  have lower : pc z root<6 := by
    have eq := congrArg Prod.fst C.root
    have start : pc z root=3 := by rw [show root=(endpoint h g.hh o 0).1 from eq]; exact paid.2.2
    omega
  have length := C.length
  have mem : S.getD j fall∈S := by
    have J' : j<S.length := by omega
    rw [← @List.getElem_eq_getD _ S j J' fall]
    exact List.getElem_mem _
  have own := (C.entries _ mem).2
  rw [pos] at own
  have same : (beforeOutgoing geom raw K p).2=p := by
    unfold beforeOutgoing BStarLongArithmetic.visit
    split
    · rfl
    · rw [op,show BStarLongArithmetic.nodeOf stageOp=none by decide]
  have writer := BStarStageWriterAuth.stage_writer hp C g.Q q g.fiber g.closed (separation P)
    G (BStarGeneratedTapeCuts.at_end hp G) lower j J i K p pos i head own d offered
    (by change Stage (beforeOutgoing geom raw K p).2; rw [same]; exact ⟨healthy,op⟩)
    (by change descOfStage (beforeOutgoing geom raw K p).2=some d; rw [same]; exact decoded)
  have auth : BStarLongOutgoing.actual (y i).long d=true := by
    unfold BStarLongOutgoing.actual
    exact Bool.and_eq_true_iff.mpr ⟨writer.1,beq_iff_eq.mpr writer.2.symm⟩
  have YY := g.fiber _ (keep g _ w q) i
  have nowHead : oldH6 (rows s) y i=true := (congrArg Prod.fst YY).symm.trans head
  exact ⟨auth,StageLatchRing.stage_at_mark hp y i d p nowHead offered healthy op decoded auth⟩

end L4.Height.FreshStageAuthority
