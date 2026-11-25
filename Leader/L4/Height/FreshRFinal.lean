import Leader.L4.Height.FreshDrainedAttempt
import Leader.L4.Height.FreshSealGeometry
import Leader.L4.Height.NoNeedTailService
import Leader.L4.Height.FreshBlockHandoff
import Leader.L4.Height.ProductionService

namespace L4.Height.ProductionCycles
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
open AllSizeProtocol PhysicalCustody ProductionCustody BStarTrace BStarSteeredLikelihood
open BStarH6WordChart BStarAcquireAnchors BStarAcquireLiteralChain BStarResetChartTouch
open BStarGeneratedOwner BStarAcquireVisitOrder BStarSeparatingRail BStarLongPublication
open BStarLongToken BStarLongLayout BStarLongLiteral BStarLongWork BStarLongClaims
open BStarLongCommand BStarLongDoor BStarLongEvents BStarSealHealthyHop
open FreshFirstAcquire BStarGrantWriterHistory BStarClearanceOffset Classical

variable {s n : Nat} {x : Raw s n} (g : CustodyWitness x)
local notation "h" => oldH6 (rows s) g.base
local notation "hp" => (show 0<2 by decide)

private theorem raw_join (x : Raw s n) (a b : Word n) :
    rawRun x (a++b)=rawRun (rawRun x a) b :=
  BStarResetSchedule.run_append (rawNext s) x a b

/-- The last physical cut, on the original stopped tape. All offset and
grant-coherence facts at the cut will be rebuilt from custody. -/
def StageCompletion (i : Header h) : Prop :=
  ∀ {S : List (Pos n)} {len : Nat} {fall : Pos n},
  ∀ (C : Chart hp g.base g.hh (ProductionClients.serviceOwner g i) S len fall),
  ∀ (k : Nat), k<len → S.getD k fall=(i.val,1) →
  ∀ (a : Word n) (r : Fin n), accepted g (ProductionClients.serviceOwner g i) a r →
  ∀ (pre post : Word n),
  let base := rawNext s (rawRun x a) r
  GeneratedOwner hp g.base (fun j => S.getD j fall) len base .idle pre .idle →
  PC (rawRun base pre) (S.getD 0 fall).1=408 →
  PC (rawRun base (pre++post)) (S.getD 0 fall).1=2 →
  ∃ u v, post=u++i.val::v ∧
    GeneratedOwner hp g.base (fun j => S.getD j fall) len base .idle (pre++u) (.busy sealOp (.out k)) ∧
    ∃ (pay : Payload) (d : Descriptor), Well pay ∧
    let old := rawRun base (pre++u)
    BStarLongPublication.decode (sourceDescriptor.read (old (S.getD 0 fall).1).long)=some d ∧
    BStarLongPublication.decode (BitVec.ofNat 7 (pay.argument.toNat/2))=some d ∧
    BStarLongOutgoing.actual (old i.val).long d=true ∧
    readOptional (BStarLongLayout.stage.read (old i.val).long)=some d ∧
    (centerLink (oldPair (rows s) old i.val),.advance pay)∈
      actualOffers (oldPair (rows s) old i.val) ((old i.val).long,(old (rightNeighbor i.val)).long)

theorem fresh_of_stage_completion
    (finish : ∀ {s n : Nat} {x : Raw s n} (g : CustodyWitness x),
      Production g → ∀ i : Header (oldH6 (rows s) g.base), StageCompletion g i) :
    FreshCyclePublishes := by
  intro s n x g P i y _ cuts z actual gap e suffix last
  apply Classical.byContradiction
  intro miss
  let target := ProductionClients.serviceOwner g i
  obtain ⟨S,len,fall,C,pre,post,split,hist,pc⟩ :=
    FreshDrainedAttempt.stage_on_stopped_history P i y.emitted gap z actual cuts e last suffix miss
  obtain ⟨i₀,bSite,k,j,head₀,own₀,_,kL,idx₀,j0,jL,jdx,ord⟩ :=
    FreshSealGeometry.center_and_bit g P C
  have center : i₀=i.val := by
    have U := (endpoint_spec (oldH6 (rows s) g.base) g.hh target 1).2.2 i₀ head₀ own₀
    exact (congrArg Prod.fst U).trans (ProductionClients.service_header g i)
  subst i₀
  obtain ⟨a,r,T,A⟩ := FreshConflicts.target_release g target cuts
  let base := rawNext s (rawRun x a) r
  have baseEq : rawRun x y.emitted=base := by
    rw [T,raw_join]; rfl
  have start : PC (rawRun base pre) (S.getD 0 fall).1=408 := by
    rw [←baseEq,←raw_join]; exact pc
  have rootID : (S.getD 0 fall).1=(endpoint (oldH6 (rows s) g.base) g.hh target 0).1 := congrArg Prod.fst C.root
  have stop : PC (rawRun base (pre++post)) (S.getD 0 fall).1=2 := by
    rw [←baseEq,←raw_join,←split,rootID]; exact last.2.1
  have hist' : GeneratedOwner hp g.base (fun j => S.getD j fall) len base .idle pre .idle := by
    rw [←baseEq]; exact hist
  obtain ⟨u,v,postEq,history,pay,d,well,source,darg,writer,staged,offer⟩ :=
    finish g P i C k kL idx₀ a r A pre post hist' start stop
  let lead := pre++u
  let old := rawRun base lead
  have oldEq : rawRun x (y.emitted++lead)=old := by rw [raw_join,baseEq]
  have q := ready_run P (y.emitted++lead)
  rw [oldEq] at q
  have tapeSplit : z.emitted=(y.emitted++lead)++i.val::(v++[e]) := by
    simp only [suffix,split,postEq,lead,List.append_assoc,List.cons_append]
  have noPub (p t : Word n) (E : v=p++i.val::t) :
      NoPublication hp (rawRun (rawNext s old i.val) p) i.val i.val := by
    apply Classical.byContradiction
    intro N
    apply miss
    apply actual.2.2.mpr
    refine ⟨(y.emitted++lead)++i.val::p,t++[e],?_,?_⟩
    · simp only [tapeSplit,E,List.append_assoc,List.cons_append]
    · have eq : rawRun x ((y.emitted++lead)++i.val::p)=rawRun (rawNext s old i.val) p := by
        rw [raw_join,oldEq]; rfl
      exact eq.symm ▸ N
  have stop' : PC (rawRun (rawNext s old i.val) v) (S.getD 0 fall).1=2 := by
    have eq : pre++post=lead++i.val::v := by rw [postEq,List.append_assoc]
    rw [eq,raw_join] at stop
    exact stop
  cases need : d.need with
  | true =>
    have safe := FreshNeedPrefixBand.accepted_need_seal_on_miss hp C g.Q g.fiber
      (fun y q e => g.closed y e q) (separation P) i.val k kL idx₀ head₀ own₀ bSite j
      ⟨j0,jL⟩ jdx ord lead history pay well d need ⟨q.1,q.2,g.coherent _ q.1 i.val,source,darg,writer,staged,offer⟩ g.heads g.cont v noPub
    exact safe v ⟨[],List.append_nil _⟩ stop'
  | false =>
    have safe := NoNeedTailService.accepted_no_need_seal_on_miss hp C g.Q g.fiber
      (fun y q e => g.closed y e q) (separation P) i.val k kL idx₀ head₀ own₀ j
      ⟨j0,jL⟩ lead history pay well d need ⟨q.1,q.2,g.coherent _ q.1 i.val,source,darg,writer,staged,offer⟩ g.heads g.cont v noPub
    exact safe v ⟨[],List.append_nil _⟩ stop'

#print axioms fresh_of_stage_completion
end L4.Height.ProductionCycles
