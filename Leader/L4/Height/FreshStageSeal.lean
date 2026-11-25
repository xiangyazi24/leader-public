import Leader.L4.Height.StageSealOldFacts
import Leader.L4.Height.StageFirstIssue
import Leader.L4.Height.StageScopedLaunch
import Leader.L4.Height.StageAuthorityScoped

namespace L4.Height.FreshStageSeal
open AllSizeProtocol BStarTrace PhysicalCustody ProductionCustody ProductionCycles
open BStarLongWork BStarLongClaims BStarLongToken BStarLongCommand BStarLongDoor
open BStarLongLayout BStarLongPublication BStarLongLiteral BStarLongEvents BStarBankTrace
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetChartTouch BStarGeneratedOwner BStarSteeredLikelihood BStarOwnerLaunchOrigin
open BStarStageDescriptorHistory BStarResetMarkAdapter BStarStageCandidateJoined
open BStarAcquireAnchors BStarGeneratedBandScan BStarClearanceSource BStarLongGrant
open BStarGrantReaderHistory BStarSealHealthyHop BStarAcquireHistoryReturn

variable {s n : Nat} {x : Raw s n} {g : CustodyWitness x}
local notation "hp" => (show 0<2 by decide)
local notation "h" => oldH6 (rows s) g.base

private theorem decoded_valid (bits : BitVec 7) (d : Descriptor) (D : BStarLongPublication.decode bits=some d) :
    d.valid=true := by
  unfold BStarLongPublication.decode at D
  dsimp only at D
  split at D <;> try contradiction
  split at D <;> try contradiction
  split at D <;> try contradiction
  split at D <;> try contradiction
  have V := Option.some.inj D
  rw [←V]
  assumption

/-- An actual idle ISSUE408 on the released owner's original word,
continued to PC2, forces the exact accepted healthy SEAL center mark.
All latch, writer and matching source/packet descriptor fields are from
the same physical replay. No eventual successful COMMIT is assumed. -/
theorem accepted_seal_facts (P : Production g) (o : Owners h) (a : Word n) (rrel : Fin n)
    (paid : accepted g o a rrel) {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp g.base g.hh o S len fall)
    (i : Fin n) (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1))
    (head : oldH6 (rows s) g.base i=true) (own : commandOwner h i 1=o.val)
    (lead w : Word n) (m : Mode) :
    let z := rawNext s (rawRun x a) rrel
    let slot := fun j=>S.getD j fall
    let root := (slot 0).1
    let y := rawRun z lead
    GeneratedOwner hp g.base slot len z .idle lead .idle →
    pc y root=408 →
    GeneratedOwner hp g.base slot len y .idle w m →
    pc (rawRun y w) root=2 →
    ∃ before tail pay d,
      w=before++i::tail ∧
      GeneratedOwner hp g.base slot len z .idle (lead++before) (.busy sealOp (.out k)) ∧
      let old := rawRun y before
      Well pay ∧ g.Q old ∧ conflict (ports old i)=false ∧
      BStarLongPublication.decode (sourceDescriptor.read (old root).long)=some d ∧
      BStarLongPublication.decode (BitVec.ofNat 7 (pay.argument.toNat/2))=some d ∧
      BStarLongOutgoing.actual (old i).long d=true ∧ readOptional (stage.read (old i).long)=some d ∧
      (centerLink (oldPair (rows s) old i),.advance pay)∈actualOffers (oldPair (rows s) old i)
        ((old i).long,(old (rightNeighbor i)).long) := by
  dsimp only
  let z := rawNext s (rawRun x a) rrel
  let slot := fun j=>S.getD j fall
  let root := (slot 0).1
  let y := rawRun z lead
  intro prior pcStage T later
  let sep := separation P
  let cl := fun x q e=>g.closed x e q
  have qz := g.closed _ rrel (ready_run P a).1
  have qy := keep g z lead qz
  have early : pc z root<6 := by
    have rt : root=(endpoint h g.hh o 0).1 := congrArg Prod.fst C.root
    have actual : pc z root=3 := rt ▸ paid.2.2
    omega
  obtain ⟨d,D,_,_⟩ := FreshStageAuthority.idle_stage P o a rrel paid C lead prior pcStage
  obtain ⟨idle,door,rest,W,foreign,PC,U,Door,_Launch,after⟩ :=
    StageFirstIssue.first_stage_launch hp C g.Q g.fiber cl sep T qy d pcStage D later
  let atDoor := rawRun y idle
  let v := rawNext s atDoor door
  let source := (atDoor root).long
  have qdoor := keep g y idle qy
  have Local : GeneratedOwner hp g.base slot len y .idle idle .idle := by
    obtain ⟨md,J,_⟩ := BStarGeneratedTapeCuts.split hp idle (door::rest) (W ▸ T)
    have I := BStarGeneratedTapeCuts.idle_foreign_prefix hp J (by
      intro e mem eq
      exact foreign e mem ((RearTrace.predecessor_right e).symm.trans (congrArg RearTrace.predecessor eq)))
      idle [] (List.append_nil idle).symm
    have same := L4.Height.current_mode_unique hp _ _ (BStarGeneratedTapeCuts.at_end hp J) I
    exact same ▸ J
  obtain ⟨E,I,Wire,Src⟩ :=
    StageScopedLaunch.actual_launch_at_door hp C g.Q g.fiber cl sep qdoor
      (BStarGeneratedTapeCuts.at_end hp Local) d door Door PC U
  have A := StageSealExactFrame.generated_append hp prior Local
  let launched := lead++idle++[door]
  have atCut : rawRun z (lead++idle)=atDoor := BStarResetSchedule.run_append _ _ _ _
  have one : GeneratedOwner hp g.base slot len atDoor .idle [door] (.busy stageOp (.out 0)) :=
    .next (BStarGeneratedTapeCuts.at_end hp Local) E (.endpoint I)
  have G : GeneratedOwner hp g.base slot len z .idle launched (.busy stageOp (.out 0)) :=
    StageSealExactFrame.generated_append hp A (atCut.symm ▸ one)
  have landed : rawRun z launched=v := by
    calc
      _ = rawRun (rawRun z (lead++idle)) [door] := BStarResetSchedule.run_append _ _ _ _
      _ = rawRun atDoor [door] := congrArg (fun y => rawRun y [door]) atCut
      _ = _ := rfl
  have Auth := StageAuthorityScoped.prefixAuth_of_release P o a rrel paid C launched rest source d U G
  change StageScopedReplay.PrefixAuth hp g.base (rawRun z launched) slot len 0 source d rest at Auth
  rw [landed] at Auth
  have laterV : pc (rawRun v rest) root=2 := by
    rw [W] at later
    have E : rawRun y (idle++door::rest)=rawRun v rest := BStarResetSchedule.run_append _ _ _ _
    change pc (rawRun y (idle++door::rest)) root=2 at later
    rw [E] at later
    exact later
  obtain ⟨pre,tail,pay,F,H,old⟩ := StageSealOldFacts.accepted_seal_facts hp C g.Q g.fiber cl sep
    i own k K idx head launched landed G source d (decoded_valid _ _ U) U Src after
    (g.closed _ door qdoor) Wire Auth qz early laterV
  let before := idle++door::pre
  have replay : rawRun y before=rawRun v pre := BStarResetSchedule.run_append _ _ _ _
  refine ⟨before,tail,pay,d,?_,?_,?_⟩
  · simp only [W,F,before,List.append_assoc,List.cons_append]
  · simpa only [launched,before,List.append_assoc,List.singleton_append] using H
  · rw [replay]
    exact old

end L4.Height.FreshStageSeal
