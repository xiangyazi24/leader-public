import Leader.L4.Height.StageScopedFlight
import Leader.L4.Height.FreshStageAuthority

namespace L4.Height.StageAuthorityScoped
open AllSizeProtocol BStarTrace PhysicalCustody ProductionCustody ProductionCycles
open BStarLongWork BStarLongClaims BStarLongToken BStarLongCommand BStarLongDoor
open BStarLongLayout BStarLongPublication BStarLongLiteral BStarLongEvents BStarBankTrace
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetChartTouch BStarGeneratedOwner BStarSteeredLikelihood BStarOwnerLaunchOrigin
open BStarStageDescriptorHistory BStarResetMarkAdapter BStarStageCandidateJoined

variable {s n : Nat} {x : Raw s n} {g : CustodyWitness x}
local notation "hp" => (show 0<2 by decide)
local notation "h" => oldH6 (rows s) g.base

/-- Production center authorization on the reached STAGE flight, from
the genuine earlier owner RREL and actual issued-word ancestry. -/
theorem prefixAuth_of_release (P : Production g) (o : Owners h) (a : Word n) (rrel : Fin n)
    (paid : accepted g o a rrel) {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp g.base g.hh o S len fall) (lead w : Word n) (source : BitVec LW) (d : Descriptor)
    (D : BStarLongPublication.decode (sourceDescriptor.read source)=some d)
    (G : let z := rawNext s (rawRun x a) rrel
      GeneratedOwner hp g.base (fun j=>S.getD j fall) len z .idle lead (.busy stageOp (.out 0))) :
    let z := rawNext s (rawRun x a) rrel
    StageScopedReplay.PrefixAuth hp g.base (rawRun z lead) (fun j=>S.getD j fall) len 0 source d w := by
  dsimp only at G ⊢
  intro u e v _ k T K addr
  dsimp only
  intro sel hh one
  let z := rawNext s (rawRun x a) rrel
  let y := rawRun (rawRun z lead) u
  let geom := oldPair (rows s) y e
  have mem : K∈orderedCommands geom := by
    rw [←actualOffers_claims geom ((y e).long,(y (rightNeighbor e)).long)]
    exact List.mem_map.mpr ⟨_,sel,rfl⟩
  have same : K=centerLink geom := by
    have H : K∈(orderedCommands geom).filter centerClaim :=
      List.mem_filter.mpr ⟨mem,by simp [centerClaim,one]⟩
    rw [one_center_claim] at H
    exact List.mem_singleton.mp H
  subst K
  have Y : rawRun z (lead++u)=y := BStarResetSchedule.run_append (rawNext s) z lead u
  have split (zz : Raw s n) (left right : Word n) (m₁ m₂ m₃ : Mode)
      (A : GeneratedOwner hp g.base (fun j=>S.getD j fall) len zz m₁ left m₂)
      (B : GeneratedOwner hp g.base (fun j=>S.getD j fall) len (rawRun zz left) m₂ right m₃) :
      GeneratedOwner hp g.base (fun j=>S.getD j fall) len zz m₁ (left++right) m₃ := by
    induction A with
    | endpoint _ => exact B
    | next I E _ ih => exact .next I E (ih B)
  have toGen {q : Raw s n} {word : Word n} {j j' : BStarSeparatingRail.Cursor}
      (T' : BusyOnly hp g.base (fun j=>S.getD j fall) len stageOp q j word j') :
      GeneratedOwner hp g.base (fun j=>S.getD j fall) len q (.busy stageOp j) word (.busy stageOp j') := by
    induction T' with
    | nil I => exact .endpoint I
    | cons I E _ ih => exact .next I E ih
  have history := split z lead u _ _ _ G (toGen T)
  have now := BStarAcquireHistoryReturn.busy_end hp T
  have bound : k≤len := now.2.1.1
  have oldHead : oldH6 (rows s) g.base e=true := by
    have H : oldH6 (rows s) y e=true := hh
    exact (congrArg Prod.fst (now.1.1 e)).trans H
  have idx : S.getD k fall=(e,1) := addr
  have decoded := (BStarStageIssue.issued_descriptor source).trans D
  have A := FreshStageAuthority.stage_writes_from_history P o a rrel paid C (lead++u)
    (.busy stageOp (.out k)) k bound e idx oldHead d (BStarStageIssue.payload source)
    history (by rw [Y]; exact sel) rfl rfl decoded
  rw [Y] at A
  exact A.1

end L4.Height.StageAuthorityScoped
