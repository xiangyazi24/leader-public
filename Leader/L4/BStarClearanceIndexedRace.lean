import Leader.L4.BStarClearanceIndexedWait
import Leader.L4.BStarClearanceRaceOwner

namespace L4.BStarClearanceIndexedRace
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarAcquireLiteralChain BStarAcquireVisitOrder BStarH6WordChart BStarLongFiberOwner
open BStarResetChartTouch BStarClearanceIndexedSum BStarClearanceCommandSum
open BStarLongFixedRouting BStarClearanceOffset BStarResetMarkAdapter
open BStarLongTransport BStarLongRouting BStarLongCommand BStarLongEvents
open BStarClearanceIndexedWait BStarClearanceRaceMark BStarClearanceRaceOwner

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => BStarClearanceOffset.X k₁ k₂ t₂ J₁ J₂ r c p c₁ n

/-- On the one nominated real incidence a live race either encounters
the caller's exact pre-service boundary or pays strict descent in
the same fixed owner F sum as an ordinary command advance. -/
theorem nominate {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (chart : Chart hp base hh o S len fallback)
    (same : ∀ i, Layout B base i=Layout B x i)
    (cb : correct (oldH6 B base) hh 5 base) (cx : correct (oldH6 B base) hh 5 x)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (j : Fin 11) (u : Payload) (member : (i,j)∈S)
    (old : BStarLongCommand.bind (longGeometry B (x i)) j (atSite (x i).long j)=.forward u)
    (fault : u.fault=0)
    (gateSpec : (j.val==1 &&
      ((u.opcode.toNat==admit && min 5 (BStarH6Ordinal.ordinal (oldH6 B base) hh i)==2) ||
       (u.opcode.toNat==bitOp && min 5 (BStarH6Ordinal.ordinal (oldH6 B base) hh i)==4)))=true)
    (race : u.race.toNat=1 ∨ u.race.toNat=2 ∨ u.race.toNat=3) :
    ∃ s, (u.race.toNat=2 → s=.left) ∧ (u.race.toNat=3 → s=.right) ∧
      let e := incident i s
      BeforeOwnService hp x (endpoint (oldH6 B base) hh o 0).1 e →
      BStarClearanceAggregate.total
        (physicalRank B base (AllSizeS1Geometry.step B x e) (distance S)) S <
      BStarClearanceAggregate.total (physicalRank B base x (distance S)) S := by
  have hs : oldH6 B x=oldH6 B base :=
    funext (fun i => (congrArg Prod.fst (same i)).symm)
  obtain ⟨s,L,R,V⟩ :=
    physical_race hp x (oldH6 B base) hh i j u (distance S)
      (congrFun hs) cx old fault gateSpec race sep
  refine ⟨s,L,R,?_⟩
  dsimp only
  intro wait
  let e := incident i s
  rcases V with W|⟨C,q,A,E⟩
  · obtain ⟨part,own,links⟩ := chart_owner_hypotheses hp chart same e
    obtain ⟨safe,door⟩ := pre_service_hypotheses hp chart same e (sep e) wait
    have pay := owner_pointwise_pays hp x e (sep e) o.val S (distance S)
      chart.nodup part own safe
      (fun C hc ho => ⟨(links C hc ho).1,(links C hc ho).2,door C hc ho⟩)
      ⟨(i,j),member,W⟩
    have RF (z : X) : physicalRank B base z (distance S)=physicalRank B x z (distance S) :=
      funext (rank_fixed hp _ hh base x z (fun _ => rfl) (congrFun hs) cb cx _)
    rw [RF x,RF (AllSizeS1Geometry.step B x e)]
    exact pay
  · apply (pre_service_sum hp chart same cb cx e (sep e) wait).2
    have Own : physicalOwner (oldH6 B base) e cmdDispl (⟨s,j⟩ : At (Fin 11))=o.val := by
      have h := (chart.entries _ member).2
      unfold physicalOwner
      rw [incident_site i s]
      exact h
    exact ⟨C,q,A,(by rw [hs] at E; exact E.trans Own)⟩

end L4.BStarClearanceIndexedRace
