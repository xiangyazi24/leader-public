import Leader.L4.Height.ProductionGates
import Leader.L4.Height.ProductionPace
import Leader.L4.Height.ProductionWidths
import Leader.L4.BStarFenceReceiverChart

namespace L4.Height.ProductionClients
open AllSizeProtocol PhysicalCustody ProductionCustody BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarAcquireAnchors BStarFenceReceiverChart BStarGeneratedOwner
open BStarSteeredLikelihood BStarLongClaims BStarParkedSteering BStarSteeringSupport
open Classical
noncomputable section

variable {s n : Nat} {x : Raw s n} (g : CustodyWitness x)
local notation "h" => oldH6 (rows s) g.base
local notation "hp" => (show 0<2 by decide)

theorem production_overflow (P : Production g) (o : Owners h) (live : Fin 5 → Word n → Prop) :
    let R := redirect g o live
    let t := 2*(2^20*n*width g)
    8*wordSum (BStarRawBlockDrift.massInd (fun v =>
      5*longBudget < decisions (prescribed R) [] (emit (chooseBy R) [] v))) t ≤ n^t := by
  let os := client h g.hh o
  have package (j : Fin 5) :
      ∃ S len fall, BStarResetChartTouch.Chart hp g.base g.hh (os j) S len fall ∧
        ∀ w, ∃ m d, GeneratedOwner hp g.base (fun k=>S.getD k fall) len x m w d := by
    obtain ⟨_,_,_,S,len,fall,_,_,C,_,m,_,cur⟩ := generated_at_every_history P (os j) []
    refine ⟨S,len,fall,C,?_⟩
    intro w
    obtain ⟨d,G,_,_⟩ := generated_word hp C g.Q g.fiber (fun y q e => g.closed y e q)
      (separation P) w m (ready_run P []).1 cur
    exact ⟨m,d,G⟩
  let S j := (package j).choose
  let L j := (package j).choose_spec.choose
  let fall j := (package j).choose_spec.choose_spec.choose
  have facts j := (package j).choose_spec.choose_spec.choose_spec
  have C (j : Fin 5) : BStarResetChartTouch.Chart hp g.base g.hh (os j) (S j) (L j) (fall j) := (facts j).1
  have roots (j : Fin 5) : ((S j).getD 0 (fall j)).1=(endpoint h g.hh (os j) 0).1 :=
    congrArg Prod.fst (C j).root
  have chartIssue : (fun j => ProductionAdmissions.issues hp x ((S j).getD 0 (fall j)).1)=issue g o :=
    funext (fun j => congrArg (ProductionAdmissions.issues hp x) (roots j))
  obtain ⟨i,_⟩ := g.hh
  have bound := ProductionPace.five_client_overflow hp os S L fall C (separation P)
    (fun b i => g.fiber _ (ready_run P b).1 i) (fun j => (facts j).2) (width g)
    (fun j => (chart_sizes g (C j)).2.1) (fun j => (chart_sizes g (C j)).2.2)
    (Nat.zero_lt_of_lt i.isLt) (gate g o) live
    (fun _ k => if commandOwner h k 1=o.val then .left else .right)
  dsimp only at bound
  rw [chartIssue] at bound
  exact bound

end
end L4.Height.ProductionClients

