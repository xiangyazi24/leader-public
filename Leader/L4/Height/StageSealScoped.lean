import Leader.L4.Height.StageSealPreserve
import Leader.L4.BStarSealOwnerFrame

namespace L4.Height.StageSealScoped
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongCommand BStarLongPublication BStarLongLayout BStarLongLiteral BStarLongEvents
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch BStarGeneratedOwner

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- Same-tape STAGE latch retention at every cut before the chosen SEAL.
Exclusion is stated solely on the actual generated cursor, not on raw
write masks or a supposed absence of concurrent foreign operations. -/
theorem scoped_stage_until_seal {base origin : X} {hh : ∃ j, oldH6 B base j=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (i : Fin n) (k : Nat) (le : k≤len) (idx : S.getD k fall=(i,1))
    (lead : List (Fin n)) (d : Descriptor) (p : Payload)
    (w : List (Fin n)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (scope : ∀ u e v,w=u++e::v → ∃ m,
      GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle ((lead++[i])++u) m ∧
      Current hp base (fun j=>S.getD j fall) len (play origin ((lead++[i])++u)) m ∧
      oldH6 B (play origin ((lead++[i])++u)) i=true ∧ BStarSealOwnerFrame.Excluded k m) :
    let x := play origin lead
    oldH6 B x i=true →
    (centerLink (oldPair B x i),.advance p)∈actualOffers (oldPair B x i) ((x i).long,(x (rightNeighbor i)).long) →
    p.fault=0 → p.opcode.toNat=stageOp →
    BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/2^18))=some d →
    BStarLongOutgoing.actual (x i).long d=true →
    ∀ a b,w=a++b → stage.read (play origin ((lead++[i])++a) i).long=packOptional (some d) := by
  dsimp only
  intro head offered healthy op decoded auth a b F
  let x := play origin lead
  have split (u : List (Fin n)) : play origin ((lead++[i])++u)=play (step x i) u := by
    rw [BStarResetSchedule.run_append,BStarResetSchedule.run_append]
    rfl
  rw [split]
  apply StageSealPreserve.staged_until_seal hp x i d p head offered healthy op decoded auth w sep _ a b F
  intro u e v E
  obtain ⟨m,P,N,H,off⟩ := scope u e v E
  have safe := BStarSealOwnerFrame.no_latch hp C sep i k le idx P N off e
  rw [split] at H safe
  exact ⟨H,safe⟩

end L4.Height.StageSealScoped
