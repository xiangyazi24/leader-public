import Leader.L4.Height.StageSelectorRing
import Leader.L4.Height.StageSealScoped
import Leader.L4.BStarSealWriterInterval

namespace L4.Height.StageCenterSeed
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongLiteral BStarLongEvents BStarLongCommand BStarLongDoor BStarLongLayout BStarLongPublication
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarGeneratedOwner BStarLongGrant BStarGrantReaderHistory BStarLongLandingFrame BStarLongFiberOwner BStarPublicationBirth BStarGrantBirth BStarAcquireAnchors
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step


/-- The actual selected STAGE mark establishes the entire center seed:
packed latch, same selected bank, continued writer and conflict freedom. -/
theorem at_stage {base origin x : X} {hh : ∃ j,oldH6 B base j=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (own : commandOwner (oldH6 B base) i 1=o.val)
    (lead : List (Fin n)) (landed : play origin lead=x) (j : Nat)
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle lead (.busy stageOp (.out j)))
    (I : Current hp base (fun j=>S.getD j fall) len x (.busy stageOp (.out j)))
    (head : oldH6 B x i=true)
    (d : Descriptor) (pay : Payload)
    (offered : (centerLink (oldPair B x i),.advance pay)∈
      actualOffers (oldPair B x i) ((x i).long,(x (rightNeighbor i)).long))
    (healthy : pay.fault=0) (op : pay.opcode.toNat=stageOp)
    (decoded : BStarLongPublication.decode (BitVec.ofNat 7 (pay.argument.toNat/2^18))=some d)
    (auth : BStarLongOutgoing.actual (x i).long d=true)
    (free : conflict (ports x i)=false) :
    BStarLongOutgoing.actual (step x i i).long d=true ∧
      conflict (ports (step x i) i)=false ∧
      stage.read (step x i i).long=packOptional (some d) := by
  have A := Bool.and_eq_true_iff.mp auth
  have live : bit x i 1≠0 := by
    intro zero
    change (grant 1).read (x i).long=0 at zero
    rw [zero] at A
    exact (by decide : ¬ (0 : BitVec 1).getLsbD 0=true) A.1
  have retained := BStarSealWriterInterval.live_writer_word hp C sep i own lead [i] landed ⟨live,free⟩
    (by
      intro u e v W
      cases u with
      | nil =>
        have E : i::[]=e::v := W
        obtain ⟨rfl,_⟩ := List.cons.inj E
        exact ⟨_,by simpa only [List.append_nil] using G,I,head,
          fun a eq=>by cases eq⟩
      | cons f u =>
        have L := congrArg List.length W
        simp at L) [i] [] rfl
  change bit (step x i) i 1≠0 ∧ conflict (ports (step x i) i)=false at retained
  have selectorEq := StageSelectorRing.selector_at_stage hp x i d pay head offered healthy op decoded auth
  have latch := StageLatchRing.stage_at_mark hp x i d pay head offered healthy op decoded auth
  refine ⟨?_,retained.2,latch⟩
  unfold BStarLongOutgoing.actual
  have eq : readSel (step x i i).long=readSel (x i).long := by
    unfold readSel
    rw [selectorEq]
  rw [eq]
  exact Bool.and_eq_true_iff.mpr ⟨BStarSealWriterInterval.live_at_end_bit retained.1,A.2⟩

#print axioms at_stage
end L4.Height.StageCenterSeed
