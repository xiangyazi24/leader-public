import Leader.L4.BStarStageOwnerOrigin
import Leader.L4.BStarStageIssuedHistory
import Leader.L4.BStarBodyStageOwner
import Leader.L4.BStarReaderExclusion

namespace L4.BStarBodyStageProvenance
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongTransport BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireRailCoverage
open BStarAcquireLiteralChain BStarLongFiberOwner BStarLongFixedRouting BStarResetChartTouch
open BStarResetMarkAdapter BStarResetSchedule BStarGeneratedOwner BStarLongEvents
open BStarLongLayout BStarLongDoor BStarLongCommand BStarClearanceSource
open BStarStageDescriptorHistory BStarStageProvenance

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- The actual STAGE handler's input (after arithmetic) decodes
the descriptor of the same owner's genuinely issued source mark.
Thus contextual bank custody is needed only at that source, not as
an additional assumption on every node a STAGE visits. -/
theorem selected_descriptor {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {m : Mode} {w : List (Fin n)}
    (P : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (now : Current hp base (fun j => S.getD j fall) len (run x w) m)
    (i : Nat) (hi : i≤len) (e : Fin n) (K : CommandClaim) (p : Payload)
    (idx : S.getD i fall=address e K.source) :
    let state := run x w
    let g := oldPair B state e
    let raw : Pair (BitVec LW) := ((state e).long,(state (rightNeighbor e)).long)
    (K,.advance p)∈actualOffers g raw →
    Stage (BStarBankTrace.beforeOutgoing g raw K p).2 →
    m=.busy stageOp (.out i) ∧
    ∃ pre post door, w=pre++door::post ∧
      let old := run x pre
      let root := (S.getD 0 fall).1
      door=RearTrace.predecessor root ∧
      Launch (old root).long ((step old door) root).long ∧
      (ctrlOp.read (old root).long).toNat=stageOp ∧
      descOfStage (BStarBankTrace.beforeOutgoing g raw K p).2=
        BStarLongPublication.decode (sourceDescriptor.read (old root).long) ∧
      BStarOwnerLaunchOrigin.BusyOnly hp base (fun j => S.getD j fall) len stageOp
        (step old door) (.out 0) post (.out i) := by
  dsimp only
  intro sel healthy
  let y := run x w
  let g := oldPair B y e
  let raw : Pair (BitVec LW) := ((y e).long,(y (rightNeighbor e)).long)
  have ⟨S₀,eq₀⟩ := before_outgoing_back g raw K p healthy
  obtain ⟨M,pre,post,door,a,W,D,L,opcode, args,req,tape⟩ :=
    BStarStageOwnerOrigin.offered_from_generated hp C sep P now i hi e K p idx S₀ sel
  refine ⟨M,pre,post,door,W,D,L,opcode,?_,tape⟩
  let q : Payload := ⟨0,BitVec.ofNat 9 stageOp,0,0,BitVec.ofNat 34 a⟩
  have bounds : a<2^34 := by
    -- The source registry admits only the packed 7+18 bits for STAGE.
    let old : BitVec LW := ((run x pre) (S.getD 0 fall).1).long
    have A : initial stageOp old=some a := args
    have E : BitVec.ofNat 7 (sourceDescriptor.read old).toNat=sourceDescriptor.read old := by simp
    have I := (sourceDescriptor.read old).isLt
    have J := (candidateHeaders.read old).isLt
    change (sourceDescriptor.read old).toNat<128 at I
    change (candidateHeaders.read old).toNat<262144 at J
    simp [initial,stageOp,acquire,copyLoad,sealOp,commitOp,E] at A
    split at A
    · contradiction
    · simp at A
      omega
  have aq : arg q=low a 25 := by
    unfold arg q
    dsimp only
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt bounds]
  have same : arg q=arg (BStarBankTrace.beforeOutgoing g raw K p).2 :=
    aq.trans (req.trans eq₀)
  change BStarLongPublication.decode (descriptorBits _) = _
  rw [←descriptor_of_arg same]
  exact stage_packet _ a args (show forward stageOp a=.forward q from rfl)

open BStarBodyBankHistory BStarBankTrace BStarLongGrant

/-- The missing chronological content is located at one old word:
an effective body STAGE carries the center writer and that same
writer's currently selected bank. No other remote grant or digit
selector is allowed to stand in for that center. -/
def BodyAuthority (x : X) (e i H : Fin n) : Prop :=
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  ∀ (C : CommandClaim) (q : Payload),
    (C,.advance q)∈offers g raw → site e C.source.side=i →
    C.source.occurrence.val=1 →
    physicalOwner (oldH6 B x) e cmdDispl C.source=commandOwner (oldH6 B x) H 1 →
    (BStarLongCommand.geometry g C.source.side).inside=true →
    Stage (beforeOutgoing g raw C q).2 →
    ∀ d, descOfStage (beforeOutgoing g raw C q).2=some d →
      original (x H).long 1=true ∧ d.old=BStarLongPublication.readSel (x H).long

/-- The old writer being absent rules out body STAGE after recovery. -/
theorem unwritten_body (x : X) (e i H : Fin n) (b : Fin 3)
    (absent : original (x H).long 1=false)
    (body : oldH6 B x i=false) (same : word (oldH6 B x) H=word (oldH6 B x) i)
    (auth : BodyAuthority hp x e i H) : BodyCustody hp x e i b := by
  apply BStarBodyStageOwner.body_custody_of_center hp x e i H b body same
  dsimp only
  intro C q Q side own idx fault inside op d D _
  have h6 : (geometry (oldPair B x e) C.source.side).axes.h6=false := by
    have E : (geometry (oldPair B x e) C.source.side).axes.h6=
        oldH6 B x (site e C.source.side) := by
      cases SC : C.source.side <;> rfl
    exact E.trans ((congrArg (oldH6 B x) side).trans body)
  have inside' : (geometry (oldPair B x e) C.source.side).inside=true := by
    rw [h6,Bool.false_or] at inside
    exact inside
  have W := (auth C q Q side idx own inside' ⟨fault,op⟩ d D).1
  rw [absent] at W
  contradiction

/-- A live canonical reader excludes *every* effective STAGE from
the common body on an authoritative word. The conditional relates
the actual center holder, not a fictitious local body grant. -/
theorem reader_body (x : X) (e i H : Fin n) (j : Fin 3) (jreader : j≠1) (b : Fin 3)
    (active : canonical (original (x H).long) j=true)
    (body : oldH6 B x i=false) (same : word (oldH6 B x) H=word (oldH6 B x) i)
    (auth : BodyAuthority hp x e i H) : BodyCustody hp x e i b :=
  unwritten_body hp x e i H b (BStarReaderExclusion.writer_false _ j jreader active) body same auth

/-- For the current center writer the body still frames its own
selected bank: eligible STAGE writes only the other two banks. -/
theorem writer_body (x : X) (e i H : Fin n) (b : Fin 3)
    (current : BStarLongPublication.readSel (x H).long=b)
    (body : oldH6 B x i=false) (same : word (oldH6 B x) H=word (oldH6 B x) i)
    (auth : BodyAuthority hp x e i H) : BodyCustody hp x e i b := by
  apply BStarBodyStageOwner.body_custody_of_center hp x e i H b body same
  dsimp only
  intro C q Q side own idx fault inside op d D _
  have h6 : (geometry (oldPair B x e) C.source.side).axes.h6=false := by
    have E : (geometry (oldPair B x e) C.source.side).axes.h6=
        oldH6 B x (site e C.source.side) := by
      cases SC : C.source.side <;> rfl
    exact E.trans ((congrArg (oldH6 B x) side).trans body)
  have inside' : (geometry (oldPair B x e) C.source.side).inside=true := by
    rw [h6,Bool.false_or] at inside
    exact inside
  exact ((auth C q Q side idx own inside' ⟨fault,op⟩ d D).2).trans current

end L4.BStarBodyStageProvenance
