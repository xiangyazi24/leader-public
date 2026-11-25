import Leader.L4.BStarAcquisitionToStage
import Leader.L4.BStarGeneratedIdleStage
import Leader.L4.BStarBodyStageProvenance

namespace L4.BStarStageCaptureOrigin
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongTransport BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireRailCoverage
open BStarAcquireLiteralChain BStarLongFiberOwner BStarLongFixedRouting BStarResetChartTouch
open BStarResetMarkAdapter BStarResetChartService BStarResetSchedule BStarGeneratedOwner
open BStarLongLayout BStarLongDoor BStarLongCommand BStarClearanceSource
open BStarStageDescriptorHistory BStarStageProvenance BStarLiteralPC BStarFinalCandidate
open BStarGeneratedBandScan

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

private theorem keeps (Q : X → Prop) (closed : ∀ y e, Q y → Q (step y e))
    (x : X) (w : List (Fin n)) (I : Q x) : Q (run x w) := by
  induction w generalizing x with
  | nil => exact I
  | cons e w ih => exact ih _ (closed x e I)

/-- From a clean recovered early PC to idle STAGE on that owner's
actual tape, the old descriptor's center bank came from the previous
successful ACQUIRE consume on this tape. Both marks are extracted,
not supplied as chronology premises. -/
theorem idle_desc_from_capture {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X → Prop) (I : Q x)
    (fiber : ∀ y,Q y → ∀ i, Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y → Q (step y e))
    (sep : ∀ e : Fin n,e≠rightNeighbor e) {w : List (Fin n)}
    (T : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w .idle)
    (start : pc x (S.getD 0 fall).1<6)
    (finish : pc (run x w) (S.getD 0 fall).1=408) :
    let i := (S.getD 0 fall).1
    let old := (run x w i).long
    ∃ (pre : List (Fin n)) (e : Fin n) (mid : List (Fin n)) (a : Payload) (d : BStarLongPublication.Descriptor), w=pre++e::mid ∧ e=RearTrace.predecessor i ∧
      bind (longGeometry B (run x pre i)) 0 (atSite (run x pre i).long 0)=.reply a ∧
      BStarLongPublication.decode (sourceDescriptor.read old)=some d ∧
      d.old.val=(BStarAcquireDigits.fieldsAt a 1).1 ∧
      d.old.val=((capturedSelector 1).read old).toNat := by
  dsimp only
  let i := (S.getD 0 fall).1
  have hdr (z : X) (J : Q z) : oldH6 B z i=true := (root_header hp C (fiber z J)).1
  have K := BStarGeneratedIdleStage.capture_origin_from_early hp C Q I fiber closed sep T start finish
  obtain ⟨pre,e,mid,a,W,E,R,entries⟩ :=
    BStarAcquisitionToStage.origin_capture_fields hp x i w sep
      (fun u m v _ => hdr _ (keeps hp Q closed x u I)) K
  have G := BStarGeneratedIdleStage.stage_origin_from_early hp C Q I fiber closed sep T (by omega) finish
  obtain ⟨lead,fm,tail,f,Word,atDoor,⟨num,phase,reply,h⟩,healthy,opcode,_,foreign⟩ := G
  let y := run x lead
  let z := step y fm
  have fy : Q y := keeps hp Q closed x lead I
  have fz : Q z := closed _ _ fy
  have NE : rightNeighbor fm=i := atDoor.symm ▸ RearTrace.right_predecessor i
  have valid : LongDoorGuard.valid manifest (y i).long=true := by
    change ((((ctrlPhase.read (y i).long).toNat==1)||((ctrlPhase.read (y i).long).toNat==2)) &&
      decide ((ctrlOp.read (y i).long).toNat<413))=true
    change (ctrlOp.read (y i).long).toNat=407 at num
    change (ctrlPhase.read (y i).long).toNat=2 at phase
    simp [phase,num]
  have arrival := BStarStageIssuedHistory.final_arrival hp y fm (sep fm) f
    (NE.symm ▸ hdr y fy) (NE.symm ▸ valid) (NE.symm ▸ phase) (NE.symm ▸ num)
    (NE.symm ▸ reply) healthy opcode (NE.symm ▸ h)
  have Arr : sourceDescriptor.read (z i).long=BStarLongPublication.encode (finalDesc (y i).long h) ∧
      (capturedSelector 1).read (z i).long=(capturedSelector 1).read (y i).long := by
    have M := arrival.2
    simpa only [NE] using M
  have fp (m) (M : m∈tail) : rightNeighbor m≠i := by
    intro H
    apply foreign m M
    change m=RearTrace.predecessor i
    rw [←H,RearTrace.predecessor_right]
  have Hold := BStarStageSourceFrame.foreign_word hp z i tail fp
    (fun u m v _ => hdr _ (keeps hp Q closed z u fz))
  have Xeq : run x w=run z tail := by rw [Word,BStarResetSchedule.run_append]; rfl
  refine ⟨pre,e,mid,a,finalDesc (y i).long h,W,E,R,?_,?_,?_⟩
  · rw [Xeq,Hold.1,Arr.1]
    exact decode_final _ h
  · have p : ((capturedSelector 1).read (run x w i).long).toNat=(BStarAcquireDigits.fieldsAt a 1).1 :=
      congrArg Prod.fst (entries 1)
    change ((capturedSelector 1).read (y i).long).toNat=_
    rw [Xeq,Hold.2,Arr.2] at p
    exact p
  · change ((capturedSelector 1).read (y i).long).toNat=_
    rw [Xeq,Hold.2,Arr.2]

#print axioms idle_desc_from_capture

open BStarLongEvents BStarBankTrace

/-- The real body STAGE (after arithmetic) carries the center
selector from the earlier successful consume on the recovered
owner's own physical tape. This identifies the protected candidate
bank once that earlier receipt is linked to its winning header. -/
theorem selected_desc_from_capture {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (Q : X → Prop) (I : Q x)
    (fiber : ∀ y,Q y → ∀ i, Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y → Q (step y e))
    (sep : ∀ e : Fin n,e≠rightNeighbor e) {m : Mode} {w : List (Fin n)}
    (T : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (now : Current hp base (fun j => S.getD j fall) len (run x w) m)
    (start : pc x (S.getD 0 fall).1<6)
    (j : Nat) (hj : j≤len) (e : Fin n) (K : CommandClaim) (p : Payload)
    (idx : S.getD j fall=address e K.source) :
    let state := run x w
    let g := oldPair B state e
    let raw : Pair (BitVec LW) := ((state e).long,(state (rightNeighbor e)).long)
    (K,.advance p)∈actualOffers g raw → Stage (beforeOutgoing g raw K p).2 →
    ∃ (pre mid post : List (Fin n)) (dA dS : Fin n) (a : Payload) (d : BStarLongPublication.Descriptor),
      w=pre++dA::mid++dS::post ∧
      let root := (S.getD 0 fall).1
      dA=RearTrace.predecessor root ∧ dS=RearTrace.predecessor root ∧
      bind (longGeometry B (run x pre root)) 0 (atSite (run x pre root).long 0)=.reply a ∧
      descOfStage (beforeOutgoing g raw K p).2=some d ∧ d.old.val=(BStarAcquireDigits.fieldsAt a 1).1 := by
  dsimp only
  intro sel healthy
  obtain ⟨_,lead,post,dS,W,door,L,pcStage,D,_⟩ :=
    BStarBodyStageProvenance.selected_descriptor hp chart sep T now j hj e K p idx sel healthy
  have initial : Current hp base (fun j => S.getD j fall) len x .idle := by cases T <;> assumption
  obtain ⟨atLaunch,H,_,current⟩ := generated_word hp chart Q fiber
    (fun y A mark => closed y mark A) sep lead .idle I initial
  have idle : atLaunch=.idle := by
    cases atLaunch with
    | idle => rfl
    | busy op z =>
      have P := current.1.2.2.1
      have J := L.1.2
      exact False.elim ((by decide : (2 : Nat)≠1) (P.symm.trans J))
  subst atLaunch
  obtain ⟨pre,dA,mid,a,d,E,r0,R,K',V,_⟩ :=
    idle_desc_from_capture hp chart Q I fiber closed sep H start pcStage
  refine ⟨pre,mid,post,dA,dS,a,d,?_,r0,door,R,D.trans K',V⟩
  rw [W,E]

#print axioms selected_desc_from_capture
end L4.BStarStageCaptureOrigin
