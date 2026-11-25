import Leader.L4.BStarRetainedActualSamples
import Leader.L4.BStarAcquireAckWindow
import Leader.L4.BStarWriterTransferWindow

namespace L4.BStarStageWriterAuth
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongTransport BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarLongFiberOwner BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter
open BStarResetSchedule BStarGeneratedOwner BStarOwnerLaunchOrigin BStarLongDoor BStarLongCommand
open BStarGrantBirth BStarLongGrant BStarGeneratedBandScan BStarLongEvents BStarLongLayout
open BStarStageDescriptorHistory BStarStageProvenance BStarBankTrace BStarWriterTransferWindow

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- A healthy selected STAGE on a recovered owner's actual tape uses
its currently held center writer and that same center's selector.
The needed hold goes all the way back to the actual center capture
mark; the packed descriptor is not trusted independently. -/
theorem stage_writer {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X → Prop) (I : Q x)
    (fiber : ∀ y,Q y → ∀ i, Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y → Q (step y e))
    (sep : ∀ e : Fin n,e≠rightNeighbor e) {m : Mode} {w : List (Fin n)}
    (T : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (now : Current hp base (fun j => S.getD j fall) len (run x w) m)
    (start : pc x (S.getD 0 fall).1<6)
    (j : Nat) (hj : j≤len) (e : Fin n) (K : CommandClaim) (p : Payload)
    (idx : S.getD j fall=address e K.source)
    (center : Fin n) (hdr : oldH6 B base center=true)
    (own : commandOwner (oldH6 B base) center 1=o.val)
    (d : BStarLongPublication.Descriptor) :
    let y := run x w
    let g := oldPair B y e
    let raw : Pair (BitVec LW) := ((y e).long,(y (rightNeighbor e)).long)
    (K,.advance p)∈actualOffers g raw →
    Stage (beforeOutgoing g raw K p).2 →
    descOfStage (beforeOutgoing g raw K p).2=some d →
    original (y center).long 1=true ∧ d.old=BStarLongPublication.readSel (y center).long := by
  dsimp only
  intro sel healthy given
  let root := (S.getD 0 fall).1
  obtain ⟨_,lead,last,issue,E,_,LaunchIssue,pcStage,selectedDesc,flight⟩ :=
    BStarBodyStageProvenance.selected_descriptor hp C sep T now j hj e K p idx sel healthy
  have initial : Current hp base (fun j => S.getD j fall) len x .idle := by cases T <;> assumption
  obtain ⟨q,H,_,current⟩ := generated_word hp C Q fiber
    (fun y A mark => closed y mark A) sep lead .idle I initial
  have idle : q=.idle := by
    cases q with
    | idle => rfl
    | busy op z =>
      have P := current.1.2.2.1
      have J := LaunchIssue.1.2
      exact False.elim ((by decide : (2 : Nat)≠1) (P.symm.trans J))
  subst q
  have O := BStarGeneratedIdleStage.capture_origin_from_early hp C Q I fiber closed sep H start pcStage
  obtain ⟨before,accept,mid,W,G,D,op6,retain⟩ :=
    BStarRetainedActualSamples.origin_consume hp C Q I fiber closed sep initial lead O
  obtain ⟨pre,birth,post,i,v,U,ownV,hdrV,won,_,selV,_,fields,_,safe⟩ :=
    BStarAcquireAckWindow.consume_six_owned_window hp C sep 1 G D op6
  have P := (endpoint_spec (oldH6 B base) hh o 1).2.2
  have loc : i=center := congrArg Prod.fst ((P i hdrV ownV).trans (P center hdr own).symm)
  subst i
  let born := step (run x pre) birth
  let intake := step (run x before) accept
  let sz := run x lead
  let word := (post++[accept])++(mid++(issue::last))
  have beforeEq : run x before=run born post := by
    rw [U,BStarResetSchedule.run_append]
    rfl
  have intakeEq : run born (post++[accept])=intake := by
    rw [BStarResetSchedule.run_append,←beforeEq]
    rfl
  have stageEq : run intake mid=sz := by
    change _=run x lead
    rw [W,BStarResetSchedule.run_append]
    rfl
  have exactWord : w=pre++birth::word := by
    rw [E,W,U]
    simp [word,List.append_assoc]
  have safeW : SafePC hp root born word := by
    unfold word
    refine safe_append hp _ _ _ _ safe ?_
    rw [intakeEq]
    refine safe_append hp _ _ mid _ (safe_band hp _ _ _ retain) ?_
    rw [stageEq]
    change SafePC hp root sz ([issue]++last)
    refine safe_append hp root sz [issue] last ?_ ?_
    · apply safe_single
      have pc : pc sz root=stageOp := pcStage
      rw [pc]
      exact ⟨by decide,by decide⟩
    · have fl : BusyOnly hp base (fun j => S.getD j fall) len stageOp
          (step sz issue) (.out 0) last (.out j) := flight
      change SafePC hp root (step sz issue) last
      intro u mark v eq
      have O := busy_prefix_pc hp fl u (mark::v) eq
      change pc (run (step sz issue) u) root=stageOp at O
      rw [O]
      exact ⟨by decide,by decide⟩
  have Hold := follows_safe_word hp C Q I fiber closed sep initial pre birth center word own hdr won safeW
  have realY : run x w=run born word := by
    rw [exactWord,BStarResetSchedule.run_append]
    rfl
  have alive : bit (run x w) center 1≠0 := by
    rw [realY]
    exact Hold.2.1 word [] (by simp)
  have rawTrue : original (run x w center).long 1=true := by
    cases no : original (run x w center).long 1
    · apply (alive ?_).elim
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      have h : j=0 := by omega
      subst j
      exact no
    · rfl
  refine ⟨rawTrue,?_⟩
  have sameDesc : BStarLongPublication.decode (sourceDescriptor.read (sz root).long)=some d :=
    selectedDesc.symm.trans given
  obtain ⟨_,_,_,_,d0,_,_,_,decode,_,sameSel⟩ :=
    BStarStageCaptureOrigin.idle_desc_from_capture hp C Q I fiber closed sep H start pcStage
  have dd : d=d0 := Option.some.inj (sameDesc.symm.trans decode)
  have heldFields := (BStarCaptureDoorHistory.word_capture_hold hp intake root mid sep
    (fun u m tail eq => (retain u m tail eq).2)).2.2
  change (capturedSelector 1).read (run intake mid root).long=
    (capturedSelector 1).read (intake root).long at heldFields
  rw [stageEq] at heldFields
  apply Fin.ext
  calc
    d.old.val = d0.old.val := congrArg (fun z : BStarLongPublication.Descriptor => z.old.val) dd
    _ = ((capturedSelector 1).read (sz root).long).toNat := sameSel
    _ = ((capturedSelector 1).read (intake root).long).toNat := congrArg BitVec.toNat heldFields
    _ = v.selector.val := congrArg Prod.fst fields
    _ = (BStarLongPublication.readSel (run x pre center).long).val := congrArg Fin.val selV
    _ = (BStarLongPublication.readSel (run x w center).long).val :=
      congrArg (fun q : Fin 3 => q.val) (Hold.2.2.symm.trans (congrArg (fun y : X =>
        BStarLongPublication.readSel (y center).long) realY.symm))

#print axioms stage_writer
end L4.BStarStageWriterAuth
