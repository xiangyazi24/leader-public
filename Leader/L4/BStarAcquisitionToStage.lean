import Leader.L4.BStarCaptureDoorHistory
import Leader.L4.BStarStageIssuedHistory
import Leader.L4.BStarAcquireReadout
import Leader.L4.BStarGeneratedBandScan

namespace L4.BStarAcquisitionToStage
open AllSizeProtocol BStarTrace BStarLongWork BStarLongTransport BStarLongToken BStarH6WordChart
open BStarLongLayout BStarLongDoor BStarLongCommand BStarFinalCandidate BStarClearanceSource
open BStarStageDescriptorHistory BStarAcquireDigits

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- The actual selected ACQUIRE receipt fills the live source capture
fields. These are the fields consumed by the arithmetic and STAGE
door; this theorem does not authenticate a reply from the bits alone. -/
theorem capture_mark (x : X) (e : Fin n) (sep : e≠rightNeighbor e) (a : Payload)
    (hdr : oldH6 B x (rightNeighbor e)=true)
    (V : LongDoorGuard.valid manifest (x (rightNeighbor e)).long=true)
    (ph : (ctrlPhase.read (x (rightNeighbor e)).long).toNat=2)
    (op : (ctrlOp.read (x (rightNeighbor e)).long).toNat=acquire)
    (R : bind (longGeometry B (x (rightNeighbor e))) 0 (atSite (x (rightNeighbor e)).long 0)=.reply a)
    (F : a.fault=0) (O : a.opcode.toNat=acquire) (S : a.outcome=0) :
    let i := rightNeighbor e
    BStarAcquireJoined.snapshot (step x e i).long = BStarAcquireLanding.expected a := by
  dsimp only
  let pair := (x e,x (rightNeighbor e))
  have Y : step x e (rightNeighbor e)=(largePair B pair).2 := by
    simp only [AllSizeS1Geometry.step,if_neg (Ne.symm sep),if_true,pair]
  rw [Y]
  exact Prod.ext (BStarCaptureDoorHistory.joined_capture hp pair a hdr V ph op R F O S).1
    (BStarCaptureDoorHistory.joined_capture hp pair a hdr V ph op R F O S).2

/-- From a true selected successful receipt and an intervening
non-restarting computation history, the actual STAGE's old bank
equals the center selector sampled by that receipt, not a resample. -/
theorem capture_into_stage (x : X) (e : Fin n)
    (sep : ∀ m : Fin n,m≠rightNeighbor m)
    (a f : Payload)
    (hdr : oldH6 B x (rightNeighbor e)=true)
    (V : LongDoorGuard.valid manifest (x (rightNeighbor e)).long=true)
    (ph : (ctrlPhase.read (x (rightNeighbor e)).long).toNat=2)
    (op : (ctrlOp.read (x (rightNeighbor e)).long).toNat=acquire)
    (R : bind (longGeometry B (x (rightNeighbor e))) 0 (atSite (x (rightNeighbor e)).long 0)=.reply a)
    (F : a.fault=0) (O : a.opcode.toNat=acquire) (S : a.outcome=0)
    (mid tail : List (Fin n))
    (live : ∀ pre m suf, mid=pre++m::suf →
      BStarCaptureDoorHistory.LiveMark hp (run (step x e) pre) (rightNeighbor e) m)
    (foreign : ∀ m∈tail, rightNeighbor m≠rightNeighbor e)
    (header : ∀ u m v, tail=u++m::v →
      oldH6 B (run (step (run (step x e) mid) e) u) (rightNeighbor e)=true) :
    let i := rightNeighbor e
    let y := run (step x e) mid
    let old := (y i).long
    let z := run (step y e) tail
    let wx := (z i).long
    oldH6 B y i=true → LongDoorGuard.valid manifest old=true →
    (ctrlPhase.read old).toNat=2 → (ctrlOp.read old).toNat=lastOp →
    bind (longGeometry B (y i)) 0 (atSite old 0)=.reply f →
    f.fault=0 → f.opcode.toNat=lastOp → ((capturedSelector 1).read old).toNat<3 →
    (ctrlOp.read wx).toNat=stageOp → Launch wx (step z e i).long →
    ∃ p d, atSite (step z e i).long 0=.forward p ∧
      descOfStage p=some d ∧ d.old.val=(fieldsAt a 1).1 := by
  dsimp only
  intro hdr' V' ph' op' R' F' O' h pc L
  let i := rightNeighbor e
  let y := run (step x e) mid
  have got := capture_mark hp x e (sep e) a hdr V ph op R F O S
  have frame := BStarCaptureDoorHistory.word_capture_hold hp (step x e) i mid sep live
  have fields := BStarAcquireReadout.source_fields_payload (step x e i).long a got 1
  obtain ⟨p,fl,desc,oldSel⟩ :=
    BStarStageIssuedHistory.final_to_issue hp y e (sep e) f hdr' V' ph' op' R' F' O' h
      tail foreign header pc L
  refine ⟨p,finalDesc (y i).long h,fl,desc,oldSel.trans ?_⟩
  exact (congrArg BitVec.toNat frame.2.2).trans (congrArg Prod.fst fields)

/-- Extract the exact retained capture file on the same marked tape
that the computation-band scan certified. In particular the center
selector is not read from a subsequent header state. -/
theorem origin_capture_fields (x : X) (i : Fin n) (w : List (Fin n))
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (hdr : ∀ pre e tail, w=pre++e::tail → oldH6 B (run x pre) i=true)
    (A : BStarGeneratedBandScan.Origin hp i x w) :
    ∃ pre e mid a, w=pre++e::mid ∧ e=RearTrace.predecessor i ∧
      let old := run x pre
      let result := run x w
      bind (longGeometry B (old i)) 0 (atSite (old i).long 0)=.reply a ∧
      ∀ j : Fin 3,
        (((capturedSelector j).read (result i).long).toNat,
          ((BStarAcquireReadout.headerBlock j).read (result i).long).toNat)=fieldsAt a j := by
  obtain ⟨pre,e,mid,a,W,E,⟨pc,V,ph,R⟩,F,O,S,_,normal⟩ := A
  let old := run x pre
  let y := step old e
  have Z : rightNeighbor e=i := E.symm ▸ RearTrace.right_predecessor i
  have H0 : oldH6 B old (rightNeighbor e)=true := Z.symm ▸ hdr pre e mid W
  have V0 : LongDoorGuard.valid manifest (old (rightNeighbor e)).long=true := Z.symm ▸ V
  have P0 : (ctrlPhase.read (old (rightNeighbor e)).long).toNat=2 := Z.symm ▸ ph
  have C0 : (ctrlOp.read (old (rightNeighbor e)).long).toNat=acquire := Z.symm ▸ pc
  have R0 : bind (longGeometry B (old (rightNeighbor e))) 0 (atSite (old (rightNeighbor e)).long 0)=.reply a :=
    Z.symm ▸ R
  have x0 := capture_mark hp old e (sep e) a H0 V0 P0 C0 R0 F O S
  have got : BStarAcquireJoined.snapshot (y i).long=BStarAcquireLanding.expected a := Z ▸ x0
  have hold := BStarCaptureDoorHistory.word_capture_hold hp y i mid sep
    (fun u m v M => (normal u m v M).2)
  have S0 : BStarAcquireJoined.snapshot ((run y mid) i).long=BStarAcquireJoined.snapshot (y i).long :=
    Prod.ext hold.1 hold.2.1
  refine ⟨pre,e,mid,a,W,E,R,?_⟩
  intro j
  rw [W,BStarResetSchedule.run_append]
  exact BStarAcquireReadout.source_fields_payload _ a (S0.trans got) j

end L4.BStarAcquisitionToStage
