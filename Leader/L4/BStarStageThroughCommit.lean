import Leader.L4.BStarStageTailHold

namespace L4.BStarStageThroughCommit
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarResetChartTouch BStarGeneratedOwner BStarLongFixedRouting BStarLongFiberOwner
open BStarLongCommand BStarLongDoor BStarClearanceSource BStarOwnerLaunchOrigin
open BStarGeneratedTapeCuts BStarCommitTailScan BStarCommitGeneratedTail BStarLongEvents
open BStarStageCandidateRetention BStarStagePast BStarStageTailHold BStarSeparatingRail

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step
local notation "pc" => BStarGeneratedBandScan.pc

private theorem app {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b c : Mode} {u v : List (Fin n)}
    (P : GeneratedOwner hp base addr len x a u b)
    (Q : GeneratedOwner hp base addr len (run x u) b v c) :
    GeneratedOwner hp base addr len x a (u++v) c := by
  induction P with
  | endpoint _ => exact Q
  | next I E _ ih => exact .next I E (ih Q)

private theorem busy_word {base x : X} {addr : Nat → Pos n} {len op : Nat}
    {z d : Cursor} {w : List (Fin n)} (P : BusyOnly hp base addr len op x z w d) :
    GeneratedOwner hp base addr len x (.busy op z) w (.busy op d) := by
  induction P with
  | nil I => exact .endpoint I
  | cons I E _ ih => exact .next I E ih

/-- Stitch all literal same-attempt segments. From an actual selected
STAGE write at a fixed K1 through its forward/return tail, accepted
ACK, pre-choice 409/410 band, ready411 hold, and genuine busy411
flight, each candidate bank is still the same after the designated
publication mark. No per-mark absence of a STAGE is assumed. -/
theorem bank_survives {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (k j : Nat) (hk : k≤len) (atK0 : (S.getD 0 fall).2=0)
    (lead back mid hold fly : List (Fin n)) (e ack pick door pub : Fin n)
    (idx : S.getD k fall=(e,1))
    (own : commandOwner (oldH6 B base) e 1=o.val)
    (b : Fin 3) (C : CommandClaim) (p : Payload) (center : C.source.occurrence.val=1)
    (z : Cursor) (modePick : Mode) :
    let addr := fun a => S.getD a fall
    let root := (addr 0).1
    let old := run x lead
    let staged := step old e
    let atAck := run staged back
    let atMid := step atAck ack
    let atPick := run atMid mid
    let ready := step atPick pick
    let atDoor := run ready hold
    let launched := step atDoor door
    (C,.advance p)∈actualOffers (oldPair B old e) ((old e).long,(old (rightNeighbor e)).long) →
    GeneratedOwner hp base addr len x .idle lead (.busy stageOp (.out k)) →
    Event hp addr len old e (.busy stageOp (.out k)) (.busy stageOp z) →
    BusyOnly hp base addr len stageOp staged z back (.back 0) →
    Event hp addr len atAck ack (.busy stageOp (.back 0)) .idle →
    GeneratedOwner hp base addr len atMid .idle mid modePick →
    PreBand hp atMid root mid → pc atMid root≥409 →
    Event hp addr len atPick pick modePick .idle →
    pc ready root=411 →
    GeneratedOwner hp base addr len ready .idle hold .idle →
    TailBand hp ready root hold →
    (∀ d∈hold,rightNeighbor d≠root) →
    Event hp addr len atDoor door .idle (.busy commitOp (.out 0)) →
    BusyOnly hp base addr len commitOp launched (.out 0) fly (.out j) →
    BankAt b (run launched fly e).long=BankAt b (staged e).long ∧
    BankAt b (step (run launched fly) pub e).long=BankAt b (staged e).long := by
  dsimp only
  intro sel G ev backTrace ackEv midTrace band start pickEv ready411 holdTrace tailBand foreign issue flight
  let addr := fun a => S.getD a fall
  let old := run x lead
  let staged := step old e
  let atAck := run staged back
  let atMid := step atAck ack
  let atPick := run atMid mid
  let ready := step atPick pick
  let atDoor := run ready hold
  let launched := step atDoor door
  have b0 := busy_keeps_after_departure hp chart sep lead (xOld:=rfl) e k hk idx
    G C p sel center ev backTrace b
  have g0 := app hp G (.next (at_end hp G) ev (.endpoint (busy_start hp backTrace)))
  have g1 := app hp g0 (show GeneratedOwner hp base addr len (run x (lead++[e]))
      (.busy stageOp z) back (.busy stageOp (.back 0)) by
    rw [BStarResetSchedule.run_append]; exact busy_word hp backTrace)
  let lead1 := (lead++[e])++back
  have ra : run x lead1=atAck := by simp only [lead1,BStarResetSchedule.run_append]; rfl
  have noAck : RingNoStage hp atAck ack e := ra ▸ excludes_stage_at hp chart sep g1 (at_end hp g1)
    ack e k hk idx (by intro H; cases H)
  have ackBank := ring_keeps hp atAck ack e (sep ack) b noAck
  have ackOne : GeneratedOwner hp base addr len (run x lead1) (.busy stageOp (.back 0)) [ack] .idle := by
    rw [ra]
    exact .next (at_end hp (busy_word hp backTrace)) ackEv (.endpoint (at_start hp midTrace))
  have g2 := app hp g1 ackOne
  let lead2 := lead1++[ack]
  have rm : run x lead2=atMid := by rw [BStarResetSchedule.run_append,ra]; rfl
  have bMid := holds_after_ack_band hp chart sep lead2 mid rm.symm g2 midTrace atK0 band start e b own
  have midFixed : GeneratedOwner hp base addr len (run x lead2) .idle mid modePick := by
    rw [rm]; exact midTrace
  have g3 := app hp g2 midFixed
  let lead3 := lead2++mid
  have rp : run x lead3=atPick := by rw [BStarResetSchedule.run_append,rm]
  have pickOld := before_choice_ge409 hp midTrace atK0 sep band start mid [] (List.append_nil _).symm
  have pickBank := holds_with_pc hp chart sep lead3 [pick] rp.symm g3
    (.next (at_end hp midTrace) pickEv (.endpoint (at_start hp holdTrace)))
    (by intro a q v W; cases a with
        | cons u a => have H := congrArg List.length W; simp at H <;> omega
        | nil => exact Nat.ne_of_gt pickOld)
    e b own
  have pickOne : GeneratedOwner hp base addr len (run x lead3) modePick [pick] .idle := by
    rw [rp]
    exact .next (at_end hp midTrace) pickEv (.endpoint (at_start hp holdTrace))
  have g4 := app hp g3 pickOne
  let lead4 := lead3++[pick]
  have rr : run x lead4=ready := by rw [BStarResetSchedule.run_append,rp]; rfl
  have H411 := ready411_pc hp (addr 0).1 hold ready411 tailBand foreign
  have holdBank := holds_with_pc hp chart sep lead4 hold rr.symm g4 holdTrace
    (fun a q v W D => (by decide : (411:Nat)≠408) ((H411 a (q::v) W).symm.trans D)) e b own
  have holdFixed : GeneratedOwner hp base addr len (run x lead4) .idle hold .idle := by
    rw [rr]; exact holdTrace
  have g5 := app hp g4 holdFixed
  let lead5 := lead4++hold
  have rd : run x lead5=atDoor := by rw [BStarResetSchedule.run_append,rr]
  have doorBank := holds_with_pc hp chart sep lead5 [door] rd.symm g5
    (.next (at_end hp holdTrace) issue (.endpoint (busy_start hp flight)))
    (by
      intro a q v W D
      cases a with
      | cons u a => have H := congrArg List.length W; simp at H <;> omega
      | nil => exact (by decide : (411:Nat)≠408) ((H411 hold [] (List.append_nil _).symm).symm.trans D))
    e b own
  have doorOne : GeneratedOwner hp base addr len (run x lead5) .idle [door] (.busy commitOp (.out 0)) := by
    rw [rd]
    exact .next (at_end hp holdTrace) issue (.endpoint (busy_start hp flight))
  have g6 := app hp g5 doorOne
  let lead6 := lead5++[door]
  have rl : run x lead6=launched := by rw [BStarResetSchedule.run_append,rd]; rfl
  have early := doorBank.trans (holdBank.trans (pickBank.trans (bMid.trans (ackBank.trans b0))))
  have flyBank := holds_with_pc hp chart sep lead6 fly rl.symm g6 (busy_word hp flight)
    (fun a q v W D => (by decide : commitOp≠408)
      ((BStarWriterTransferWindow.busy_prefix_pc hp flight a (q::v) W).symm.trans D)) e b own
  exact ⟨flyBank.trans early,
    (commit_flight_keeps hp chart sep lead6 fly rl.symm g6 flight pub e b own).trans early⟩

open BStarLongLayout BStarLongOutgoing BStarStageCandidateWrite
open BStarBankTrace BStarLongPublication

/-- Read the actual staged candidate at an arbitrary later endpoint
whose `BankAt` equality was proved by `bank_survives`. Thus the
center header and every IN digit expose their own exact staged
data at the old or new COMMIT state. -/
theorem retained_values (old : X) (e : Fin n) (C : CommandClaim) (pay : Payload)
    (d : Descriptor) (which : Bool) (endSite : BitVec LW) :
    let g := oldPair B old e
    let raw := ((old e).long,(old (rightNeighbor e)).long)
    C.source.occurrence.val=1 →
    (C,.advance pay)∈offers g raw →
    pay.fault=0 → pay.opcode.toNat=stageOp →
    BStarLongPublication.decode (BitVec.ofNat 7 (pay.argument.toNat/2^18))=some d →
    (g.1.axes.h6=true → actual raw.1 d=true) →
    BankAt (candidate d which) endSite=BankAt (candidate d which) (step old e e).long →
    (g.1.inside=true → ∀ i : Fin 9,
      (bankDigit (candidate d which) i).read endSite=readDigit raw.1 which i) ∧
    (g.1.axes.h6=true → ∀ i : Fin 9,
      (bankHeader (candidate d which) i).read endSite=argumentHeader pay.argument.toNat which i) := by
  dsimp only
  intro center sel healthy opcode DD auth retained
  have K := BStarStageCandidateJoined.bStar_writes k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (old e,old (rightNeighbor e)) C pay d center sel healthy opcode DD auth
  have E : step old e e=(largePair B (old e,old (rightNeighbor e))).1 := by
    simp only [AllSizeS1Geometry.step,if_pos rfl]
  rw [E] at retained
  refine ⟨fun H i => ?_,fun H i => ?_⟩
  · have R := congrArg (fun a : (Fin 9 → BitVec 4) × (Fin 9 → BitVec 1) => a.1 i) retained
    exact R.trans (K.1 H which i)
  · have R := congrArg (fun a : (Fin 9 → BitVec 4) × (Fin 9 → BitVec 1) => a.2 i) retained
    exact R.trans (K.2 H which i)

#print axioms retained_values
#print axioms bank_survives
end L4.BStarStageThroughCommit
