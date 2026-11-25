import Leader.L4.BStarCopyCaptureIdentity
import Leader.L4.BStarAttemptWins
import Leader.L4.BStarCopyRightAttempt

namespace L4.BStarCopyLeftCaptureIdentity
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongTransport
open BStarH6WordChart BStarLongGrant BStarGrantBirth BStarGrantReaderHistory BStarLongCommand
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireAnchors BStarResetChartTouch
open BStarCommitOperands BStarLongLayout BStarLongPublication BStarLongPackets
open BStarGeneratedOwner BStarGeneratedBandScan BStarAcquireHistoryReturn BStarSeparatingRail
open BStarCopyRightStrip

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

open BStarCopyCaptureIdentity
open BStarLongFixedRouting BStarAcquireAckWindow BStarOwnedGrantLife BStarAttemptSafety
theorem left_ack_matches_acquisition {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q x) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (ring y e))
    {tape cut lead after : List (Fin n)} {ack : Fin n}
    (A : Acquisition hp x cut tape (endpoint (oldH6 B base) hh o 0).1 0)
    (W : tape=lead++ack::after)
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle lead (.busy acquire (.back 0)))
    (E : Event hp (fun j=>S.getD j fall) len (play x lead) ack (.busy acquire (.back 0)) .idle)
    (P : pc (ring (play x lead) ack) (S.getD 0 fall).1=6)
    (safe : ReleaseFree hp (S.getD 0 fall).1 (ring (play x lead) ack) after) :
    (∃ t,lead=A.lead++A.mark::t) ∧
    ((capturedSelector 0).read (ring (play x lead) ack (S.getD 0 fall).1).long).toNat=
      (readSel ((play x A.lead) (endpoint (oldH6 B base) hh o 0).1).long).val := by
  obtain ⟨pre,birth,post,i,v,split,own,head,won,_,sel,_,fields,_,prior⟩ :=
    consume_six_owned_window hp chart sep (0 : Fin 3) G E P
  let slot := fun j => S.getD j fall
  let root := (slot 0).1
  let h := (endpoint (oldH6 B base) hh o 0).1
  have atI : i=h := congrArg Prod.fst ((endpoint_spec (oldH6 B base) hh o 0).2.2 i head own)
  have before : play (ring (play x pre) birth) post=play x lead := by
    rw [split,BStarResetSchedule.run_append]; rfl
  have entered : play (ring (play x pre) birth) (post++[ack])=ring (play x lead) ack := by
    rw [BStarResetSchedule.run_append,before]; rfl
  have S0 : ReleaseFree hp root (ring (play x pre) birth) (post++[ack]) := by
    intro u e v T
    exact (prior u e v T).1
  have S1 : ReleaseFree hp root (ring (play x pre) birth) ((post++[ack])++after) :=
    release_append hp root _ (post++[ack]) after S0 (entered.symm ▸ safe)
  have T : tape=pre++birth::((post++[ack])++after) := by
    rw [W,split]
    simp [List.append_assoc,List.cons_append]
  have L := BStarGeneratedTapeCuts.at_start hp G
  have life : Continuous hp (ring (play x pre) birth) i 0 ((post++[ack])++after) := by
    apply continuous hp chart sep pre birth i 0 ((post++[ack])++after) own won
    intro u e v U
    let markPrefix := pre++birth::u
    have replay : play x markPrefix=play (ring (play x pre) birth) u :=
      BStarResetSchedule.run_append ring x pre (birth::u)
    obtain ⟨m,H,ok,C⟩ := generated_word hp chart Q fiber (fun y q a => closed y a q) sep
      markPrefix .idle I L
    refine ⟨m,H,C,?_,?_⟩
    · rw [replay]
      exact S1 u e v U
    · exact (congrArg Prod.fst (fiber _ ok i)).symm.trans head
  have exactly := continuous_reader_birth_unique hp sep x h 0 (by decide)
    pre A.lead ((post++[ack])++after) A.post birth A.mark (T.symm.trans A.exactTape)
    (atI ▸ won) A.won (atI ▸ life) A.live
  have readout := congrArg Prod.fst fields
  change ((capturedSelector 0).read (ring (play x lead) ack root).long).toNat=v.selector.val at readout
  refine ⟨⟨post,?_⟩,?_⟩
  · rwa [←exactly.1,←exactly.2]
  · rw [readout,sel,atI,exactly.1]

end L4.BStarCopyLeftCaptureIdentity
