import Leader.L4.BStarBitControllerOrigin
import Leader.L4.BStarSealTourAccepted
import Leader.L4.BStarWriterTransferWindow

namespace L4.BStarRawReadSealOrigin
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongEvents BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter BStarLongFixedRouting
open BStarSeparatingRail BStarGeneratedOwner BStarOwnerLaunchOrigin BStarAcquireForwardTrace
open BStarLongDoor BStarLongLayout BStarResetChartService BStarClearanceSource
open BStarH6Ordinal BStarClearanceOffset BStarLongLiteral BStarLongPublication BStarSealHealthyHop BStarAcquireAnchors
open BStarNeedPrefixFresh BStarGrantWriterHistory BStarFirstDoorService BStarBitControllerOrigin
open BStarCommitTailScan BStarNeedPrefix BStarNeedTrace BStarWriterTransferWindow

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

private theorem after_single {x : X} {w : List (Fin n)} {e : Fin n} {v : List (Fin n)} :
    play x (w++e::v)=play (step (play x w) e) v :=
  BStarResetSchedule.run_append step x w (e::v)

private theorem safe_suffix (x : X) (i : Fin n) (u v : List (Fin n))
    (S : SafePC hp i x (u++v)) : SafePC hp i (play x u) v := by
  intro pre e tail E
  have R : u++v=(u++pre)++e::tail := by rw [E,List.append_assoc]
  have H := S (u++pre) e tail R
  rwa [BStarResetSchedule.run_append] at H

/-- Every post-reset raw first read has a real preceding accepted
NEED SEAL. The theorem names both cuts of the original tape and
excludes any intervening publication by this owner, not by others.
Initial post-reset ISSUE410 states are excluded explicitly. The
settled-chart/grant properties are supplied at the fixed-layout cut. -/
theorem matching_old_seal {base x : X} {hh : ∃ j,oldH6 B base j=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ j,Layout B base j=Layout B x j)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (qx : Q x) (off0 : correct (oldH6 B base) hh 5 x)
    (coherent : ∀ (x : X), Q x → ∀ i,oldH6 B x i=true →
      BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false)
    (i : Fin n) (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1)) (head : oldH6 B base i=true)
    (own : commandOwner (oldH6 B base) i 1=o.val)
    (g : Nat) (G : g≤len)
    {m : Mode} (w : List (Fin n))
    (history : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w m)
    (notInherited : pc x (S.getD 0 fall).1≠bitOp)
    (e : Fin n) (read : RawFirstRead (fun j=>S.getD j fall) g (play x w) e) :
    ∃ (lead remain : List (Fin n)) (p : Payload) (d : Descriptor), w=lead++i::remain ∧
      GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle lead (.busy sealOp (.out k)) ∧
      Well p ∧ d.need=true ∧
      BeforePublication hp (step (play x lead) i) i remain ∧
      let y := play x lead
      Q y ∧ correct (oldH6 B base) hh 5 y ∧ BStarLongGrant.conflict (BStarGrantReaderHistory.ports y i)=false ∧
      BStarLongPublication.decode (sourceDescriptor.read (y (S.getD 0 fall).1).long)=some d ∧
      BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/2))=some d ∧
      BStarLongOutgoing.actual (y i).long d=true ∧ readOptional (stage.read (y i).long)=some d ∧
      (centerLink (oldPair B y i),.advance p)∈actualOffers (oldPair B y i)
        ((y i).long,(y (rightNeighbor i)).long) := by
  let addr := fun j=>S.getD j fall
  let root := (addr 0).1
  have now := BStarGeneratedTapeCuts.at_end hp history
  have readTyped := raw_read_is_owned hp C sep g G w e history read
  have mode := BStarNeedQuietRead.first_read_mode hp now readTyped
  have pcBit : pc (play x w) root=bitOp := readTyped.1.1.2.2.2
  obtain ⟨sealWord,ack,bitRest,d,f,first,sealHist,atAck,Ev,_,stay,reply,F,Op,_,need,desc⟩ :=
    last_entry_to_bit hp C Q fiber closed sep qx w history notInherited pcBit
  obtain ⟨launchPre,flight,launchMark,L,ownMark,launch,pcSeal,SealFlight⟩ := from_idle hp sealHist
  let src := play x launchPre
  let issued := step src launchMark
  have srcLayout := fiber src (stable_word hp Q closed x launchPre qx)
  have rootFacts := root_header hp C srcLayout
  obtain ⟨lane,U,_⟩ := BStarGeneratedTapeCuts.split hp launchPre (launchMark::flight) (L ▸ sealHist)
  have ready0 := BStarGeneratedTapeCuts.at_end hp U
  have wasIdle := BStarGeneratedTapeCuts.idle_of_issue hp ready0 launch.1
  have idle : Current hp base addr len src .idle := wasIdle ▸ ready0
  have issueEvent : Event hp addr len src launchMark .idle (.busy sealOp (.out 0)) :=
    pcSeal ▸ Event.launch ownMark launch
  have issueKeep := (BStarCommitGeneratedTail.generated_flight hp (base:=base) (x:=src)
    (addr:=addr) (len:=len) (e:=launchMark) rootFacts.2 rootFacts.1 (sep launchMark) idle issueEvent
    (pcSeal ▸ (by decide : sealOp≠1)) (fun H=>by cases H.2.1) (fun _=>.inl (by intro H; cases H))).2
  have prefixKeep := (BStarSealBitDescriptor.busy_preserves_descriptor hp C sep SealFlight (by decide)).1
  have ackEq : play x sealWord=play issued flight := by rw [L,after_single hp]
  have Dvalid : BStarLongPublication.decode (sourceDescriptor.read (src root).long)=some d := by
    have P := (congrArg BStarLongPublication.decode (prefixKeep.trans issueKeep)).symm
    exact P.trans (ackEq ▸ desc)
  obtain ⟨pre,out,back,turn,route,preBusy,seedMark,_,_,_,p,pW,sel,packed,auth,stageEq⟩ :=
    BStarSealTourAccepted.accepted_from_tour hp C sep launchMark i k K idx head pcSeal launch
      d Dvalid flight SealFlight f ⟨F,Op⟩ (ackEq ▸ reply)
  let lead := launchPre++launchMark::pre
  let y := play x lead
  let sf := out++turn::back
  let remain := sf++ack::bitRest
  have route' : flight=pre++i::sf := by rw [route,List.append_assoc,List.cons_append]
  have tape : w=lead++i::remain := by
    rw [first,L,route']
    simp only [lead,remain,List.append_assoc,List.cons_append]
  have yEq : y=play issued pre := after_single hp
  have seedLead : GeneratedOwner hp base addr len x .idle lead (.busy sealOp (.out k)) := by
    apply generated_append hp (wasIdle ▸ U)
    exact .next idle issueEvent (busy_generated hp preBusy)
  have Dseed : BStarLongPublication.decode (sourceDescriptor.read (y root).long)=some d := by
    rw [yEq]
    have F0 := (BStarSealBitDescriptor.busy_preserves_descriptor hp C sep preBusy (by decide)).1
    exact (congrArg BStarLongPublication.decode (F0.trans issueKeep)).trans Dvalid
  have qY := stable_word hp Q closed x lead qx
  have offY : correct (oldH6 B base) hh 5 y := by
    apply BStarNativeOffsetTrace.closed_word hp _ hh sep x lead off0
    intro a b _
    exact funext (fun j=>(congrArg Prod.fst (fiber _ (stable_word hp Q closed x a qx) j)).symm)
  have H6Y : oldH6 B y i=true := (congrArg Prod.fst (fiber y qY i)).symm.trans head
  let next := step y i
  have waitSeal : SafePC hp root next sf := by
    have full := safe_busy hp SealFlight (by decide) (by decide)
    rw [route'] at full
    have append : (pre++[i])++sf=pre++i::sf := by simp [List.append_assoc]
    rw [←append] at full
    have last := safe_suffix hp issued root (pre++[i]) sf full
    have E : play issued (pre++[i])=next := by
      rw [BStarResetSchedule.run_append]
      exact congrArg (fun state=>step state i) yEq.symm
    exact E ▸ last
  have yAck : play next sf=play x sealWord := by
    calc
      play next sf = play (step (play issued pre) i) sf :=
        congrArg (fun state=>play state sf) (congrArg (fun state=>step state i) yEq)
      _ = play issued (pre++i::sf) :=
        (after_single hp (x:=issued) (w:=pre) (e:=i) (v:=sf)).symm
      _ = play x sealWord := by rw [ackEq,route']
  have ackSafe : SafePC hp root (play next sf) [ack] := by
    rw [yAck]
    have code : pc (play x sealWord) root=sealOp := atAck.1.2.2.2
    apply safe_single hp
    change pc (play x sealWord) root≠2 ∧ pc (play x sealWord) root≠411
    rw [code]
    exact ⟨by decide,by decide⟩
  have postSeal : play next (sf++[ack])=step (play x sealWord) ack := by
    rw [BStarResetSchedule.run_append,yAck]; rfl
  have bitSafe : SafePC hp root (play next (sf++[ack])) bitRest := by
    rw [postSeal]
    intro u edge v E
    change pc (play (step (play x sealWord) ack) u) (S.getD 0 fall).1≠2 ∧
      pc (play (step (play x sealWord) ack) u) (S.getD 0 fall).1≠411
    rw [stay u (edge::v) E]
    exact ⟨by decide,by decide⟩
  have prePublication : SafePC hp root next remain := by
    have R := safe_append hp root next (sf++[ack]) bitRest
      (safe_append hp root next sf [ack] waitSeal ackSafe) bitSafe
    simpa only [remain,List.append_assoc,List.singleton_append] using R
  have clean : BeforePublication hp next i remain := by
    intro u mark v E
    have actual := BStarGeneratedTapeCuts.at_start hp history
    let prefixWord := lead++i::u
    obtain ⟨m',T,_,cur⟩ := generated_word hp C Q fiber closed sep prefixWord .idle qx actual
    have align : play x prefixWord=play next u := after_single hp
    have noCOM : pc (play x prefixWord) root≠commitOp := by
      rw [align]
      exact (prePublication u mark v E).2
    have noMode := BStarWriterOwnerInterval.not_busy_of_old_pc hp cur commitOp noCOM
    exact align ▸ BStarWriterOwnerInterval.no_publication hp C sep T cur mark i own noMode
  refine ⟨lead,remain,p,d,tape,seedLead,pW,need,clean,qY,offY,coherent y qY i H6Y,Dseed,packed,?_,?_,?_⟩
  · change BStarLongOutgoing.actual (y i).long d=true
    rwa [yEq]
  · change readOptional (stage.read (y i).long)=some d
    rwa [yEq]
  · change (centerLink (oldPair B y i),.advance p)∈actualOffers (oldPair B y i)
      ((y i).long,(y (rightNeighbor i)).long)
    rwa [yEq]

end L4.BStarRawReadSealOrigin
