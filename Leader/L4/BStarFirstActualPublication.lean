import Leader.L4.BStarRawReadSeparation

namespace L4.BStarFirstActualPublication
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongEvents BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter BStarLongFixedRouting
open BStarSeparatingRail BStarGeneratedOwner BStarOwnerLaunchOrigin BStarAcquireForwardTrace
open BStarLongDoor BStarLongLayout BStarCommitIssue BStarResetChartService BStarClearanceSource
open BStarFirstDoorService BStarH6Ordinal BStarClearanceOffset BStarBitSegment BStarBitParity
open BStarClearanceRaceMark BStarStageCandidateWrite BStarLongLiteral BStarLongPublication
open BStarBitNoAbort BStarLongLandingFrame BStarSealHealthyHop BStarAcquireAnchors BStarNeedServicePlan

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

open BStarGrantWriterHistory

/-- A first publication identified after a logical service extension already
belongs to the original word if that word contains any publication. -/
theorem first_publication_on_original (x : X) (i e : Fin n)
    (w service pre rest : List (Fin n))
    (split : w++service=pre++e::rest)
    (before : BeforePublication hp x i pre)
    (hasPublication : ¬BeforePublication hp x i w) :
    (pre++[e])<+:w := by
  have P : w<+:w++service := ⟨service,rfl⟩
  have Q : pre<+:w++service := ⟨e::rest,split.symm⟩
  have R : (pre++[e])<+:w++service :=
    ⟨rest,by simpa [List.append_assoc] using split.symm⟩
  apply Classical.byContradiction
  intro H
  have longer : ¬(pre++[e]).length≤w.length :=
    fun bound=>H (List.prefix_of_prefix_length_le R P bound)
  have shorter : w.length≤pre.length := by
    simp only [List.length_append,List.length_cons,List.length_nil] at longer
    omega
  obtain ⟨suffix,E⟩ := List.prefix_of_prefix_length_le P Q shorter
  exact hasPublication (by
    intro t a u cut
    exact before t a (u++suffix) (by rw [←E,cut]; simp [List.append_assoc]))

theorem first_need_publication_on_original {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1)) (head : oldH6 B base i=true)
    (own : commandOwner (oldH6 B base) i 1=o.val)
    (bSite : Fin n) (g : Nat) (G : 0<g ∧ g<len)
    (gateIdx : S.getD g fall=(bSite,1)) (ord : oldOrdinal B base hh bSite=4)
    (lead : List (Fin n))
    (history : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle lead (.busy sealOp (.out k)))
    (pay : Payload) (well : Well pay) (d : Descriptor) (need : d.need=true)
    (oldFacts : let x := play origin lead
      Q x ∧ correct (oldH6 B base) hh 5 x ∧ BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false ∧
      BStarLongPublication.decode (sourceDescriptor.read (x (S.getD 0 fall).1).long)=some d ∧
      BStarLongPublication.decode (BitVec.ofNat 7 (pay.argument.toNat/2))=some d ∧
      BStarLongOutgoing.actual (x i).long d=true ∧ readOptional (stage.read (x i).long)=some d ∧
      (centerLink (oldPair B x i),.advance pay)∈actualOffers (oldPair B x i)
        ((x i).long,(x (rightNeighbor i)).long))
    (P : Plan hp base (fun j=>S.getD j fall) len k g)
    (w : List (Fin n))
    (hasPublication : ¬BeforePublication hp (step (play origin lead) i) i w) :
    ∃ (pre tail : List (Fin n)) (s : Side),
      w=pre++i::tail ∧
      BeforePublication hp (step (play origin lead) i) i pre ∧
      let y := play (step (play origin lead) i) pre
      SealedCenter d (y i).long ∧
      (longTrace (oldPair B y i) ((y i).long,(y (rightNeighbor i)).long)).publications=
        [⟨.left,candidate d (firstBit s)⟩] := by
  let labels := service hp P i bSite
  have cover : labels.Sublist (w++labels) :=
    List.sublist_append_of_sublist_right (List.Sublist.refl _)
  obtain ⟨pre,tail,gate,s,W,_,_,before,_,sealed,published,_⟩ :=
    BStarNeedTailService.need_tail_sealed_trace hp C Q fiber closed sep
      i k K idx head own bSite g G gateIdx ord lead history
      pay well d need oldFacts P (w++labels) cover
  obtain ⟨z,Z⟩ := first_publication_on_original hp _ i i w labels pre tail W before hasPublication
  exact ⟨pre,z,s,by simpa [List.append_assoc] using Z.symm,before,sealed,published⟩

open BStarNeedPrefixFresh BStarRawReadSealOrigin BStarRawReadSeparation BStarBitControllerOrigin

/-- The first real intervening publication retains the accepted NEED SEAL's
descriptor. The artificial service suffix is not part of the conclusion. -/
theorem two_reads_separated_by_same_need {base x : X} {hh : ∃ j,oldH6 B base j=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ j,Layout B base j=Layout B x j)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (qx : Q x) (off0 : correct (oldH6 B base) hh 5 x)
    (coherent : ∀ (x : X), Q x → ∀ i,oldH6 B x i=true →
      BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false)
    (i : Fin n) (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1)) (head : oldH6 B base i=true)
    (own : commandOwner (oldH6 B base) i 1=o.val)
    (bSite : Fin n) (g : Nat) (G : 0<g ∧ g<len) (gateIdx : S.getD g fall=(bSite,1))
    (ord : oldOrdinal B base hh bSite=4)
    (P : Plan hp base (fun j=>S.getD j fall) len k g)
    (prior gap : List (Fin n)) (a b : Fin n) {m : Mode}
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle (prior++a::gap) m)
    (notInherited : BStarCommitTailScan.pc x (S.getD 0 fall).1≠bitOp)
    (first : RawFirstRead (fun j=>S.getD j fall) g (play x prior) a)
    (second : RawFirstRead (fun j=>S.getD j fall) g (play x (prior++a::gap)) b) :
    ∃ (u v : List (Fin n)) (d : Descriptor) (s : Side),
      a::gap=u++i::v ∧ d.need=true ∧
      BeforePublication hp (play x prior) i u ∧
      let y := play (play x prior) u
      SealedCenter d (y i).long ∧
      (longTrace (oldPair B y i) ((y i).long,(y (rightNeighbor i)).long)).publications=
        [⟨.left,candidate d (firstBit s)⟩] := by
  have between := two_raw_reads_separated hp C Q fiber closed sep qx off0 coherent
    i k K idx head own bSite g G gateIdx ord P prior gap a b T notInherited first second
  obtain ⟨_,past,_⟩ := BStarGeneratedTapeCuts.split hp prior (a::gap) T
  obtain ⟨lead,remain,p,d,split,leader,pW,need,noEarlier,oldFacts⟩ :=
    matching_old_seal hp C Q fiber closed sep qx off0 coherent i k K idx head own g
      (Nat.le_of_lt G.2) prior past notInherited a first
  let next := step (play x lead) i
  have time : play x prior=play next remain := by
    rw [split,BStarResetSchedule.run_append]; rfl
  have existsPub : ¬BeforePublication hp next i (remain++a::gap) := by
    intro silent
    apply between
    intro pre e tail E
    rw [time,←BStarResetSchedule.run_append]
    exact silent (remain++pre) e tail (by rw [E,List.append_assoc])
  obtain ⟨pre,tail,s,W,before,sealed,published⟩ :=
    first_need_publication_on_original hp C Q fiber closed sep i k K idx head own bSite
      g G gateIdx ord lead leader p pW d need oldFacts P (remain++a::gap) existsPub
  have stopped : ¬NoPublication hp (play next pre) i i := by
    intro N
    exact N .left rfl ⟨.left,candidate d (firstBit s)⟩ (by rw [published]; simp) rfl
  obtain ⟨u,U⟩ := BStarNeedPrefix.prefix_before_first_publish hp next i remain (a::gap)
    pre tail W stopped noEarlier
  have Z : a::gap=u++i::tail := by
    rw [←U,List.append_assoc] at W
    exact List.append_cancel_left W
  have same : play (play x prior) u=play next pre := by
    rw [time,←BStarResetSchedule.run_append,U]
  refine ⟨u,tail,d,s,Z,need,?_,?_⟩
  · intro t e v E
    rw [time,←BStarResetSchedule.run_append]
    exact before (remain++t) e v (by rw [←U,E,List.append_assoc])
  · exact ⟨same.symm ▸ sealed,same.symm ▸ published⟩

end L4.BStarFirstActualPublication
