import Leader.L4.Height.StageSealExactFrame
import Leader.L4.Height.StageCenterExtract
import Leader.L4.Height.StageCenterSeed
import Leader.L4.Height.StageSealConflictCut
import Leader.L4.BStarCommitGeneratedTail

namespace L4.Height.StageSealOldFacts
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongCommand BStarLongDoor BStarLongLayout BStarLongPublication
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarGeneratedOwner BStarLongGrant BStarGrantReaderHistory BStarLongLandingFrame BStarLongFiberOwner BStarPublicationBirth BStarGrantBirth BStarAcquireAnchors
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step
open BStarAcquireHistoryReturn BStarGeneratedTapeCuts BStarOwnerLaunchOrigin
open BStarSeparatingRail BStarAcquireForwardTrace BStarSealParity BStarResetMarkAdapter BStarClearanceSource BStarSealHealthyHop BStarLongFixedRouting
open BStarLongLiteral BStarLongEvents BStarLongTransport StageSealExactFrame StageActualBusy StageScopedReplay BStarResetChartService

/-- The same real suffix that is known eventually to reach PC2 already
contains the matching authorized STAGE→SEAL center rows, with no
assumed latch/writer interval or external service subsequence. -/
theorem accepted_seal_facts {base origin x : X} {hh : ∃ j,oldH6 B base j=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ y,Q y→∀ j,Layout B base j=Layout B y j)
    (closed : ∀ y,Q y→∀ e,Q (step y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (own : commandOwner (oldH6 B base) i 1=o.val)
    (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1)) (head : oldH6 B base i=true)
    (lead : List (Fin n)) (landed : play origin lead=x)
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle lead (.busy stageOp (.out 0)))
    (source : BitVec LW) (d : Descriptor) (valid : d.valid=true)
    (D : BStarLongPublication.decode (sourceDescriptor.read source)=some d)
    (src : sourceDescriptor.read (x (S.getD 0 fall).1).long=sourceDescriptor.read source)
    {w : List (Fin n)} {m : Mode}
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len x (.busy stageOp (.out 0)) w m)
    (qx : Q x) (wire : Wire (fun j=>S.getD j fall) x source (.out 0))
    (auth : PrefixAuth hp base x (fun j=>S.getD j fall) len 0 source d w)
    (qOrigin : Q origin)
    (early : (ctrlOp.read (origin (S.getD 0 fall).1).long).toNat<6)
    (later : (ctrlOp.read (play x w (S.getD 0 fall).1).long).toNat=2) :
    ∃ before tail pay,
      w=before++i::tail ∧
      GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle (lead++before) (.busy sealOp (.out k)) ∧
      let z := play x before
      Well pay ∧ Q z ∧ conflict (ports z i)=false ∧
      BStarLongPublication.decode (sourceDescriptor.read (z (S.getD 0 fall).1).long)=some d ∧
      BStarLongPublication.decode (BitVec.ofNat 7 (pay.argument.toNat/2))=some d ∧
      BStarLongOutgoing.actual (z i).long d=true ∧ readOptional (stage.read (z i).long)=some d ∧
      (centerLink (oldPair B z i),.advance pay)∈actualOffers (oldPair B z i)
        ((z i).long,(z (rightNeighbor i)).long) := by
  let addr := fun j=>S.getD j fall
  have qrun (y : X) (a : List (Fin n)) (hy : Q y) : Q (play y a) := by
    induction a generalizing y with
    | nil => exact hy
    | cons e a ih => exact ih _ (closed _ hy e)
  obtain ⟨all,ack,rest,W,A,E,_bound,PC,DD⟩ :=
    issue409_before_pc2 hp C Q fiber closed sep source d D src T qx wire auth later
  obtain ⟨pre,a,WA,preBusy,_stageEvent,postBusy,pay,selected,healthy,decoded⟩ :=
    stage_center_split hp C Q fiber closed sep source d D k K i idx A qx wire (auth.take hp all (ack::rest) W)
  let old := play x pre
  let xK := step old i
  have wStage : w=pre++i::(a++ack::rest) := by rw [W,WA,List.append_assoc,List.cons_append]
  have OK : play origin (lead++pre)=old := by rw [BStarResetSchedule.run_append,landed]
  have ancestry := generated_append hp G (landed.symm ▸ busy_generated hp preBusy)
  have headOld : oldH6 B old i=true := (congrArg Prod.fst (fiber _ (qrun _ pre qx) i)).symm.trans head
  -- The older authorized selected STAGE payload is the canonical source payload.
  have issued := wire_of_busy hp C Q fiber closed sep source d D preBusy qx wire (by
    intro j eq
    have Z : j=0 := (Cursor.out.inj eq).symm
    subst j
    exact auth.take hp pre (i::(a++ack::rest)) wStage)
  have raw : readK ((old i).long,(old (rightNeighbor i)).long) (centerLink (oldPair B old i)).source=
      .forward (BStarStageIssue.payload source) := by
    change atSite (old i).long 1=_
    change project addr old k=_ at issued
    change atCursor old (S.getD k fall)=_ at issued
    rw [idx] at issued
    exact issued
  have actual : (centerLink (oldPair B old i),.advance (BStarStageIssue.payload source))∈
      actualOffers (oldPair B old i) ((old i).long,(old (rightNeighbor i)).long) := by
    apply StageHealthyHop.bound_stage_selected _ _ _ _ (center_mem _) (show Cmd.link≠Cmd.door by decide) _ rfl
    unfold bound
    rw [raw]
    exact BStarStageIssue.bound_forward_exact _ _ source d D
  have authOld := auth pre i (a++ack::rest) wStage k preBusy (centerLink (oldPair B old i)) idx actual headOld rfl
  have free := StageSealConflictCut.conflict_at_center hp C Q fiber closed sep i own k K idx head lead landed G source d D qx wire auth qOrigin early
  have init := StageCenterSeed.at_stage hp C sep i own (lead++pre) OK k ancestry (busy_end hp preBusy)
    headOld d pay selected healthy.1 healthy.2 decoded authOld (free pre _ wStage preBusy)
  have replayA : play x all=play xK a := by rw [WA,BStarResetSchedule.run_append]; rfl
  have generatedAll := (exact_generated_prefix hp (W ▸ T) (busy_end hp A)).2
  let y := step (play x all) ack
  have Tidle : GeneratedOwner hp base addr len y .idle rest m := by
    cases generatedAll with
    | next _ ev ts =>
      have ownDoor : ack=RearTrace.predecessor (addr 0).1 := by
        cases E with
        | consume _ own _ => exact own
      cases ev with
      | consume _ _ _ => exact ts
      | arrived_hold _ away => exact (away ownDoor).elim
      | transit _ _ _ live _ => exact (live rfl).elim
  have yq : Q y := closed _ (qrun _ all qx) ack
  have laterY : (ctrlOp.read (play y rest (addr 0).1).long).toNat=2 := by
    rw [W,BStarResetSchedule.run_append] at later
    exact later
  obtain ⟨idle,door,b,tail,WR,foreign,P,D',Door,L,F,_sealEvent⟩ :=
    SealActualCenterCut.first_center_from409 hp C Q fiber closed sep i k K idx head Tidle yq d PC DD laterY
  let beforeSeal := play y idle
  let afterLaunch := step beforeSeal door
  have suffixGenerated : GeneratedOwner hp base addr len y .idle (idle++[door]) (.busy sealOp (.out 0)) := by
    have U : rest=(idle++[door])++(b++i::tail) := by rw [WR,List.append_assoc,List.singleton_append]
    have loc : play y (idle++[door])=afterLaunch := by rw [BStarResetSchedule.run_append]; rfl
    exact (exact_generated_prefix hp (U ▸ Tidle) (loc.symm ▸ busy_start hp F)).1
  let mid := a++ack::(idle++door::b)
  have MW : w=pre++i::(mid++i::tail) := by
    rw [wStage,WR]
    simp only [mid,List.append_assoc,List.cons_append]
  have stageCut : play origin ((lead++pre)++[i])=xK := by
    rw [BStarResetSchedule.run_append,OK]
    rfl
  have replayMid : play xK mid=play afterLaunch b := by
    simp only [mid,BStarResetSchedule.run_append,BStarResetSchedule.run,replayA,y,beforeSeal,afterLaunch]
  have scope := StageSealFrameActual.interval_scope hp K idx sep a idle b postBusy
    (congrArg (fun z : X => step z ack) replayA ▸ suffixGenerated)
    foreign (congrArg (fun z : X=>step (play (step z ack) idle) door) replayA ▸ F)
  have wholePrefix : GeneratedOwner hp base addr len origin .idle (((lead++pre)++[i])++mid) (.busy sealOp (.out k)) := by
    have T' : GeneratedOwner hp base addr len x (.busy stageOp (.out 0)) ((pre++[i]++mid)++i::tail) m := by
      have eq : w=(pre++[i]++mid)++i::tail := by rw [MW]; simp only [List.append_assoc,List.cons_append,List.nil_append]
      exact eq ▸ T
    have Z : play x (pre++[i]++mid)=play afterLaunch b := by
      have oldCut : play x (pre++[i])=xK := by
        rw [BStarResetSchedule.run_append]; rfl
      calc
        _ = play (play x (pre++[i])) mid := BStarResetSchedule.run_append _ _ _ _
        _ = _ := (congrArg (fun z : X => play z mid) oldCut).trans replayMid
    have headT := (exact_generated_prefix hp T' (Z.symm ▸ busy_end hp F)).1
    have combined := generated_append hp G (landed.symm ▸ headT)
    simpa only [List.append_assoc] using combined
  have frame := center_from_scope hp C sep i own k (Nat.le_of_lt K) idx ((lead++pre)++[i]) mid stageCut d valid init wholePrefix
    (by intro u v _; exact (congrArg Prod.fst (fiber _ (qrun _ u (closed _ (qrun _ pre qx) i)) i)).symm.trans head)
    scope

  obtain ⟨pay,Wp,_,selected,desc⟩ :=
    SealActualCenterCut.forward_at_center hp C sep door i b k K idx head P L F d D'
  have oldEq : play x (pre++i::mid)=play afterLaunch b := by
    rw [BStarResetSchedule.run_append]
    exact replayMid
  let mark := play afterLaunch b
  have st : Current hp base addr len beforeSeal .idle := by
    obtain ⟨m,I,_⟩ := BStarGeneratedTapeCuts.split hp idle [door] suffixGenerated
    exact BStarGeneratedTapeCuts.idle_foreign_prefix hp I (by
      intro e mem eq
      exact foreign e mem ((RearTrace.predecessor_right e).symm.trans (congrArg RearTrace.predecessor eq)))
      idle [] (List.append_nil idle).symm
  have headSource := root_header hp C (fiber _ (qrun _ idle yq))
  have ev : Event hp addr len beforeSeal door .idle (.busy sealOp (.out 0)) := P ▸ Event.launch Door L
  have sourceKeep := (BStarCommitGeneratedTail.generated_flight hp (addr:=addr) headSource.2 headSource.1
    (sep door) st ev (P.symm ▸ (by decide : sealOp≠1)) (by rintro ⟨_,h,_⟩; cases h)
    (fun _=>.inl (by intro h; cases h))).2
  have liveDesc : BStarLongPublication.decode (sourceDescriptor.read (mark (addr 0).1).long)=some d :=
    (congrArg BStarLongPublication.decode ((BStarSealBitDescriptor.busy_preserves_descriptor hp C sep F (by decide)).1.trans sourceKeep)).trans D'
  refine ⟨pre++i::mid,tail,pay,?_,?_,?_⟩
  · calc
      w = pre++i::(mid++i::tail) := MW
      _ = (pre++i::mid)++i::tail := by simp only [List.append_assoc,List.cons_append]
  · simpa only [List.append_assoc,List.singleton_append] using wholePrefix
  · rw [oldEq]
    rw [replayMid] at frame
    exact ⟨Wp,qrun _ b (closed _ (qrun _ idle yq) door),frame.2.2,liveDesc,desc,frame.1,frame.2.1,selected⟩

end L4.Height.StageSealOldFacts
