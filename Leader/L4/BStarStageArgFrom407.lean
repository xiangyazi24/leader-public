import Leader.L4.BStarStageHeaderFrame
import Leader.L4.BStarStageFrom407
import Leader.L4.BStarStageIssue

namespace L4.BStarStageArgFrom407
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongTransport BStarLongEvents BStarLongLiteral BStarLongRouting BStarLongCommand
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireForwardTrace BStarH6WordChart
open BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing BStarSeparatingRail
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarAcquireRailCoverage BStarAcquireAnchors
open BStarStageCandidateRetention BStarBankTrace BStarStageProvenance
open BStarLongFiberOwner BStarGeneratedTapeCuts BStarCommitTailScan
open BStarStageAckExtract BStarStageHopExtract BStarClearanceSource BStarLongDoor

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step
local notation "pc" => BStarGeneratedBandScan.pc

open BStarExactStageFlight BStarStagePast

open BStarStageFrom407 BStarGeneratedPCAncestry BStarStageSourceFrame BStarResetControllerEntry
open BStarLongLayout

private theorem foreign_pc (x : X) (i e : Fin n)
    (h : oldH6 B x i=true) (ne : rightNeighbor e≠i) :
    pc (step x e) i=pc x i := by
  by_cases E : i=e
  · subst i
    let pair := (x e,x (rightNeighbor e))
    have h' : (oldHeaders B pair.1).h6=true := h
    have t := BStarResetWaitRing.joined_left k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair h'
    unfold BStarGeneratedBandScan.pc
    simp only [AllSizeS1Geometry.step,if_true]
    exact congrArg (fun y : BitVec 2 × BitVec 9 => y.2.toNat) t
  · unfold BStarGeneratedBandScan.pc
    simp only [AllSizeS1Geometry.step,if_neg E,if_neg (Ne.symm ne)]

open BStarGeneratedPCAncestry BStarStageSourceFrame BStarResetControllerEntry

private theorem bad_issue_pc {x : X} {addr : Nat → Pos n} {e : Fin n}
    (h : oldH6 B x (addr 0).1=true)
    (sep : e≠rightNeighbor e) (I : BStarClearanceSource.Issue (x (addr 0).1).long)
    (E : e=RearTrace.predecessor (addr 0).1)
    (bad : initial (pc x (addr 0).1) (x (addr 0).1).long=none) :
    pc (step x e) (addr 0).1=0 := by
  have R : rightNeighbor e=(addr 0).1 := E ▸ RearTrace.right_predecessor _
  let pair := (x e,x (rightNeighbor e))
  have hdr : (oldHeaders B pair.2).h6=true := by change oldH6 B x (rightNeighbor e)=true; rwa [R]
  have valid : LongDoorGuard.valid manifest pair.2.long=true := by
    change LongDoorGuard.valid manifest (x (rightNeighbor e)).long=true
    rw [R]; exact I.1
  have phase : (ctrlPhase.read pair.2.long).toNat=1 := by
    change (ctrlPhase.read (x (rightNeighbor e)).long).toNat=1
    rw [R]; exact I.2
  have A := exact_issue_any_token k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair hdr valid phase
  have bad' : initial (ctrlOp.read pair.2.long).toNat pair.2.long=none := by
    change initial (pc x (rightNeighbor e)) (x (rightNeighbor e)).long=none
    rwa [R]
  rw [bad'] at A
  have eq : step x e (addr 0).1=(largePair B pair).2 := by
    rw [←R]; simp only [AllSizeS1Geometry.step,if_neg (Ne.symm sep),if_true,pair]
  exact congrArg (fun t : _ × BitVec 9 => t.2.toNat) (eq ▸ A)


open BStarLongToken BStarStageProvenance


/-- Read the exact idle/foreign prefix backwards from a physical
ISSUE408 cut. Any earlier launch/reply would have risen out of this band. -/
theorem idle_prefix_408 {base x : X} {addr : Nat → Pos n} {len : Nat}
    {w : List (Fin n)} {a b : Mode} (K : (addr 0).2=0)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (T : GeneratedOwner hp base addr len x a w b)
    (ends : b=.idle) (band : TailBand hp x (addr 0).1 w)
    (atEnd : pc (run x w) (addr 0).1=408) :
    a=.idle ∧ pc x (addr 0).1=408 ∧ ∀ e∈w,rightNeighbor e≠(addr 0).1 := by
  induction T with
  | endpoint I => exact ⟨ends,atEnd,by simp⟩
  | @next x a e w b d I E T ih =>
    have tailBand : TailBand hp (step x e) (addr 0).1 w := by
      intro a b W; exact band (e::a) b (congrArg (List.cons e) W)
    obtain ⟨m,P,F⟩ := ih ends tailBand atEnd
    subst b
    have H := band [] (e::w) rfl
    cases E with
    | idle_hold ne =>
      have own : rightNeighbor e≠(addr 0).1 := fun E =>
        ne ((RearTrace.predecessor_right e).symm.trans (congrArg RearTrace.predecessor E))
      exact ⟨rfl,(foreign_pc hp x _ e H.1 own).symm.trans P,fun f hf => by
        rcases List.mem_cons.mp hf with rfl|hf
        · exact own
        · exact F f hf⟩
    | bad_issue own bad =>
      exact ((by decide : (0:Nat)≠408) ((bad_issue_pc hp H.1 (sep e) I.1 own bad).symm.trans P)).elim
    | consume op own empty =>
      have Z := (consume_to_stage hp K H.1 (sep e) I (.consume op own empty) P).1
      have W : pc x (addr 0).1=407 := I.1.2.2.2.trans Z
      have lo : 408≤pc x (addr 0).1 := H.2.1
      omega

private theorem foreign_header_word (x : X) (root : Fin n) (w : List (Fin n))
    (away : ∀ e∈w,rightNeighbor e≠root)
    (hdr : ∀ a e b,w=a++e::b → oldH6 B (run x a) root=true) :
    let y := run x w
    candidateHeaders.read (y root).long=candidateHeaders.read (x root).long := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    have F := BStarStageHeaderFrame.foreign_headers hp x root e (away e List.mem_cons_self) (hdr [] e w rfl)
    exact (ih (step x e) (fun m H => away m (List.mem_cons_of_mem _ H))
      (fun a m b E => hdr (e::a) m b (congrArg (List.cons e) E))).trans F

private theorem launch_arg {base x y : X} {addr : Nat → Pos n} {len : Nat}
    (K : (addr 0).2=0) (L : Launch (x (addr 0).1).long (y (addr 0).1).long)
    (O : pc x (addr 0).1=408)
    (C : Current hp base addr len y (.busy stageOp (.out 0)))
    (j : Nat) (hj : j≤len) (q : Payload) (H : project addr y j=.forward q) :
    arg q=BStarStageIssue.argument (x (addr 0).1).long := by
  have J := (BStarOwnerControlHistory.pointed_unique_forward _ len _ C.2.1 C.2.2 j hj).mp ⟨q,H⟩
  subst j
  obtain ⟨a,E,P⟩ := L.2
  change (ctrlOp.read (x (addr 0).1).long).toNat=stageOp at O
  let oldBytes : BitVec LW := (x (addr 0).1).long
  change initial (ctrlOp.read oldBytes).toNat oldBytes=some a at E
  change (ctrlOp.read oldBytes).toNat=stageOp at O
  rw [O,BStarStageIssue.stage_initial] at E
  have eq : a=BStarStageIssue.argument (x (addr 0).1).long := by
    change a=BStarStageIssue.argument oldBytes
    cases D : BStarLongPublication.decode (sourceDescriptor.read oldBytes) with
    | none => rw [D] at E; cases E
    | some d => rw [D] at E; exact (Option.some.inj E).symm
  have R : atSite (y (addr 0).1).long 0=.forward q := by
    change BStarAcquireForwardTrace.atCursor y (addr 0)=.forward q at H
    unfold BStarAcquireForwardTrace.atCursor at H
    rw [K] at H
    exact H
  have old := congrArg (fun t : (Token × BitVec 2) × BitVec 9 => t.1.1) P
  change atSite (y (addr 0).1).long 0=forward (pc x (addr 0).1) a at old
  change atSite (y (addr 0).1).long 0=forward (ctrlOp.read oldBytes).toNat a at old
  rw [O,R] at old
  have Q := Token.forward.inj old
  rw [Q,eq]
  have lt := BStarStageIssue.argument_bound (x (addr 0).1).long
  have le : BStarStageIssue.argument (x (addr 0).1).long < 2^34 := by omega
  simp [arg,low,Nat.mod_eq_of_lt lt,Nat.mod_eq_of_lt le]
/-- The exact terminal packet of the given physical STAGE flight has
all 25 low argument bits from the initial post-407 source snapshot. -/
theorem turned_argument {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (K0 : (S.getD 0 fall).2=0) {w lead suffix : List (Fin n)} {m : Mode} {pay : Payload}
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w m)
    (band : TailBand hp x (S.getD 0 fall).1 w) (split : w=lead++suffix)
    (found : Found hp base (fun j=>S.getD j fall) len stageOp x lead (.out len))
    (H : project (fun j=>S.getD j fall) (run x lead) len=.forward pay)
    (healthy : Stage pay) :
    arg pay=BStarStageIssue.argument (x (S.getD 0 fall).1).long := by
  let addr := fun j=>S.getD j fall
  obtain ⟨start,out,launch,V,loc,L,issue408,Out⟩ := found
  have splitLaunch : w=start++(launch::(out++suffix)) := by
    rw [split,V]; simp only [List.append_assoc,List.cons_append]
  obtain ⟨m, Gstart,_⟩ := BStarGeneratedTapeCuts.split hp start
    (launch::(out++suffix)) (splitLaunch ▸ T)
  have mode : m=.idle := idle_of_issue hp (at_end hp Gstart) L.1
  subst m
  have initBand : TailBand hp x (addr 0).1 start := by
    intro a e W
    exact band a (e++launch::(out++suffix))
      (by rw [splitLaunch,W,List.append_assoc])
  have away := (idle_prefix_408 hp K0 sep Gstart rfl initBand issue408).2.2
  have initHead : ∀ a e b,start=a++e::b → oldH6 B (run x a) (addr 0).1=true := by
    intro a e b E
    exact (initBand a (e::b) E).1
  have D := (foreign_word hp x (addr 0).1 start away initHead).1
  have Hs := foreign_header_word hp x (addr 0).1 start away initHead
  have argument : BStarStageIssue.argument (run x start (addr 0).1).long=
      BStarStageIssue.argument (x (addr 0).1).long := by
    unfold BStarStageIssue.argument
    rw [D,Hs]
  let active := step (run x start) launch
  have toTurn : run x lead=run active out := by rw [V,BStarResetSchedule.run_append]; rfl
  have H' : project addr (run active out) len=.forward pay := toTurn ▸ H
  obtain ⟨j,hj,q0,Q0,H0,A0⟩ := BStarStageOwnerOrigin.busy_origin hp chart sep Out len
    (Nat.le_refl _) pay H' healthy
  have srcArg : arg q0=BStarStageIssue.argument (run x start (addr 0).1).long :=
    launch_arg hp (base:=base) (x:=run x start) (y:=active) (addr:=addr) (len:=len)
      K0 L issue408 (busy_start hp Out) j hj q0 Q0
  exact A0.symm.trans (srcArg.trans argument)

/-- The successful selected STAGE at any actual forward K1 occurs
strictly in the literal tail after the chosen final native receipt.
Each premark before it still sees root PC at least 408. -/
theorem selected_argument {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (hk : k<len) (idx : S.getD k fall=(i,1))
    (K0 : (S.getD 0 fall).2=0) {w : List (Fin n)}
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w .idle)
    (band : TailBand hp x (S.getD 0 fall).1 w)
    (first : pc x (S.getD 0 fall).1=408)
    (late : pc (run x w) (S.getD 0 fall).1=411)
    (leaf : TerminalHealth hp base (fun j=>S.getD j fall) len) :
    ∃ before after K pay, w=before++i::after ∧
      (∀ a e b,before=a++e::b → 408≤pc (run x a) (S.getD 0 fall).1) ∧
      let old := run x before
      let raw := ((old i).long,(old (rightNeighbor i)).long)
      (K,.advance pay)∈actualOffers (oldPair B old i) raw ∧ K.source=L 1 ∧ Stage pay ∧ arg pay=BStarStageIssue.argument (x (S.getD 0 fall).1).long := by
  let addr := fun j=>S.getD j fall
  obtain ⟨lead,back,mid,hold,turn,ack,pick,op,pay,W,found,H,healthy,
      turnEv,ret,ackEv,PC,midTrace,mb,pickEv,ready411,holdTrace,tailBand,foreign⟩ :=
    skeleton_from408 hp T K0 sep band first late leaf
  have savedFound := found
  obtain ⟨start,out,launch,V,loc,L,issue408,Out⟩ := found
  let active := step (run x start) launch
  have toTurn : run x lead=run active out := by rw [V,BStarResetSchedule.run_append]; rfl
  have H' : project addr (run active out) len=.forward pay := toTurn ▸ H
  obtain ⟨pre,e,post,E,preOut,stageEv,postOut,K,a,q,selected,_,srcAddr,dstAddr,StageQ,argQ⟩ :=
    find_stage_departure hp chart sep Out k pay healthy 0 len rfl rfl (Nat.zero_le _) hk (Nat.le_refl _) H'
  let src := run active pre
  have k1 : K.source.occurrence.val=1 :=
    (congrArg (fun p : Pos n => p.2.val) (srcAddr.symm.trans idx))
  obtain ⟨fromLeft,which⟩ := departure_trail hp src e (sep e) K q selected k1
  have exactSite : e=i := by
    rw [fromLeft] at srcAddr
    exact congrArg Prod.fst (srcAddr.symm.trans idx)
  subst e
  let before := (start++[launch])++pre
  let after := post++turn::(back++ack::(mid++pick::hold))
  have splitMain : w=before++i::after := by
    rw [W,V,E]
    simp only [before,after,List.append_assoc,List.cons_append,List.nil_append]
  have replay : run x before=src := by
    simp only [before,BStarResetSchedule.run_append]; rfl
  have stageArg := turned_argument hp chart sep K0 T band
    (suffix:=turn::(back++ack::(mid++pick::hold))) (by rw [W]) savedFound H healthy
  refine ⟨before,after,K,q,splitMain,?_,?_,fromLeft,StageQ,argQ.trans stageArg⟩
  · intro a e b E
    exact (band a (e::(b++i::after)) (by rw [splitMain,E]; simp only [List.append_assoc,List.cons_append])).2.1
  · exact replay.symm ▸ selected


#print axioms selected_argument
end L4.BStarStageArgFrom407
