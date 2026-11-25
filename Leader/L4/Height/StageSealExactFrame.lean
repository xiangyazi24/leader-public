import Leader.L4.Height.StageSealFrameActual
import Leader.L4.Height.SealActualCenterCut
import Leader.L4.Height.StageCenterExtract

namespace L4.Height.StageSealExactFrame
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongCommand BStarLongDoor BStarLongLayout BStarLongPublication
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarGeneratedOwner BStarLongGrant BStarGrantReaderHistory BStarLongLandingFrame BStarLongFiberOwner BStarPublicationBirth BStarGrantBirth BStarAcquireAnchors
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

open StageSealFrameActual BStarGeneratedTapeCuts BStarLongFixedRouting BStarLongGrant BStarOwnerLaunchOrigin
open BStarSeparatingRail

/-- Turn the exact local chronological scope into the actual whole-history
center frame. The generated ancestry and all layout facts are recovered
at the very same subword cut. -/
theorem center_from_scope {base origin x : X} {hh : ∃ j,oldH6 B base j=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (own : commandOwner (oldH6 B base) i 1=o.val)
    (k : Nat) (K : k≤len) (idx : S.getD k fall=(i,1))
    (lead w : List (Fin n)) (landed : play origin lead=x)
    (d : Descriptor) (valid : d.valid=true)
    (seed : BStarLongOutgoing.actual (x i).long d=true ∧
      conflict (ports x i)=false ∧ stage.read (x i).long=packOptional (some d))
    {m : Mode}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle (lead++w) m)
    (H : ∀ u v,w=u++v → oldH6 B (play x u) i=true)
    (scope : LocalScope hp (base:=base) (fun j=>S.getD j fall) len k i x w) :
    BStarLongOutgoing.actual (play x w i).long d=true ∧
      readOptional (stage.read (play x w i).long)=some d ∧ conflict (ports (play x w) i)=false := by
  apply ready_at_prefix hp C sep i own k K idx lead w landed d valid seed _ w [] (List.append_nil w).symm
  intro u e v W
  have A : lead++w=(lead++u)++e::v := by rw [W,List.append_assoc]
  obtain ⟨j,T,_⟩ := split hp (lead++u) (e::v) (A ▸ G)
  have eq : play origin (lead++u)=play x u := by rw [BStarResetSchedule.run_append,landed]
  obtain ⟨l,I,N,R⟩ := scope u e v W
  have same := L4.Height.current_mode_unique hp _ _ (eq ▸ at_end hp T) I
  subst j
  exact ⟨l,T,I,H u (e::v) W,N,R⟩

open BStarAcquireHistoryReturn

/-- Exact busy-word split, used to take the source state immediately
after the earlier selected STAGE departure on the same body. -/
theorem busy_split {base x : X} {addr : Nat→Pos n} {len op : Nat}
    {z d : Cursor} (pre post : List (Fin n))
    (P : BusyOnly hp base addr len op x z (pre++post) d) :
    ∃ mid, BusyOnly hp base addr len op x z pre mid ∧
      BusyOnly hp base addr len op (play x pre) mid post d := by
  induction pre generalizing x z with
  | nil => exact ⟨z,.nil (busy_start hp P),P⟩
  | cons e pre ih =>
    cases P with
    | cons I E tail =>
      obtain ⟨mid,L,R⟩ := ih tail
      exact ⟨mid,.cons I E L,R⟩

theorem generated_append {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b c : Mode} {u v : List (Fin n)}
    (P : GeneratedOwner hp base addr len x a u b)
    (Q : GeneratedOwner hp base addr len (play x u) b v c) :
    GeneratedOwner hp base addr len x a (u++v) c := by
  induction P with
  | endpoint _ => exact Q
  | next I E _ ih => exact .next I E (ih Q)

theorem busy_generated {base x : X} {addr : Nat → Pos n} {len op : Nat}
    {a b : Cursor} {w : List (Fin n)} (P : BusyOnly hp base addr len op x a w b) :
    GeneratedOwner hp base addr len x (.busy op a) w (.busy op b) := by
  induction P with
  | nil I => exact .endpoint I
  | cons I E _ ih => exact .next I E ih

theorem exact_generated_prefix {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b c : Mode} {u v : List (Fin n)}
    (P : GeneratedOwner hp base addr len x a (u++v) b)
    (I : Current hp base addr len (play x u) c) :
    GeneratedOwner hp base addr len x a u c ∧
    GeneratedOwner hp base addr len (play x u) c v b := by
  obtain ⟨d,A,R⟩ := split hp u v P
  have eq := L4.Height.current_mode_unique hp _ _ (at_end hp A) I
  exact eq ▸ ⟨A,R⟩

open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongCommand BStarLongDoor BStarLongLayout BStarLongPublication BStarLongLiteral BStarLongEvents
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarStageProvenance BStarStageCandidateJoined
open BStarLongFixedRouting StageActualBusy StageScopedReplay BStarSeparatingRail

theorem busy_append {base x : X} {addr : Nat → Pos n} {len op : Nat}
    {a b c : Cursor} {u v : List (Fin n)} (P : BusyOnly hp base addr len op x a u b)
    (Q : BusyOnly hp base addr len op (play x u) b v c) :
    BusyOnly hp base addr len op x a (u++v) c := by
  induction P with
  | nil _ => exact Q
  | cons I E _ ih => exact .cons I E (ih Q)

theorem stage_center_split {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (source : BitVec LW) (d : Descriptor)
    (D : BStarLongPublication.decode (sourceDescriptor.read source)=some d)
    (k : Nat) (K : k<len) (i : Fin n) (loc : S.getD k fall=(i,1))
    {w : List (Fin n)}
    (T : BusyOnly hp base (fun j=>S.getD j fall) len stageOp x (.out 0) w (.back 0))
    (qx : Q x) (wire : Wire (fun j=>S.getD j fall) x source (.out 0))
    (auth : PrefixAuth hp base x (fun j=>S.getD j fall) len 0 source d w) :
    ∃ pre post, w=pre++i::post ∧
      BusyOnly hp base (fun j=>S.getD j fall) len stageOp x (.out 0) pre (.out k) ∧
      let y := play x pre
      Event hp (fun j=>S.getD j fall) len y i (.busy stageOp (.out k)) (.busy stageOp (.out (k+1))) ∧
      BusyOnly hp base (fun j=>S.getD j fall) len stageOp (step y i) (.out (k+1)) post (.back 0) ∧
      ∃ pay, (centerLink (oldPair B y i),.advance pay)∈actualOffers (oldPair B y i)
        ((y i).long,(y (rightNeighbor i)).long) ∧
        Stage pay ∧ BStarStageDescriptorHistory.descOfStage pay=some d := by
  obtain ⟨u,t,v,W,O,turn,back⟩ := BStarAcquireAckAncestry.split_turn hp T
  have F := wire_of_busy hp C Q fiber closed sep source d D O qx wire (fun j eq=>by
    have E : j=0 := (Cursor.out.inj eq).symm
    subst j
    exact auth.take hp u (t::v) W)
  obtain ⟨pre,e,post,U,history,ev,after,claim,a,q,sel,_dest,atSrc,_atDst,healthy,argEq⟩ :=
    BStarStageHopExtract.find_stage_departure hp C sep O k (BStarStageIssue.payload source)
      ⟨rfl,rfl⟩ 0 len rfl rfl (Nat.zero_le _) K (Nat.le_refl _) F
  let y := play x pre
  let gg := oldPair B y e
  have mem : claim∈orderedCommands gg := by
    rw [←actualOffers_claims gg ((y e).long,(y (rightNeighbor e)).long)]
    exact List.mem_map.mpr ⟨_,sel,rfl⟩
  have one : claim.source.occurrence.val=1 :=
    congrArg (fun z : Pos n=>z.2.val) (atSrc.symm.trans loc)
  have same : claim=centerLink gg := by
    have H : claim∈(orderedCommands gg).filter centerClaim :=
      List.mem_filter.mpr ⟨mem,by simp [centerClaim,one]⟩
    rw [one_center_claim] at H
    exact List.mem_singleton.mp H
  have ei : e=i := by
    have eq := congrArg Prod.fst (atSrc.symm.trans loc)
    rw [same] at eq
    exact eq
  subst e claim
  have replay : play (step (play x pre) i) post=play x u := by
    rw [U,BStarResetSchedule.run_append]; rfl
  have joined : BusyOnly hp base (fun j=>S.getD j fall) len stageOp
      (step (play x pre) i) (.out (k+1)) (post++t::v) (.back 0) :=
    busy_append hp after (.cons (replay.symm ▸ busy_end hp O) (replay.symm ▸ turn) (replay.symm ▸ back))
  refine ⟨pre,post++t::v,by rw [W,U,List.append_assoc,List.cons_append],history,ev,joined,q,sel,healthy,?_⟩
  have E := descriptor_of_arg argEq
  exact E.trans ((BStarStageIssue.issued_descriptor source).trans D)

end L4.Height.StageSealExactFrame
