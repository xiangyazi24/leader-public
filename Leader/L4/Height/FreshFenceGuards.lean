import Leader.L4.Height.FreshPreparation
import Leader.L4.Height.FreshOrderedPrefix
import Leader.L4.BStarCopyLoadHistory
import Leader.L4.BStarCopyCleanupOriginal
import Leader.L4.BStarNativeOffsetPhysical
import Leader.L4.BStarCopyLeftFence

namespace L4.Height.FreshFenceGuards
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongPackets
open BStarLongPrep BStarLongCommandData BStarLongToken BStarLongCommand
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarResetMarkAdapter BStarGeneratedOwner BStarGeneratedBandScan BStarOwnerLaunchOrigin
open BStarLongFixedRouting BStarAcquireAnchors BStarClearanceDataChart BStarCopyCleanupFrame
open BStarCopyCleanupCoverage BStarCopyEntryGates BStarCopyGateAuthority BStarCopyCleanupWindow
open BStarLongDoor BStarLongLiteral BStarLongEvents BStarLongTransport
open BStarCopyPreIssueEmpty BStarResetRailRing BStarAcquireForwardTrace
open BStarCopyInjection (sourceOccurrence sourceLane)

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step

def CleanLane (v : Lane) : Prop := v.error=false ∧ v.mobile.isBad=false ∧ v.retained.isBad=false

def CleanOwner (base x : X) (o : Int) : Prop :=
  ∀ i sh,activeSheet (longGeometry B (base i)) sh=true → dataOwner (oldH6 B base) i sh=o →
    CleanLane (readLane (Sheet.index sh) (x i).long)

private def CleanLeaf : Leaf→Prop
  | .error b => b=false
  | .mobile d | .retained d => d.isBad=false
  | _ => True

private theorem clean_leaf_put (l : Leaf) (v : Lane) (L : CleanLeaf l) (V : CleanLane v) :
    CleanLane (l.put v) := by
  cases l <;> simp_all [CleanLeaf,CleanLane,Leaf.put]

private theorem clean_fold (s : At Sheet) (old : At Sheet→Lane) (A : List (At Sheet×Leaf))
    (init : CleanLane (old s)) (ready : ∀ l,(s,l)∈A → CleanLeaf l) :
    CleanLane ((A.foldl update old) s) := by
  induction A generalizing old with
  | nil => exact init
  | cons a A ih =>
    apply ih (update old a) _ (fun l M=>ready l (List.mem_cons_of_mem _ M))
    obtain ⟨q,l⟩ := a
    by_cases H : q=s
    · subst q
      simpa [update] using clean_leaf_put l (old s) (ready l List.mem_cons_self) init
    · simpa [update,H,Ne.symm H] using init

private theorem prep_clean (old : At Sheet→Lane) (a : BStarLongPrep.Offer)
    (init : CleanLane (old a.claim.lane)) (safe : (selectedEffects old a).fault=false)
    (l : Leaf) (mem : l∈(selectedEffects old a).writes) : CleanLeaf l := by
  have error := init.1
  cases op : a.claim.op with
  | stop | rstop | enable | clear | rclear =>
    simp [selectedEffects,op,effects] at mem
    repeat' first | rcases mem with rfl|mem
    all_goals simp_all [CleanLeaf,Digit9.isBad]
  | load =>
    have good : a.payload.isBad=false := by
      cases E : a.payload <;> simp_all [selectedEffects,effects,validPayload,Digit9.isBad]
    rcases (show l=.frozen a.payload ∨ l=.error ((old a.claim.lane).error || a.payload.isBad) from
      by simpa [selectedEffects,op,effects] using mem) with rfl|rfl <;>
      simp [CleanLeaf,error,good]
  | inject =>
    have condition : (! (old a.claim.lane).gate || !validPayload (old a.claim.lane).frozen ||
        (old a.claim.lane).mobile != .empty)=false := by
      cases H : (! (old a.claim.lane).gate || !validPayload (old a.claim.lane).frozen ||
          (old a.claim.lane).mobile != .empty) <;> simp_all [selectedEffects,effects]
    have good : (old a.claim.lane).frozen.isBad=false := by
      cases V : (old a.claim.lane).frozen <;> simp_all [validPayload,Digit9.isBad]
    rcases (show l=.mobile (old a.claim.lane).frozen ∨ l=.frozen .empty from
      by simpa [selectedEffects,op,effects,condition] using mem) with rfl|rfl <;>
      simp [CleanLeaf,good]

/-- These checks only constrain data claims that can write this particular
old lane. A closed destination does not require its incoming donor clean. -/
structure SafeDataAt (old : At Sheet→Lane) (a : At Sheet) (D : DataClaim) : Prop where
  terminal : D.kind=.ending → D.source=a → (old a).mobile=.empty
  outgoing : ∀ v,D.destination=some v → D.source=a → (old a).mobile≠.empty →
    ((old a).gate && (old v).gate)=true
  incoming : ∀ v,D.destination=some v → v=a → (old D.source).gate=true → (old a).gate=true →
    (old D.source).mobile.isBad=false

private theorem data_clean (g : Pair LongGeometry) (old : At Sheet→Lane) (a : At Sheet)
    (D : DataClaim) (safe : SafeDataAt old a D) (init : CleanLane (old a))
    (l : Leaf) (mem : (a,l)∈dataEffects g old D) : CleanLeaf l := by
  obtain ⟨clean,mobile,retained⟩ := init
  obtain ⟨kind,src,dst⟩ := D
  cases kind with
  | ending =>
    have atSource : a=src := by
      obtain ⟨q,_,H⟩ := List.mem_map.mp mem
      exact (congrArg Prod.fst H).symm
    subst src
    have empty := safe.terminal rfl rfl
    simp [dataEffects,endEffects,empty] at mem
  | hop =>
    cases dst with
    | none => simp [dataEffects] at mem
    | some v =>
      simp only [dataEffects,List.mem_append] at mem
      rcases mem with left|right
      · obtain ⟨q,hq,H⟩ := List.mem_map.mp left
        have atSource : a=src := (congrArg Prod.fst H).symm
        have leaf : l=q := (congrArg Prod.snd H).symm
        subst src
        subst q
        by_cases empty : (old a).mobile=.empty
        · simp [hopEffects,empty] at hq
        have gate := safe.outgoing v rfl rfl empty
        by_cases vacant : (old v).mobile=.empty
        · rcases (show l=.mobile .empty ∨ l=.error ((old a).error || (old a).mobile.isBad) from
            by simpa [hopEffects,empty,gate,vacant] using hq) with rfl|rfl <;>
            first | exact rfl | simp [CleanLeaf,clean,mobile]
        · simp [hopEffects,empty,gate,vacant] at hq
      · obtain ⟨q,hq,H⟩ := List.mem_map.mp right
        have atDest : a=v := (congrArg Prod.fst H).symm
        have leaf : l=q := (congrArg Prod.snd H).symm
        subst v
        subst q
        by_cases empty : (old src).mobile=.empty
        · simp [hopEffects,empty] at hq
        cases G : ((old src).gate && (old a).gate) with
        | false => simp [hopEffects,empty,G] at hq
        | true =>
          have openG := Bool.and_eq_true_iff.mp G
          have donor := safe.incoming a rfl rfl openG.1 openG.2
          by_cases vacant : (old a).mobile=.empty
          · cases R : BStarLongPackets.retains g a <;>
              simp [hopEffects,empty,G,vacant,R] at hq
            all_goals repeat' first | rcases hq with rfl|hq
            all_goals simp [CleanLeaf,clean,retained,donor]
          · simp [hopEffects,empty,G,vacant] at hq

/-- Literal selected writes on the joined physical pair preserve all
three clean-lane bytes. Prep and data still use the same immutable old
pair, even on a mark which operates on more than one sheet. -/
theorem ring_clean_step (x : X) (e i : Fin n) (sh : Sheet) (sep : e≠rightNeighbor e)
    (init : CleanLane (readLane (Sheet.index sh) (x i).long))
    (ready : let g := oldPair B x e
      let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
      ∀ a : At Sheet,site e a.side=i → a.occurrence=sh →
        (∀ q∈(arbitration (round g raw).prep).1,q.claim.lane=a → (selectedEffects (view raw) q).fault=false) ∧
        (∀ D∈orderedData g (reserved (round g raw).prep),SafeDataAt (view raw) a D)) :
    CleanLane (readLane (Sheet.index sh) (step x e i).long) := by
  have touch (side : Side) (atSite : site e side=i) :
      CleanLane (readLane (Sheet.index sh) (step x e i).long) := by
    subst i
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    let a : At Sheet := ⟨side,sh⟩
    let old := view raw
    have pre : CleanLane (old a) := by
      change CleanLane (view raw a)
      rwa [BStarCopyRightMark.old_access]
    have R := ready a rfl rfl
    have joined := BStarClearanceMobileJoined.joined_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
      (x e,x (rightNeighbor e))
    have J := congrFun joined a
    change view (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) a=
      view (patchPair (patch g raw) raw) a at J
    rw [BStarCopyRightMark.new_access hp x e a sep] at J
    rw [J,BStarLongCommandData.round_transfer]
    apply clean_fold a old _ pre
    intro l M
    rcases List.mem_append.mp M with P|D
    · obtain ⟨q,Q,m⟩ := List.mem_flatMap.mp P
      obtain ⟨t,H,E⟩ := List.mem_map.mp m
      have loc : q.claim.lane=a := congrArg Prod.fst E
      have leaf : t=l := congrArg Prod.snd E
      subst t
      apply prep_clean old q _ (R.1 q Q loc) l H
      rwa [loc]
    · obtain ⟨d,D,H⟩ := List.mem_flatMap.mp D
      exact data_clean g old a d (R.2 d D) pre l H
  by_cases L : i=e
  · exact touch .left L.symm
  · by_cases R : i=rightNeighbor e
    · exact touch .right R.symm
    · rwa [show step x e i=x i from by simp [AllSizeS1Geometry.step,L,R]]

/-- A lane whose gate remains closed after its CLEAR cannot receive
and has no packet to send or discard. The prep fault condition is the
only additional way that mark could change its clean error bit. -/
theorem closed_clean_step (x : X) (e i : Fin n) (sh : Sheet) (sep : e≠rightNeighbor e)
    (init : CleanLane (readLane (Sheet.index sh) (x i).long))
    (closed : (readLane (Sheet.index sh) (x i).long).gate=false)
    (empty : (readLane (Sheet.index sh) (x i).long).mobile=.empty)
    (prep : let g := oldPair B x e
      let raw := ((x e).long,(x (rightNeighbor e)).long)
      ∀ q∈(arbitration (round g raw).prep).1,
        site e q.claim.lane.side=i → q.claim.lane.occurrence=sh → (selectedEffects (view raw) q).fault=false) :
    CleanLane (readLane (Sheet.index sh) (step x e i).long) := by
  apply ring_clean_step hp x e i sh sep init
  dsimp only
  intro a loc sheet
  have V := BStarCopyRightMark.old_access x e a
  rw [loc,sheet] at V
  refine ⟨fun q Q L=>prep q Q ((congrArg (fun t : At Sheet=>site e t.side) L).trans loc)
    ((congrArg At.occurrence L).trans sheet),?_⟩
  intro D _
  refine ⟨fun _ _=> (congrArg Lane.mobile V).trans empty,
    fun _ _ _ notEmpty=>(notEmpty ((congrArg Lane.mobile V).trans empty)).elim,
    fun _ _ _ _ gate=> by rw [V,closed] at gate; contradiction⟩

private theorem load_code (k : Nat) (H : prepOf k=some .load) : k=8 := by
  unfold prepOf at H
  split at H <;> simp_all

private theorem inject_code (k : Nat) (H : prepOf k=some .inject) : k=10 := by
  unfold prepOf at H
  split at H <;> simp_all

private theorem no_prep_fault_of_origin (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (a : BStarLongPrep.Offer) (win : a∈(arbitration (round g raw).prep).1)
    (safe : a.claim.origin∉(round g raw).faults) : (selectedEffects (view raw) a).fault=false := by
  cases test : (selectedEffects (view raw) a).fault
  · rfl
  · apply False.elim
    apply safe
    change a.claim.origin∈prepFaults (view raw) (round g raw).prep
    exact List.mem_append.mpr (.inr (List.mem_map.mpr ⟨a,List.mem_filter.mpr ⟨win,test⟩,rfl⟩))

/-- A winning LOAD of the real owner reads the valid capture operand
installed by its own ISSUE8. A failure would appear in the actual
immutable-old cancellation list, which the LOAD flight excludes. -/
theorem owned_load_clean {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {m : Mode}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w m)
    (same : ∀ i,Layout B base i=Layout B (run x w) i)
    (e : Fin n) (a : BStarLongPrep.Offer) (load : a.claim.op=.load)
    (own : dataOwner (oldH6 B base) (site e a.claim.lane.side) a.claim.lane.occurrence=o.val)
    (win : a∈(arbitration (round (oldPair B (run x w) e)
      (((run x w) e).long,((run x w) (rightNeighbor e)).long)).prep).1) :
    (selectedEffects (view (((run x w) e).long,((run x w) (rightNeighbor e)).long)) a).fault=false := by
  let y := run x w
  let g := oldPair B y e
  let raw : Pair (BitVec LW) := ((y e).long,(y (rightNeighbor e)).long)
  have cur := BStarGeneratedTapeCuts.at_end hp G
  cases m with
  | idle =>
    have safe := BStarCopyOwnedFrozen.safe_idle hp chart same e (site e a.claim.lane.side)
      a.claim.lane.occurrence own cur.2
    have eq : a.claim.lane=⟨a.claim.lane.side,a.claim.lane.occurrence⟩ := by cases a.claim.lane; rfl
    rcases safe a.claim.lane.side rfl a win eq with H|H|H <;>
        exact Prep.noConfusion (load.symm.trans H)
  | busy op z =>
    have E := winning_prep_pc hp chart sep G cur same e a own win
    rw [load] at E
    have PC8 := load_code _ E
    have exactOp : op=8 := cur.1.2.2.2.symm.trans PC8
    subst op
    obtain ⟨C,f,q,H,selected,_,_,origin,owner⟩ := BStarCopyOwnedFrozen.winner_owner hp y e a win
    have heads : oldH6 B y=oldH6 B base := funext fun i=>(congrArg Prod.fst (same i)).symm
    rw [heads,own] at owner
    obtain ⟨j,J,loc⟩ := BStarCopyOwnedFrozen.actual_owner_departure hp chart same e C q z selected owner cur.2.1 cur.2.2
    subst z
    obtain ⟨lead,launch,tail,_,_,pc8,issued,_,stored⟩ := BStarCopyLoadHistory.generated_load_word hp chart sep G
    let rawRoot := ((run x lead) (S.getD 0 fall).1).long
    let u := (captures.read rawRoot).toNat
    obtain ⟨_,argument,arg,_⟩ := issued
    change initial (ctrlOp.read rawRoot).toNat rawRoot=some argument at arg
    rw [pc8] at arg
    obtain ⟨value,valid⟩ := BStarCopyOperand.issue_load_operand rawRoot argument arg
    rw [value] at valid
    have width : u<64 := (captures.read rawRoot).isLt
    have pointed : readK raw C.source=.forward (BStarCopyLoadCarry.payload u) :=
      (old_read y e _).trans ((congrArg (atCursor y) loc).symm.trans stored)
    have Cmem := ((gated_mem g raw C _).mp H).1
    have nd : C.kind≠.door := by
      intro door
      have gated := ((gated_mem g raw C _).mp H).2
      simp [gatedAt,classifyOld,classify,door,checkOffer] at gated
    have expected := BStarCopyLoadHistory.load_gated g raw C u width valid Cmem nd pointed
    have safe := BStarCopyLoadHistory.valid_load_no_fault g raw C u width valid expected
    exact no_prep_fault_of_origin g raw a win (by rwa [origin])

/-- Clean owned prep, including the actual LOAD, at any old cut where
INJECT has yet to begin. -/
theorem owned_noninject_clean {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {m : Mode}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w m)
    (same : ∀ i,Layout B base i=Layout B (run x w) i)
    (e : Fin n) (a : BStarLongPrep.Offer) (nonInject : a.claim.op≠.inject)
    (own : dataOwner (oldH6 B base) (site e a.claim.lane.side) a.claim.lane.occurrence=o.val)
    (win : a∈(arbitration (round (oldPair B (run x w) e)
      (((run x w) e).long,((run x w) (rightNeighbor e)).long)).prep).1) :
    (selectedEffects (view (((run x w) e).long,((run x w) (rightNeighbor e)).long)) a).fault=false := by
  cases op : a.claim.op with
  | load => exact owned_load_clean hp chart sep G same e a op own win
  | inject => exact (nonInject op).elim
  | stop | rstop | clear | rclear | enable => simp [selectedEffects,effects,op]

private theorem inject_sheet {g : LongGeometry} {k : Fin 11} {sh : Sheet}
    (hit : sh∈prepSites g k .inject) : g.inside=true ∧
      ∃ rev : Bool,k=sourceOccurrence rev ∧ sh=sourceLane rev := by
  by_cases active : g.inside=true
  · refine ⟨active,?_⟩
    by_cases L : k=5
    · exact ⟨false,L,by simpa [prepSites,active,L,sourceLane] using hit⟩
    · by_cases R : k=2
      · exact ⟨true,R,by simpa [prepSites,active,L,R,sourceLane] using hit⟩
      · simp [prepSites,active,L,R] at hit
  · simp [prepSites,Bool.eq_false_iff.mpr active] at hit

/-- The actual winning INJECT originates at the owner's pointed K5 or
K2. The already-established frozen input, vacancy and gate at that
point imply a clean literal action, independently of its post-state. -/
theorem owned_copy_prep_clean {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {m : Mode}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w m)
    (same : ∀ i,Layout B base i=Layout B (run x w) i) (e : Fin n)
    (prepared : ∀ j,m=.busy 10 (.out j) → ∀ C : CommandClaim,
      S.getD j fall=address e C.source → FreshOrderedPrefix.ReadyPort (oldPair B (run x w) e)
        (((run x w) e).long,((run x w) (rightNeighbor e)).long) C)
    (a : BStarLongPrep.Offer)
    (own : dataOwner (oldH6 B base) (site e a.claim.lane.side) a.claim.lane.occurrence=o.val)
    (win : a∈(arbitration (round (oldPair B (run x w) e)
      (((run x w) e).long,((run x w) (rightNeighbor e)).long)).prep).1) :
    (selectedEffects (view (((run x w) e).long,((run x w) (rightNeighbor e)).long)) a).fault=false := by
  by_cases inject : a.claim.op=.inject
  · let y := run x w
    let g := oldPair B y e
    let raw : Pair (BitVec LW) := ((y e).long,(y (rightNeighbor e)).long)
    have cur := BStarGeneratedTapeCuts.at_end hp G
    cases m with
    | idle =>
      have safe := BStarCopyOwnedFrozen.safe_idle hp chart same e (site e a.claim.lane.side)
        a.claim.lane.occurrence own cur.2
      have eq : a.claim.lane=⟨a.claim.lane.side,a.claim.lane.occurrence⟩ := by cases a.claim.lane; rfl
      rcases safe a.claim.lane.side rfl a win eq with H|H|H <;>
        exact Prep.noConfusion (inject.symm.trans H)
    | busy op z =>
      have P := winning_prep_pc hp chart sep G cur same e a own win
      rw [inject] at P
      have exactOp : op=10 := cur.1.2.2.2.symm.trans (inject_code _ P)
      subst op
      obtain ⟨C,f,q,H,selected,_,_,originC,owner⟩ := BStarCopyOwnedFrozen.winner_owner hp y e a win
      have heads : oldH6 B y=oldH6 B base := funext fun i=>(congrArg Prod.fst (same i)).symm
      rw [heads,own] at owner
      obtain ⟨j,J,loc⟩ := BStarCopyOwnedFrozen.actual_owner_departure hp chart same e C q z selected owner cur.2.1 cur.2.2
      subst z
      obtain ⟨C',f',q',H',_,_,_,origin,side,slots⟩ := BStarCopyOwnedFrozen.winner_origin g raw a win
      have src : C'.source=C.source := origin.symm.trans originC
      rw [src,inject] at slots
      obtain ⟨active,rev,k,sh⟩ := inject_sheet slots
      obtain ⟨gate,empty,data,frozen⟩ := prepared j rfl C loc rev k active
      have lane : a.claim.lane=(⟨C.source.side,sourceLane rev⟩ : At Sheet) := by
        rw [src] at side
        generalize E : a.claim.lane=w at side sh ⊢
        cases w
        simp_all
      change (selectedEffects (view raw) a).fault=false
      change (view raw ⟨C.source.side,sourceLane rev⟩).gate=true at gate
      change (view raw ⟨C.source.side,sourceLane rev⟩).mobile=.empty at empty
      change (view raw ⟨C.source.side,sourceLane rev⟩).frozen=.data data at frozen
      simp [selectedEffects,inject,effects,lane,gate,empty,frozen,validPayload]
  · exact owned_noninject_clean hp chart sep G same e a inject own win

private theorem run_property {x : X} (w : List (Fin n)) (P : X→Prop)
    (init : P x) (next : ∀ a e b,w=a++e::b → P (run x a) → P (step (run x a) e)) :
    P (run x w) := by
  induction w generalizing x with
  | nil => exact init
  | cons e w ih =>
    exact ih (next [] e w rfl init) (fun a b c E=>next (e::a) b c (congrArg (List.cons e) E))

private theorem active_at_layout {base x : X} (i : Fin n) (sh : Sheet)
    (same : Layout B base i=Layout B x i) :
    activeSheet (longGeometry B (base i)) sh=activeSheet (longGeometry B (x i)) sh := by
  have E := congrArg (fun t : Bool×Bool×Bool=>t.2.1) same
  cases sh <;> first | rfl | exact E

/-- The genuine CLEAR departure zeroes each active error latch. Its
own suffix preserves both the drain and that clean image on the same
marks, using the STOP-closed gates and no injecting winner. -/
theorem cleared_clean_window {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (tour tail : List (Fin n))
    (out : BusyOnly hp base (fun j=>S.getD j fall) len 7 x (.out 0) tour (.out len))
    (pay : Payload) (endFront : project (fun j=>S.getD j fall) (run x tour) len=.forward pay)
    (healthy : pay.fault=0) (op : pay.opcode.toNat=7)
    (layout : ∀ a b,tour++tail=a++b → ∀ i,Layout B base i=Layout B (run x a) i)
    (closed : ∀ a e b,tour++tail=a++e::b → ClosedOwner hp base (run x a) o.val)
    (noInject : ∀ a e b,tour++tail=a++e::b → NoOwnerInject hp base (run x a) e o.val)
    (healthyPrep : ∀ a e b,tour++tail=a++e::b →
      let y := run x a
      let raw : Pair (BitVec LW) := ((y e).long,(y (rightNeighbor e)).long)
      ∀ q∈(arbitration (round (oldPair B y e) raw).prep).1,
        dataOwner (oldH6 B base) (site e q.claim.lane.side) q.claim.lane.occurrence=o.val →
          (selectedEffects (view raw) q).fault=false) :
    CleanOwner hp base (run x (tour++tail)) o.val := by
  intro i sh act own
  obtain ⟨a,e,b,q,T,opQ,atQ,sheet,win⟩ := outward_cleanup hp chart sep .clear rfl (.inr rfl)
    (by decide) out pay endFront healthy op i sh act own
  have clear := ring_clear hp (run x a) e (sep e) q (.inl opQ) win
  dsimp only at clear
  rw [atQ,sheet] at clear
  let property (y : X) := CleanLane (readLane (Sheet.index sh) (y i).long) ∧
    Drained (readLane (Sheet.index sh) (y i).long)
  have initial : property (step (run x a) e) := by
    dsimp [property]
    rw [clear]
    exact ⟨⟨rfl,rfl,rfl⟩,rfl,rfl⟩
  have rest : property (run (step (run x a) e) (b++tail)) := by
    apply run_property hp (b++tail) property initial
    intro u z v E state
    have W : tour++tail=(a++e::u)++z::v := by
      simp only [T,E,List.append_assoc,List.cons_append]
    have replay : run x (a++e::u)=run (step (run x a) e) u := by
      rw [BStarResetSchedule.run_append]; rfl
    rw [←replay] at state ⊢
    have active := (active_at_layout hp i sh (layout (a++e::u) (z::v) W i)).symm.trans act
    have shut := closed (a++e::u) z v W i sh active own
    exact ⟨closed_clean_step hp _ z i sh (sep z) state.1 shut state.2.1
        (fun q Q loc S=>healthyPrep (a++e::u) z v W q Q (by rwa [loc,S])),
      ring_drained hp _ z i sh (sep z) state.2
        (fun q Q loc S=>noInject (a++e::u) z v W q Q (by rwa [loc,S])) (.inl shut)⟩
  have W : tour++tail=a++e::(b++tail) := by simp only [T,List.append_assoc,List.cons_append]
  rw [W,BStarResetSchedule.run_append]
  exact rest.1

open BStarCopyCleanupCuts BStarCopyCleanupOriginal

/-- At the genuine CLEAR7 acceptance and all original PC8 old cuts
thereafter, every active target-owned error latch is clean. This even
covers a partially executed LOAD8, whose operand is verified above. -/
theorem clean_original_after_clear {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {m : Mode} {w : List (Fin n)}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w m)
    (valid : ∀ a b,w=a++b →
      (∀ i,Layout B base i=Layout B (run x a) i) ∧ Band (run x a) (S.getD 0 fall).1)
    (init : pc x (S.getD 0 fall).1≤6) (done : pc (run x w) (S.getD 0 fall).1=8) :
    CleanOwner hp base (run x w) o.val := by
  obtain ⟨pre,ack,tail,W,H,event,new⟩ := accepted_cut hp chart sep G valid 7 (by omega) (by omega)
  obtain ⟨lead,back,turn,pay,A,F,Fpay,healthy,op⟩ :=
    accepted_cleanup_terminal hp chart sep 7 (by decide) H event new
  obtain ⟨u,tour,launch,T,_,_,issue,out⟩ := F
  change pc (run x u) (S.getD 0 fall).1=7 at issue
  let before := u++[launch]
  let later := turn::(back++ack::tail)
  have all : w=before++(tour++later) := by rw [W,A,T]; simp [before,later,List.append_assoc]
  have E1 : run x before=step (run x u) launch := by rw [BStarResetSchedule.run_append]; rfl
  have E2 : run (run x before) tour=run x lead := by
    rw [←BStarResetSchedule.run_append step x before tour,T]; simp [before,List.append_assoc]
  have result := cleared_clean_window hp chart sep tour later (E1.symm ▸ out) pay (E2.symm ▸ Fpay) healthy op
  rw [←BStarResetSchedule.run_append step x before (tour++later),←all] at result
  apply result
  · intro a b Z
    have WW : w=(before++a)++b := by rw [all,Z,←List.append_assoc]
    simpa only [BStarResetSchedule.run_append] using (valid _ _ WW).1
  · intro a e b Z
    have WW : w=(before++a)++e::b := by rw [all,Z,←List.append_assoc]
    obtain ⟨mid,GH,_⟩ := history_prefix hp (before++a) (e::b) (WW ▸ G)
    have valid' (i j : List (Fin n)) (P : before++a=i++j) :
        (∀ k,Layout B base k=Layout B (run x i) k) ∧ Band (run x i) (S.getD 0 fall).1 :=
      valid i (j++e::b) (by rw [WW,P,List.append_assoc])
    have U : before++a=u++launch::a := by simp [before,List.append_assoc]
    have low := prefix_pc_le hp chart sep GH valid' u (launch::a) U
    have upper := prefix_pc_le hp chart sep G valid (before++a) (e::b) WW
    have stopped := stopped_original hp chart sep GH valid' init (by omega) (by omega)
    simpa only [BStarResetSchedule.run_append] using stopped
  · intro a e b Z
    have WW : w=(before++a)++e::b := by rw [all,Z,←List.append_assoc]
    obtain ⟨mid,GH,C⟩ := history_prefix hp (before++a) (e::b) (WW ▸ G)
    have upper := prefix_pc_le hp chart sep G valid (before++a) (e::b) WW
    have ni := no_inject_before_10 hp chart sep GH C (valid _ _ WW).1 (by omega) e
    simpa only [BStarResetSchedule.run_append] using ni
  · intro a e b Z
    dsimp only
    intro q win own
    have WW : w=(before++a)++e::b := by rw [all,Z,←List.append_assoc]
    obtain ⟨mid,GH,C⟩ := history_prefix hp (before++a) (e::b) (WW ▸ G)
    have upper := prefix_pc_le hp chart sep G valid (before++a) (e::b) WW
    have ni := no_inject_before_10 hp chart sep GH C (valid _ _ WW).1 (by omega) e
    have eq : run x (before++a)=run (run x before) a := BStarResetSchedule.run_append _ _ _ _
    rw [←eq] at win ⊢
    exact owned_noninject_clean hp chart sep GH (valid _ _ WW).1 e q (ni q win own) own win

private theorem active_data_slot (g : Pair LongGeometry) (rsv : List (At Sheet))
    (D : DataClaim) (mem : D∈orderedData g rsv) (a : At Sheet) (hit : a∈D.slots) :
    activeSheet (geometry g a.side) a.occurrence=true := by
  cases sh : a.occurrence
  · rfl
  · simpa [activeSheet,sh] using BStarCopyPaddingFrame.data_active g rsv D a mem hit (.inl sh)
  · simpa [activeSheet,sh] using BStarCopyPaddingFrame.data_active g rsv D a mem hit (.inr sh)
  · rfl

private theorem raw_lane_active {base x : X} (e : Fin n)
    (same : ∀ i,Layout B base i=Layout B x i) (a : At Sheet)
    (A : activeSheet (geometry (oldPair B x e) a.side) a.occurrence=true) :
    activeSheet (longGeometry B (base (site e a.side))) a.occurrence=true := by
  rw [active_at_layout hp _ _ (same _)]
  cases side : a.side <;> simpa [oldPair,geometry,site,side] using A

private theorem raw_owner_transfer {base x : X} (e : Fin n)
    (same : ∀ i,Layout B base i=Layout B x i) (rsv : List (At Sheet))
    (D : DataClaim) (a : At Sheet) (mem : D∈orderedData (oldPair B x e) rsv)
    (dest : D.destination=some a) :
    dataOwner (oldH6 B base) (site e D.source.side) D.source.occurrence =
      dataOwner (oldH6 B base) (site e a.side) a.occurrence := by
  have H := reserved_hop_owner B x e rsv D a mem dest
  have heads : oldH6 B x=oldH6 B base := funext fun i=>(congrArg Prod.fst (same i)).symm
  rwa [heads] at H

/-- The data side of an original pre-INJECT mark cannot dirty a
drained owner. Both touched endpoints use the same owner and fixed
active-lane footprint, so every selected incoming sender is empty. -/
theorem empty_owner_clean_step {base x : X} (e : Fin n) (sep : e≠rightNeighbor e) (o : Int)
    (same : ∀ i,Layout B base i=Layout B x i)
    (clean : CleanOwner hp base x o) (empty : DrainedOwner hp base x o)
    (ready : let g := oldPair B x e
      let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
      ∀ q∈(arbitration (round g raw).prep).1,
        dataOwner (oldH6 B base) (site e q.claim.lane.side) q.claim.lane.occurrence=o →
          (selectedEffects (view raw) q).fault=false) :
    CleanOwner hp base (step x e) o := by
  intro i sh act own
  apply ring_clean_step hp x e i sh sep (clean i sh act own)
  dsimp only
  intro a loc sheet
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have emptyA : (view raw a).mobile=.empty := by
    change (view ((x e).long,(x (rightNeighbor e)).long) a).mobile=.empty
    rw [BStarCopyRightMark.old_access,loc,sheet]
    exact (empty i sh ((active_at_layout hp i sh (same i)).symm.trans act) own).1
  refine ⟨fun q Q L=>ready q Q (by rw [L,loc,sheet]; exact own),?_⟩
  intro D mem
  refine ⟨fun _ _=>emptyA, fun _ _ _ bad=>(bad emptyA).elim,?_⟩
  intro v dest atA _ _
  subst v
  have owner := raw_owner_transfer hp e same _ D a mem dest
  rw [loc,sheet,own] at owner
  have hit : D.source∈D.slots := by simp [Claim.slots,dest]
  have active := raw_lane_active hp e same D.source (active_data_slot g _ D mem D.source hit)
  have E := (empty _ _ ((active_at_layout hp _ _ (same _)).symm.trans active) owner).1
  change (view ((x e).long,(x (rightNeighbor e)).long) D.source).mobile.isBad=false
  rw [BStarCopyRightMark.old_access,E]
  rfl

open BStarCopyDrainedHistory BStarCopyAttemptBand

private theorem preissue_no_winner {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} (G : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w .idle)
    (valid : ∀ a b,w=a++b →
      (∀ i,Layout B base i=Layout B (run x a) i) ∧ Band (run x a) (S.getD 0 fall).1)
    (done : pc (run x w) (S.getD 0 fall).1=10)
    (a b : List (Fin n)) (W : w=a++b) (e : Fin n)
    (lower : 8≤pc (run x a) (S.getD 0 fall).1) : NoOwnerInject hp base (run x a) e o.val := by
  obtain ⟨mode,GA,GB⟩ := BStarGeneratedTapeCuts.split hp a b (W ▸ G)
  have C := BStarGeneratedTapeCuts.at_end hp GA
  have upper := prefix_pc_le hp chart sep G valid a b W
  have layout := (valid a b W).1
  by_cases small : pc (run x a) (S.getD 0 fall).1<10
  · exact no_inject_before_10 hp chart sep GA C layout small e
  · have equal : pc (run x a) (S.getD 0 fall).1=10 := by omega
    cases mode with
    | idle =>
      intro q win own
      have safe := BStarCopyOwnedFrozen.safe_idle hp chart layout e (site e q.claim.lane.side)
        q.claim.lane.occurrence own C.2
      have shape : q.claim.lane=⟨q.claim.lane.side,q.claim.lane.occurrence⟩ := by cases q.claim.lane; rfl
      rcases safe q.claim.lane.side rfl q win shape with H|H|H <;> rw [H] <;> decide
    | busy j z =>
      have code : j=10 := C.1.2.2.2.symm.trans equal
      subst j
      apply False.elim (BStarCopyRightMiddle.busy10_never_idle hp chart sep GB ?_ z rfl)
      intro u v U
      have all : w=(a++u)++v := by simp only [W,U,List.append_assoc]
      have top := prefix_pc_le hp chart sep G valid (a++u) v all
      obtain ⟨_,priorTape,_⟩ := BStarGeneratedTapeCuts.split hp u v (U ▸ GB)
      have bot := band_word hp chart sep priorTape (fun t z T=>by
        have E : w=(a++t)++(z++v) := by rw [all,T]; simp [List.append_assoc]
        simpa only [BStarResetSchedule.run_append] using valid (a++t) (z++v) E)
      rw [BStarResetSchedule.run_append step x a u] at top
      exact ⟨by omega,by omega⟩

/-- The genuine STOP/CLEAR/LOAD/ENABLE word leaves every active owned
lane drained and clean at an actual idle ISSUE10, including idle
waits before the selected launch. Every LOAD on that word is checked. -/
theorem clean_before_inject {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} (G : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w .idle)
    (valid : ∀ a b,w=a++b →
      (∀ i,Layout B base i=Layout B (run x a) i) ∧ Band (run x a) (S.getD 0 fall).1)
    (init : pc x (S.getD 0 fall).1≤6) (done : pc (run x w) (S.getD 0 fall).1=10) :
    CleanOwner hp base (run x w) o.val ∧ DrainedOwner hp base (run x w) o.val := by
  obtain ⟨pre,ack,tail,W,_,_,next⟩ := accepted_cut hp chart sep G valid 7 (by omega) (by omega)
  let lead := pre++[ack]
  have split : w=lead++tail := by rw [W]; simp [lead,List.append_assoc]
  have h8 : pc (run x lead) (S.getD 0 fall).1=8 := by
    rw [show run x lead=step (run x pre) ack from by rw [BStarResetSchedule.run_append]; rfl]
    exact next
  obtain ⟨_,H,rest⟩ := BStarGeneratedTapeCuts.split hp lead tail (split ▸ G)
  have leadOK (a b : List (Fin n)) (E : lead=a++b) :
      (∀ i,Layout B base i=Layout B (run x a) i) ∧ Band (run x a) (S.getD 0 fall).1 :=
    valid a (b++tail) (by simp only [split,E,List.append_assoc])
  let P (y : X) := CleanOwner hp base y o.val ∧ DrainedOwner hp base y o.val
  have I : P (run x lead) := ⟨clean_original_after_clear hp chart sep H leadOK init h8,
    cleared_original hp chart sep H leadOK init h8⟩
  rw [split,BStarResetSchedule.run_append]
  apply run_property hp tail P I
  intro a e b T state
  have E : w=(lead++a)++e::b := by simp only [split,T,List.append_assoc]
  obtain ⟨_,GA,_⟩ := history_prefix hp (lead++a) (e::b) (E ▸ G)
  have L := (valid _ _ E).1
  have L' := (valid ((lead++a)++[e]) b (by simp [E,List.append_assoc])).1
  rw [BStarResetSchedule.run_append step x lead a] at L
  rw [BStarResetSchedule.run_append step x (lead++a) [e],BStarResetSchedule.run_append step x lead a] at L'
  have low : 8≤pc (run x (lead++a)) (S.getD 0 fall).1 := by
    have N := prefix_pc_le hp chart sep GA
      (fun s t Q=>valid s (t++e::b) (by rw [E,Q,List.append_assoc])) lead a rfl
    omega
  have no := preissue_no_winner hp chart sep G valid done (lead++a) (e::b) E e low
  have safe := fun q win own=>owned_noninject_clean hp chart sep GA (valid _ _ E).1 e q (no q win own) own win
  rw [BStarResetSchedule.run_append step x lead a] at no
  have opened := empty_owner_clean_step hp e (sep e) o.val L state.1 state.2 (by
    simpa only [BStarResetSchedule.run_append] using safe)
  exact ⟨opened,drained_step hp e (sep e) o.val L L' state.2 no⟩

def OpenOwner (base x : X) (o : Int) : Prop :=
  ∀ i sh,activeSheet (longGeometry B (base i)) sh=true → dataOwner (oldH6 B base) i sh=o →
    (readLane (Sheet.index sh) (x i).long).gate=true

def EndReady (base x : X) (e : Fin n) (o : Int) : Prop :=
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  ∀ D∈orderedData g (reserved (round g raw).prep),D.kind=.ending →
    dataOwner (oldH6 B base) (site e D.source.side) D.source.occurrence=o →
      (view raw D.source).mobile=.empty

private def compactGeometry (h i l : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,h⟩,i,l,0,false⟩

private theorem ending_shape (g : Pair LongGeometry) (rsv : List (At Sheet)) (D : DataClaim)
    (sel : D∈orderedData g rsv) (kind : D.kind=.ending) :
    (D.source=L .ld ∧ ends g.1=true) ∨ (D.source=R .rd ∧ g.2.axes.h6=true) := by
  let test (g : Pair LongGeometry) (c : DataClaim) : Bool :=
    if c.kind==.ending then (c.source==L .ld && ends g.1) || (c.source==R .rd && g.2.axes.h6) else true
  have all (I T H J : Bool) :
      let q := (compactGeometry false I T,compactGeometry H J false)
      (dataClaims q).all (test q)=true := by
    cases I <;> cases T <;> cases H <;> cases J <;> decide +kernel
  obtain ⟨l,r⟩ := g
  let z := (compactGeometry false l.inside l.last,compactGeometry r.axes.h6 r.inside false)
  have raw : D∈dataClaims z := BStarLongFenceTopology.selected_data_raw _ _ _ sel
  have M : test (l,r) D=true := List.all_eq_true.mp (all l.inside l.last r.axes.h6 r.inside) D raw
  simpa [test,kind,Bool.or_eq_true,Bool.and_eq_true] using M

open BStarH6Ordinal BStarLongFiberOwner BStarCopyFIFO BStarCopyMarkedLedger
open BStarCopyRightStrip (addr)

private theorem same_data_word {n : Nat} (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (i j : Fin n) (sh : Sheet) (E : dataOwner h i sh=dataOwner h j sh) : word h i=word h j := by
  have inverse (u : Fin n) : addressWord (total h) (dataOwner h u sh) (dataDispl sh)=word h u :=
    (address_inverse (total h) (word h u) _).trans (Int.emod_eq_of_lt (word_range h u hh).1 (word_range h u hh).2)
  rw [←inverse i,←inverse j,E]

/-- Exact terminal vacancy from the two compatible old ledgers.
The symbolic label capacities force both last travel cells empty,
and the production chart identifies the only owned END sheets. -/
theorem end_ready_of_ledgers {L R : Type} (lDigits : L→BitVec 36) (rDigits : R→BitVec 36)
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (e : Fin n) (width : Nat) (pos : 0<width)
    (root : Fin n) (rootAt : root=(S.getD len fall).1)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<width) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=width))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → width≤oldOrdinal B base hh i+1)
    (same : ∀ i,Layout B base i=Layout B x i)
    {lPlan : List L} {rPlan : List R} {ls : Ledger L} {rs : Ledger R}
    (lSize : lPlan.length=width) (rSize : rPlan.length=width)
    (lOrd : Prefix lPlan ls) (rOrd : Prefix rPlan rs)
    (lMatch : BStarCopyLeftRetained.RetainedMatches lDigits x root width ls)
    (rMatch : BStarCopyRightRetained.RetainedMatches rDigits x root width rs) :
    EndReady hp base x e o.val := by
  intro D sel kind own
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  obtain ⟨_,_,_,_,ordLast,_,ownerLast,_,_,_⟩ := BStarFenceReceiverChart.endpoints hp chart pos
    (fun i=>(flags i).1) notShort
  let last := addr root (width-1)
  have bound : width-1<width := by omega
  have endLoc : last=BStarFenceReceiverChart.digitFrom (S.getD len fall).1 (width-1) := by
    rw [show last=addr root (width-1) from rfl,rootAt,BStarCopyLeftFence.addr_digits]
  rw [←endLoc] at ordLast ownerLast
  have leftMobile := (lMatch (width-1) bound).1
  have leftEmpty := terminal_empty lOrd (by omega)
  rw [lSize] at leftEmpty
  rw [leftEmpty] at leftMobile
  have rightMobile := (rMatch 0 pos).1
  have rightEmpty := terminal_empty rOrd (by omega)
  rw [rSize] at rightEmpty
  rw [Nat.sub_zero,rightEmpty] at rightMobile
  rcases ending_shape g _ D sel kind with ⟨source,atEnd⟩|⟨source,atHead⟩
  · have currentLast : (longGeometry B (x e)).last=true := by
      exact (Bool.and_eq_true_iff.mp atEnd).2
    have oldLast : (longGeometry B (base e)).last=true :=
      (congrArg (fun v : Bool×Bool×Bool=>v.2.2) (same e)).trans currentLast
    have ord : oldOrdinal B base hh e+1=width := of_decide_eq_true ((flags e).2.symm.trans oldLast)
    have ownerE : dataOwner (oldH6 B base) e .ld=o.val := by
      simpa [source,BStarLongClaims.L,site] using own
    have equalOrdinal : ordinal (oldH6 B base) hh e=ordinal (oldH6 B base) hh last := by
      change oldOrdinal B base hh e=oldOrdinal B base hh last
      omega
    have atLast : e=last := BStarNativeOffsetPhysical.same_ordinal_same_word _ hh e last
      equalOrdinal (same_data_word _ hh e last .ld (ownerE.trans ownerLast.symm))
    change (view ((x e).long,(x (rightNeighbor e)).long) D.source).mobile=.empty
    rw [BStarCopyRightMark.old_access,source]
    change (readLane (Sheet.index .ld) (x e).long).mobile=.empty
    rw [atLast]
    exact leftMobile
  · have isHead : oldH6 B base (rightNeighbor e)=true :=
      (congrArg Prod.fst (same (rightNeighbor e))).trans atHead
    have ownerK : commandOwner (oldH6 B base) (rightNeighbor e) 10=o.val := by
      have E : dataOwner (oldH6 B base) (rightNeighbor e) .rd=o.val := by
        simpa [source,BStarLongClaims.R,site] using own
      exact E
    have endpoint := (endpoint_spec (oldH6 B base) hh o 10).2.2 _ isHead ownerK
    have atRoot : rightNeighbor e=root := (congrArg Prod.fst (endpoint.trans chart.terminal.symm)).trans rootAt.symm
    change (view ((x e).long,(x (rightNeighbor e)).long) D.source).mobile=.empty
    rw [BStarCopyRightMark.old_access,source]
    change (readLane (Sheet.index .rd) (x (rightNeighbor e)).long).mobile=.empty
    rw [atRoot,←show addr root 0=root from Fin.ext (Nat.mod_eq_of_lt root.isLt)]
    exact rightMobile

/-- After ENABLE, all active owned data hops read open endpoints. A
selected END is the only ordinary data write that can dirty a clean
owner, and its emptiness is read from this mark's old ledger. -/
theorem open_owner_clean_step {base x : X} (e : Fin n) (sep : e≠rightNeighbor e) (o : Int)
    (same : ∀ i,Layout B base i=Layout B x i) (clean : CleanOwner hp base x o)
    (opened : OpenOwner hp base x o) (terminal : EndReady hp base x e o)
    (ready : let g := oldPair B x e
      let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
      ∀ q∈(arbitration (round g raw).prep).1,
        dataOwner (oldH6 B base) (site e q.claim.lane.side) q.claim.lane.occurrence=o →
          (selectedEffects (view raw) q).fault=false) :
    CleanOwner hp base (step x e) o := by
  intro i sh act own
  apply ring_clean_step hp x e i sh sep (clean i sh act own)
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  change ∀ a : At Sheet, site e a.side=i → a.occurrence=sh →
    (∀ q∈(arbitration (round g raw).prep).1,q.claim.lane=a →
      (selectedEffects (view raw) q).fault=false) ∧
    (∀ D∈orderedData g (reserved (round g raw).prep),SafeDataAt (view raw) a D)
  intro a loc sheet
  have aOwner : dataOwner (oldH6 B base) (site e a.side) a.occurrence=o := by rwa [loc,sheet]
  have viewGate (v : At Sheet) (V : activeSheet (geometry g v.side) v.occurrence=true)
      (W : dataOwner (oldH6 B base) (site e v.side) v.occurrence=o) : (view raw v).gate=true := by
    change (view ((x e).long,(x (rightNeighbor e)).long) v).gate=true
    rw [BStarCopyRightMark.old_access]
    exact opened _ _ (raw_lane_active hp e same v V) W
  refine ⟨fun q Q L=>ready q Q (by rwa [L]),?_⟩
  intro D mem
  refine ⟨?_,?_,?_⟩
  · intro kind atA
    have M := terminal D mem kind (atA.symm ▸ aOwner)
    rwa [atA] at M
  · intro v dest src _
    have owner := raw_owner_transfer hp e same _ D v mem dest
    rw [src,aOwner] at owner
    have T : v∈D.slots := by simp [Claim.slots,dest]
    have S : a∈D.slots := by simp [Claim.slots,dest,src]
    have A := viewGate a (active_data_slot g _ D mem a S) aOwner
    have G := viewGate v (active_data_slot g _ D mem v T) owner.symm
    simp [A,G]
  · intro v dest atA _ _
    subst v
    have owner := (raw_owner_transfer hp e same _ D a mem dest).trans aOwner
    have S : D.source∈D.slots := by simp [Claim.slots,dest]
    have act := raw_lane_active hp e same D.source (active_data_slot g _ D mem D.source S)
    change (view ((x e).long,(x (rightNeighbor e)).long) D.source).mobile.isBad=false
    rw [BStarCopyRightMark.old_access]
    exact (clean _ _ act owner).2.1

/-- Clean decoded bytes on the same generated COPY continuation. The
original idle ISSUE10 is authenticated by STOP/CLEAR/LOAD/ENABLE.
The only data premise on later marks is the old terminal vacancy.
The chosen INJECT's readiness is exactly the previous source theorem. -/
theorem clean_copy_word {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (lead tail : List (Fin n)) {m : Mode}
    (idle : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle lead .idle)
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle (lead++tail) m)
    (valid : ∀ a b,lead++tail=a++b →
      (∀ i,Layout B base i=Layout B (run x a) i) ∧ Band (run x a) (S.getD 0 fall).1)
    (init : pc x (S.getD 0 fall).1=6) (issue : pc (run x lead) (S.getD 0 fall).1=10)
    (terminal : ∀ a e b,tail=a++e::b → EndReady hp base (run x (lead++a)) e o.val)
    (prepared : ∀ a e b,tail=a++e::b → ∀ j,
      Current hp base (fun t=>S.getD t fall) len (run x (lead++a)) (.busy 10 (.out j)) →
      ∀ C : CommandClaim,S.getD j fall=address e C.source →
        FreshOrderedPrefix.ReadyPort (oldPair B (run x (lead++a)) e)
          (((run x (lead++a)) e).long,((run x (lead++a)) (rightNeighbor e)).long) C) :
    CleanOwner hp base (run x (lead++tail)) o.val := by
  have front (a b : List (Fin n)) (E : lead=a++b) :
      (∀ i,Layout B base i=Layout B (run x a) i) ∧ Band (run x a) (S.getD 0 fall).1 :=
    valid a (b++tail) (by rw [E,List.append_assoc])
  have old := (clean_before_inject hp chart sep idle front (by omega) issue).1
  rw [BStarResetSchedule.run_append]
  apply run_property hp tail (fun y=>CleanOwner hp base y o.val) old
  intro a e b T state
  have W : lead++tail=(lead++a)++e::b := by rw [T,List.append_assoc]
  obtain ⟨now,GA,I⟩ := history_prefix hp (lead++a) (e::b) (W ▸ G)
  have localValid (u v : List (Fin n)) (E : lead++a=u++v) :
      (∀ i,Layout B base i=Layout B (run x u) i) ∧ Band (run x u) (S.getD 0 fall).1 :=
    valid u (v++e::b) (by rw [W,E,List.append_assoc])
  have late := prefix_pc_le hp chart sep GA localValid lead a rfl
  have allOpen : OpenOwner hp base (run x (lead++a)) o.val :=
    FreshPreparation.gates_after_enable hp chart sep GA localValid init (by omega)
  have prep : ∀ C : BStarLongPrep.Offer,
      C∈(arbitration (round (oldPair B (run x (lead++a)) e)
        (((run x (lead++a)) e).long,((run x (lead++a)) (rightNeighbor e)).long)).prep).1 →
      dataOwner (oldH6 B base) (site e C.claim.lane.side) C.claim.lane.occurrence=o.val →
      (selectedEffects (view (((run x (lead++a)) e).long,((run x (lead++a)) (rightNeighbor e)).long)) C).fault=false := by
    intro C win own
    exact owned_copy_prep_clean hp chart sep GA (valid _ _ W).1 e
      (fun j mode D loc=>prepared a e b T j (mode ▸ I) D loc) C own win
  rw [←BStarResetSchedule.run_append step x lead a] at state ⊢
  exact open_owner_clean_step hp e (sep e) o.val (valid _ _ W).1 state allOpen (terminal a e b T) prep

private theorem mapped_sheet (g : LongGeometry) (k : Fin 11) (sh : Sheet)
    (H : fenceSheet g k=some sh) : activeSheet g sh=true ∧ dataDispl sh=cmdDispl k := by
  have rows (inside : Bool) : ∀ (j : Fin 11) (s : Sheet),
      fenceSheet (compactGeometry false inside false) j=some s →
        activeSheet (compactGeometry false inside false) s=true ∧ dataDispl s=cmdDispl j := by
    cases inside <;> decide +kernel
  exact rows g.inside k sh H

/-- A real pointed FENCE inspection reads the open gate and clean
error latch of the same owned physical sheet. The production owner
displacement agrees at every mapped command port. -/
theorem pointed_inspection_clean {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (e : Fin n) (k : Nat) (bound : k≤len)
    (a : AtK) (loc : S.getD k fall=address e a) (sh : Sheet)
    (inspect : fenceSheet (geometry (oldPair B x e) a.side) a.occurrence=some sh)
    (same : ∀ i,Layout B base i=Layout B x i)
    (openAll : OpenOwner hp base x o.val) (cleanAll : CleanOwner hp base x o.val) :
    let lane := view ((x e).long,(x (rightNeighbor e)).long) (⟨a.side,sh⟩ : At Sheet)
    lane.gate=true ∧ CleanLane lane := by
  let j := site e a.side
  let v : At Sheet := ⟨a.side,sh⟩
  obtain ⟨active,displ⟩ := mapped_sheet _ _ _ inspect
  have act := raw_lane_active hp e same v active
  have length := chart.length
  have mem : S.getD k fall∈S := by
    have K : k<S.length := by omega
    rw [← @List.getElem_eq_getD _ S k K fall]
    exact List.getElem_mem _
  have owner := (chart.entries _ mem).2
  rw [loc] at owner
  have data : dataOwner (oldH6 B base) j sh=o.val := by
    unfold dataOwner
    rw [displ]
    exact owner
  dsimp only
  rw [BStarCopyRightMark.old_access]
  exact ⟨openAll j sh act data,cleanAll j sh act data⟩

end L4.Height.FreshFenceGuards
