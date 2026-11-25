import Leader.L4.Height.FreshAttempt
import Leader.L4.BStarAcquireAckAncestry
import Leader.L4.BStarCopyGateAuthority
import Leader.L4.BStarCopyOwnedFrozen
import Leader.L4.BStarResetNoFault

namespace L4.Height.FreshAcquireTour
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongCommand BStarLongCommandData BStarLongGrant BStarLongPrep
open BStarLongTransport BStarLongLiteral BStarLongLayout
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarAcquireRailCoverage BStarAcquireForwardTrace BStarAcquireMarkedSample
open BStarAcquireLatch BStarResetChartTouch BStarResetChartIndex
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarResetMarkAdapter BStarResetRailRing
open BStarLongFixedRouting BStarOwnerControlHistory BStarSeparatingRail BStarResetSchedule
open BStarLongDoor BStarClearanceSource BStarAcquireSource
open BStarSeparatorControl (anyTag)

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step
local notation "bit" => BStarGrantBirth.bit
local notation "slot" => BStarResetNoAcquire.slot

/-- The only old rival conditions used by an ACQUIRE sample. At a
reader we also exclude a new writer proposal on this same mark. -/
def RivalsClear (x : X) (i : Fin n) (port : Fin 3) : Prop :=
  if port=1 then bit x i 0=0 ∧ bit x i 2=0
  else bit x i 1=0 ∧ BStarResetNoAcquire.NoAcquireAt x i 1

/-- Zero grants on the as-yet-unvisited grant slots of the target chart. -/
def PendingZero (x : X) (S : List (Pos n)) (fall : Pos n) (len k : Nat) : Prop :=
  ∀ j, k≤j → j≤len → ∀ i port, S.getD j fall=(i,slot port) → bit x i port=0

private theorem advance_mark {x : X} {addr : Nat→Pos n} {len k j op : Nat}
    {e : Fin n}
    (E : Event hp addr len x e (.busy op (.out k)) (.busy op (.out j))) :
    BStarSeparatingRail.Advance len (.out k) (.out j) := by
  cases E with
  | transit _ _ _ _ S =>
    cases S with
    | cons _ _ A _ tail => cases tail; exact A

private theorem index_mem {S : List (Pos n)} {fall : Pos n} {len j : Nat}
    (L : S.length=len+1) (jL : j≤len) : S.getD j fall∈S := by
  rw [←List.getElem_eq_getD (h:=show j<S.length by omega)]
  exact List.getElem_mem _

private theorem same_slot {a b : AtK} (side : a.side=b.side)
    (occ : a.occurrence.val=b.occurrence.val) : a=b := by
  obtain ⟨s,j⟩ := a
  obtain ⟨t,k⟩ := b
  cases side
  exact congrArg (At.mk s) (Fin.ext occ)

private theorem healthy_offered (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (f : Payload)
    (F : BStarAcquireHop.Healthy f) (H : (C,.advance f)∈gated g raw) :
    (C,.advance f)∈(round g raw).offered := by
  have ok : C.source∉(round g raw).faults := by
    intro bad
    change C.source∈prepFaults (view raw) (round g raw).prep at bad
    simp only [prepFaults,BStarResetNoFault.arb_no_losers g raw,List.map_nil,List.nil_append] at bad
    obtain ⟨a,mem,origin⟩ := List.mem_map.mp bad
    obtain ⟨D,q,_,Q,_,kind,_,fromD,_,_⟩ :=
      BStarCopyOwnedFrozen.winner_origin g raw a (List.mem_filter.mp mem).1
    have CX := (gated_mem g raw C _).mp H
    have DX := (gated_mem g raw D _).mp Q
    have same := BStarResetNoFault.origin_unique g D C DX.1 CX.1 (fromD.symm.trans origin)
    subst D
    have eq := BStarLongCommand.Offer.advance.inj (DX.2.trans CX.2.symm)
    subst q
    simp [F.2.1,acquire,prepOf] at kind
  have unchanged : cancel (round g raw).faults (C,.advance f)=(C,.advance f) := by
    change (if C.source∈(round g raw).faults then (C,BStarLongCommand.Offer.advance failedPayload) else (C,BStarLongCommand.Offer.advance f))=(C,BStarLongCommand.Offer.advance f)
    exact if_neg ok
  exact List.mem_map.mpr ⟨(C,.advance f),H,unchanged⟩

private theorem no_same_port_release (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (port : Fin 3) (f : Payload) (F : BStarAcquireHop.Healthy f)
    (loc : C.source.occurrence.val=port.val) (old : readK raw C.source=.forward f) :
    requested (round g raw).offered C.source.side port releaseOp=false := by
  apply Bool.eq_false_iff.mpr
  intro req
  obtain ⟨D,_,q,_,side,occ,_,_,Q,rel⟩ :=
    BStarReleaseOrigin.pre_grant_release_origin g raw C.source.side port req
  have addr : D.source=C.source := same_slot side (occ.trans loc.symm)
  change readK raw D.source=.forward q at Q
  rw [addr,old] at Q
  have eq := Token.forward.inj Q
  subst q
  have impossible := F.2.1.symm.trans rel.2
  exact (by decide : acquire≠releaseOp) impossible

/-- With its old port still zero, an actual selected header hop samples
a win. A selected RREL at the same port is impossible on the mark. -/
theorem selected_sample_wins (x : X) (e : Fin n) (C : CommandClaim) (D : AtK)
    (f : Payload) (F : BStarAcquireHop.Healthy f)
    (H : C∈orderedCommands (oldPair B x e)) (dst : C.destination=some D)
    (old : readK ((x e).long,(x (rightNeighbor e)).long) C.source=.forward f)
    (port : Fin 3) (loc : C.source.occurrence.val=port.val)
    (header : (geometry (oldPair B x e) C.source.side).axes.h6=true)
    (self : bit x (site e C.source.side) port=0)
    (rivals : RivalsClear x (site e C.source.side) port) :
    ((event (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long) C).toList.all
      Visit.wins)=true := by
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have noDoor : C.kind≠.door := by
    rw [(BStarAcquireReturn.link_shape g C D H dst).2.1]
    decide
  have gate := BStarAcquireLandingHop.gated_acquire_advance g raw C f H noDoor old F
  have offered := healthy_offered g raw C f F gate
  have ask : requested (round g raw).offered C.source.side port acquire=true :=
    List.any_eq_true.mpr ⟨(C,.advance f),offered,by simp [loc,F.1,F.2.1]⟩
  have rel := no_same_port_release g raw C port f F loc old
  have rawAt : BStarLongGrant.atOld raw C.source.side=(x (site e C.source.side)).long := by
    cases h : C.source.side <;> rfl
  have eqOld (j : Fin 3) (Z : bit x (site e C.source.side) j=0) :
      original (BStarLongGrant.atOld raw C.source.side) j=false := by
    unfold original
    rw [rawAt]
    change (bit x (site e C.source.side) j).getLsbD 0=false
    rw [Z]
    rfl
  have W : BStarAcquireHop.won g raw (round g raw).offered C port=true := by
    unfold BStarAcquireHop.won
    by_cases P : port=1
    · subst port
      have R := (show bit x (site e C.source.side) 0=0 ∧
          bit x (site e C.source.side) 2=0 from rivals)
      exact FreshAttempt.acquire_wins _ _ _ 1 (eqOld _ self) (eqOld _ self) ask rel
        (by simp [eqOld _ R.1,eqOld _ R.2])
    · rw [RivalsClear,if_neg P] at rivals
      have R := rivals
      exact FreshAttempt.acquire_wins _ _ _ port (eqOld _ self) (eqOld _ R.1) ask rel
        (by simp only [if_neg P]; exact FreshAttempt.no_request_at hp x e C.source.side 1 R.2)
  have hlt : C.source.occurrence.val<3 := by rw [loc]; exact port.isLt
  have same : (⟨C.source.occurrence.val,hlt⟩ : Fin 3)=port := Fin.ext loc
  change ((event g raw C).toList.all Visit.wins)=true
  simp [event,hlt,show (geometry g C.source.side).axes.h6=true from header,same,W]

/-- A port still pending after an outward step retains its released
zero. A birth would require a selected old ACQUIRE at the pointer.
Such a selection leaves Trail, so it cannot remain pending. -/
theorem pending_zero_step {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (e : Fin n)
    (sep : e≠rightNeighbor e) (k l : Nat) (f : Payload)
    (I : Current hp base (fun j=>S.getD j fall) len x (.busy acquire (.out k)))
    (J : Current hp base (fun j=>S.getD j fall) len (step x e) (.busy acquire (.out l)))
    (E : Event hp (fun j=>S.getD j fall) len x e (.busy acquire (.out k)) (.busy acquire (.out l)))
    (F : project (fun j=>S.getD j fall) x k=.forward f)
    (healthy : BStarAcquireHop.Healthy f)
    (Z : PendingZero x S fall len k) :
    PendingZero (step x e) S fall len l := by
  intro j pending bounded i port atJ
  have A := advance_mark hp E
  have mono : k≤l := by cases A <;> omega
  have before := Z j (Nat.le_trans mono pending) bounded i port atJ
  apply Classical.byContradiction
  intro new
  obtain ⟨s,atSite,_,_,C,q,mem,side,occ,hf,op⟩ :=
    BStarGrantBirth.mark_birth hp x e i port sep before new
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have req : requested (round g raw).offered s port acquire=true :=
    List.any_eq_true.mpr ⟨(C,.advance q),mem,by simp [side,occ,hf,op]⟩
  obtain ⟨D,offered,old,selected,atSide,atPort,preOff,_,oldAt,_⟩ :=
    BStarReleaseOrigin.pre_grant_acquire_origin g raw s port req
  have Dloc : address e D.source=(i,slot port) :=
    Prod.ext ((congrArg (site e) atSide).trans atSite) (Fin.ext atPort)
  have atD : S.getD j fall=address e D.source := atJ.trans Dloc.symm
  have oldRead : project (fun t=>S.getD t fall) x j=.forward old := by
    change readK raw D.source=.forward old at oldAt
    exact (congrArg (atCursor x) atD).trans ((old_read x e D.source).symm.trans oldAt)
  have eq : j=k := (pointed_unique_forward _ _ _ I.2.1 I.2.2 j bounded).mp ⟨old,oldRead⟩
  have same : l=k := by omega
  subst j
  subst l
  have own := (chart.entries _ (index_mem (fall:=fall) chart.length bounded)).2
  rw [atD] at own
  obtain ⟨d,dst⟩ : ∃ d,D.destination=some d := by
    rcases selected_endpoint_or_link B base x hh I.1.1 o e D selected own with door|stop|⟨d,dst,_⟩
    · change (D,.advance offered)∈(gated g raw).map (cancel (round g raw).faults) at preOff
      obtain ⟨⟨Q,a⟩,M,H⟩ := List.mem_map.mp preOff
      have keep : (cancel (round g raw).faults (Q,a)).1=Q := by
        cases a <;> simp [cancel] <;> split <;> rfl
      have claim := keep.symm.trans (congrArg Prod.fst H)
      subst Q
      have doorOnly : gatedAt g raw D=.door (bound g (readK raw) D.source) := by
        unfold gatedAt classifyOld
        simp [door.1,classify,checkOffer,bound,readK,oldTokens]
      rw [((gated_mem g raw D a).mp M).2,doorOnly] at H
      cases H
    · have z : D.source.occurrence.val=10 :=
        (BStarAcquireChainEndpoints.terminal g D selected stop.2.1
          (by rw [stop.1]; decide)).2.2.2
      have := port.isLt
      omega
    · exact ⟨d,dst⟩
  have readF : readK raw D.source=.forward f :=
    (old_read x e D.source).trans ((congrArg (atCursor x) atD).symm.trans F)
  have trail := (BStarAcquireMarkedPath.marked_hop hp x e sep D d f selected dst readF healthy).1
  have trailAt : project (fun t=>S.getD t fall) (step x e) k=.trail :=
    (congrArg (atCursor (step x e)) atD).trans trail
  obtain ⟨g',oldForward⟩ := J.2.1.2.1
  exact Token.noConfusion (trailAt.symm.trans oldForward)

/-- A completed outward interval, replayed on the actual old pairs.
The induction couples the sampled itinerary with pending physical
zeros, so the win premise is discharged before the payload moves. -/
theorem busy_out_all_wins {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {z d : Cursor}
    (P : BusyOnly hp base (fun j=>S.getD j fall) len acquire x z w d) :
    ∀ k l f, z=.out k → d=.out l →
      project (fun j=>S.getD j fall) x k=.forward f → BStarAcquireHop.Healthy f →
      PendingZero x S fall len k →
      (∀ pre e tail,w=pre++e::tail → ∀ i port,
        oldH6 B (run x pre) i=true →
        commandOwner (oldH6 B base) i (slot port)=o.val →
        RivalsClear (run x pre) i port) →
      ∃ ps vs, Trace hp base x (S.getD k fall) w (run x w) (S.getD l fall) ps vs ∧
        vs.all Visit.wins=true := by
  revert sep
  induction P with
  | nil I =>
    intro _ k l f K L F H Z R
    have eq := Cursor.out.inj (K.symm.trans L)
    subst l
    exact ⟨[],[],.done _ _,rfl⟩
  | @cons raw z d final e w I E tail ih =>
    intro sep k l f K L F healthy zero rivals
    subst z
    obtain ⟨j,J⟩ := BStarAcquireHistorySample.busy_no_back_to_out hp tail ⟨l,L⟩
    subst d
    have adv := advance_mark hp E
    let addr := fun t=>S.getD t fall
    let g := oldPair B raw e
    let bytes : Pair (BitVec LW) := ((raw e).long,(raw (rightNeighbor e)).long)
    have endMark := busy_start hp tail
    have Q : ∀ i≤len,anyTag.F (project addr (step raw e) i) ↔ i=j :=
      pointed_unique_forward _ _ _ endMark.2.1 endMark.2.2
    have old (t : Nat) (a : AtK) (A : addr t=address e a) :
        readK bytes a=project addr raw t :=
      (old_read raw e a).trans ((congrArg (atCursor raw) A).symm)
    have nextZero := pending_zero_step hp chart e (sep e) k j f I endMark E F healthy zero
    have nextRivals (pre : List (Fin n)) (m : Fin n) (rest : List (Fin n)) (W : w=pre++m::rest) :
        ∀ i port,oldH6 B (run (step raw e) pre) i=true →
          commandOwner (oldH6 B base) i (slot port)=o.val →
          RivalsClear (run (step raw e) pre) i port :=
      rivals (e::pre) m rest (congrArg (List.cons e) W)
    by_cases link : linkAt hp raw e addr len k
    · obtain ⟨kl,C,D,mem,dst,A,B'⟩ := link
      have oldF := (old _ _ A).trans F
      have hop := BStarAcquireMarkedPath.marked_hop hp raw e (sep e) C D f mem dst oldF healthy
      let f' := BStarAcquireHop.argUpdate g bytes (round g bytes).offered C f
      have nextHealthy : BStarAcquireHop.Healthy f' :=
        BStarAcquireHealthy.actual_hop_healthy g bytes (round g bytes).offered C f healthy
      have nextF : project addr (step raw e) (k+1)=.forward f' :=
        (congrArg (atCursor (step raw e)) B').trans hop.2
      have eq := (Q (k+1) (by omega)).mp ⟨f',nextF⟩
      have sample : ((event g bytes C).toList.all Visit.wins)=true := by
        by_cases low : C.source.occurrence.val<3
        · cases header : (geometry g C.source.side).axes.h6
          · simp [event,low,header]
          · let port : Fin 3 := ⟨C.source.occurrence.val,low⟩
            have atPort : S.getD k fall=(site e C.source.side,slot port) := A
            have owner := (chart.entries _ (index_mem (fall:=fall) chart.length (Nat.le_of_lt kl))).2
            rw [atPort] at owner
            have isHeader : oldH6 B raw (site e C.source.side)=true := by
              cases h : C.source.side <;>
                simpa [g,oldPair,geometry,site,oldH6,longGeometry,h] using header
            exact selected_sample_wins hp raw e C D f healthy mem dst oldF port rfl header
              (zero k (Nat.le_refl _) (by omega) _ _ atPort) (rivals [] e w rfl _ port isHeader owner)
        · simp [event,low]
      obtain ⟨ps,vs,ht,wins⟩ :=
        ih sep (k+1) l f' (congrArg Cursor.out eq.symm) L nextF nextHealthy
          (by rw [eq]; exact nextZero) nextRivals
      have av := Trace.hop C D (sep e) (fun i=>(I.1.1 i).symm) mem dst
        (show Trace hp base (step raw e) (address e D) w _ (addr l) ps vs from by
          rw [←B']; exact ht)
      refine ⟨address e C.source::ps,(event g bytes C).toList++vs,?_,?_⟩
      · change Trace hp base raw (addr k) (e::w) _ (addr l) _ _
        rw [A]
        exact av
      · simp [List.all_append,sample,wins]
    · have noT : k=len → ¬onTerminal hp raw e addr len := by
        intro atEnd T
        obtain ⟨C,mem,kind,noDst,occ,atC⟩ := T
        have eq : j=k := by
          cases adv
          · rfl
          · have bound := endMark.2.1.1
            omega
        have FF : anyTag.F (project addr (step raw e) len) := by
          rw [atEnd.symm.trans eq.symm]
          exact endMark.2.1.2.1
        obtain ⟨q,postF⟩ := FF
        have rawOld : readK bytes C.source=.forward f := (old len _ atC).trans (atEnd ▸ F)
        obtain ⟨_,reply,_,_⟩ := BStarAcquireReturn.raw_terminal_joined k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
          (raw e,raw (rightNeighbor e)) C f occ noDst kind healthy mem rawOld
        have postR := (congrArg (atCursor (step raw e)) atC).trans
          ((new_read B raw e (sep e) C.source).symm.trans reply)
        exact Token.noConfusion (postR.symm.trans postF)
      obtain ⟨N,frame⟩ := BStarAcquireHistorySample.silent_at hp chart e (sep e)
        acquire k I.1 f I.2.1 F healthy link noT
      have F' : project addr (step raw e) k=.forward f := frame.trans F
      have eq := (Q k I.2.1.1).mp ⟨f,F'⟩
      obtain ⟨ps,vs,ht,wins⟩ :=
        ih sep k l f (congrArg Cursor.out eq.symm) L F' healthy
          (by rw [eq]; exact nextZero) nextRivals
      exact ⟨ps,vs,.idle N frame ht,wins⟩

/-- A genuine RREL clears each target slot. Its zero persists through
the preceding PACE and ADMIT lead and through the launch itself. -/
theorem launch_pending_zero {base released : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (cleared : ∀ i port,commandOwner (oldH6 B base) i (slot port)=o.val →
      bit released i port=0)
    (lead : List (Fin n))
    (setup : GeneratedOwner hp base (fun j=>S.getD j fall) len released .idle lead .idle)
    (preAcquire : ∀ a e b,lead=a++e::b → ∀ m,
      GeneratedOwner hp base (fun j=>S.getD j fall) len released .idle a m →
        ∀ z,m≠.busy acquire z)
    (launch : Fin n) :
    PendingZero (step (run released lead) launch) S fall len 0 := by
  intro k _ bound i port loc
  have own := (chart.entries _ (index_mem (fall:=fall) chart.length bound)).2
  rw [loc] at own
  have before : bit (run released lead) i port=0 := by
    apply FreshAttempt.owned_zero_without_acquire hp chart sep [] lead i port own (cleared i port own)
    intro a e b W
    obtain ⟨m,G,I⟩ := BStarCopyGateAuthority.history_prefix hp a (e::b) (W ▸ setup)
    exact ⟨m,G,I,preAcquire a e b W m G⟩
  have idle := BStarGeneratedTapeCuts.at_end hp setup
  have N := FreshAttempt.owned_no_acquire hp chart sep setup idle i port own (by intro z H; cases H)
  apply Classical.byContradiction
  intro after
  exact BStarResetNoAcquire.no_win_at hp _ launch i port N
    (BStarGrantBirth.mark_birth hp _ launch i port (sep launch) before after)

/-- The first completed ACQUIRE after the released setup succeeds on
its original raw word. The finite tape supplies the actual terminal
and consuming marks. The result retains the exact sampled itinerary. -/
theorem completed_fresh_tour {base released : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (cleared : ∀ i port,commandOwner (oldH6 B base) i (slot port)=o.val →
      bit released i port=0)
    (lead : List (Fin n))
    (setup : GeneratedOwner hp base (fun j=>S.getD j fall) len released .idle lead .idle)
    (preAcquire : ∀ a e b,lead=a++e::b → ∀ m,
      GeneratedOwner hp base (fun j=>S.getD j fall) len released .idle a m →
        ∀ z,m≠.busy acquire z)
    (launch : Fin n) (doorLaunch : launch=RearTrace.predecessor (S.getD 0 fall).1)
    (L : Launch ((run released lead) (S.getD 0 fall).1).long
      ((step (run released lead) launch) (S.getD 0 fall).1).long)
    (op : (ctrlOp.read ((run released lead) (S.getD 0 fall).1).long).toNat=acquire)
    (tour : List (Fin n))
    (busy : BusyOnly hp base (fun j=>S.getD j fall) len acquire
      (step (run released lead) launch) (.out 0) tour (.back 0))
    (rivals : ∀ a e b,tour=a++e::b → ∀ i port,
      oldH6 B (run (step (run released lead) launch) a) i=true →
      commandOwner (oldH6 B base) i (slot port)=o.val →
      RivalsClear (run (step (run released lead) launch) a) i port)
    (door : Fin n)
    (consume : Event hp (fun j=>S.getD j fall) len (run (step (run released lead) launch) tour)
      door (.busy acquire (.back 0)) .idle) :
    ∃ outward turn ret ps vs, tour=outward++turn::ret ∧
      Trace hp base (step (run released lead) launch) (S.getD 0 fall) outward
        (run (step (run released lead) launch) outward) (S.getD len fall) ps vs ∧
      vs.all Visit.wins=true ∧
      (∀ j : Fin 3,(vs.filter (fun v=>v.incidence.val==j.val)).length=1) ∧
      BStarResetControllerEntry.snapshot
        ((step (run (step (run released lead) launch) tour) door) (S.getD 0 fall).1).long =
        ((.empty,1),BitVec.ofNat 9 6) := by
  let before := run released lead
  let start := step before launch
  let root := (S.getD 0 fall).1
  have Z := launch_pending_zero hp chart sep cleared lead setup preAcquire launch
  have initialPacket : atCursor start (S.getD 0 fall)=.forward initPayload := by
    obtain ⟨_,a,arg,snap⟩ := L
    change initial (ctrlOp.read (before root).long).toNat (before root).long=some a at arg
    rw [op] at arg
    have eq : a=2^33 := (Option.some.inj (show some (2^33)=some a from arg)).symm
    subst a
    have H := (BStarResetChartService.root_header hp chart (busy_start hp busy).1.1).2
    change atSite (start root).long (S.getD 0 fall).2=_
    rw [H]
    have point := congrArg (fun q : (Token×BitVec 2)×BitVec 9=>q.1.1) snap
    change atSite (start root).long 0=forward (ctrlOp.read (before root).long).toNat (2^33) at point
    rw [op] at point
    exact point
  obtain ⟨outward,turn,ret,W,go,_,back⟩ := BStarAcquireAckAncestry.split_turn hp busy
  have rivalOut (a : List (Fin n)) (e : Fin n) (b : List (Fin n)) (A : outward=a++e::b) :
      ∀ i port,oldH6 B (run start a) i=true →
        commandOwner (oldH6 B base) i (slot port)=o.val → RivalsClear (run start a) i port :=
    rivals a e (b++turn::ret) (by rw [W,A,List.append_assoc,List.cons_append])
  obtain ⟨ps,vs,trace,allWin⟩ :=
    busy_out_all_wins hp chart sep go 0 len initPayload rfl rfl initialPacket
      BStarAcquireHealthy.initialized_healthy Z rivalOut
  have began : Found hp base (fun j=>S.getD j fall) len acquire before
      (launch::outward) (.out len) :=
    ⟨[],outward,launch,rfl,doorLaunch,L,op,go⟩
  obtain ⟨C,mem,kind,dst,occ,pos⟩ :=
    BStarAcquireAckAncestry.actual_turn hp chart sep began (busy_start hp back).2.1
  have final := FreshAttempt.successful_acquire_receipt hp chart sep trace initialPacket allWin turn
    C mem kind dst occ pos ret back door (by rwa [W,BStarResetSchedule.run_append] at consume)
  have rootSlot : (S.getD 0 fall).2.val=0 := by rw [chart.root]; rfl
  have rootHeader : oldH6 B base (S.getD 0 fall).1=true := by
    rw [chart.root]
    exact (endpoint_spec (oldH6 B base) hh o 0).1
  have lastSlot : (S.getD len fall).2.val=10 := by rw [chart.terminal]; rfl
  refine ⟨outward,turn,ret,ps,vs,W,trace,allWin,?_,?_⟩
  · exact capture_once hp trace rootSlot rootHeader lastSlot
  · rw [W,BStarResetSchedule.run_append]
    exact final

#print axioms selected_sample_wins
#print axioms pending_zero_step
#print axioms busy_out_all_wins
#print axioms launch_pending_zero
#print axioms completed_fresh_tour

end L4.Height.FreshAcquireTour

