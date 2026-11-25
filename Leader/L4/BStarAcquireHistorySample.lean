import Leader.L4.BStarOwnerLaunchOrigin
import Leader.L4.BStarWonCapture
import Leader.L4.BStarAcquireNonRouting

namespace L4.BStarAcquireHistorySample
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongTransport BStarLongRouting BStarLongEvents
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing
open BStarSeparatingRail BStarSeparatorControl BStarSeparatorQuiet
open BStarResetChartService BStarResetQuietAdapter BStarResetQuietTable
open BStarAcquireNonRouting BStarResetQuiet

private theorem fold_away (a : AtK) (w : List KWrite) (b : BitVec 52)
    (H : ∀ t∈w,t.1≠a) :
    w.foldl (fun b t => putRaw b a t) b=b := by
  induction w generalizing b with
  | nil => rfl
  | cons t w ih =>
    simp only [List.foldl_cons,putRaw,Ne.symm (H t List.mem_cons_self),if_false]
    exact ih _ (fun q h => H q (List.mem_cons_of_mem _ h))

theorem joined_silent (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (a : AtK) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    DoorSafe g raw a → (∀ w∈routing g raw,w.1≠a) →
    readK (Pair.map LargeSite.long (largePair b x)) a=readK raw a := by
  dsimp only
  intro safe H
  by_cases not0 : a.occurrence.val≠0
  · exact joined_untouched_other k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x a not0 H
  · have zero : a.occurrence.val=0 := Classical.not_not.mp not0
    change decode (readRaw _ a)=decode (readRaw _ a)
    apply congrArg decode
    rw [joined_work_raw k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x a safe.valid]
    obtain ⟨s,j⟩ := a
    have E : j=(0 : Fin 11) := Fin.ext zero
    subst j
    rw [BStarK0Frame.k0_routing_only _ _ s (safe.holds zero)]
    exact fold_away _ _ _ H

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- Exact full payload retention on each real mark which selects
neither successor nor terminal of the healthy owned ACQUIRE. -/
theorem silent_at {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (e : Fin n) (he : e≠rightNeighbor e) (op k : Nat)
    (W : Waiting hp base (S.getD 0 fall).1 op x) (pay : Payload)
    (G : Good anyTag len (project (fun j => S.getD j fall) x) (.out k))
    (F : project (fun j => S.getD j fall) x k=.forward pay) (H : BStarAcquireHop.Healthy pay)
    (noL : ¬ linkAt hp x e (fun j => S.getD j fall) len k)
    (noT : k=len → ¬ onTerminal hp x e (fun j => S.getD j fall) len) :
    let a := S.getD k fall
    BStarAcquireMarkedPath.NoDeparture (b:=B) x e a ∧
    atCursor (step x e) a=atCursor x a := by
  dsimp only
  let addr := fun j => S.getD j fall
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have old (j : Nat) (a : AtK) (E : addr j=address e a) :
      readK raw a=project addr x j :=
    (old_read x e a).trans ((congrArg (atCursor x) E).symm)
  have noOut (a : AtK) (E : addr k=address e a) (cl : CommandClaim)
      (hcl : cl∈orderedCommands g) (src : cl.source=a) : cl.kind=.door := by
    subst a
    rcases touches hp C W.1 e k G.1 cl cl.source hcl (by simp [Claim.slots]) E with D|T|L|⟨i,ik,I⟩
    · exact D.2.1
    · exact (noT T.1 T.2).elim
    · exact (noL L).elim
    · obtain ⟨_,J,d,mem,hd,_,dst⟩ := I
      have eq : cl.source=d := address_inj e he (E.symm.trans (ik ▸ dst))
      have same := BStarAcquireIncidence.same_claim g cl J cl.source hcl mem
        (by simp [Claim.slots]) (by simp [Claim.slots,hd,eq])
      subst J
      exact ((BStarAcquireReturn.link_shape g cl d hcl hd).1 eq.symm).elim
  constructor
  · rintro ⟨cl,q,mem,_,_,E⟩
    have hcl : cl∈orderedCommands g := by
      rw [←actualOffers_claims g raw]
      exact List.mem_map.mpr ⟨(cl,.advance q),mem,rfl⟩
    have nd := noOut cl.source E cl hcl rfl
    obtain ⟨_,G⟩ := BStarClearanceCommandFrame.advance_origin g raw cl q mem
    have dg : BStarLongLiteral.gatedAt g raw cl =
        .door (bound g (readK raw) cl.source) := by
      unfold BStarLongLiteral.gatedAt BStarLongLiteral.classifyOld
      simp [nd,classify,BStarLongCommandData.checkOffer,bound,readK,BStarLongCommandData.oldTokens]
    have Z := actual_door g raw (cl,.advance q) mem _ dg
    cases Z
  · have frame (a : AtK) (E : addr k=address e a) :
        project addr (step x e) k=project addr x k := by
      have MF := frames_any hp C W.1 e (.out k) (by intro zz; cases zz) G W.2.1 W.2.2.1
      obtain ⟨keep,safe⟩ := MF.safe k G.1 a E
      have noPred (cl : CommandClaim) (hc : cl∈orderedCommands g) (hd : cl.destination=some a) :
          readK raw cl.source=.trail := by
        obtain ⟨ne,kind,_⟩ := BStarAcquireReturn.link_shape g cl a hc hd
        rcases touches hp C W.1 e k G.1 cl a hc (by simp [Claim.slots,hd]) E with D|T|L|⟨i,ik,I⟩
        · rw [kind] at D; cases D.2.1
        · exact (noT T.1 T.2).elim
        · exact (noL L).elim
        · obtain ⟨_,J,d,mem,dh,src,dst⟩ := I
          have ed : a=d := address_inj e he (E.symm.trans (ik ▸ dst))
          have same := BStarAcquireIncidence.same_claim g cl J a hc mem
            (by simp [Claim.slots,hd]) (by simp [Claim.slots,dh,ed])
          subst J
          exact (old _ _ src).trans (G.2.2 i (by omega))
      have route := row_silent g raw a pay ((old _ _ E).trans F) H keep (noOut a E) noPred
      have post := (new_read B x e he a).trans ((congrArg (atCursor (step x e)) E).symm)
      exact post.symm.trans ((joined_silent k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
        (x e,x (rightNeighbor e)) a safe route).trans (old _ _ E))
    by_cases l : (addr k).1=e
    · exact frame (L (addr k).2) (Prod.ext l rfl)
    · by_cases r : (addr k).1=rightNeighbor e
      · exact frame (R (addr k).2) (Prod.ext r rfl)
      · exact BStarResetIdleRing.idle_off_pair hp x e (addr k) l r


open BStarOwnerLaunchOrigin BStarGeneratedOwner BStarAcquireMarkedPath BStarResetSchedule

private theorem seen_single {len : Nat} {x : X} {e : Fin n} {addr : Nat → Pos n}
    {z d : Cursor} (s : Seen step (project addr) anyTag len x z [e] d) :
    BStarSeparatingRail.Advance len z d := by
  cases s with
  | cons _ _ A _ rest =>
    cases rest
    exact A

theorem busy_no_back_to_out {base x : X} {addr : Nat → Pos n} {len op : Nat}
    {z d : Cursor} {w : List (Fin n)}
    (P : BusyOnly hp base addr len op x z w d) :
    (∃ j,d=.out j) → ∃ j,z=.out j := by
  induction P with
  | nil _ => exact id
  | cons I E P ih =>
    intro D
    obtain ⟨j,J⟩ := ih D
    cases E with
    | arrived_hold _ => cases J
    | transit _ _ _ _ S =>
      have A := seen_single hp S
      rw [J] at A
      cases A with
      | stay => exact ⟨_,rfl⟩
      | forward => exact ⟨_,rfl⟩

/-- Recover the exact old-mark itinerary and full capture fold on any
busy segment ending outward which starts with a healthy ACQUIRE.
The one-mark cursor alignment is checked against selected old claims,
even though the abstract history's Seen could carry a weaker Mark. -/
theorem busy_out_trace {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {z d : Cursor}
    (P : BusyOnly hp base (fun j => S.getD j fall) len acquire x z w d) :
    ∀ k l pay, z=.out k → d=.out l →
      project (fun j => S.getD j fall) x k=.forward pay →
      BStarAcquireHop.Healthy pay →
      ∃ (ps : List (Pos n)) (vs : List BStarAcquireLatch.Visit),
        BStarAcquireForwardTrace.Trace hp base x (S.getD k fall) w
          (BStarResetSchedule.run step x w) (S.getD l fall) ps vs := by
  induction P with
  | nil I =>
    intro k l f E D F h
    have Q := Cursor.out.inj (E.symm.trans D)
    subst l
    exact ⟨[],[],.done _ _⟩
  | @cons raw z d final e w I E tail ih =>
    intro k l f Z finalEq F healthy
    subst z
    obtain ⟨k',atOut⟩ := busy_no_back_to_out hp tail ⟨l,finalEq⟩
    subst d
    have adv : BStarSeparatingRail.Advance len (.out k) (.out k') := by
      cases E with
      | transit _ _ _ _ S => exact seen_single hp S
    let addr := fun j => S.getD j fall
    let pair := (raw e, raw (rightNeighbor e))
    let g := oldPair B raw e
    let bytes : Pair (BitVec LW) := ((raw e).long,(raw (rightNeighbor e)).long)
    have J := (busy_start hp tail).2.1
    have Jc := (busy_start hp tail).2.2
    have Q : ∀ i≤len, anyTag.F (project addr (step raw e) i) ↔ i=k' :=
      BStarOwnerControlHistory.pointed_unique_forward _ _ _ J Jc
    have old (i : Nat) (a : AtK) (E : addr i=address e a) :
        readK bytes a=project addr raw i :=
      (old_read raw e a).trans ((congrArg (atCursor raw) E).symm)
    by_cases link : linkAt hp raw e addr len k
    · obtain ⟨kl,A,b,mem,hd,src,dst⟩ := link
      have a := marked_hop hp raw e (sep e) A b f mem hd ((old _ _ src).trans F) healthy
      let pay' := BStarAcquireHop.argUpdate g bytes (BStarLongCommandData.round g bytes).offered A f
      have H' := BStarAcquireHealthy.actual_hop_healthy g bytes (BStarLongCommandData.round g bytes).offered A f healthy
      have F' : project addr (step raw e) (k+1)=.forward pay' :=
        (congrArg (atCursor (step raw e)) dst).trans a.2
      have eq := (Q (k+1) (by omega)).mp ⟨pay',F'⟩
      obtain ⟨ps,vs,ht⟩ := ih (k+1) l pay' (congrArg Cursor.out eq.symm) finalEq F' H'
      have av := BStarAcquireForwardTrace.Trace.hop A b (sep e) (fun i => (I.1.1 i).symm) mem hd
        (show Trace hp base (step raw e) (address e b) w _ (addr l) ps vs from by
          rw [←dst]; exact ht)
      refine ⟨address e A.source::ps,(BStarAcquireMarkedSample.event g bytes A).toList++vs,?_⟩
      change Trace hp base raw (addr k) (e::w) _ (addr l) _ _
      rw [src]
      exact av
    · have noT : k=len → ¬ onTerminal hp raw e addr len := by
        intro K t
        obtain ⟨T,mem,kind,hd,h10,hit⟩ := t
        have ksame : k'=k := by
          cases adv
          · rfl
          · have bound := J.1
            omega
        have FF : anyTag.F (project addr (step raw e) len) := by
          have eq : len=k' := K.symm.trans ksame.symm
          exact eq ▸ J.2.1
        obtain ⟨q,Q'⟩ := FF
        have rawOld : readK bytes T.source=.forward f := (old len _ hit).trans (K ▸ F)
        obtain ⟨d,D,_,_⟩ := BStarAcquireReturn.raw_terminal_joined k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
          pair T f h10 hd kind healthy mem rawOld
        have nD := (congrArg (atCursor (step raw e)) hit).trans ((new_read B raw e (sep e) T.source).symm.trans D)
        exact Token.noConfusion (nD.symm.trans Q')
      obtain ⟨N,S'⟩ := silent_at hp C e (sep e) acquire k I.1 f I.2.1 F healthy link noT
      have F' : project addr (step raw e) k=.forward f := S'.trans F
      have eq := (Q k I.2.1.1).mp ⟨f,F'⟩
      obtain ⟨ps,vs,ht⟩ := ih k l f (congrArg Cursor.out eq.symm) finalEq F' healthy
      exact ⟨ps,vs,.idle N S' ht⟩


open BStarClearanceSource BStarResetControllerEntry BStarAcquireSource BStarLongLayout BStarLongDoor

/-- A recovered exact ISSUE5 witness supplies the initial payload of
the literal sampled itinerary, with all genuine capture updates. -/
theorem found_out_trace {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {j : Nat}
    (F : Found hp base (fun j => S.getD j fall) len acquire x w (.out j)) :
    ∃ (pre post : List (Fin n)) (e : Fin n) (ps : List (Pos n)) (vs : List BStarAcquireLatch.Visit),
      w=pre++e::post ∧
      let preState := BStarResetSchedule.run step x pre
      let launched := step preState e
      Launch (preState (S.getD 0 fall).1).long (launched (S.getD 0 fall).1).long ∧
      atCursor launched (S.getD 0 fall)=.forward initPayload ∧
      BStarAcquireForwardTrace.Trace hp base launched (S.getD 0 fall) post
        (BStarResetSchedule.run step x w) (S.getD j fall) ps vs := by
  obtain ⟨pre,post,e,eq,_,L,op,P⟩ := F
  let old := BStarResetSchedule.run step x pre
  let z := step old e
  obtain ⟨I,a,H,snap⟩ := L
  have pc : (ctrlOp.read (old (S.getD 0 fall).1).long).toNat=acquire := op
  have A : a=2^33 := by
    change initial (ctrlOp.read (old (S.getD 0 fall).1).long).toNat _=some a at H
    rw [pc] at H
    exact (Option.some.inj (show some (2^33)=some a from H)).symm
  subst a
  have K := (root_header hp C (busy_start hp P).1.1).2
  have init : atCursor z (S.getD 0 fall)=.forward initPayload := by
    change atSite (z (S.getD 0 fall).1).long (S.getD 0 fall).2=_
    rw [K]
    have Q := congrArg (fun t : (Token × BitVec 2) × BitVec 9 => t.1.1) snap
    change atSite (z (S.getD 0 fall).1).long 0=
      forward (ctrlOp.read (old (S.getD 0 fall).1).long).toNat (2^33) at Q
    rw [pc] at Q
    exact Q
  obtain ⟨ps,vs,T⟩ := busy_out_trace hp C sep P 0 j _ rfl rfl init BStarAcquireHealthy.initialized_healthy
  have endEq : BStarResetSchedule.run step x w=BStarResetSchedule.run step z post := by
    rw [eq,BStarResetSchedule.run_append]
    rfl
  refine ⟨pre,post,e,ps,vs,eq,⟨I,2^33,H,snap⟩,init,?_⟩
  rw [endEq]
  exact T


/-- The terminal of the actual begun itinerary samples every port once.
The resulting reply is the exact fold; success requires every visit's
old-pair arbitration win. -/
theorem found_terminal {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)}
    (F : Found hp base (fun j => S.getD j fall) len acquire x w (.out len))
    (e : Fin n)
    (T : onTerminal hp (BStarResetSchedule.run step x w) e (fun j => S.getD j fall) len) :
    ∃ (vs : List BStarAcquireLatch.Visit) (receipt : Payload),
      (∀ j : Fin 3, (vs.filter (fun v => v.incidence.val==j.val)).length=1) ∧
      let payload := vs.foldl (fun q v => v.apply q) initPayload
      atCursor (step (BStarResetSchedule.run step x w) e) (S.getD len fall)=.reply receipt ∧
      finish payload=.reply receipt ∧ BStarAcquireReturn.ValidReply receipt ∧
      BStarAcquireLatch.latch payload=vs.all BStarAcquireLatch.Visit.wins := by
  obtain ⟨pre,post,d,ps,vs,_,_,init,trace⟩ := found_out_trace hp C sep F
  obtain ⟨cl,mem,kind,hd,occ,EQ⟩ := T
  have pos0 : (S.getD 0 fall).2.val=0 := by rw [C.root]; rfl
  have hbase : oldH6 B base (S.getD 0 fall).1=true := by
    rw [C.root]
    exact (endpoint_spec (oldH6 B base) hh o 0).1
  have z10 : (S.getD len fall).2.val=10 := by rw [C.terminal]; rfl
  obtain ⟨q,A,bp,C',D⟩ := completes_at hp trace init e (sep e) cl mem kind hd occ EQ
  exact ⟨vs,q,fun j => capture_once hp trace pos0 hbase z10 j,A,bp,C',D⟩

#print axioms busy_out_trace
#print axioms found_out_trace
#print axioms found_terminal
end L4.BStarAcquireHistorySample
