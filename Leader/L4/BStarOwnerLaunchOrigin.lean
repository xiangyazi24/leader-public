import Leader.L4.BStarGeneratedOwner
import Leader.L4.BStarForwardProvenance
import Leader.L4.BStarGrantBirth
import Leader.L4.BStarReleaseOrigin

namespace L4.BStarOwnerLaunchOrigin
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing
open BStarSeparatingRail BStarSeparatorControl BStarResetSchedule BStarGeneratedOwner
open BStarLongDoor BStarClearanceSource BStarLongCommand

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- A physical suffix on which the same launch remains live. The
indexed steps cannot pass through idle and cannot include another
launch. -/
inductive BusyOnly (base : X) (addr : Nat → Pos n) (len op : Nat) :
    X → Cursor → List (Fin n) → Cursor → Prop
  | nil {x z} (I : Current hp base addr len x (.busy op z)) :
      BusyOnly base addr len op x z [] z
  | cons {x z d endC e w}
      (I : Current hp base addr len x (.busy op z))
      (E : Event hp addr len x e (.busy op z) (.busy op d))
      (tail : BusyOnly base addr len op (step x e) d w endC) :
      BusyOnly base addr len op x z (e::w) endC

def Found (base : X) (addr : Nat → Pos n) (len op : Nat) (x : X)
    (w : List (Fin n)) (z : Cursor) : Prop :=
  ∃ pre post e, w=pre++e::post ∧
    let old := BStarResetSchedule.run step x pre
    let new := step old e
    e=RearTrace.predecessor (addr 0).1 ∧
    Launch (old (addr 0).1).long (new (addr 0).1).long ∧
    (ctrlOp.read (old (addr 0).1).long).toNat=op ∧
    BusyOnly hp base addr len op new (.out 0) post z

private theorem found_cons (base : X) (addr : Nat → Pos n) (len op : Nat) (x : X)
    (w : List (Fin n)) (z : Cursor) (e : Fin n)
    (H : Found hp base addr len op (step x e) w z) :
    Found hp base addr len op x (e::w) z := by
  obtain ⟨pre,post,d,E,T⟩ := H
  exact ⟨e::pre,post,d,congrArg (List.cons e) E,T⟩

/-- Invert a busy ending without searching by payload bytes. An
idle-starting actual history must exhibit a genuine earlier own
launch, with an uninterrupted old-mark busy suffix. -/
theorem extract {base : X} {addr : Nat → Pos n} {len : Nat}
    {x : X} {a : Mode} {w : List (Fin n)} {op : Nat} {z : Cursor}
    (H : GeneratedOwner hp base addr len x a w (.busy op z)) :
    Found hp base addr len op x w z ∨
      ∃ init, a=.busy op init ∧ BusyOnly hp base addr len op x init w z := by
  generalize E : Mode.busy op z = dest at H
  induction H with
  | endpoint I =>
    cases E
    exact .inr ⟨z,rfl,.nil I⟩
  | next I T R ih =>
    rcases ih E with F|⟨init,D,Htail⟩
    · exact .inl (found_cons hp _ _ _ _ _ _ _ _ F)
    · subst D
      cases T with
      | launch same L => exact .inl ⟨[],_,_,rfl,same,L,rfl,Htail⟩
      | transit pc cur dest live S =>
        exact .inr ⟨_,rfl,.cons I (Event.transit op _ _ live S) Htail⟩
      | arrived_hold pc ne =>
        exact .inr ⟨.back 0,rfl,.cons I (Event.arrived_hold op ne) Htail⟩

theorem from_idle {base : X} {addr : Nat → Pos n} {len : Nat}
    {x : X} {w : List (Fin n)} {op : Nat} {z : Cursor}
    (H : GeneratedOwner hp base addr len x .idle w (.busy op z)) :
    Found hp base addr len op x w z := by
  rcases extract hp H with F|⟨_,E,_⟩
  · exact F
  · cases E

open BStarForwardProvenance BStarLongClaims BStarLongTransport BStarLongRouting
open BStarLongCommandData BStarLongEvents BStarResetQuiet BStarResetQuietTable BStarResetIdleRing

private theorem bind_back (g : LongGeometry) (j : Fin 11) (t : Token) (p : Payload)
    (E : BStarLongCommand.bind g j t=.forward p) (H : p.fault=0) :
    ∃ q, t=.forward q ∧ q.fault=0 ∧ q.opcode=p.opcode := by
  have no : fault false ≠ .forward p := by
    intro e
    unfold fault at e
    cases e
    contradiction
  cases t with
  | empty => contradiction
  | trail => contradiction
  | reply q =>
    simp only [BStarLongCommand.bind] at E
    split at E
    · contradiction
    · split at E <;> contradiction
  | forward q =>
    let n := q.opcode.toNat
    let r := q.race.toNat
    let ok := if gate n j g then decide (1≤r ∧ r≤5) else r==0
    change (if q.fault != 0 || decide (n≥413) || q.outcome != 0 || !ok then fault false
      else match forwardWidth n q.argument.toNat with
        | none => fault false
        | some w => .forward (cropped q w))=.forward p at E
    split at E
    · exact (no E).elim
    · split at E
      · exact (no E).elim
      · cases E
        exact ⟨q,rfl,H,rfl⟩

private theorem observe_back (g : LongGeometry) (a : AtK) (p q : Payload)
    (H : observe a g p=some q) : Back p q := by
  unfold observe at H
  split at H
  · dsimp only at H
    let s := if a.side==.left then 3 else 2
    change (if p.race.toNat==1 then some {p with race:=BitVec.ofNat 3 s}
        else if (p.race.toNat==2 || p.race.toNat==3) && p.race.toNat != s then
          some {p with race:=BitVec.ofNat 3 (p.race.toNat+2)} else none)=some q at H
    split at H
    · cases H; exact fun f => ⟨f,rfl⟩
    · split at H
      · cases H; exact fun f => ⟨f,rfl⟩
      · contradiction
  · contradiction

private def Origin (old new : Token) : Prop :=
  ∀ p, new=.forward p → p.fault=0 →
    ∃ q, old=.forward q ∧ q.fault=0 ∧ q.opcode=p.opcode

private theorem fold_origin (a : AtK) (old : Token) (ws : List KWrite) (k : BitVec 52)
    (H : Origin old (decode k))
    (W : ∀ w∈ws,w.1=a → Origin old w.2) :
    Origin old (decode (ws.foldl (fun k w => putRaw k a w) k)) := by
  induction ws generalizing k with
  | nil => exact H
  | cons b ws ih =>
    apply ih
    · by_cases J : a=b.1
      · simpa [putRaw,J,decode_encode] using W b List.mem_cons_self J.symm
      · simpa [putRaw,J] using H
    · exact fun w hw => W w (List.mem_cons_of_mem _ hw)

private theorem quiet_routing_origin (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (a : AtK) (M : avoids a (middle g raw)) :
    Origin (readK raw a)
      (decode ((routing g raw).foldl (fun k w => putRaw k a w) (readRaw raw a))) := by
  apply fold_origin
  · intro p E H
    exact ⟨p,E,H,rfl⟩
  intro w hw wa p W H
  rw [routing_parts] at hw
  rcases List.mem_append.mp hw with pre|obs
  · rcases List.mem_append.mp pre with norm|mid
    · unfold normalization at norm
      rcases List.mem_append.mp norm with nm|nm
      · obtain ⟨z,_,E⟩ := List.mem_filterMap.mp nm
        change (if isFault (bound g (readK raw) z) then some (z,bound g (readK raw) z)
          else none)=some w at E
        split at E
        · rename_i faulty
          have D := Option.some.inj E
          subst w
          change z=a at wa
          subst z
          change bound g (readK raw) a=.forward p at W
          simp [W,isFault,H] at faulty
        · contradiction
      · obtain ⟨z,_,E⟩ := List.mem_map.mp nm
        subst w
        contradiction
    · exact (M w mid wa).elim
  · obtain ⟨z,_,E⟩ := List.mem_filterMap.mp obs
    split at E
    · contradiction
    · split at E
      · rename_i q oldBound
        cases U : observe z (geometry g z.side) q <;>
          simp only [U,Option.map_some,Option.map_none] at E
        · contradiction
        · have Q := Option.some.inj E
          subst w
          change z=a at wa
          subst z
          change Token.forward _ = Token.forward p at W
          cases W
          have L := observe_back _ _ _ _ U H
          obtain ⟨v,V,T,Z⟩ := bind_back _ _ _ _ oldBound L.1
          exact ⟨v,V,T,Z.trans L.2⟩
      · contradiction

theorem joined_idle_origin (k₁ k₂ t₂ J₁ J₂ r n p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r n p c₁)))
    (a : AtK) (after : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    avoids a (middle g raw) → DoorSafe g raw a →
    readK y a=.forward after → after.fault=0 →
    ∃ old, readK raw a=.forward old ∧ old.fault=0 ∧ old.opcode=after.opcode := by
  dsimp only
  intro M S F H
  change decode (readRaw _ a)=_ at F
  erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp x a S.valid] at F
  let g := Pair.map (longGeometry (bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp)) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have N := M
  have J := S.holds
  have T := quiet_routing_origin g raw a N after
  by_cases Z : a.occurrence.val=0
  · obtain ⟨side,j⟩ := a
    have K : j=(0:Fin 11) := Fin.ext Z
    subst j
    rw [BStarK0Frame.k0_routing_only _ _ side (J Z)] at F
    exact T F H
  · rw [raw_transit _ _ _ Z] at F
    exact T F H

open BStarClearanceForward

theorem joined_slot_origin (k₁ k₂ t₂ J₁ J₂ r tune p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r tune p c₁)))
    (a : AtK) (f : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r tune p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let out : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    DoorSafe g raw a → readK out a=.forward f → f.fault=0 →
    (∃ q, readK raw a=.forward q ∧ q.fault=0 ∧ q.opcode=f.opcode) ∨
    ∃ C q, C∈orderedCommands g ∧ C.destination=some a ∧
      readK raw C.source=.forward q ∧ q.fault=0 ∧ q.opcode=f.opcode := by
  dsimp only
  intro safe F hf
  let b := bStar k₁ k₂ t₂ J₁ J₂ r tune p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have joined := BStarAcquireReturn.joined_reads k₁ k₂ t₂ J₁ J₂ r tune p c₁ hp x a
    (fun hr h0 => by
      have E : a=R 0 := by cases a; simp_all [R]
      by_cases H : g.2.axes.h6=true
      · exact .inr (safe.valid E H)
      · exact .inl (Bool.eq_false_iff.mpr H))
  have out := joined.symm.trans F
  by_cases M : avoids a (middle g raw)
  · exact .inl (joined_idle_origin k₁ k₂ t₂ J₁ J₂ r tune p c₁ hp x a f M safe F hf)
  · have Ex : ∃ w∈middle g raw, w.1=a := by
      classical
      apply Classical.byContradiction
      intro bad
      exact M (fun w h E => bad ⟨w,h,E⟩)
    obtain ⟨w,hw,hit⟩ := Ex
    obtain ⟨⟨C,A⟩,act,hw⟩ := List.mem_flatMap.mp hw
    have hc : C∈orderedCommands g := by
      rw [←actualOffers_claims g raw]
      exact List.mem_map.mpr ⟨(C,A),act,rfl⟩
    cases A with
    | hold => cases hw
    | door t =>
      dsimp only [selected] at hw
      split at hw <;> cases hw
    | clear =>
      have U : w=(C.source,.empty) := by simpa [selected,direct] using hw
      subst w
      change C.source=a at hit
      subst a
      have dst := BStarAcquireReturn.last_selected_lands g raw C .clear C.source .empty [] []
        act (by simp [selected,direct]) (by simp)
      exact Token.noConfusion (dst.symm.trans out)
    | reverse t =>
      cases E : C.destination with
      | none => simp [selected,direct,E] at hw
      | some d =>
        have ne := (BStarAcquireReturn.link_shape g C d hc E).1
        obtain ⟨q,rfl⟩ := (BStarClearanceCommandFrame.reverse_origin g raw C d t E act).2
        have K := reverse_endpoints g raw C d (.reply q) E (Ne.symm ne) act
        simp only [selected,direct,E,List.mem_cons,List.not_mem_nil,or_false] at hw
        rcases hw with rfl|rfl
        · change C.source=a at hit
          subst a
          change decode (readRaw _ C.source)=_ at out
          rw [K.1,decode_encode] at out
          cases out
        · change d=a at hit
          subst a
          change decode (readRaw _ d)=_ at out
          rw [K.2,decode_encode] at out
          cases out
    | advance q =>
      change w∈advanceK g C (carried g raw C q) at hw
      cases E : C.destination with
      | none =>
        have H : w=(C.source,finish (carried g raw C q)) := by simpa [advanceK,E] using hw
        subst w
        change C.source=a at hit
        subst a
        change decode (readRaw _ C.source)=_ at out
        rw [terminal_finish g raw C q E act,decode_encode] at out
        exact (BStarCommitLineage.terminal_not_forward _ _ out).elim
      | some d =>
        have ne := (BStarAcquireReturn.link_shape g C d hc E).1
        simp only [advanceK,E,List.mem_cons,List.not_mem_nil,or_false] at hw
        rcases hw with rfl|rfl
        · change C.source=a at hit
          subst a
          change decode (readRaw _ C.source)=_ at out
          rw [(move_lands g raw C q d E act (Ne.symm ne)).1,decode_encode] at out
          cases out
        · change d=a at hit
          subst a
          obtain ⟨v,H⟩ := joined_hop k₁ k₂ t₂ J₁ J₂ r tune p c₁ hp x C d q f E act F hf
          exact .inr ⟨C,v,hc,E,H⟩

open BStarSeparatorQuiet BStarResetChartService

/-- In a live WAIT on the settled chart, every healthy new F at an
owner address has an old healthy F of identical opcode on that
same owner chart, regardless of the selected raw mark. -/
theorem ring_origin {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (e : Fin n) (he : e≠rightNeighbor e) (op : Nat) (z : Cursor)
    (live : z≠.back 0) (W : Waiting hp base (S.getD 0 fall).1 op x)
    (G : Good anyTag len (project (fun j => S.getD j fall) x) z)
    (i : Nat) (hi : i≤len) (pay : Payload)
    (F : project (fun j => S.getD j fall) (step x e) i=.forward pay)
    (H : pay.fault=0) :
    ∃ j≤len, ∃ q, project (fun j => S.getD j fall) x j=.forward q ∧
      q.fault=0 ∧ q.opcode=pay.opcode := by
  let addr := fun j => S.getD j fall
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let g := oldPair B x e
  have active (a : AtK) (E : addr i=address e a) :
      ∃ j≤len, ∃ q, project addr x j=.forward q ∧ q.fault=0 ∧ q.opcode=pay.opcode := by
    have dst := (new_read B x e he a).trans ((congrArg (atCursor (step x e)) E).symm)
    have safe := ((frames_any hp chart W.1 e z live G W.2.1 W.2.2.1).safe i hi a E).2
    have old (j : Nat) (r : AtK) (eq : addr j=address e r) :
        readK raw r=project addr x j :=
      (old_read x e r).trans ((congrArg (atCursor x) eq).symm)
    rcases joined_slot_origin k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e)) a pay safe
        (dst.trans F) H with ⟨q,Q,A,O⟩|⟨K,q,mem,des,Q,A,O⟩
    · exact ⟨i,hi,q,(old _ _ E).symm.trans Q,A,O⟩
    · have L := BStarAcquireReturn.link_shape g K a mem des
      have own : a∈K.slots := by simp [Claim.slots,des]
      rcases touches hp chart W.1 e i hi K a mem own E with D|T|U|⟨j,J,inc⟩
      · have Z := D.2.1
        rw [L.2.1] at Z
        cases Z
      · obtain ⟨eqi,Kt,memT,kindT,noneT,_,srcT⟩ := T
        have hit := BStarResetMarkAdapter.address_inj e he (E.symm.trans (eqi ▸ srcT))
        have eq := BStarAcquireIncidence.same_claim g K Kt a mem memT own (by simp [Claim.slots,hit])
        subst Kt
        rw [noneT] at des
        cases des
      · obtain ⟨_,Kt,d,memT,desT,srcT,_⟩ := U
        have hit := BStarResetMarkAdapter.address_inj e he (E.symm.trans srcT)
        have eq := BStarAcquireIncidence.same_claim g K Kt a mem memT own (by simp [Claim.slots,desT,hit])
        subst Kt
        exact (L.1 hit).elim
      · obtain ⟨jlen,Kt,d,memT,desT,srcT,dstT⟩ := inc
        have hit : a=d := BStarResetMarkAdapter.address_inj e he (E.symm.trans (J ▸ dstT))
        have eq := BStarAcquireIncidence.same_claim g K Kt a mem memT own (by simp [Claim.slots,desT,hit])
        subst Kt
        exact ⟨j,by omega,q,(old _ _ srcT).symm.trans Q,A,O⟩
  by_cases l : (addr i).1=e
  · exact active (L (addr i).2) (Prod.ext l rfl)
  · by_cases rr : (addr i).1=rightNeighbor e
    · exact active (R (addr i).2) (Prod.ext rr rfl)
    · exact ⟨i,hi,pay,(idle_off_pair hp x e (addr i) l rr).symm.trans F,H,rfl⟩

theorem busy_start {base : X} {addr : Nat → Pos n} {len op : Nat}
    {x : X} {z d : Cursor} {w : List (Fin n)}
    (P : BusyOnly hp base addr len op x z w d) : Current hp base addr len x (.busy op z) := by
  cases P with
  | nil I => exact I
  | cons I _ _ => exact I

theorem busy_origin {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {op : Nat} {z d : Cursor} {w : List (Fin n)}
    (P : BusyOnly hp base (fun j => S.getD j fall) len op x z w d)
    (i : Nat) (hi : i≤len) (pay : Payload)
    (F : project (fun j => S.getD j fall) (BStarResetSchedule.run step x w) i=.forward pay)
    (hf : pay.fault=0) :
    ∃ j≤len, ∃ q, project (fun j => S.getD j fall) x j=.forward q ∧
      q.fault=0 ∧ q.opcode=pay.opcode := by
  induction P with
  | nil I => exact ⟨i,hi,pay,F,hf,rfl⟩
  | @cons a z d endC e w I E tail ih =>
    obtain ⟨j,hj,q,Q,hq,opc⟩ := ih F
    cases E with
    | transit _ _ _ live _ =>
      obtain ⟨s,hs,v,V,hv,eq⟩ := ring_origin hp C e (sep e) op z live I.1 I.2.1 j hj q Q hq
      exact ⟨s,hs,v,V,hv,eq.trans opc⟩
    | arrived_hold _ =>
      exact (BStarOwnerControlHistory.pointed_backward_no_forward _ len 0
        (busy_start hp tail).2.1 j hj ⟨q,Q⟩).elim

/-- A healthy old front on a recovered owner chart is the genuine
same-opcode launch. The actual old/new rows, not byte equality, carry
this fact across intervening physical marks. -/
theorem healthy_forward_origin {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {m : Mode} {w : List (Fin n)}
    (P : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (now : Current hp base (fun j => S.getD j fall) len (BStarResetSchedule.run step x w) m)
    (i : Nat) (hi : i≤len) (pay : Payload)
    (F : project (fun j => S.getD j fall) (BStarResetSchedule.run step x w) i=.forward pay)
    (wanted : Nat) (hf : pay.fault=0) (A : pay.opcode.toNat=wanted) :
    m=.busy wanted (.out i) ∧
      Found hp base (fun j => S.getD j fall) len wanted x w (.out i) := by
  cases m with
  | idle =>
    rw [now.2 i hi] at F
    cases F
  | busy op z =>
    cases z with
    | back k =>
      exact (BStarOwnerControlHistory.pointed_backward_no_forward _ len k now.2.1 i hi ⟨pay,F⟩).elim
    | out k =>
      have eq : i=k := (BStarOwnerControlHistory.pointed_unique_forward _ len k now.2.1 now.2.2 i hi).mp ⟨pay,F⟩
      subst k
      have hist := from_idle hp P
      obtain ⟨pre,post,e,split,atDoor,L,pc,busy⟩ := hist
      let old := BStarResetSchedule.run step x pre
      let start := step old e
      have Eq : BStarResetSchedule.run step x w=BStarResetSchedule.run step start post := by
        rw [split,BStarResetSchedule.run_append]
        rfl
      have oldF := busy_origin hp C sep busy i hi pay (Eq ▸ F) hf
      obtain ⟨j,hj,q,Q,_,opEq⟩ := oldF
      have cur := busy_start hp busy
      have j0 : j=0 := (BStarOwnerControlHistory.pointed_unique_forward _ len 0 cur.2.1 cur.2.2 j hj).mp ⟨q,Q⟩
      subst j
      obtain ⟨_,arg,_,snap⟩ := L
      have root := (root_header hp C cur.1.1).2
      change atSite (start (S.getD 0 fall).1).long (S.getD 0 fall).2=.forward q at Q
      rw [root] at Q
      have Bt : forward (ctrlOp.read (old (S.getD 0 fall).1).long).toNat arg=.forward q :=
        (congrArg (fun t : (Token × BitVec 2) × BitVec 9 => t.1.1) snap).symm.trans Q
      injection Bt with payload
      have key : q.opcode=BitVec.ofNat 9 op :=
        (congrArg Payload.opcode payload).symm.trans (congrArg (BitVec.ofNat 9) pc)
      have bound : op<512 := by
        have R := (ctrlOp.read (old (S.getD 0 fall).1).long).isLt
        change (ctrlOp.read (old (S.getD 0 fall).1).long).toNat<512 at R
        exact pc ▸ R
      have P' : op=wanted := by
        have K := congrArg BitVec.toNat (key.symm.trans opEq)
        rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound,A] at K
        exact K
      have PE : Mode.busy op (.out i)=Mode.busy wanted (.out i) := congrArg (fun n => Mode.busy n (.out i)) P'
      exact ⟨PE,from_idle hp (PE ▸ P)⟩

theorem healthy_capture_origin {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {m : Mode} {w : List (Fin n)}
    (P : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (now : Current hp base (fun j => S.getD j fall) len (BStarResetSchedule.run step x w) m)
    (i : Nat) (hi : i≤len) (pay : Payload)
    (F : project (fun j => S.getD j fall) (BStarResetSchedule.run step x w) i=.forward pay)
    (hf : pay.fault=0) (A : pay.opcode.toNat=acquire) :
    m=.busy acquire (.out i) ∧
      Found hp base (fun j => S.getD j fall) len acquire x w (.out i) :=
  healthy_forward_origin hp C sep P now i hi pay F acquire hf A

open BStarLongGrant BStarGrantBirth

/-- The actual 0→1 grant mark witnesses its old arbitration win. If the
literal grant port belongs to the chart of the recovered owner, the
winning ACQUIRE traces back to its genuine own ISSUE5 on the same tape. -/
theorem grant_birth_origin {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {m : Mode} {w : List (Fin n)}
    (P : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (now : Current hp base (fun j => S.getD j fall) len (BStarResetSchedule.run step x w) m)
    (i : Nat) (hi : i≤len) (e v : Fin n) (j : Fin 3)
    (addr : S.getD i fall=(v,⟨j.val,by have := j.isLt; omega⟩))
    (old : bit (BStarResetSchedule.run step x w) v j=0)
    (new : bit (step (BStarResetSchedule.run step x w) e) v j≠0) :
    WonAt hp (BStarResetSchedule.run step x w) e v j ∧
    m=.busy acquire (.out i) ∧
      Found hp base (fun j => S.getD j fall) len acquire x w (.out i) := by
  let y := BStarResetSchedule.run step x w
  have won : WonAt hp y e v j := mark_birth hp y e v j (sep e) old new
  refine ⟨won,?_⟩
  obtain ⟨s,siteEq,header,win,c,p,mem,src,occ,healthy,opcode⟩ := won
  let g := oldPair B y e
  let raw : Pair (BitVec LW) := ((y e).long,(y (rightNeighbor e)).long)
  have req : requested (round g raw).offered s j acquire=true := by
    apply List.any_eq_true.mpr
    refine ⟨(c,.advance p),mem,?_⟩
    simp [src,occ,healthy,opcode]
  obtain ⟨K,q,f,_,ks,kj,_,_,F,H,A⟩ :=
    BStarReleaseOrigin.pre_grant_acquire_origin g raw s j req
  have slot : address e K.source=S.getD i fall := by
    rw [addr]
    exact Prod.ext (show site e K.source.side=v from ks.symm ▸ siteEq) (Fin.ext kj)
  have read : oldTokens raw K.source=.forward f := F
  have R : project (fun j => S.getD j fall) y i=.forward f :=
    (congrArg (atCursor y) slot.symm).trans ((old_read y e K.source).symm.trans read)
  exact healthy_capture_origin hp C sep P now i hi f R H A

end L4.BStarOwnerLaunchOrigin
