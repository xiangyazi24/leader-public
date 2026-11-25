import Leader.L4.BStarCommitOwnerOrigin
import Leader.L4.BStarCommitService
import Leader.L4.BStarBitUniqueGate
import Leader.L4.BStarBitCarry

namespace L4.BStarBitHealthyService
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongClaims
open BStarLongCommand BStarLongEvents BStarLongCommandData BStarLongTransport
open BStarLongLiteral BStarLongRouting

private theorem prep_fault_origin (g : Pair LongGeometry) (x : Pair (BitVec LW)) (j : AtK)
    (h : j∈(round g x).faults) :
    ∃ c q, c.source=j ∧ (c,.advance q)∈gated g x ∧
      ∃ op, prepOf q.opcode.toNat=some op := by
  let L := preparedBy g x (gated g x)
  have hf : j∈BStarLongPrep.prepFaults (BStarLongPrep.view x) L := h
  unfold BStarLongPrep.prepFaults at hf
  have selected_mem (o : BStarLongPrep.Offer)
      (h : o∈(BStarLongPrep.arbitration L).1) : o∈L := by
    have H : o∈(offers BStarLongPrep.offerPriority L) := by
      unfold BStarLongPrep.arbitration at h
      rw [BStarLongPrep.arbitrate_winners] at h
      exact (select_sublist _ _ _).subset h
    have general (xs : List BStarLongPrep.Offer) (h : o∈offers BStarLongPrep.offerPriority xs) : o∈xs := by
      induction xs with
      | nil => exact h
      | cons b rest ih =>
        change o∈insert BStarLongPrep.offerPriority b (offers BStarLongPrep.offerPriority rest) at h
        rcases (mem_insert BStarLongPrep.offerPriority b o _).mp h with h|h
        · exact List.mem_cons.mpr (.inl h)
        · exact List.mem_cons_of_mem _ (ih h)
    exact general L H
  have loser_mem (o : BStarLongPrep.Offer) (h : o∈(BStarLongPrep.arbitration L).2) :
      o∈L := by
    have H := (BStarLongPrep.arbitrate_losers [] (offers BStarLongPrep.offerPriority L)).subset h
    have general (xs : List BStarLongPrep.Offer) (h : o∈offers BStarLongPrep.offerPriority xs) : o∈xs := by
      induction xs with
      | nil => exact h
      | cons b rest ih =>
        change o∈insert BStarLongPrep.offerPriority b (offers BStarLongPrep.offerPriority rest) at h
        rcases (mem_insert BStarLongPrep.offerPriority b o _).mp h with h|h
        · exact List.mem_cons.mpr (.inl h)
        · exact List.mem_cons_of_mem _ (ih h)
    exact general L H
  have witness : ∃ o∈L, o.claim.origin=j := by
    rcases List.mem_append.mp hf with H|H
    · obtain ⟨o,ho,rfl⟩ := List.mem_map.mp H
      exact ⟨o,loser_mem o ho,rfl⟩
    · obtain ⟨o,ho,rfl⟩ := List.mem_map.mp H
      exact ⟨o,selected_mem o (List.mem_filter.mp ho).1,rfl⟩
  obtain ⟨o,ho,he⟩ := witness
  unfold L preparedBy at ho
  obtain ⟨⟨c,s⟩,hc,hO⟩ := List.mem_flatMap.mp ho
  cases s <;> simp only at hO
  all_goals try cases hO
  rename_i q
  unfold fieldOffers at hO
  split at hO
  · cases hO
  · split at hO
    · cases hO
    · rename_i op hOp
      obtain ⟨cl,hcl,rfl⟩ := List.mem_map.mp hO
      obtain ⟨sh,hsh,rfl⟩ := List.mem_map.mp hcl
      exact ⟨c,q,he,hc,op,hOp⟩

/-- Each actual non-door claim whose bound old forward token is BIT
selects that very payload, independent of other commands, the
destination's token, and the authorization at the body. -/
theorem bound_bit_selected (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (C : CommandClaim) (p : Payload) (M : C∈orderedCommands g) (nd : C.kind≠.door)
    (B : bound g (readK x) C.source=.forward p) (op : p.opcode.toNat=bitOp)
    (off : gate bitOp C.source.occurrence (geometry g C.source.side)=false) :
    (C,.advance p)∈actualOffers g x := by
  have D : depart (geometry g C.source.side) C.source.occurrence p=some p := by
    simp [depart,op,off]
  have cl : classifyOld g x C=.advance p := by
    change classify C _ (bound g (readK x) C.source) _=_
    simp [classify,nd,B,D]
  have gateEq : gatedAt g x C=.advance p := by
    unfold gatedAt
    rw [cl]
    simp [checkOffer,checkFence,op,bitOp]
  have cg : (C,.advance p)∈gated g x := (gated_mem g x C _).mpr ⟨M,gateEq.symm⟩
  have keep : C.source∉(round g x).faults := by
    intro bad
    obtain ⟨b,q,eq,hq,k,P⟩ := prep_fault_origin g x C.source bad
    obtain ⟨mb,Q⟩ := (gated_mem g x b _).mp hq
    have E := BStarAcquireIncidence.same_claim g b C b.source mb M
      (by simp [Claim.slots]) (by simp [Claim.slots,eq])
    subst b
    have eq := Offer.advance.inj (Q.trans gateEq)
    subst q
    simp [op,bitOp,prepOf] at P
  have pre : (C,.advance p)∈(round g x).offered :=
    List.mem_map.mpr ⟨(C,.advance p),cg,by
      change (if C.source∈(round g x).faults then (C,Offer.advance failedPayload) else (C,Offer.advance p))=_
      rw [if_neg keep]⟩
  exact List.mem_map.mpr ⟨(C,.advance p),pre,by
    by_cases h : C.source.occurrence.val<3
    · simp [BStarLongGrant.update,h,op,bitOp,acquire]
    · simp [BStarLongGrant.update,h]⟩

/-- Raw invariants needed to get a healthy bound BIT. Healthy opcode
and fault alone are insufficient: outcome, race, and packed descriptor
and bank shape must pass the actual binder. -/
theorem bind_bit (g : LongGeometry) (k : Fin 11) (p : Payload)
    (F : p.fault=0) (O : p.opcode.toNat=bitOp) (R : p.race=0) (T : p.outcome=0)
    (W : forwardWidth bitOp p.argument.toNat=some 1)
    (off : gate bitOp k g=false) :
    BStarLongCommand.bind g k (.forward p)=.forward (cropped p 1) := by
  have W' : forwardWidth 410 p.argument.toNat=some 1 := W
  have off' : gate 410 k g=false := off
  simp [BStarLongCommand.bind,F,O,R,T,W',off',bitOp]

/-- No successful publication is assumed. A well-formed literal old
BIT at any selected non-door claim yields a healthy actual offer. -/
theorem raw_bit_selected (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (C : CommandClaim) (p : Payload) (M : C∈orderedCommands g) (nd : C.kind≠.door)
    (F : p.fault=0) (O : p.opcode.toNat=bitOp) (R : p.race=0) (T : p.outcome=0)
    (W : forwardWidth bitOp p.argument.toNat=some 1)
    (H : readK x C.source=.forward p)
    (off : gate bitOp C.source.occurrence (geometry g C.source.side)=false) :
    (C,.advance (cropped p 1))∈actualOffers g x := by
  apply bound_bit_selected g x C (cropped p 1) M nd _ O off
  change BStarLongCommand.bind _ _ (readK x C.source)=_
  rw [H]
  exact bind_bit _ _ p F O R T W off

open BStarResetQuiet BStarClearanceForward

/-- Well-formed canonical BIT on an ordinary (non-race) address. -/
structure Wire (p : Payload) : Prop where
  fault : p.fault=0
  op : p.opcode.toNat=bitOp
  race : p.race=0
  outcome : p.outcome=0
  small : p.argument.toNat<2

private theorem selected_wire (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (p : Payload) (M : C∈orderedCommands g)
    (nd : C.kind≠.door) (H : Wire p) (old : readK raw C.source=.forward p)
    (off : gate bitOp C.source.occurrence (geometry g C.source.side)=false) :
    (C,.advance p)∈actualOffers g raw := by
  have croppedSelf : cropped p 1=p := by
    have argEq : BitVec.ofNat 34 (low p.argument.toNat 1)=p.argument := by
      rw [show low p.argument.toNat 1=p.argument.toNat from Nat.mod_eq_of_lt H.small]
      simp
    cases p
    simp_all [cropped]
  have E : forwardWidth bitOp p.argument.toNat=some 1 := by
    simp [forwardWidth,bitOp,admit]
  have sel := raw_bit_selected g raw C p M nd H.fault H.op H.race H.outcome E old off
  rwa [croppedSelf] at sel

/-- Every real joined link from a non-gate BIT address copies its
canonical packet, except landing at the gate sets race=1/argument=0
in that same mark. No assumption about a later terminal is used. -/
theorem joined_bit_link (k₁ k₂ t₂ J₁ J₂ r n p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r n p c₁)))
    (C : CommandClaim) (a : AtK) (pay : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    C∈orderedCommands g → C.destination=some a →
    gate bitOp C.source.occurrence (geometry g C.source.side)=false →
    readK raw C.source=.forward pay → Wire pay →
      readK y a=.forward (if gate bitOp a.occurrence (geometry g a.side)
        then {pay with race:=1,argument:=0} else pay) := by
  dsimp only
  intro cm dst off front H
  let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have shape := BStarAcquireReturn.link_shape g C a cm dst
  have sel := selected_wire g raw C pay cm (by rw [shape.2.1]; decide) H front off
  have V : a=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true := by
    intro E Z
    have J : a.occurrence.val=0 := congrArg (fun z : AtK => z.occurrence.val) E
    have W := (BStarAcquireJoinedHop.k0_dest g C a cm dst J).2
    simp [Z] at W
  have A := (move_lands g raw C pay a dst sel (Ne.symm shape.1)).2
  change decode (readRaw _ a)=_
  rw [joined_work_raw _ _ _ _ _ _ _ _ _ hp x a V,A,decode_encode,
    BStarBitCarry.carried_bit g raw C pay H.op]
  simp only [arrive,H.fault,H.op,beq_self_eq_true,Bool.true_and]
  split <;> rfl

open BStarClearanceSource BStarLongDoor BStarResetControllerEntry

/-- Genuine ISSUE410 starts with the canonical padded-zero packet. -/
theorem launched_wire (old new : BitVec LW) (op : (ctrlOp.read old).toNat=bitOp)
    (L : Launch old new) :
    ∃ p, atSite new 0=.forward p ∧ Wire p ∧ p.argument=0 := by
  obtain ⟨_,a,I,S⟩ := L
  rw [op] at I
  have eq : a=0 := (Option.some.inj (show some 0=some a from I)).symm
  subst a
  have R := congrArg (fun q : (Token × BitVec 2) × BitVec 9 => q.1.1) S
  change atSite new 0=forward (ctrlOp.read old).toNat 0 at R
  rw [op] at R
  exact ⟨_,R,⟨rfl,rfl,rfl,rfl,by decide⟩,rfl⟩

open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing
open BStarSeparatingRail BStarGeneratedOwner BStarOwnerLaunchOrigin
open BStarClearanceOffset BStarBitGateGeometry BStarBitUniqueGate
open BStarResetChartNomination BStarAcquireRailCoverage BStarSeparatingProgress

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- Positive actual cursor progress under a nominated mark outside the
gate, with exact packed landing, including first arrival at the gate. -/
theorem nominated_step {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (qx : Q x) (e : Fin n) (j : Nat) (pay : Payload)
    (cur : Current hp base (fun k=>S.getD k fall) len x (.busy bitOp (.out j)))
    (old : project (fun k=>S.getD k fall) x j=.forward pay) (well : Wire pay)
    (link : linkAt hp x e (fun k=>S.getD k fall) len j)
    (off : gate bitOp (S.getD j fall).2 (longGeometry B (x (S.getD j fall).1))=false) :
    let next := if gate bitOp (S.getD (j+1) fall).2 (longGeometry B (x (S.getD (j+1) fall).1))
      then {pay with race:=1,argument:=0} else pay
    Event hp (fun k=>S.getD k fall) len x e (.busy bitOp (.out j)) (.busy bitOp (.out (j+1))) ∧
      Current hp base (fun k=>S.getD k fall) len (step x e) (.busy bitOp (.out (j+1))) ∧
      project (fun k=>S.getD k fall) (step x e) (j+1)=.forward next := by
  dsimp only
  obtain ⟨J,K,a,mem,dest,src,dst⟩ := link
  have geom (u : AtK) (j : Nat) (E : S.getD j fall=address e u) :
      gate bitOp u.occurrence (geometry (oldPair B x e) u.side)=
      gate bitOp (S.getD j fall).2 (longGeometry B (x (S.getD j fall).1)) := by
    rw [E]
    cases u with
    | mk s k => cases s <;> rfl
  have R := (old_read x e K.source).trans ((congrArg (atCursor x) src).symm.trans old)
  have out := joined_bit_link k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e))
    K a pay mem dest ((geom K.source j src).trans off) R well
  change readK _ a=.forward (if gate bitOp a.occurrence (geometry (oldPair B x e) a.side)
    then {pay with race:=1,argument:=0} else pay) at out
  rw [geom a (j+1) dst] at out
  have post := (congrArg (atCursor (step x e)) dst).trans ((new_read B x e (sep e) a).symm.trans out)
  obtain ⟨m,ev,nxt⟩ := current_step hp C Q fiber closed sep qx e (.busy bitOp (.out j)) cur
  cases ev with
  | transit _ _ d live seen =>
    cases seen with
    | cons M go advance gd tail =>
      cases tail
      cases advance with
      | stay =>
        have empty := nxt.2.2 (j+1) (by omega) J
        exact Token.noConfusion (empty.symm.trans post)
      | forward => exact ⟨.transit _ _ _ live (.cons M go (.forward j) gd (.nil _ _)),nxt,post⟩
      | turn => exact (Nat.lt_irrefl _ J).elim

open BStarH6Ordinal

/-- The pre-gate service certificate is state-independent in its
nominations. The last step lands the exact initialized pending BIT,
rather than inferring it backwards from a successful terminal. -/
theorem ordered_to_gate {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (l : Nat) (L : l<len)
    (gateK : (S.getD l fall).2=1)
    (gateOrdinal : oldOrdinal B base hh (S.getD l fall).1=4)
    (p : Payload) (well : Wire p)
    (m : Nat) :
    ∀ (x : X) (j : Nat), j+(m+1)=l → Q x → correct (oldH6 B base) hh 5 x →
    Current hp base (fun k=>S.getD k fall) len x (.busy bitOp (.out j)) →
    project (fun k=>S.getD k fall) x j=.forward p →
    ∃ w : List (Fin n), w.length=m+1 ∧
      BusyOnly hp base (fun k=>S.getD k fall) len bitOp x (.out j) w (.out l) ∧
      Current hp base (fun k=>S.getD k fall) len (play x w) (.busy bitOp (.out l)) ∧
      project (fun k=>S.getD k fall) (play x w) l=.forward {p with race:=1,argument:=0} ∧
      ∀ (k : Nat) (h : k<w.length) (y : X), (∀ i, Layout B base i=Layout B y i) →
        linkAt hp y w[k] (fun t=>S.getD t fall) len (j+k) := by
  have one (x : X) (qx : Q x) (ready : correct (oldH6 B base) hh 5 x) :
      ∀ j≤len, gate bitOp (S.getD j fall).2 (longGeometry B (x (S.getD j fall).1))=true ↔ j=l := by
    intro j J
    have fixed : ∀ i,oldH6 B x i=oldH6 B base i := fun i => (congrArg Prod.fst (fiber x qx i)).symm
    have on : gate bitOp (S.getD l fall).2 (longGeometry B (x (S.getD l fall).1))=true := by
      rw [gateK]
      exact (bit_gate_iff hp hh fixed ready _ 1).mpr ⟨rfl,gateOrdinal⟩
    exact ⟨fun H => chart_no_second_gate hp C fixed ready J (Nat.le_of_lt L) H on,
      fun E => E.symm ▸ on⟩
  have stepReady (x : X) (qx : Q x) (e : Fin n) (ready : correct (oldH6 B base) hh 5 x) :
      correct (oldH6 B base) hh 5 (step x e) :=
    stable hp _ hh x e (sep e) (fun i => (congrArg Prod.fst (fiber x qx i)).symm)
      (BStarClearanceOffsetMask.leftFrame hp x e) ready
  have edge (x : X) (j : Nat) (J : j<l) (qx : Q x) (ready : correct (oldH6 B base) hh 5 x)
      (I : Current hp base (fun k=>S.getD k fall) len x (.busy bitOp (.out j)))
      (F : project (fun k=>S.getD k fall) x j=.forward p) :
      ∃ e, (∀ y : X, (∀ i, Layout B base i=Layout B y i) →
            linkAt hp y e (fun t=>S.getD t fall) len j) ∧
        Event hp (fun k=>S.getD k fall) len x e (.busy bitOp (.out j)) (.busy bitOp (.out (j+1))) ∧
        Current hp base (fun k=>S.getD k fall) len (step x e) (.busy bitOp (.out (j+1))) ∧
        project (fun k=>S.getD k fall) (step x e) (j+1)=
          .forward (if j+1=l then {p with race:=1,argument:=0} else p) := by
    have J' : j<len := by omega
    obtain ⟨e,N⟩ := nominate hp C head cont j (Nat.le_of_lt J')
    have nom (y : X) (H : ∀ i,Layout B base i=Layout B y i) :
        linkAt hp y e (fun k=>S.getD k fall) len j :=
      (mem_link hp y e _ len j).mp (by simpa only [if_pos J'] using N y H)
    have off := Bool.eq_false_iff.mpr (fun H => (Nat.ne_of_lt J) ((one x qx ready j (by omega)).mp H))
    obtain ⟨E,U,P⟩ := nominated_step hp C Q fiber closed sep qx e j p I F well (nom x (fiber x qx)) off
    exact ⟨e,nom,E,U,by simpa only [one x qx ready (j+1) (by omega)] using P⟩
  induction m with
  | zero =>
    intro x j J qx ready I F
    obtain ⟨e,nom,E,U,P⟩ := edge x j (by omega) qx ready I F
    have Eql : j+1=l := J
    rw [if_pos Eql] at P
    have T : BusyOnly hp base (fun k=>S.getD k fall) len bitOp x (.out j) [e] (.out (j+1)) := .cons I E (.nil U)
    refine ⟨[e],rfl,Eql ▸ T,Eql ▸ U,Eql ▸ P,?_⟩
    intro k hk y H
    have K : k=0 := by simp at hk; omega
    subst k
    exact nom y H
  | succ m ih =>
    intro x j J qx ready I F
    obtain ⟨e,nom,E,U,P⟩ := edge x j (by omega) qx ready I F
    rw [if_neg (show j+1≠l by omega)] at P
    obtain ⟨w,sz,T,I',out,labels⟩ := ih (step x e) (j+1) (by omega) (closed _ qx e)
      (stepReady x qx e ready) U P
    refine ⟨e::w,by simp [sz],.cons I E T,I',out,?_⟩
    intro k hk y H
    cases k with
    | zero => exact nom y H
    | succ k =>
      have hk' : k<w.length := by simpa using hk
      have M := labels k hk' y H
      have E : j+k.succ=(j+1)+k := by omega
      simpa only [List.getElem_cons_succ,E] using M

open BStarFenceReceiverChart

/-- From a literal valid ISSUE410 (already paired with its generated
current-state certificate), an ordered physical service reaches the real
ordinal-four gate with a pending race-one packet. -/
theorem launch_reaches_gate {base old : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (hw : 5≤r)
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (door : Fin n)
    (op : (ctrlOp.read (old (S.getD 0 fall).1).long).toNat=bitOp)
    (launch : Launch (old (S.getD 0 fall).1).long ((step old door) (S.getD 0 fall).1).long)
    (qx : Q (step old door)) (ready : correct (oldH6 B base) hh 5 (step old door))
    (I : Current hp base (fun k=>S.getD k fall) len (step old door) (.busy bitOp (.out 0))) :
    let x := step old door
    let i := digitFrom (S.getD len fall).1 4
    ∃ (l : Nat) (w : List (Fin n)) (pay : Payload), 0<l ∧ l<len ∧ w.length=l ∧
      S.getD l fall=(i,1) ∧ oldOrdinal B base hh i=4 ∧
      BusyOnly hp base (fun k=>S.getD k fall) len bitOp x (.out 0) w (.out l) ∧
      Current hp base (fun k=>S.getD k fall) len (play x w) (.busy bitOp (.out l)) ∧
      atSite (play x w i).long 1=.forward pay ∧
      pay.fault=0 ∧ pay.opcode.toNat=bitOp ∧ pay.outcome=0 ∧ pay.race=1 ∧ pay.argument=0 ∧
      ∀ (k : Nat) (h : k<w.length) (y : X), (∀ i, Layout B base i=Layout B y i) →
        linkAt hp y w[k] (fun t=>S.getD t fall) len k := by
  dsimp only
  let x := step old door
  let i := digitFrom (S.getD len fall).1 4
  have fixed : ∀ a,oldH6 B x a=oldH6 B base a := fun a => (congrArg Prod.fst (fiber x qx a)).symm
  obtain ⟨_,on,_,l,L,loc⟩ := chart_gate hp C hw notShort fixed ready
  have ordinal := ((bit_gate_iff hp hh fixed ready i 1).mp on).2
  have pos : l≠0 := by
    intro E
    rw [E,C.root] at loc
    exact (by decide : (0:Fin 11)≠1) (congrArg Prod.snd loc)
  obtain ⟨p,P,H,_⟩ := launched_wire _ _ op launch
  have kz : (S.getD 0 fall).2=0 := congrArg Prod.snd C.root
  have init : project (fun k=>S.getD k fall) x 0=.forward p := by
    change atSite (x (S.getD 0 fall).1).long (S.getD 0 fall).2=_
    rwa [kz]
  have J : 0+(l-1+1)=l := by omega
  have atL : oldOrdinal B base hh (S.getD l fall).1=4 := by rw [loc]; exact ordinal
  obtain ⟨w,W,T,Cur,Out,N⟩ := ordered_to_gate hp C Q fiber closed sep head cont l L
    (congrArg Prod.snd loc) atL p H (l-1) x 0 J qx ready I init
  have exactOld : atSite (play x w i).long 1=.forward {p with race:=1,argument:=0} := by
    change atCursor (play x w) (S.getD l fall)=_ at Out
    rwa [loc] at Out
  exact ⟨l,w,_,Nat.pos_of_ne_zero pos,L,by omega,loc,ordinal,T,Cur,exactOld,
    H.fault,H.op,H.outcome,rfl,rfl,fun k hk y E => by simpa only [Nat.zero_add] using N k hk y E⟩

end L4.BStarBitHealthyService
