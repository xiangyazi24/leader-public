import Leader.L4.BStarStageTerminalHealth
import Leader.L4.BStarReplyBack
import Leader.L4.BStarSeparatorRing

namespace L4.BStarSealNoRefusal
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongLayout BStarLongDoor BStarLongTransport BStarLongEvents
open BStarLongRouting BStarResetQuiet BStarResetQuietTable BStarClearanceForward
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarResetMarkAdapter BStarResetRailRing BStarOwnerLaunchOrigin BStarGeneratedOwner
open BStarSeparatingRail BStarAcquireForwardTrace BStarSeparatorControl
open BStarSeparatorTags BStarSeparatorJoinedTags BStarResetChartService BStarSeparatorQuiet

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B

def HealthySeal (p : Payload) : Prop := p.fault=0 ∧ p.opcode.toNat=sealOp

private theorem finish_health (p q : Payload) (R : finish p=.reply q) (H : HealthySeal q) :
    HealthySeal p := by
  unfold finish at R
  dsimp only at R
  split at R
  · change (.reply _ : Token)=.reply q at R
    cases R
    exact ((show (1 : BitVec 1)≠0 by decide) H.1).elim
  · rename_i N
    have healthy : p.fault=0 := by
      apply Classical.byContradiction
      intro ne
      exact N (bne_iff_ne.mpr ne)
    split at R
    · rename_i A
      have op : p.opcode.toNat=acquire := beq_iff_eq.mp A
      split at R <;> cases R <;> exact False.elim ((by decide : acquire≠sealOp) (op.symm.trans H.2))
    · split at R
      · change (.reply _ : Token)=.reply q at R
        cases R
        exact ((show (1 : BitVec 1)≠0 by decide) H.1).elim
      · cases R
        exact ⟨healthy,H.2⟩

theorem selected_terminal_health {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (e : Fin n) (sep : e≠rightNeighbor e)
    (old : Current hp base (fun j => S.getD j fall) len x (.busy sealOp (.out len)))
    (fresh : Current hp base (fun j => S.getD j fall) len (step x e) (.busy sealOp (.back len)))
    (q : Payload) (new : project (fun j => S.getD j fall) (step x e) len=.reply q) (H : HealthySeal q) :
    ∃ p C offer,
      project (fun j => S.getD j fall) x len=.forward p ∧ HealthySeal p ∧
      (C,.advance offer)∈actualOffers (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long) ∧
      C.source.occurrence.val=10 ∧ HealthySeal offer := by
  obtain ⟨C,v,sel,kind,dest,tag,idx⟩ := BStarStageTerminalHealth.selected_turn hp chart e sep sealOp old fresh
  let g := oldPair B x e
  let raw := ((x e).long,(x (rightNeighbor e)).long)
  have D := (new_read B x e sep C.source).trans
    ((congrArg (atCursor (step x e)) idx).symm.trans new)
  have valid : C.source=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true := by
    intro E _
    rw [E] at tag
    contradiction
  change BStarLongToken.decode (readRaw _ C.source)=_ at D
  erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp (x e,x (rightNeighbor e)) C.source valid] at D
  change BStarLongToken.decode (readRaw (patchPair (longWork g raw) raw) C.source)=.reply q at D
  rw [terminal_finish g raw C v dest sel,BStarLongToken.decode_encode] at D
  have vEq : carried g raw C v=v := by
    have N : C.source.occurrence.val≠1 := by omega
    unfold carried BStarLongArithmetic.visit
    have M : (C.source.occurrence.val != 1)=true := bne_iff_ne.mpr N
    simp only [M,Bool.true_or,if_true]
    rw [BStarLongOutgoing.noncenter_hold _ _ _ _ N]
    rfl
  change finish (carried g raw C v)=.reply q at D
  rw [vEq] at D
  have Hv := finish_health v q D H
  obtain ⟨p,P,Q,op⟩ := BStarForwardProvenance.offer_origin g raw C v sel Hv.1
  exact ⟨p,C,v,(congrArg (atCursor x) idx).trans ((old_read x e C.source).symm.trans P),
    ⟨Q,(congrArg BitVec.toNat op).trans Hv.2⟩,sel,tag,Hv⟩

theorem terminal_of_ack {base y : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (turn : Fin n) (back : List (Fin n)) (f : Payload)
    (old : Current hp base (fun j=>S.getD j fall) len y (.busy sealOp (.out len)))
    (ret : BusyOnly hp base (fun j=>S.getD j fall) len sealOp
      (step y turn) (.back len) back (.back 0))
    (bound : let x := BStarResetSchedule.run step (step y turn) back (S.getD 0 fall).1
      bind (longGeometry B x) 0 (atSite x.long 0)=.reply f)
    (H : HealthySeal f) :
    ∃ p, project (fun j=>S.getD j fall) y len=.forward p ∧ HealthySeal p := by
  have nonacq : f.opcode.toNat≠acquire := H.2.symm ▸ (by decide : sealOp≠acquire)
  obtain ⟨q,Q,_,F,E⟩ := BStarReplyBack.from_arrival hp C sep ret f H.1 nonacq bound
  obtain ⟨p,_,_,P,hP,_,_,_⟩ := selected_terminal_health hp C turn (sep turn) old
    (busy_start hp ret) q Q ⟨F,(congrArg BitVec.toNat E).trans H.2⟩
  exact ⟨p,P,hP⟩

/-- The literal SEAL handler refuses unless the offered descriptor decodes,
the old writer/selector authorizes it, and the old STAGE latch matches. -/
theorem refused_execute (g : LongGeometry) (raw : BitVec LW) (p : Payload)
    (head : g.axes.h6=true) (H : HealthySeal p)
    (bad : ¬ ∃ d, BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/2))=some d ∧
      BStarLongOutgoing.actual raw d=true ∧
      BStarLongPublication.readOptional (BStarLongLayout.stage.read raw)=some d) :
    BStarLongOutgoing.execute g 1 raw p=BStarLongOutgoing.refuse := by
  obtain ⟨F,P⟩ := H
  cases D : BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/2)) with
  | none => simp [BStarLongOutgoing.execute,F,P,head,stageOp,sealOp,D]
  | some d =>
    have no (a : BStarLongOutgoing.actual raw d=true) : BStarLongPublication.readOptional (BStarLongLayout.stage.read raw)≠some d := fun b => bad ⟨d,D,a,b⟩
    by_cases A : BStarLongOutgoing.actual raw d=true
    · simp [BStarLongOutgoing.execute,F,P,head,stageOp,sealOp,D,A,no A]
    · simp [BStarLongOutgoing.execute,F,P,head,stageOp,sealOp,D,Bool.eq_false_iff.mpr A]

/-- Refusal is materialized as the canonical fault at the literal selected destination. -/
theorem joined_refused_seal (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (K : CommandClaim) (a : AtK) (pay : Payload) (H : HealthySeal pay) :
    let g := Pair.map (longGeometry B) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    K.source.occurrence=1 → (geometry g K.source.side).axes.h6=true →
    K.destination=some a → (K,.advance pay)∈actualOffers g raw →
    (¬ ∃ d, BStarLongPublication.decode (BitVec.ofNat 7 (pay.argument.toNat/2))=some d ∧
      BStarLongOutgoing.actual (atOld raw K.source) d=true ∧
      BStarLongPublication.readOptional (stage.read (atOld raw K.source))=some d) →
    readK (Pair.map LargeSite.long (largePair B x)) a=fault false := by
  dsimp only
  intro k1 head dst sel bad
  let g := Pair.map (longGeometry B) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have mem : K∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,sel,rfl⟩
  have exe : BStarLongOutgoing.execute (geometry g K.source.side) K.source.occurrence
      (atOld raw K.source) pay=BStarLongOutgoing.refuse := by
    rw [k1]
    exact refused_execute _ _ _ head H bad
  have Carried : carried g raw K pay=⟨1,0,0,0,0⟩ := by
    have node : BStarLongArithmetic.nodeOf sealOp=none := by decide
    unfold carried
    dsimp only
    rw [show (BStarLongArithmetic.visit (geometry g K.source.side) K.source.occurrence
      (atOld raw K.source) pay).2=pay by
        simp [BStarLongArithmetic.visit,H.2,node],exe]
    rfl
  have neq := (BStarAcquireReturn.link_shape g K a mem dst).1
  have V : a=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true := by
    intro E Z
    have J : a.occurrence.val=0 := congrArg (fun z : AtK => z.occurrence.val) E
    have W := (BStarAcquireJoinedHop.k0_dest g K a mem dst J).2
    simp [Z] at W
  have A := (move_lands g raw K pay a dst sel (Ne.symm neq)).2
  change BStarLongToken.decode (readRaw _ a)=_
  rw [joined_work_raw _ _ _ _ _ _ _ _ _ hp x a V]
  change BStarLongToken.decode (readRaw (patchPair (longWork g raw) raw) a)=_
  rw [A,BStarLongToken.decode_encode,Carried]
  rfl

/-- Any healthy ACK rules out a fault at the actual outgoing cursor of
a same-tour postcenter cut: backwards ancestry requires a healthy
forward, and the pointed chart admits exactly one forward at that cut. -/
theorem fault_cannot_return {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (k : Nat)
    (out : List (Fin n)) (turn : Fin n) (back : List (Fin n))
    (P : BusyOnly hp base (fun j=>S.getD j fall) len sealOp x (.out k) out (.out len))
    (Ret : BusyOnly hp base (fun j=>S.getD j fall) len sealOp
      (step (BStarResetSchedule.run step x out) turn) (.back len) back (.back 0))
    (f : Payload) (H : HealthySeal f)
    (Ack : let y := (BStarResetSchedule.run step (step (BStarResetSchedule.run step x out) turn) back)
      let site := y (S.getD 0 fall).1
      bind (longGeometry B site) 0 (atSite site.long 0)=.reply f) :
    project (fun j=>S.getD j fall) x k ≠ fault false := by
  intro dead
  obtain ⟨p,atEnd,ok⟩ := terminal_of_ack hp C sep turn back f
    (BStarAcquireHistoryReturn.busy_end hp P) Ret Ack H
  obtain ⟨j,J,q,Q,qF,_⟩ := busy_origin hp C sep P len (Nat.le_refl _) p atEnd ok.1
  have I := busy_start hp P
  have key := (BStarOwnerControlHistory.pointed_unique_forward _ len k I.2.1 I.2.2 j J).mp ⟨q,Q⟩
  subst j
  rw [dead] at Q
  have eq := Token.forward.inj Q
  have F : (1 : BitVec 1)=0 := (congrArg Payload.fault eq).trans qF
  exact (by decide : (1 : BitVec 1)≠0) F

#print axioms joined_refused_seal
#print axioms fault_cannot_return
open BStarLongFixedRouting BStarLongLiteral

/-- On the specified genuine chart tour, a healthy returned SEAL
certifies that its selected H6 center departure was not refused. The
postcenter slice and return use the same physical cut and mark. -/
theorem ack_certifies_center {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (j : Nat) (J : j<len)
    (loc : S.getD j fall=(i,1)) (head : oldH6 B base i=true)
    (cur : Current hp base (fun t=>S.getD t fall) len x (.busy sealOp (.out j)))
    (pay : Payload) (H : HealthySeal pay)
    (sel : let g := oldPair B x i
      (centerLink g,.advance pay)∈actualOffers g ((x i).long,(x (rightNeighbor i)).long))
    (out : List (Fin n)) (turn : Fin n) (back : List (Fin n))
    (P : BusyOnly hp base (fun t=>S.getD t fall) len sealOp (step x i) (.out (j+1)) out (.out len))
    (Ret : BusyOnly hp base (fun t=>S.getD t fall) len sealOp
      (step (BStarResetSchedule.run step (step x i) out) turn) (.back len) back (.back 0))
    (f : Payload) (F : HealthySeal f)
    (Ack : let y := BStarResetSchedule.run step (step (BStarResetSchedule.run step (step x i) out) turn) back
      let site := y (S.getD 0 fall).1
      bind (longGeometry B site) 0 (atSite site.long 0)=.reply f) :
    ∃ d, BStarLongPublication.decode (BitVec.ofNat 7 (pay.argument.toNat/2))=some d ∧
      BStarLongOutgoing.actual (x i).long d=true ∧
      BStarLongPublication.readOptional (BStarLongLayout.stage.read (x i).long)=some d := by
  apply Classical.byContradiction
  intro bad
  let g := oldPair B x i
  let K := centerLink g
  let a : AtK := R (if g.2.axes.h6 then 2 else 1)
  let addr := fun t=>S.getD t fall
  have D : K.destination=some a := rfl
  have idx : addr j=address i K.source := loc
  have forward : Edge B x (address i K.source) (address i a) :=
    ⟨i,K,a,center_mem g,D,rfl,rfl⟩
  have sz := C.length
  have mem : addr j∈S := by
    change S.getD j fall∈S
    rw [←List.getElem_eq_getD (h:=show j<S.length by omega)]
    exact List.getElem_mem _
  obtain ⟨k,hk,src,dst⟩ := C.edge _ _ (idx ▸ mem)
    ((edge_fixed B base x cur.1.1 _ _).mpr forward)
  have sk : S.getD k fall=address i K.source := (List.getElem_eq_getD _).symm.trans src
  have ident : k=j := (List.getD_inj (by omega) (by omega) C.nodup).mp (sk.trans idx.symm)
  subst k
  have next : addr (j+1)=address i a := (List.getElem_eq_getD _).symm.trans dst
  have h : (geometry g K.source.side).axes.h6=true :=
    (congrArg Prod.fst (cur.1.1 i)).symm.trans head
  have fail := joined_refused_seal hp (x i,x (rightNeighbor i)) K a pay H rfl h D sel bad
  have post : project addr (step x i) (j+1)=fault false :=
    (congrArg (atCursor (step x i)) next).trans ((new_read B x i (sep i) a).symm.trans fail)
  exact fault_cannot_return hp C sep (j+1) out turn back P Ret f F Ack post

#print axioms ack_certifies_center
end L4.BStarSealNoRefusal
