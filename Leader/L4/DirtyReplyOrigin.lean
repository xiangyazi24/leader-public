import Leader.L4.DirtyLeastForward
import Leader.L4.BStarClearanceDTBlock
import Leader.L4.BStarClearanceReplyService
import Leader.L4.ResetReturnIID
import Leader.L4.BStarClearanceSource

namespace L4.DirtyReplyOrigin
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken
open BStarLongRouting BStarLongWork BStarLongCommand BStarLongEvents BStarLongTransport BStarResetQuiet
open BStarLongLiteral BStarLongCommandData
open BStarClearanceAggregate BStarClearanceCommandFrame BStarClearanceCommandSum BStarClearanceDTBlock BStarResetQuietTable

private def proper (c : CommandClaim) : Offer → Prop
  | .door _ => c.kind=.door
  | .advance _ => c.kind≠.door
  | .reverse _ => c.destination.isSome=true
  | _ => True

private theorem proper_actual (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (a : Offer) (h : (C,a)∈actualOffers g raw) : proper C a := by
  change (C,a)∈(round g raw).offered.map _ at h
  obtain ⟨o,ho,oe⟩ := List.mem_map.mp h
  change o∈(gated g raw).map _ at ho
  obtain ⟨v,hv,ve⟩ := List.mem_map.mp ho
  change proper (C,a).1 (C,a).2
  rw [←oe,←ve]
  obtain ⟨c,t⟩ := v
  have K := (BStarLongLiteral.gated_mem g raw c t).mp hv
  let M := fun a : AtK => bound g (readK raw) a
  have A : proper c (BStarLongLiteral.classifyOld g raw c) := by
    change proper c (classify c (geometry g c.source.side) (M c.source)
      ((c.destination.map M).getD .empty))
    unfold classify
    split
    · rename_i H
      exact beq_iff_eq.mp H
    · rename_i H
      have N : c.kind≠.door := fun E => H (beq_iff_eq.mpr E)
      split
      · split <;> first | exact True.intro | exact N
      · split
        · split <;> exact True.intro
        · split
          · rename_i q Q
            cases E : c.destination <;> simp [E,proper] at Q ⊢
          · split <;> exact True.intro
  have Z := K.2
  change t=checkOffer g (BStarLongPrep.view raw) (c,BStarLongLiteral.classifyOld g raw c) at Z
  have T : proper c t := by
    rw [Z]
    generalize BStarLongLiteral.classifyOld g raw c=w at A ⊢
    cases w <;> try exact A
    change proper c (match checkFence g (BStarLongPrep.view raw) c.source _ with
      | .advance => .advance _ | .hold => .hold | .fault => .advance failedPayload)
    split <;> first | exact A | exact True.intro
  let F := (round g raw).faults
  have Cancel (w : Offer) (W : proper c w) :
      proper (cancel F (c,w)).1 (cancel F (c,w)).2 := by
    cases w <;> try exact W
    by_cases E : c.source∈F <;> simpa only [cancel,E,if_true,if_false,proper] using W
  have Grant (w : CmdOffer) (W : proper w.1 w.2) :
      proper (BStarLongGrant.update g raw (round g raw).offered w).1
        (BStarLongGrant.update g raw (round g raw).offered w).2 := by
    obtain ⟨k,j⟩ := w
    unfold BStarLongGrant.update
    dsimp only
    split
    · cases j <;> try exact W
      rename_i pay
      by_cases A : ((geometry g k.source.side).axes.h6 && pay.fault == 0 && pay.opcode.toNat == acquire)=true <;> simpa only [A,Bool.false_eq_true,if_true,if_false,proper] using W
    · exact W
  exact Grant _ (Cancel t T)

abbrev IsReply (raw : BitVec 52) : Prop := returnCount (decode raw)=1

/-- A single old-pair mark with no old forward at the relevant owner
footprint. A reply can persist or originate at the link successor. -/
theorem pair_reply_origin (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (a : AtK) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw := Pair.map LargeSite.long x
    let y := Pair.map LargeSite.long (largePair b x)
    (∀ C∈orderedCommands g, a∈C.slots → ∀ u∈C.slots, DoorSafe g raw u) →
    DoorSafe g raw a →
    (∀ C∈orderedCommands g, a∈C.slots → ¬DirtyLeastForward.IsForward g C.source (readRaw raw C.source)) →
    IsReply (readRaw y a) →
    IsReply (readRaw raw a) ∨ ∃ C∈orderedCommands g, C.source=a ∧
      ∃ d, C.destination=some d ∧ IsReply (readRaw raw d) := by
  classical
  dsimp only
  intro safe sa noF R
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw := Pair.map LargeSite.long x
  let y := Pair.map LargeSite.long (largePair b x)
  change returnCount (readK y a)=1 at R
  by_cases touch : ∃ C∈orderedCommands g,a∈C.slots
  · obtain ⟨C,hC,hA⟩ := touch
    have H := hC
    rw [←actualOffers_claims g raw] at H
    obtain ⟨⟨C₂,act⟩,H,Eq⟩ := List.mem_map.mp H
    change C₂=C at Eq
    subst C₂
    have distinct (d : AtK) (D : C.destination=some d) : C.source≠d :=
      (BStarAcquireReturn.link_shape g C d hC D).1.symm
    let w := fun q : AtK => if a=q then 1 else 0
    have sum_eq (z : Pair (BitVec LW)) :
        total (fun q => w q*small true (readK z q)) C.slots=returnCount (readK z a) := by
      cases hd : C.destination with
      | none =>
        have q : a=C.source := by simpa [Claim.slots,hd] using hA
        subst a
        simp [Claim.slots,hd,total,w,small]
      | some d =>
        have q : a=C.source ∨ a=d := by simpa [Claim.slots,hd] using hA
        have neq := distinct d hd
        rcases q with rfl|rfl
        · simp [Claim.slots,hd,total,w,small,neq]
        · simp [Claim.slots,hd,total,w,small,neq.symm]
    have persist (P : total (fun q=>w q*small true (readK y q)) C.slots ≤
        total (fun q=>w q*small true (readK raw q)) C.slots) :
        IsReply (readRaw raw a) := by
      erw [sum_eq y,sum_eq raw,R] at P
      change returnCount (readK raw a)=1
      cases T : readK raw a <;> simp_all [returnCount]
    cases act with
    | hold => exact .inl (persist (joined_hold_block_DT _ _ _ _ _ _ _ _ _ hp x C true w H (safe C hC hA)))
    | clear => exact .inl (persist (joined_clear_block_DT _ _ _ _ _ _ _ _ _ hp x C true w H
        (safe C hC hA) distinct))
    | door t => exact .inl (persist (joined_door_block_DT _ _ _ _ _ _ _ _ _ hp x C t true w H (safe C hC hA)))
    | advance t =>
      obtain ⟨old,F⟩ := advance_origin g raw C t H
      exact (noF C hC hA ⟨old,F⟩).elim
    | reverse t =>
      cases D : C.destination with
      | none =>
        have Q := proper_actual g raw C (.reverse t) H
        simp [proper,D] at Q
      | some d =>
        obtain ⟨old,⟨pay,rfl⟩⟩ := reverse_origin g raw C d t D H
        obtain ⟨_,afterD⟩ := reverse_endpoints _ _ C d (.reply pay) D (distinct d D) H
        have ha : a=C.source ∨ a=d := by simpa [Claim.slots,D] using hA
        rcases ha with rfl|rfl
        · refine .inr ⟨C,hC,rfl,d,D,?_⟩
          have E := congrArg (fun t : Nat × Nat × Nat=>t.2.1)
            (bind_counts (geometry g d.side) d.occurrence (readK raw d))
          change returnCount (bound g (readK raw) d)=returnCount (readK raw d) at E
          rw [old] at E
          exact E.symm
        · have Q := joined_work_raw _ _ _ _ _ _ _ _ _ hp x a (sa.valid)
          change returnCount (decode (readRaw y a))=1 at R
          erw [Q,afterD,decode_encode] at R
          contradiction
  · have M := joined_idle_DT _ _ _ _ _ _ _ _ _ hp x a true 1
      (BStarClearanceChartFootprint.no_touch_middle g raw a (fun C H I=>touch ⟨C,H,I⟩)) sa
    change 1*returnCount (readK y a)≤1*returnCount (readK raw a) at M
    rw [R] at M
    apply Or.inl
    change returnCount (readK raw a)=1
    cases T : readK raw a <;> simp_all [returnCount]

open BStarAcquireVisitOrder BStarLongFiberOwner BStarAcquireLiteralChain
open BStarResetChartTouch BStarLongFixedRouting BStarClearanceOffset BStarResetMarkAdapter
open BStarClearanceIndexedSum BStarClearanceIndexedWait BStarH6WordChart DirtyLeastForward

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => BStarClearanceOffset.X k₁ k₂ t₂ J₁ J₂ r c p c₁ n

/-- Raw reply occupancy on the owner chart. -/
def ringD (x : X) (u : Pos n) : Prop :=
  BStarClearanceCommandFrame.returnCount (atSite (x u.1).long u.2)=1

theorem ring_reply_origin {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (same : ∀ i,Layout B base i=Layout B x i)
    (e : Fin n) (he : e≠rightNeighbor e)
    (wait : BeforeOwnService hp x (endpoint (oldH6 B base) hh o 0).1 e)
    (noF : ∀ u∈S, ¬ringF x u)
    (u : Pos n) (us : u∈S) :
    ringD (AllSizeS1Geometry.step B x e) u →
    ringD x u ∨ ∃ v∈S, ringD x v ∧ distance S u=distance S v+1 := by
  intro D
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let z := (x e,x (rightNeighbor e))
  let y := AllSizeS1Geometry.step B x e
  let ar := address e
  by_cases cut : u.1=e ∨ u.1=rightNeighbor e
  · obtain ⟨a,ha⟩ : ∃ a : AtK, ar a=u := by
      obtain ⟨i,j⟩ := u
      rcases cut with h|h <;> dsimp only at h <;> subst i
      · exact ⟨L j,rfl⟩
      · exact ⟨R j,rfl⟩
    subst u
    obtain ⟨part,own,adj⟩ := chart_owner_hypotheses hp chart same e
    obtain ⟨safe,_⟩ := pre_service_hypotheses hp chart same e he wait
    have old (t : AtK) : IsReply (readRaw raw t) ↔ ringD x (ar t) := by
      rcases t with ⟨side,j⟩; cases side <;> rfl
    have oldF (t : AtK) : forwardCount (decode (readRaw raw t))=1 ↔ ringF x (ar t) := by
      rcases t with ⟨side,j⟩; cases side <;> rfl
    have new (t : AtK) :
        IsReply (readRaw (Pair.map LargeSite.long (largePair B z)) t) ↔ ringD y (ar t) := by
      rcases t with ⟨side,j⟩
      cases side <;> simp [ringD,y,ar,AllSizeS1Geometry.step,site,Ne.symm he,z] <;> rfl
    have mem (C : CommandClaim) (hc : C∈orderedCommands g) (atA : a∈C.slots)
        (t : AtK) (ht : t∈C.slots) : ar t∈S := by
      have oq := (BStarClearanceChartFootprint.footprint_owner B x e C hc a atA).symm.trans (own a us)
      exact part (List.mem_flatten.mpr ⟨_,List.mem_map.mpr ⟨C,
        List.mem_filter.mpr ⟨hc,beq_iff_eq.mpr oq⟩,rfl⟩,List.mem_map.mpr ⟨t,ht,rfl⟩⟩)
    have nav := pair_reply_origin _ _ _ _ _ _ _ _ _ hp z a
      (fun C hc ha t ht => safe t (mem C hc ha t ht)) (safe a us)
      (fun C hc ha H => noF _ (mem C hc ha C.source (by simp [Claim.slots]))
        ((oldF _).mp ((isForward_iff _ _ _).mp H)))
      ((new a).mpr D)
    rcases nav with h|⟨C,hc,src,v,edge,V⟩
    · exact .inl ((old a).mp h)
    · have ma := mem C hc (by simp [Claim.slots,src]) C.source (by simp [Claim.slots])
      have mv := mem C hc (by simp [Claim.slots,src]) v (by simp [Claim.slots,edge])
      have E := (adj C hc (own _ ma)).1 _ edge
      rw [src] at E
      exact .inr ⟨ar v,mv,(old _).mp V,E⟩
  · have Y : y u.1=x u.1 := by
      simp [y,AllSizeS1Geometry.step,show u.1≠e from fun h => cut (.inl h),show u.1≠rightNeighbor e from fun h => cut (.inr h)]
    exact .inl (by simpa only [ringD,Y] using (show ringD y u from D))

open BStarClearanceReplyService BStarClearanceSource BStarAcquireForwardTrace

theorem reply_distance_mem {S : List (Pos n)} (nodup : S.Nodup) {u : Pos n}
    (U : u∈S) : ∃ (i : Nat) (hi : i<S.length), S[i]=u ∧ replyDistance S u=i+1 := by
  obtain ⟨i,hi,E⟩ := List.mem_iff_getElem.mp U
  exact ⟨i,hi,E,E ▸ replyDistance_idx nodup hi⟩

/-- A nominated reverse literally erases its selected destination reply.
Offers, fixed chart membership, and valid-door framing remain explicit. -/
theorem reverse_clears_chart_reply {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (same : ∀ i,Layout B base i=Layout B x i)
    (e : Fin n) (he : e≠rightNeighbor e)
    (wait : BeforeOwnService hp x (endpoint (oldH6 B base) hh o 0).1 e)
    (C : CommandClaim) (a : AtK) (q : Payload)
    (hD : C.destination=some a) (mem : address e a∈S)
    (R : (C,.reverse (.reply q))∈actualOffers (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)) :
    ¬ringD (AllSizeS1Geometry.step B x e) (address e a) := by
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have hC : C∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,R,rfl⟩
  obtain ⟨safe,_⟩ := pre_service_hypotheses hp chart same e he wait
  have ne := (BStarAcquireReturn.link_shape g C a hC hD).1.symm
  have D := (reverse_endpoints g raw C a (.reply q) hD ne R).2
  have J := joined_work_raw _ _ _ _ _ _ _ _ _ hp (x e,x (rightNeighbor e)) a (safe a mem).valid
  have rd := BStarResetRailRing.new_read B x e he a
  have A : readK (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) a=.empty := by
    change decode (readRaw _ a)=_
    erw [J,D,BStarLongToken.decode_encode]
  intro H
  change returnCount (atCursor (AllSizeS1Geometry.step B x e) (address e a))=1 at H
  rw [←rd,A] at H
  contradiction

/-- The real clock for the reply suffix: no sum of per-packet travel is
charged. The bounded rank is the last live reply index plus one. -/
theorem reply_suffix_expected {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (head : ∀ i,let g:=longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i,let g:=oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q x)
    (layout : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (AllSizeS1Geometry.step B y e))
    (noF : ∀ u∈S, ¬ringF x u) :
    let root := (endpoint (oldH6 B base) hh o 0).1
    Height.IIDExpectedHittingTimeAtMost (AllSizeS1Geometry.step B)
      (fun y=>¬Held (y root).long ∨ ∀ u∈S, ¬ringD y u) x (n*S.length) := by
  classical
  dsimp only
  let root := (endpoint (oldH6 B base) hh o 0).1
  let step := AllSizeS1Geometry.step (n:=n) B
  let stop := fun y : X=>¬Held (y root).long ∨ ∀ u∈S, ¬ringD y u
  let Bound := fun (y : X) (r : Nat) => ∀ u∈S,ringD y u → replyDistance S u≤r
  let Live := fun (y : X) (r : Nat) => Q y ∧ (∀ u∈S, ¬ringF y u) ∧ ¬stop y ∧ Bound y r
  have lenS := chart.length
  have pos (y : X) (r : Nat) (Y : Live y r) : 0<r := by
    have E : ∃ u∈S, ringD y u := by
      by_cases D : ∃ u∈S,ringD y u
      · exact D
      · exact (Y.2.2.1 (.inr (fun u U R=>D ⟨u,U,R⟩))).elim
    obtain ⟨u,U,D⟩ := E
    obtain ⟨i,_,_,rE⟩ := reply_distance_mem chart.nodup U
    have A := Y.2.2.2 u U D
    omega
  have advance (y : X) (r : Nat) (Y : Live y r) : ∃ d : Fin n,∀ e : Fin n,
      stop (step y e) ∨ ∃ r',Live (step y e) r' ∧ r'≤r ∧ (e=d→r'<r) := by
    have H : Held (y root).long := Classical.not_not.mp (fun h=>Y.2.2.1 (.inl h))
    have origin (e : Fin n) (u : Pos n) (U : u∈S) (R : ringD (step y e) u) :=
      ring_reply_origin hp chart (layout _ Y.1) e (sep e) (held_before hp y root e H) Y.2.1 u U R
    have preserve (e : Fin n) : ∀ u∈S, ¬ringF (step y e) u := by
      intro u U F
      rcases ring_origin hp chart (layout _ Y.1) e (sep e) (held_before hp y root e H) u U F with same|⟨v,V,old,_⟩
      · exact Y.2.1 u U same
      · exact Y.2.1 v V old
    have weak (e : Fin n) : Bound (step y e) r := by
      intro u U R
      rcases origin e u U R with same|⟨v,V,old,T⟩
      · exact Y.2.2.2 u U same
      · have M := Y.2.2.2 v V old
        have Wu : replyDistance S u=S.length+1-distance S u := rfl
        have Wv : replyDistance S v=S.length+1-distance S v := rfl
        have Ule : distance S u≤S.length := Nat.sub_le _ _
        omega
    suffices Pay : ∃ d : Fin n, Bound (step y d) (r-1) by
      obtain ⟨d,J⟩ := Pay
      refine ⟨d,fun e=>?_⟩
      by_cases Hit : stop (step y e)
      · exact .inl Hit
      by_cases E : e=d
      · subst e
        exact .inr ⟨r-1,⟨closed _ _ Y.1,preserve _,Hit,J⟩,Nat.sub_le _ _,fun _=>by have := pos y r Y; omega⟩
      · exact .inr ⟨r,⟨closed _ _ Y.1,preserve _,Hit,weak _⟩,Nat.le_refl _,fun F=>(E F).elim⟩
    by_cases top : ∃ u∈S,ringD y u ∧ replyDistance S u=r
    · obtain ⟨u,U,D,rEq⟩ := top
      obtain ⟨i,hi,Id,Ieq⟩ := reply_distance_mem chart.nodup U
      have uid : S.getD i fall=u := (List.getElem_eq_getD (h:=hi) fall).symm.trans Id
      have ip : 0<i := by
        by_cases i0 : i=0
        · rw [i0,chart.root] at uid
          have E : returnCount (atSite (y root).long 0)=1 := by
            rw [←uid] at D
            exact D
          rcases H.2.2 with ho|⟨p,ho⟩ <;> rw [ho] at E <;> contradiction
        · omega
      let j := i-1
      have jlt : j<len := by dsimp [j]; omega
      have eq : j+1=i := by dsimp [j]; omega
      have srcNoF : ∀ p, atCursor y (S.getD j fall)≠.forward p := by
        have J : j<S.length := by omega
        have M : S.getD j fall∈S := by rw [←List.getElem_eq_getD (h:=J) fall]; exact List.getElem_mem _
        intro p F
        apply Y.2.1 _ M
        change forwardCount (atCursor y (S.getD j fall))=1
        rw [F]; rfl
      have oldD : ∃ p,atCursor y (S.getD (j+1) fall)=.reply p := by
        rw [eq,uid]
        change returnCount (atCursor y u)=1 at D
        cases J : atCursor y u <;> simp_all [returnCount]
      obtain ⟨p,Dp⟩ := oldD
      obtain ⟨d,C,a,q,R,_,dst,hD,_⟩ :=
        nominate_reverse hp chart head cont (layout _ Y.1) jlt p Dp srcNoF
      have Ua : address d a=u := dst.trans ((congrArg (fun k=>S.getD k fall) eq).trans uid)
      have erased := reverse_clears_chart_reply hp chart (layout _ Y.1) d (sep d)
        (held_before hp y root d H) C a q hD (Ua.symm ▸ U) R
      rw [Ua] at erased
      refine ⟨d,fun v V Vr=>?_⟩
      rcases origin d v V Vr with same|⟨w,W,old,t⟩
      · obtain ⟨k,hk,E,K⟩ := reply_distance_mem chart.nodup V
        have J := Y.2.2.2 v V same
        by_cases eqk : k=i
        · subst k
          exact (erased (Id ▸ (E.symm ▸ Vr))).elim
        · omega
      · have M := Y.2.2.2 w W old
        have Wv : replyDistance S v=S.length+1-distance S v := rfl
        have Ww : replyDistance S w=S.length+1-distance S w := rfl
        have Ule : distance S v≤S.length := Nat.sub_le _ _
        omega
    · obtain ⟨d,_⟩ := hh
      refine ⟨d,fun u U R=>?_⟩
      rcases origin d u U R with same|⟨v,V,old,t⟩
      · have M := Y.2.2.2 u U same
        have N : replyDistance S u≠r := fun N=>top ⟨u,U,same,N⟩
        omega
      · have M := Y.2.2.2 v V old
        have Wu : replyDistance S u=S.length+1-distance S u := rfl
        have Wv : replyDistance S v=S.length+1-distance S v := rfl
        have Ule : distance S u≤S.length := Nat.sub_le _ _
        omega
  apply ResetReturnIID.iid_of_relational_rank step stop Live pos advance
  by_cases Hit : stop x
  · exact .inl Hit
  · refine .inr ⟨I,noF,Hit,fun u U _=>?_⟩
    obtain ⟨i,hi,_,E⟩ := reply_distance_mem chart.nodup U
    omega

end L4.DirtyReplyOrigin
