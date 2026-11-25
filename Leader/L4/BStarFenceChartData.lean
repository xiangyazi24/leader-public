import Leader.L4.BStarFenceTerminalData
import Leader.L4.BStarStageTerminalHealth
import Leader.L4.BStarNumericChronology
import Leader.L4.BStarNativeAttemptReceipts

namespace L4.BStarFenceChartData
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongTransport BStarLongEvents BStarLongRouting BStarLongLiteral
open BStarResetQuiet BStarResetQuietTable BStarClearanceForward BStarLongCommandData
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireForwardTrace
open BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing BStarSeparatingRail
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarSeparatorControl BStarResetSchedule
open BStarFenceTerminalData BStarLongPackets BStarLongPrep BStarLongFiberOwner
open BStarAcquireAnchors BStarAcquireRailCoverage

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

def Fence (p : Payload) : Prop := p.fault=0 ∧ p.opcode.toNat=11

private theorem pre_grant (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (C : CommandClaim)
    (p : Payload) (large : 3≤C.source.occurrence.val)
    (sel : (C,.advance p)∈actualOffers g raw) :
    (C,.advance p)∈(round g raw).offered := by
  change (C,.advance p)∈((round g raw).offered.map
    (BStarLongGrant.update g raw (round g raw).offered)) at sel
  obtain ⟨o,h,E⟩ := List.mem_map.mp sel
  have K : o.1=C := (update_claim g raw _ o).symm.trans (congrArg Prod.fst E)
  obtain ⟨J,t⟩ := o
  change J=C at K
  subst J
  unfold BStarLongGrant.update at E
  dsimp only at E
  rw [dif_neg (Nat.not_lt_of_ge large)] at E
  rwa [E] at h

private theorem finish_fence (p q : Payload) (R : finish p=.reply q) (H : Fence q) :
    Fence p := by
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
      split at R <;> cases R <;> exact False.elim ((by decide : acquire≠11) (op.symm.trans H.2))
    · split at R
      · change (.reply _ : Token)=.reply q at R
        cases R
        exact ((show (1 : BitVec 1)≠0 by decide) H.1).elim
      · cases R
        exact ⟨healthy,H.2⟩

private theorem not_center_carries (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (v : Payload) (N : C.source.occurrence.val≠1) :
    carried g raw C v=v := by
  unfold carried BStarLongArithmetic.visit
  have M : (C.source.occurrence.val != 1)=true := bne_iff_ne.mpr N
  simp only [M,Bool.true_or,if_true]
  rw [BStarLongOutgoing.noncenter_hold _ _ _ _ N]
  rfl

/-- At a real FENCE turn, a healthy accepted door reply forces the
exact old selected K10 command and its right retained data. -/
theorem terminal_fence {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (turn : Fin n) (back : List (Fin n))
    (old : Current hp base (fun j => S.getD j fall) len x (.busy 11 (.out len)))
    (ret : BusyOnly hp base (fun j => S.getD j fall) len 11 (step x turn) (.back len) back (.back 0))
    (ans : Payload) (healthy : Fence ans)
    (reply : let y := run (step x turn) back
      let i := (S.getD 0 fall).1
      bind (longGeometry B (y i)) 0 (atSite (y i).long 0)=.reply ans)
    (inside : (longGeometry B (base (S.getD len fall).1)).inside=true) :
    let g := oldPair B x turn
    let raw := ((x turn).long,(x (rightNeighbor turn)).long)
    ∃ C v f, (C,.advance v)∈actualOffers g raw ∧ C.source.occurrence=10 ∧
      S.getD len fall=address turn C.source ∧ Fence v ∧
      project (fun j => S.getD j fall) x len=.forward f ∧ Fence f ∧
      let d := BStarLongPrep.view raw ⟨C.source.side,.rd⟩
      d.mobile=.empty ∧ ∃ z,d.retained=.data z := by
  have N : ans.opcode.toNat≠acquire := healthy.2.symm ▸ (by decide : 11≠acquire)
  obtain ⟨p,P,_,F,E⟩ := BStarReplyBack.from_arrival hp chart sep ret ans healthy.1 N reply
  have HP : Fence p := ⟨F,(congrArg BitVec.toNat E).trans healthy.2⟩
  obtain ⟨C,v,sel,_,dest,tag,idx⟩ :=
    BStarStageTerminalHealth.selected_turn hp chart turn (sep turn) 11 old (busy_start hp ret)
  let g := oldPair B x turn
  let raw : Pair (BitVec LW) := ((x turn).long,(x (rightNeighbor turn)).long)
  have D := (new_read B x turn (sep turn) C.source).trans
    ((congrArg (atCursor (step x turn)) idx).symm.trans P)
  have valid : C.source=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true := by
    intro E _
    rw [E] at tag
    contradiction
  change BStarLongToken.decode (readRaw _ C.source)=_ at D
  erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp (x turn,x (rightNeighbor turn)) C.source valid] at D
  change BStarLongToken.decode (readRaw (patchPair (longWork g raw) raw) C.source)=.reply p at D
  rw [terminal_finish g raw C v dest sel,BStarLongToken.decode_encode] at D
  change finish (carried g raw C v)=.reply p at D
  rw [not_center_carries g raw C v (by omega)] at D
  have H := finish_fence v p D HP
  obtain ⟨f,Y,Q,op⟩ := BStarForwardProvenance.offer_origin g raw C v sel H.1
  have hz : C.source.occurrence=10 := Fin.ext tag
  have oldInside : (geometry g C.source.side).inside=true := by
    have X0 : (longGeometry B (x (S.getD len fall).1)).inside=true :=
      (congrArg (fun z : Bool × Bool × Bool => z.2.1) (old.1.1 _)).symm.trans inside
    have U : (S.getD len fall).1=site turn C.source.side := congrArg Prod.fst idx
    rw [U] at X0
    cases Z : C.source.side <;> rw [Z] at X0 <;> exact X0
  exact ⟨C,v,f,sel,hz,idx,H,
    (congrArg (atCursor x) idx).trans ((old_read x turn C.source).symm.trans Y),
    ⟨Q,(congrArg BitVec.toNat op).trans H.2⟩,
    surviving_k10_data g raw C v hz oldInside H.1 H.2 (pre_grant g raw C v (by omega) sel)⟩

theorem joined_noncenter_hop_offer (k₁ k₂ t₂ J₁ J₂ r n p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r n p c₁)))
    (c : CommandClaim) (a : AtK) (offer after : Payload)
    (N : c.source.occurrence.val≠1) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    c.destination=some a → (c,.advance offer)∈actualOffers g raw →
    readK y a=.forward after → Fence after →
    Fence offer := by
  dsimp only
  intro dst sel land healthy
  let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
  have hm : c∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,sel,rfl⟩
  have ne := (BStarAcquireReturn.link_shape g c a hm dst).1
  have V : a=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true := by
    intro E Z
    have J : a.occurrence.val=0 := congrArg (fun z : AtK => z.occurrence.val) E
    have H := (BStarAcquireJoinedHop.k0_dest g c a hm dst J).2
    simp [Z] at H
  have A := (move_lands g raw c offer a dst sel (Ne.symm ne)).2
  have Arr : arrive (geometry g a.side) a.occurrence (carried g raw c offer)=.forward after := by
    change decode (readRaw y a)=.forward after at land
    erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp x a V,A,BStarLongToken.decode_encode] at land
    exact land
  rw [not_center_carries g raw c offer N] at Arr
  unfold arrive at Arr
  split at Arr <;> cases Arr <;> exact healthy

open BStarAcquireHistorySample

private theorem single_advance {x : X} {addr : Nat → Pos n} {len : Nat} {e : Fin n}
    {z d : Cursor} (seen : Seen step (project addr) anyTag len x z [e] d) :
    Advance len z d := by
  cases seen with
  | cons _ _ t _ tail => cases tail; exact t

/-- Every chosen chart position strictly before the terminal is crossed
once on its exact actual healthy outward STAGE flight. Extract its
original raw split, old and new owner modes, offer and unchanged
effective argument; no independent favorable route is chosen. -/
theorem find_fence_departure {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {z d : Cursor}
    (T : BusyOnly hp base (fun j => S.getD j fall) len 11 x z w d)
    (k : Nat) (k7 : (S.getD k fall).2=7) (pay : Payload) (healthy : Fence pay) :
    ∀ f l, z=.out f → d=.out l → f≤k → k<l → l≤len →
      project (fun j => S.getD j fall) (run x w) l=.forward pay →
      ∃ pre e post, w=pre++e::post ∧
        BusyOnly hp base (fun j => S.getD j fall) len 11 x (.out f) pre (.out k) ∧
        let old := run x pre
        let raw := ((old e).long,(old (rightNeighbor e)).long)
        Event hp (fun j => S.getD j fall) len old e (.busy 11 (.out k)) (.busy 11 (.out (k+1))) ∧
        BusyOnly hp base (fun j => S.getD j fall) len 11 (step old e) (.out (k+1)) post (.out l) ∧
        ∃ K a q, (K,.advance q)∈actualOffers (oldPair B old e) raw ∧
          K.destination=some a ∧ S.getD k fall=address e K.source ∧
          S.getD (k+1) fall=address e a ∧ K.source.occurrence=7 ∧ Fence q := by
  induction T with
  | nil I =>
    intro f l F L fk kl _ _
    have := Cursor.out.inj (F.symm.trans L)
    omega
  | @cons x z next d e w I E tail ih =>
    intro f l F L fk kl le ok
    subst z
    obtain ⟨j,J⟩ := busy_no_back_to_out hp tail ⟨l,L⟩
    subst next
    have A : Advance len (.out f) (.out j) := by
      cases E with
      | transit _ _ _ _ seen => exact single_advance hp seen
    cases A with
    | stay =>
      obtain ⟨pre,m,post,R,lead,ev,after,sel⟩ := ih f l rfl L fk kl le ok
      exact ⟨e::pre,m,post,congrArg (List.cons e) R,.cons I E lead,ev,after,sel⟩
    | forward =>
      by_cases eq : f=k
      · subst f
        obtain ⟨j,hj,q,Q,F,Op⟩ :=
          BStarOwnerLaunchOrigin.busy_origin hp C sep tail l le pay ok healthy.1
        have W := busy_start hp tail
        have eq := (BStarOwnerControlHistory.pointed_unique_forward _ len _ W.2.1 W.2.2 j hj).mp ⟨q,Q⟩
        subst j
        obtain ⟨K,a,v,sel,dest,src,arr⟩ :=
          BStarNumericChronology.ring_departure hp C e (sep e) 11 k (by omega) I.1 I.2.1 I.2.2 q Q F
        have occ : K.source.occurrence=7 := (congrArg Prod.snd src).symm.trans k7
        have land := (new_read B x e (sep e) a).trans
          ((congrArg (atCursor (step x e)) arr).symm.trans Q)
        have qFence : Fence q := ⟨F,(congrArg BitVec.toNat Op).trans healthy.2⟩
        have vFence := joined_noncenter_hop_offer _ _ _ _ _ _ _ _ _ hp
          (x e,x (rightNeighbor e)) K a v q (by rw [occ]; decide) dest sel land qFence
        exact ⟨[],e,w,rfl,.nil I,E,L ▸ tail,K,a,v,sel,dest,src,arr,occ,vFence⟩
      · obtain ⟨pre,m,post,R,lead,ev,after,sel⟩ := ih (f+1) l rfl L (by omega) kl le ok
        exact ⟨e::pre,m,post,congrArg (List.cons e) R,.cons I E lead,ev,after,sel⟩

open BStarNativeReceiptTape

/-- Both data checkpoints belong to the single actual successful FENCE
tour. The generated ACK identifies the tour, not a match of field bytes.
The left slot is specified by its chart ordinal; the right is its
terminal chart address. Each conclusion reads the immutable old site. -/
theorem data_of_accepted_fence {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (k : Nat) (hk : k<len) (k7 : (S.getD k fall).2=7)
    (leftIn : (longGeometry B (base (S.getD k fall).1)).inside=true)
    (rightIn : (longGeometry B (base (S.getD len fall).1)).inside=true)
    (w : List (Fin n)) (ack : Fin n)
    (T : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w (.busy 11 (.back 0)))
    (H : Hit hp base (fun j => S.getD j fall) len (run x w) ack 11) :
    ∃ (pre gap back : List (Fin n)) (mark turn : Fin n)
      (L R : CommandClaim) (lq rq : Payload),
      w=pre++mark::(gap++turn::back) ∧
      let left := run x pre
      let right := run (step left mark) gap
      let gl := oldPair B left mark
      let gr := oldPair B right turn
      let xl := ((left mark).long,(left (rightNeighbor mark)).long)
      let xr := ((right turn).long,(right (rightNeighbor turn)).long)
      (L,.advance lq)∈actualOffers gl xl ∧ (R,.advance rq)∈actualOffers gr xr ∧
      S.getD k fall=address mark L.source ∧ S.getD len fall=address turn R.source ∧
      L.source.occurrence=7 ∧ R.source.occurrence=10 ∧ Fence lq ∧ Fence rq ∧
      (let d := view xl ⟨L.source.side,.ld⟩
       d.mobile=.empty ∧ ∃ z,d.retained=.data z) ∧
      (let d := view xr ⟨R.source.side,.rd⟩
       d.mobile=.empty ∧ ∃ z,d.retained=.data z) := by
  let addr := fun j => S.getD j fall
  obtain ⟨lead,turn,back,E,found,_,ret⟩ := BStarAcquireAckAncestry.found_split_turn hp (from_idle hp T)
  have align : run x w=run (step (run x lead) turn) back := by rw [E,BStarResetSchedule.run_append]; rfl
  obtain ⟨_,_,_,_,_,ans,reply,F,OP⟩ := H
  rw [align] at reply
  obtain ⟨ini,out,issue,W,_,_,_,flight⟩ := found
  let start := step (run x ini) issue
  have Eq : run x lead=run start out := by rw [W,BStarResetSchedule.run_append]; rfl
  have cur := Eq.symm ▸ BStarAcquireHistoryReturn.busy_end hp flight
  obtain ⟨R,rq,fp,selR,iR,addrR,fr,forward,health,dataR⟩ :=
    terminal_fence hp chart sep turn back cur ret ans ⟨F,OP⟩ reply rightIn
  obtain ⟨sub,mark,gap,S0,preFlight,_,_,L,_,lq,selL,_,addrL,_,iL,fl⟩ :=
    find_fence_departure hp chart sep flight k k7 fp health 0 len rfl rfl (Nat.zero_le _) hk
      (Nat.le_refl _) (Eq ▸ forward)
  let pre := ini++issue::sub
  have stream : w=pre++mark::(gap++turn::back) := by
    rw [E,W,S0]
    simp only [pre,List.append_assoc,List.cons_append]
  have ls : run x pre=run start sub := by rw [BStarResetSchedule.run_append]; rfl
  have rs : run (step (run x pre) mark) gap=run x lead := by
    rw [ls,Eq,S0,BStarResetSchedule.run_append]; rfl
  let y := run start sub
  let gl := oldPair B y mark
  let xl := ((y mark).long,(y (rightNeighbor mark)).long)
  have lo := BStarAcquireHistoryReturn.busy_end hp preFlight
  have oldInside : (geometry gl L.source.side).inside=true := by
    have X0 : (longGeometry B (y (addr k).1)).inside=true :=
      (congrArg (fun z : Bool × Bool × Bool => z.2.1) (lo.1.1 _)).symm.trans leftIn
    have U : (addr k).1=site mark L.source.side := congrArg Prod.fst addrL
    rw [U] at X0
    cases Z : L.source.side <;> rw [Z] at X0 <;> exact X0
  have dataL := surviving_k7_data gl xl L lq iL oldInside fl.1 fl.2
    (pre_grant gl xl L lq (by rw [iL]; decide) selL)
  refine ⟨pre,gap,back,mark,turn,L,R,lq,rq,stream,?_,?_,addrL,addrR,iL,iR,fl,fr,?_,?_⟩
  · exact ls.symm ▸ selL
  · exact rs.symm ▸ selR
  · exact ls.symm ▸ dataL
  · exact rs.symm ▸ dataR

open BStarPostCutAttempt BStarGeneratedTapeCuts BStarNativeAttemptReceipts
local notation "pc" => BStarGeneratedBandScan.pc

/-- The successful FENCE receipt lies on the caller's generated
successful-attempt word, after the recorded PC5 consume. This uses
the first threshold 12 of the exact 6..408 band, not another attempt. -/
theorem fence_ack_of_attempt {base x : X} {addr : Nat → Pos n} {len : Nat}
    {w : List (Fin n)} (K : (addr 0).2=0)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (T : GeneratedOwner hp base addr len x .idle w .idle)
    (head : ∀ u v,w=u++v → oldH6 B (run x u) (addr 0).1=true)
    (A : AttemptPrefix hp base x addr len w) :
    ∃ pre ack rest,w=pre++ack::rest ∧
      GeneratedOwner hp base addr len x .idle pre (.busy 11 (.back 0)) ∧
      Hit hp base addr len (run x pre) ack 11 := by
  obtain ⟨lead,mid,_,hold,accept,sel,_,W,_,_,pc6,first,finish,M,pc408,live,_⟩ := A
  let start6 := step (run x lead) accept
  change pc start6 (addr 0).1=6 at pc6
  change pc (run start6 first) (addr 0).1=408 at pc408
  let rest := finish++sel::hold
  have splitWord : w=(lead++[accept])++(first++rest) := by
    rw [W,M]
    simp only [rest,List.append_assoc]
    rfl
  obtain ⟨_,_,G⟩ := BStarGeneratedTapeCuts.split hp (lead++[accept]) (first++rest) (splitWord ▸ T)
  have cut6 : run x (lead++[accept])=start6 := by rw [BStarResetSchedule.run_append]; rfl
  rw [cut6] at G
  obtain ⟨_,firstG,_⟩ := BStarGeneratedTapeCuts.split hp first rest G
  have mb : MidBand hp start6 (addr 0).1 first := by
    intro u v H
    cases v with
    | nil =>
      have U : first=u := by simpa using H
      subst u
      have E : w=((lead++[accept])++first)++rest := by simpa only [List.append_assoc] using splitWord
      have HH := head _ _ E
      rw [BStarResetSchedule.run_append,cut6] at HH
      exact ⟨HH,by omega,by omega⟩
    | cons e tail =>
      exact (live u e tail H).2.1 |> fun hh => ⟨hh,(live u e tail H).1⟩
  obtain ⟨toAck,ack,remaining,W12,_,hit,_⟩ :=
    threshold hp K sep firstG mb 11 (by omega) (by omega)
  let pre := lead++accept::toAck
  have begin : run x pre=run start6 toAck := by rw [BStarResetSchedule.run_append]; rfl
  have split : w=pre++ack::(remaining++rest) := by
    rw [splitWord,W12]
    simp only [pre,List.append_assoc,List.cons_append,List.nil_append]
  have H : Hit hp base addr len (run x pre) ack 11 := begin.symm ▸ hit
  obtain ⟨m,P,_⟩ := BStarGeneratedTapeCuts.split hp pre (ack::(remaining++rest)) (split ▸ T)
  have old := at_end hp P
  have eq : m=.busy 11 (.back 0) := by
    cases m with
    | idle => exact ((by decide : (2:Nat)≠1) (H.1.1.2.2.1.symm.trans old.1.2)).elim
    | busy op j =>
      have opEq : op=11 := old.1.2.2.2.symm.trans H.1.1.2.2.2
      subst op
      cases j with
      | out j =>
        exact (BStarOwnerControlHistory.pointed_backward_no_forward _ len 0 H.1.2.1 j old.2.1.1 old.2.1.2.1).elim
      | back j =>
        cases j with
        | zero => rfl
        | succ j =>
          have st := old.2.1.2.2.1 0 (Nat.zero_lt_succ _)
          obtain ⟨q,F⟩ := H.1.2.1.2.1
          exact Token.noConfusion (st.symm.trans F)
  exact ⟨pre,ack,remaining++rest,split,eq ▸ P,H⟩

end L4.BStarFenceChartData
