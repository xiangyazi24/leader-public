import Leader.L4.BStarOwnerLaunchOrigin
import Leader.L4.BStarStageProvenance

namespace L4.BStarStageOwnerOrigin
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

open BStarOwnerLaunchOrigin BStarStageProvenance BStarClearanceForward
open BStarLongClaims BStarLongTransport BStarLongRouting BStarLongCommandData
open BStarLongEvents BStarResetQuiet BStarResetQuietTable BStarResetIdleRing

theorem joined_slot_origin (k₁ k₂ t₂ J₁ J₂ r tune p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r tune p c₁)))
    (a : AtK) (f : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r tune p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let out : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    DoorSafe g raw a → readK out a=.forward f → Stage f →
    (∃ q, readK raw a=.forward q ∧ Stage q ∧ arg q=arg f) ∨
    ∃ C q, C∈orderedCommands g ∧ C.destination=some a ∧
      readK raw C.source=.forward q ∧ Stage q ∧ arg q=arg f := by
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
  · exact .inl (joined_idle k₁ k₂ t₂ J₁ J₂ r tune p c₁ hp x a f M safe F hf)
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

/-- In a live WAIT on the settled chart, every healthy new STAGE at an
owner address has an old healthy STAGE of identical effective payload on that
same owner chart, regardless of the selected raw mark. -/
theorem ring_origin {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (e : Fin n) (he : e≠rightNeighbor e) (op : Nat) (z : Cursor)
    (live : z≠.back 0) (W : Waiting hp base (S.getD 0 fall).1 op x)
    (G : Good anyTag len (project (fun j => S.getD j fall) x) z)
    (i : Nat) (hi : i≤len) (pay : Payload)
    (F : project (fun j => S.getD j fall) (step x e) i=.forward pay)
    (H : Stage pay) :
    ∃ j≤len, ∃ q, project (fun j => S.getD j fall) x j=.forward q ∧
      Stage q ∧ arg q=arg pay := by
  let addr := fun j => S.getD j fall
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let g := oldPair B x e
  have active (a : AtK) (E : addr i=address e a) :
      ∃ j≤len, ∃ q, project addr x j=.forward q ∧ Stage q ∧ arg q=arg pay := by
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

theorem busy_origin {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {op : Nat} {z d : Cursor} {w : List (Fin n)}
    (P : BusyOnly hp base (fun j => S.getD j fall) len op x z w d)
    (i : Nat) (hi : i≤len) (pay : Payload)
    (F : project (fun j => S.getD j fall) (BStarResetSchedule.run step x w) i=.forward pay)
    (hf : Stage pay) :
    ∃ j≤len, ∃ q, project (fun j => S.getD j fall) x j=.forward q ∧
      Stage q ∧ arg q=arg pay := by
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

/-- A healthy actual STAGE on the generated owner rail traces to its
genuine own ISSUE408, with equality of the full effective payload and
a literal uninterrupted busy suffix. -/
theorem from_generated {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {m : Mode} {w : List (Fin n)}
    (P : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (now : Current hp base (fun j => S.getD j fall) len (BStarResetSchedule.run step x w) m)
    (i : Nat) (hi : i≤len) (pay : Payload)
    (F : project (fun j => S.getD j fall) (BStarResetSchedule.run step x w) i=.forward pay)
    (hf : Stage pay) :
    m=.busy stageOp (.out i) ∧
      ∃ pre post e a, w=pre++e::post ∧
        let old := BStarResetSchedule.run step x pre
        let root := (S.getD 0 fall).1
        e=RearTrace.predecessor root ∧ Launch (old root).long ((step old e) root).long ∧ (ctrlOp.read (old root).long).toNat=stageOp ∧
        initial stageOp (old root).long=some a ∧ low a 25=arg pay ∧
        BusyOnly hp base (fun j => S.getD j fall) len stageOp (step old e) (.out 0) post (.out i) := by
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
      obtain ⟨j,hj,q,Q,Qstage,argEq⟩ := oldF
      have cur := busy_start hp busy
      have j0 : j=0 := (BStarOwnerControlHistory.pointed_unique_forward _ len 0 cur.2.1 cur.2.2 j hj).mp ⟨q,Q⟩
      subst j
      obtain ⟨valid,a,init,snap⟩ := L
      have root := (root_header hp C cur.1.1).2
      change atSite (start (S.getD 0 fall).1).long (S.getD 0 fall).2=.forward q at Q
      rw [root] at Q
      have Bt : forward (ctrlOp.read (old (S.getD 0 fall).1).long).toNat a=.forward q :=
        (congrArg (fun t : (Token × BitVec 2) × BitVec 9 => t.1.1) snap).symm.trans Q
      injection Bt with payload
      have key : q.opcode=BitVec.ofNat 9 op :=
        (congrArg Payload.opcode payload).symm.trans (congrArg (BitVec.ofNat 9) pc)
      have bound : op<512 := by
        have R := (ctrlOp.read (old (S.getD 0 fall).1).long).isLt
        change (ctrlOp.read (old (S.getD 0 fall).1).long).toNat<512 at R
        exact pc ▸ R
      have P' : op=stageOp := by
        have K := congrArg BitVec.toNat key
        rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound] at K
        exact K.symm.trans Qstage.2
      have A0 : low a 25=arg q := by
        have Arg := congrArg Payload.argument payload
        change BitVec.ofNat 34 a=q.argument at Arg
        unfold arg
        rw [←Arg]
        exact (Nat.mod_mod_of_dvd a (by decide : 2^25 ∣ 2^34)).symm
      exact ⟨congrArg (fun op => Mode.busy op (.out i)) P',pre,post,e,a,split,atDoor,
        ⟨valid,a,init,snap⟩,pc.trans P',by rwa [pc,P'] at init,A0.trans argEq,P' ▸ busy⟩

/-- Actual healthy STAGE offered by the selected body row of the
same owner. Starting from idle, its full effective payload has
an authenticated physical ISSUE408 ancestor on the given tape. -/
theorem offered_from_generated {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {m : Mode} {w : List (Fin n)}
    (P : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (now : Current hp base (fun j => S.getD j fall) len (BStarResetSchedule.run step x w) m)
    (i : Nat) (hi : i≤len) (e : Fin n) (K : CommandClaim) (p : Payload)
    (idx : S.getD i fall=address e K.source) (good : Stage p) :
    let state := BStarResetSchedule.run step x w
    (K,.advance p)∈actualOffers (oldPair B state e)
      ((state e).long,(state (rightNeighbor e)).long) →
    m=.busy stageOp (.out i) ∧
    ∃ pre post door a, w=pre++door::post ∧
      let old := BStarResetSchedule.run step x pre
      let root := (S.getD 0 fall).1
      door=RearTrace.predecessor root ∧
      Launch (old root).long ((step old door) root).long ∧
      (ctrlOp.read (old root).long).toNat=stageOp ∧
      initial stageOp (old root).long=some a ∧ low a 25=arg p ∧
      BusyOnly hp base (fun j => S.getD j fall) len stageOp
        (step old door) (.out 0) post (.out i) := by
  dsimp only
  intro sel
  let state := BStarResetSchedule.run step x w
  obtain ⟨q,Q,H,E⟩ := offer_origin _ _ K p sel good
  have F : project (fun j => S.getD j fall) state i=.forward q := by
    change atCursor state (S.getD i fall)=_
    rw [idx,←old_read state e K.source]
    exact Q
  obtain ⟨mode,pre,post,door,a,split,nom,launched,op,init,val,busy⟩ :=
    from_generated hp C sep P now i hi q F H
  exact ⟨mode,pre,post,door,a,split,nom,launched,op,init,val.trans E,busy⟩

end L4.BStarStageOwnerOrigin
