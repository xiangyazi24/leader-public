import Leader.L4.BStarAcquireHistorySample
import Leader.L4.BStarAcquireDoorHistory
import Leader.L4.BStarAcquireReadout

namespace L4.BStarAcquireHistoryReturn
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing
open BStarSeparatingRail BStarSeparatorControl BStarSeparatorQuiet BStarSeparatorParked
open BStarSeparatorJoinedTags BStarResetSchedule BStarAcquireWaitControl
open BStarLongDoor BStarResetChartService BStarSeparatorRing BStarOwnerControlHistory

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "XX" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

open BStarResetQuiet BStarLongTransport BStarLongRouting BStarLongEvents BStarLongToken BStarLongCommand
open BStarResetQuietTable BStarAcquireReturn

theorem reply_routing (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (a : AtK) (pay : Payload) (D : readK raw a=.reply pay)
    (V : ValidReply pay) (keep : a∉discarded g) (mid : avoids a (middle g raw)) :
    avoids a (routing g raw) := by
  have bindEq : bound g (readK raw) a=.reply pay := by
    unfold bound
    rw [D,valid_reply_binding _ _ _ V]
  rw [routing_parts]
  intro w hw E
  rcases w with ⟨q,t⟩
  change q=a at E
  subst q
  rcases List.mem_append.mp hw with H|H
  · rcases List.mem_append.mp H with H|H
    · rcases List.mem_append.mp H with H|H
      · obtain ⟨q,_,Q⟩ := List.mem_filterMap.mp H
        dsimp only at Q
        split at Q
        · have e := congrArg Prod.fst (Option.some.inj Q)
          change q=a at e
          subst q
          rename_i h
          rw [bindEq] at h
          simp [isFault,V.1] at h
        · contradiction
      · obtain ⟨q,h,Q⟩ := List.mem_map.mp H
        have e := congrArg Prod.fst Q
        change q=a at e
        subst q
        exact keep h
    · exact mid _ H rfl
  · obtain ⟨q,_,Q⟩ := List.mem_filterMap.mp H
    split at Q
    · contradiction
    · split at Q
      all_goals try contradiction
      rename_i f hf
      cases h : observe q (geometry g q.side) f with
      | none => simp [h] at Q
      | some z =>
        rw [h] at Q
        have e := congrArg Prod.fst (Option.some.inj Q)
        change q=a at e
        subst q
        rw [bindEq] at hf
        contradiction

theorem arrived_payload {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (same : ∀ i, Layout B base i=Layout B x i)
    (e : Fin n) (he : e≠rightNeighbor e)
    (away : e≠RearTrace.predecessor (S.getD 0 fall).1) :
    let addr := fun j => S.getD j fall
    let y := AllSizeS1Geometry.step B x e
    ∀ pay : Payload, BStarAcquireReturn.ValidReply pay → Clean (project addr) anyTag len x →
    project addr x 0=.reply pay → project addr y 0=.reply pay := by
  dsimp only
  intro pay valid J D0
  let addr := fun j => S.getD j fall
  let root := (addr 0).1
  let y := AllSizeS1Geometry.step B x e
  have R : root≠rightNeighbor e := fun r => away
    ((RearTrace.predecessor_right e).symm.trans (congrArg RearTrace.predecessor r.symm))
  have Hh := root_header hp C same
  by_cases E : root=e
  · have hit : addr 0=address e (L 0) := Prod.ext E Hh.2
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    have mid : BStarResetQuiet.avoids (L 0) (middle g raw) := by
      apply middle_avoids_of_chart
      intro v hv ha
      have mc : v.1∈orderedCommands g := by
        rw [←actualOffers_claims g raw]
        exact List.mem_map.mpr ⟨v,hv,rfl⟩
      rcases touches hp C same e 0 (Nat.zero_le _) v.1 (L 0) mc ha hit with D|T|L|⟨i,U,_⟩
      · cases D.2.2
      · obtain ⟨Eq,k,hk,_,_,idx,H⟩ := T
        have val := congrArg (fun z : Pos n => z.2.val) (hit.symm.trans (Eq ▸ H))
        exact (by change 0=k.source.occurrence.val at val; omega : False).elim
      · obtain ⟨lim,k,d,hk,hd,src,dst⟩ := L
        have eq := address_inj e he (hit.symm.trans src)
        have old (j : Nat) (a : AtK) (h : addr j=address e a) :
            readK raw a=project addr x j :=
          (old_read x e a).trans ((congrArg (atCursor x) h).symm)
        have D' := (old 0 k.source src).trans D0
        have E' := (old 1 d dst).trans (J.2 1 (by decide) (by omega))
        have Lh : LinkHold (bound g (readK raw) k.source) (bound g (readK raw) d) := by
          unfold bound
          rw [D',E']
          obtain ⟨p,Bd⟩ := bound_D (geometry g k.source.side) k.source.occurrence pay
          rw [Bd]
          exact .de p
        have H := link_avoids g raw k d hk (BStarAcquireReturn.link_shape g k d hk hd).2.1 hd Lh
        exact fun w hw heq => H.1 w (List.mem_flatMap.mpr ⟨v,hv,hw⟩) (heq.trans eq)
      · omega
    have old : readK raw (L 0)=project addr x 0 :=
      (old_read x e _).trans ((congrArg (atCursor x) hit).symm)
    have new : readK (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) (L 0)
        =project addr y 0 :=
      (new_read B x e he _).trans ((congrArg (atCursor y) hit).symm)
    have keep := not_discarded hp C same e 0 (Nat.zero_le _) _ hit
    have route := reply_routing g raw (L 0) pay ((old.trans D0)) valid keep mid
    exact new.symm.trans ((BStarAcquireHistorySample.joined_silent k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
      (x e,x (rightNeighbor e)) (L 0) (safe_nonright _ _ _ (by decide)) route).trans (old.trans D0))
  · exact (BStarResetIdleRing.idle_off_pair hp x e (addr 0) E R).trans D0


open scoped Classical

theorem reverse_or_hold {base x : XX} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (e : Fin n) (he : e≠rightNeighbor e) (op k : Nat)
    (W : Waiting hp base (S.getD 0 fall).1 op x) (pay : Payload) (V : ValidReply pay)
    (G : Good anyTag len (project (fun j => S.getD j fall) x) (.back (k+1)))
    (D : project (fun j => S.getD j fall) x (k+1)=.reply pay) :
    let addr := fun j => S.getD j fall
    let y := AllSizeS1Geometry.step B x e
    if linkAt hp x e addr len k then
      project addr y k=.reply pay ∧ project addr y (k+1)=.empty
    else project addr y (k+1)=.reply pay := by
  classical
  dsimp only
  let addr := fun j => S.getD j fall
  let y := AllSizeS1Geometry.step B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let g := oldPair B x e
  split
  · rename_i h
    obtain ⟨_,cl,d,hcl,hd,A,E⟩ := h
    have T := G.2.2.1 k (by omega)
    change addr k=address e cl.source at A
    change addr (k+1)=address e d at E
    have equiv (z : XX) (a : AtK) :
        BStarAcquireDoorHistory.readSite (fun i => (z i).long)
          (BStarAcquireDoorHistory.addr e a)=atCursor z (address e a) := by
      obtain ⟨s,j⟩ := a
      cases s <;> rfl
    have P := BStarAcquireDoorHistory.ring_reverse k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
      x e (Ne.symm he) cl d pay hcl hd
      (by rw [equiv,←A]; exact T) (by rw [equiv,←E]; exact D) V
    constructor
    · change atCursor y (addr k) = _; rw [A,←equiv]; exact P.1
    · change atCursor y (addr (k+1)) = _; rw [E,←equiv]; exact P.2
  · rename_i noPred
    have old (j : Nat) (a : AtK) (E : addr j=address e a) :
        readK raw a=project addr x j :=
      (old_read x e a).trans ((congrArg (atCursor x) E).symm)
    have boundD (a : AtK) (E : addr (k+1)=address e a) :
        bound g (readK raw) a=.reply pay := by
      unfold bound
      rw [old _ _ E,D,valid_reply_binding _ _ _ V]
    have inside (a : AtK) (E : addr (k+1)=address e a) :
        project addr y (k+1)=.reply pay := by
      have MF := frames_any hp C W.1 e (.back (k+1)) (by intro h; cases h) G W.2.1 W.2.2.1
      obtain ⟨keep,safe⟩ := MF.safe (k+1) G.1 a E
      have mid : avoids a (middle g raw) := by
        apply middle_avoids_of_chart
        intro v hv ha
        have mem : v.1∈orderedCommands g := by
          rw [←actualOffers_claims g raw]
          exact List.mem_map.mpr ⟨v,hv,rfl⟩
        rcases touches hp C W.1 e (k+1) G.1 v.1 a mem ha E with Dr|T|Lk|⟨i,I,Lk⟩
        · have eq := Dr.2.2
          omega
        · obtain ⟨idx,cl,hcl,kind,_,_,src⟩ := T
          have F : addr (k+1)=address e cl.source := by
            change k+1=len at idx
            rw [idx]; exact src
          have eq : a=cl.source := address_inj e he (E.symm.trans F)
          subst a
          have avoid := terminal_avoids g raw cl hcl kind (by rw [boundD _ F]; exact .d pay)
          exact fun w hw => avoid w (List.mem_flatMap.mpr ⟨v,hv,hw⟩)
        · obtain ⟨_,cl,d,hcl,hd,A,Bd⟩ := Lk
          have eq : a=cl.source := address_inj e he (E.symm.trans A)
          have ed := (old _ _ Bd).trans (G.2.2.2 (k+1+1) (by omega) (by omega))
          have hold : LinkHold (bound g (readK raw) cl.source) (bound g (readK raw) d) := by
            rw [boundD _ A,quiet_bound g _ d (Or.inl ed),ed]
            exact .de pay
          have avoid := (link_avoids g raw cl d hcl (link_shape g cl d hcl hd).2.1 hd hold).1
          exact fun w hw h => avoid w (List.mem_flatMap.mpr ⟨v,hv,hw⟩) (h.trans eq)
        · have eq : i=k := by omega
          exact (noPred (eq ▸ Lk)).elim
      have result := BStarAcquireHistorySample.joined_silent k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
        (x e,x (rightNeighbor e)) a safe (reply_routing g raw a pay ((old _ _ E).trans D) V keep mid)
      have post := (new_read B x e he a).trans ((congrArg (atCursor y) E).symm)
      exact post.symm.trans (result.trans ((old _ _ E).trans D))
    by_cases l : (addr (k+1)).1=e
    · exact inside (L (addr (k+1)).2) (Prod.ext l rfl)
    · by_cases rr : (addr (k+1)).1=rightNeighbor e
      · exact inside (R (addr (k+1)).2) (Prod.ext rr rfl)
      · exact (BStarResetIdleRing.idle_off_pair hp x e (addr (k+1)) l rr).trans D


open BStarOwnerLaunchOrigin BStarGeneratedOwner BStarResetSchedule

private theorem seen_advance {len : Nat} {x : XX} {e : Fin n} {addr : Nat → Pos n}
    {z d : Cursor}
    (s : Seen (AllSizeS1Geometry.step B) (project addr) anyTag len x z [e] d) :
    Advance len z d := by
  cases s with
  | cons _ _ A _ tail => cases tail; exact A

/-- On the actual busy suffix, the valid return carries the exact same
52-bit token up to and including the arrived, not yet consumed state. -/
theorem busy_return_payload {base x : XX} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {op : Nat} {w : List (Fin n)} {z d : Cursor}
    (P : BusyOnly hp base (fun j => S.getD j fall) len op x z w d)
    (pay : Payload) (V : ValidReply pay) :
    ∀ k, z=.back k → project (fun j => S.getD j fall) x k=.reply pay →
      ∃ j, d=.back j ∧
        project (fun j => S.getD j fall) (BStarResetSchedule.run (AllSizeS1Geometry.step B) x w) j=.reply pay := by
  induction P with
  | nil _ =>
    intro k E D
    exact ⟨k,E,D⟩
  | @cons raw z d final e w I E tail ih =>
    intro k Z D
    subst z
    let addr := fun j => S.getD j fall
    let next := AllSizeS1Geometry.step (n:=n) B
    change project addr raw k=.reply pay at D
    have good := I.2.1
    have uniq (l j : Nat) (J : Good anyTag len (project addr (next raw e)) (.back l))
        (Lj : j≤len) (D' : project addr (next raw e) j=.reply pay) : l=j := by
      rcases Nat.lt_trichotomy l j with hj|eq|hj
      · exact Token.noConfusion (D'.symm.trans (J.2.2.2 j hj Lj))
      · exact eq
      · exact Token.noConfusion (D'.symm.trans (J.2.2.1 j hj))
    cases k with
    | zero =>
      cases E with
      | arrived_hold _ away =>
        have Dr := arrived_payload hp C I.1.1 e (sep e) away pay V ⟨good.2.1,good.2.2.2⟩ D
        exact ih 0 rfl Dr
      | transit _ _ _ nz _ => exact (nz rfl).elim
    | succ k =>
      have A : Advance len (.back (k+1)) d := by
        cases E with
        | transit _ _ _ _ h => exact seen_advance hp h
      have post := (busy_start hp tail).2.1
      have rr := reverse_or_hold hp C e (sep e) op k I.1 pay V good D
      dsimp only at rr
      split at rr
      · have idx : d=.back k := by
          cases A
          · have h := uniq (k+1) k post (by have := good.1; omega) rr.1
            omega
          · rfl
        exact ih k idx rr.1
      · have idx : d=.back (k+1) := by
          cases A
          · rfl
          · have h := uniq k (k+1) post good.1 rr
            omega
        exact ih (k+1) idx rr

#print axioms arrived_payload
#print axioms reverse_or_hold
#print axioms busy_return_payload

theorem busy_end {base x : XX} {addr : Nat → Pos n} {len op : Nat}
    {w : List (Fin n)} {z d : Cursor}
    (P : BusyOnly hp base addr len op x z w d) :
    Current hp base addr len (BStarResetSchedule.run (AllSizeS1Geometry.step B) x w)
      (.busy op d) := by
  induction P with
  | nil I => exact I
  | cons _ _ _ ih => exact ih

open BStarLongLayout BStarAcquireReadout

/-- Same tape from the original ISSUE5 to the literal consuming mark.
Every last won visit of its completed all-win itinerary is read out
at the source with the actual selector and headers sampled on that visit. -/
theorem found_install {base x : XX} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w ret : List (Fin n)} (e : Fin n)
    (F : Found hp base (fun j => S.getD j fall) len acquire x w (.out len))
    (T : onTerminal hp (BStarResetSchedule.run (AllSizeS1Geometry.step B) x w) e
      (fun j => S.getD j fall) len)
    (P : BusyOnly hp base (fun j => S.getD j fall) len acquire
      (BStarResetSchedule.run (AllSizeS1Geometry.step B) x (w++[e]))
      (.back len) ret (.back 0)) :
    let root := (S.getD 0 fall).1
    let door := RearTrace.predecessor root
    let y := BStarResetSchedule.run (AllSizeS1Geometry.step B) x ((w++[e])++ret++[door])
    ∃ vs : List BStarAcquireLatch.Visit,
      (∀ j : Fin 3, (vs.filter (fun v => v.incidence.val==j.val)).length=1) ∧
      (vs.all BStarAcquireLatch.Visit.wins=true →
      ∀ v∈vs,
        (((capturedSelector v.incidence).read (y root).long).toNat,
          ((headerBlock v.incidence).read (y root).long).toNat) =
          (v.selector.val,v.headers.toNat)) := by
  dsimp only
  let addr := fun j => S.getD j fall
  let root := (addr 0).1
  let door := RearTrace.predecessor root
  let next := AllSizeS1Geometry.step (n:=n) B
  let z := BStarResetSchedule.run next x (w++[e])
  let s := BStarResetSchedule.run next z ret
  have Hdoor : rightNeighbor door=root := RearTrace.right_predecessor root
  obtain ⟨vs,receipt,once,tag,R,V,_⟩ := BStarAcquireHistorySample.found_terminal hp C sep F e T
  have init : project addr z len=.reply receipt := by
    change atCursor (BStarResetSchedule.run next x (w++[e])) (addr len)=_
    rw [BStarResetSchedule.run_append]
    exact tag
  obtain ⟨j,J,D⟩ := busy_return_payload hp C sep P receipt V len rfl init
  have j0 : j=0 := (Cursor.back.inj J).symm
  subst j
  have WT := busy_end hp P
  have wait : Waiting hp base root acquire s := WT.1
  obtain ⟨head,K⟩ := root_header hp C wait.1
  have RD : atSite (s (rightNeighbor door)).long 0=.reply receipt := by
    rw [Hdoor]
    change project addr s 0=.reply receipt at D
    unfold project at D
    change atSite (s root).long (addr 0).2=.reply receipt at D
    rw [K] at D
    exact D
  have bound : bind (longGeometry B (s (rightNeighbor door))) 0
      (atSite (s (rightNeighbor door)).long 0)=.reply receipt := by
    rw [RD]
    exact valid_reply_binding _ _ _ V
  have Y : next s door root=(largePair B (s door,s (rightNeighbor door))).2 := by
    simp only [next,AllSizeS1Geometry.step,←Hdoor,if_neg (Ne.symm (sep door)),if_true]
  refine ⟨vs,once,?_⟩
  intro allWin v inVs
  obtain ⟨before,after,cover,_⟩ := List.eq_append_cons_of_mem inVs
  have allSeg := allWin
  rw [cover,List.all_append,List.all_cons] at allSeg
  simp only [Bool.and_eq_true] at allSeg
  obtain ⟨hw,win,hwa⟩ := allSeg
  have last : ∀ q∈after,q.incidence≠v.incidence := by
    intro q mq eq
    have L := once v.incidence
    rw [cover,List.filter_append,List.filter_cons] at L
    simp only [BEq.rfl,if_true,List.length_append,List.length_cons] at L
    have H : q∈after.filter (fun u => u.incidence.val==v.incidence.val) :=
      List.mem_filter.mpr ⟨mq,by simp [eq]⟩
    have N := List.length_pos_of_mem H
    omega
  have readout := joined_recovers_sample k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (s door,s (rightNeighbor door)) before after v hw win hwa last
    (by change oldH6 B (s) (rightNeighbor door)=true; rw [Hdoor]; exact head)
    (by change (ctrlPhase.read (s (rightNeighbor door)).long).toNat=2; rw [Hdoor]; exact wait.2.2.1)
    (by change (ctrlOp.read (s (rightNeighbor door)).long).toNat=acquire; rw [Hdoor]; exact wait.2.2.2)
    (by rw [←cover]; exact bound.trans R.symm)
  change _ = _ at readout
  rw [←Y] at readout
  rw [BStarResetSchedule.run_append, BStarResetSchedule.run_append next x (w++[e]) ret]
  exact readout

#print axioms found_install
end L4.BStarAcquireHistoryReturn
