import Leader.L4.BStarNumericTerminal

namespace L4.BStarReplyBack
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongLayout BStarLongDoor BStarLongTransport
open BStarLongRouting BStarResetQuiet BStarSeparatorJoinedTags BStarSeparatorControl BStarResetQuietTable

/-- Binding of old D depends only on the payload, not the mark or slot. -/
def normal (p : Payload) : Token :=
  if p.fault != 0 || decide (p.opcode.toNat≥413) || p.race != 0 then fault true
  else match replyWidth p.opcode.toNat p.outcome.toNat p.argument.toNat with
    | none => fault true
    | some w => .reply (cropped p w)

theorem normal_eq (g : LongGeometry) (j : Fin 11) (p : Payload) :
    BStarLongCommand.bind g j (.reply p)=normal p := rfl

theorem normal_reply (p : Payload) : anyTag.D (normal p) := by
  unfold normal
  split <;> try exact ⟨_,rfl⟩
  split <;> exact ⟨_,rfl⟩

private theorem width_argument {op out n m : Nat} (A : op≠acquire) :
    replyWidth op out n=replyWidth op out m := by
  unfold replyWidth
  simp [A]

private theorem crop_twice (p : Payload) (k : Nat) : cropped (cropped p k) k=cropped p k := by
  unfold cropped low
  have b := Nat.lt_of_le_of_lt
    (Nat.mod_le (p.argument.toNat%2^k) (2^34)) (Nat.mod_lt p.argument.toNat (Nat.two_pow_pos k))
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt b]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat,Nat.mod_mod]

/-- If binding a previously bound D yields a healthy non-ACQUIRE
reply, the first bind already yielded exactly those same bytes. -/
theorem healthy_rebind (old p q : Payload) (A : normal old=.reply p)
    (B : normal p=.reply q) (Q : q.fault=0) (T : q.opcode.toNat≠acquire) :
    p=q := by
  have Back (u v : Payload) (E : normal u=.reply v) (h : v.fault=0) :
      ∃ w, v=cropped u w ∧
        (u.fault != 0 || decide (u.opcode.toNat≥413) || u.race != 0)=false ∧
        replyWidth u.opcode.toNat u.outcome.toNat u.argument.toNat=some w := by
    unfold normal at E
    split at E
    · cases E
      contradiction
    · rename_i hf
      split at E
      · cases E
        contradiction
      · rename_i k W
        cases E
        exact ⟨k,rfl,Bool.eq_false_iff.mpr hf,W⟩
  obtain ⟨k,R,V,W⟩ := Back p q B Q
  have P : p.fault=0 := (congrArg Payload.fault R).symm ▸ Q
  obtain ⟨j,S,_,J⟩ := Back old p A P
  subst p
  have L : old.opcode.toNat≠acquire := by
    intro H
    apply T
    rw [R]
    exact H
  change replyWidth old.opcode.toNat old.outcome.toNat (cropped old j).argument.toNat=some k at W
  rw [width_argument L (m:=old.argument.toNat),J] at W
  cases W
  rw [R,crop_twice]

private theorem fold_choices (a : AtK) (ws : List KWrite) (x : BitVec 52) (t : Token)
    (H : ∀ w∈ws, w.1=a → w.2=t) :
    ws.foldl (fun b w => putRaw b a w) x=x ∨
    ws.foldl (fun b w => putRaw b a w) x=encode t := by
  induction ws generalizing x with
  | nil => exact .inl rfl
  | cons w ws ih =>
    simp only [List.foldl_cons]
    cases ih (putRaw x a w) (fun z Z => H z (List.mem_cons_of_mem _ Z)) with
    | inr B => exact .inr B
    | inl A =>
      rw [A]
      by_cases E : w.1=a
      · exact .inr (by simp [putRaw,E.symm,H w List.mem_cons_self E])
      · exact .inl (by simp [putRaw,Ne.symm E])

private theorem only_normalizes (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (a : AtK) (p : Payload) (D : readK raw a=.reply p)
    (keep : a∉discarded g) (mid : avoids a (middle g raw)) :
    ∀ w∈routing g raw, w.1=a → w.2=normal p := by
  have bindEq : bound g (readK raw) a=normal p := by unfold bound; rw [D,normal_eq]
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
          exact (congrArg Prod.snd (Option.some.inj Q)).symm.trans bindEq
        · contradiction
      · obtain ⟨q,h,Q⟩ := List.mem_map.mp H
        have e := congrArg Prod.fst Q
        change q=a at e
        subst q
        exact (keep h).elim
    · exact (mid _ H rfl).elim
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
        obtain ⟨s,S⟩ := normal_reply p
        rw [S] at hf
        contradiction

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

theorem joined_hold (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (a : AtK) (p : Payload) :
    let g := Pair.map (longGeometry B) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let dst : Pair (BitVec LW) := Pair.map LargeSite.long (largePair B x)
    DoorSafe g raw a → readK raw a=.reply p → a∉discarded g → avoids a (middle g raw) →
    readK dst a=.reply p ∨ readK dst a=normal p := by
  dsimp only
  intro safe D keep mid
  let g := Pair.map (longGeometry B) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have H := only_normalizes g raw a p D keep mid
  have M : readRaw (patchPair (longWork g raw) raw) a =
      (routing g raw).foldl (fun b w => putRaw b a w) (readRaw raw a) := by
    by_cases h : a.occurrence.val=0
    · obtain ⟨s,j⟩ := a
      have J : j=(0 : Fin 11) := Fin.ext h
      subst j
      exact BStarK0Frame.k0_routing_only g raw s (safe.holds h)
    · exact raw_transit g raw a h
  change decode (readRaw _ a)=_ ∨ decode (readRaw _ a)=_
  erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp x a safe.valid,M]
  rcases fold_choices a (routing g raw) (readRaw raw a) (normal p) H with P|P
  · exact .inl ((congrArg decode P).trans D)
  · exact .inr ((congrArg decode P).trans (decode_encode _))

open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing
open BStarSeparatingRail BStarSeparatorQuiet BStarSeparatorParked
open BStarAcquireWaitControl BStarResetChartService BStarSeparatorRing BStarOwnerControlHistory
open BStarResetSchedule BStarLongEvents BStarAcquireReturn BStarSeparatorTags

theorem arrived_payload {base x : X} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (same : ∀ i, Layout B base i=Layout B x i)
    (e : Fin n) (he : e≠rightNeighbor e)
    (away : e≠RearTrace.predecessor (S.getD 0 fall).1) :
    let addr := fun j => S.getD j fall
    let y := AllSizeS1Geometry.step B x e
    ∀ pay : Payload, Clean (project addr) anyTag len x →
    project addr x 0=.reply pay →
    (project addr y 0=.reply pay ∨ project addr y 0=normal pay) := by
  dsimp only
  intro pay J D0
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
    rcases joined_hold hp (x e,x (rightNeighbor e)) (L 0) pay
      (safe_nonright _ _ _ (by decide)) (old.trans D0) keep mid with H|H
    · exact .inl (new.symm.trans H)
    · exact .inr (new.symm.trans H)
  · exact .inl ((BStarResetIdleRing.idle_off_pair hp x e (addr 0) E R).trans D0)

open scoped Classical

private theorem link_safety (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (c : CommandClaim) (a : AtK) (hm : c∈orderedCommands g) (hd : c.destination=some a) :
    c.source≠a ∧ DoorSafe g raw c.source ∧
      (a=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true) := by
  obtain ⟨ne,_,S⟩ := BStarAcquireReturn.link_shape g c a hm hd
  refine ⟨Ne.symm ne, safe_nonright _ _ _ ?_,?_⟩
  · intro E
    rw [E] at S
    exact S rfl rfl
  · intro E H
    have h0 : a.occurrence.val=0 := congrArg (fun z : AtK => z.occurrence.val) E
    have N := (BStarAcquireJoinedHop.k0_dest g c a hm hd h0).2
    rw [H] at N
    contradiction

theorem reverse_or_hold {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (e : Fin n) (he : e≠rightNeighbor e) (op k : Nat)
    (W : Waiting hp base (S.getD 0 fall).1 op x) (pay : Payload)
    (G : Good anyTag len (project (fun j => S.getD j fall) x) (.back (k+1)))
    (D : project (fun j => S.getD j fall) x (k+1)=.reply pay) :
    let addr := fun j => S.getD j fall
    let y := AllSizeS1Geometry.step B x e
    if linkAt hp x e addr len k then
      project addr y k=normal pay ∧ project addr y (k+1)=.empty
    else (project addr y (k+1)=.reply pay ∨ project addr y (k+1)=normal pay) := by
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
    have Q := (old_read x e d).trans ((congrArg (atCursor x) E).symm.trans D)
    have Q' := (old_read x e cl.source).trans ((congrArg (atCursor x) A).symm.trans T)
    have boundS : quiet (bound g (readK raw) cl.source) := by
      rw [quiet_bound g _ _ (.inr Q'),Q']
      exact .inr rfl
    obtain ⟨q,Eq⟩ := normal_reply pay
    have boundD : bound g (readK raw) d=.reply q := by
      unfold bound
      rw [Q,normal_eq,Eq]
    obtain ⟨_,safeS,safeD⟩ := link_safety g raw cl d hcl hd
    obtain ⟨P,clear⟩ := reply_lands g raw cl d q hcl hd boundS boundD
    have next (v : AtK) (safe : v=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true) :
        readK (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) v =
        readK (patchPair (longWork g raw) raw) v :=
      congrArg decode (joined_work_raw _ _ _ _ _ _ _ _ _ hp (x e,x (rightNeighbor e)) v safe)
    rw [←Eq] at P
    refine ⟨?_,?_⟩
    · exact (congrArg (atCursor y) A).trans
        ((new_read B x e he cl.source).symm.trans ((next _ safeS.valid).trans P))
    · exact (congrArg (atCursor y) E).trans
        ((new_read B x e he d).symm.trans ((next _ safeD).trans clear))
  · rename_i noPred
    have old (j : Nat) (a : AtK) (E : addr j=address e a) :
        readK raw a=project addr x j :=
      (old_read x e a).trans ((congrArg (atCursor x) E).symm)
    obtain ⟨q,Eq⟩ := normal_reply pay
    have boundD (a : AtK) (E : addr (k+1)=address e a) :
        bound g (readK raw) a=.reply q := by
      unfold bound
      rw [old _ _ E,D,normal_eq,Eq]
    have inside (a : AtK) (E : addr (k+1)=address e a) :
        project addr y (k+1)=.reply pay ∨ project addr y (k+1)=normal pay := by
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
          have avoid := terminal_avoids g raw cl hcl kind (by rw [boundD _ F]; exact .d q)
          exact fun w hw => avoid w (List.mem_flatMap.mpr ⟨v,hv,hw⟩)
        · obtain ⟨_,cl,d,hcl,hd,A,Bd⟩ := Lk
          have eq : a=cl.source := address_inj e he (E.symm.trans A)
          have ed := (old _ _ Bd).trans (G.2.2.2 (k+1+1) (by omega) (by omega))
          have hold : LinkHold (bound g (readK raw) cl.source) (bound g (readK raw) d) := by
            rw [boundD _ A,quiet_bound g _ d (Or.inl ed),ed]
            exact .de q
          have avoid := (link_avoids g raw cl d hcl (link_shape g cl d hcl hd).2.1 hd hold).1
          exact fun w hw h => avoid w (List.mem_flatMap.mpr ⟨v,hv,hw⟩) (h.trans eq)
        · have eq : i=k := by omega
          exact (noPred (eq ▸ Lk)).elim
      have result := joined_hold hp (x e,x (rightNeighbor e)) a pay safe ((old _ _ E).trans D) keep mid
      have post := (new_read B x e he a).trans ((congrArg (atCursor y) E).symm)
      exact result.elim (fun H => .inl (post.symm.trans H)) (fun H => .inr (post.symm.trans H))
    by_cases l : (addr (k+1)).1=e
    · exact inside (L (addr (k+1)).2) (Prod.ext l rfl)
    · by_cases rr : (addr (k+1)).1=rightNeighbor e
      · exact inside (R (addr (k+1)).2) (Prod.ext rr rfl)
      · exact .inl ((BStarResetIdleRing.idle_off_pair hp x e (addr (k+1)) l rr).trans D)

open BStarOwnerLaunchOrigin BStarGeneratedOwner BStarGeneratedPCAncestry

private theorem seen_advance {len : Nat} {x : X} {e : Fin n} {addr : Nat → Pos n}
    {z d : Cursor}
    (s : Seen step (project addr) anyTag len x z [e] d) : Advance len z d := by
  cases s with
  | cons _ _ A _ tail => cases tail; exact A

theorem backwards {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {op : Nat} {w : List (Fin n)} {z d : Cursor}
    (P : BusyOnly hp base (fun j => S.getD j fall) len op x z w d)
    (q : Payload) (healthy : q.fault=0) (nonacq : q.opcode.toNat≠acquire) :
    ∀ k l, z=.back k → d=.back l →
    (∃ p, project (fun j => S.getD j fall) (BStarResetSchedule.run step x w) l=.reply p ∧ normal p=.reply q) →
    ∃ p, project (fun j => S.getD j fall) x k=.reply p ∧ normal p=.reply q := by
  induction P with
  | nil _ =>
    intro k l A E D
    have h := Cursor.back.inj (A.symm.trans E)
    subst l
    exact D
  | @cons raw z d final e w I E tail ih =>
    intro k l Z L D
    subst z
    let addr := fun j => S.getD j fall
    have good := I.2.1
    obtain ⟨old,oldRead⟩ := good.2.1
    have quiet (j k : Nat) (J : Good anyTag len (project addr (step raw e)) (.back j))
        (K : k≤len) (A : anyTag.D (project addr (step raw e) k)) : j=k := by
      obtain ⟨u,U⟩ := A
      rcases Nat.lt_trichotomy j k with h|h|h
      · exact Token.noConfusion (U.symm.trans (J.2.2.2 k h K))
      · exact h
      · exact Token.noConfusion (U.symm.trans (J.2.2.1 k h))
    have finish (j : Nat) (idx : d=.back j)
        (edit : project addr (step raw e) j=.reply old ∨ project addr (step raw e) j=normal old) :
        ∃ p, project addr raw k=.reply p ∧ normal p=.reply q := by
      obtain ⟨p,P,Q⟩ := ih j l idx L D
      refine ⟨old,oldRead,?_⟩
      rcases edit with Ea|Ea
      · have Eq := Token.reply.inj (P.symm.trans Ea)
        exact Eq ▸ Q
      · have Eq := healthy_rebind old p q (Ea.symm.trans P) Q healthy nonacq
        exact (Ea.symm.trans P).trans (congrArg Token.reply Eq)
    cases k with
    | zero =>
      cases E with
      | arrived_hold _ away =>
        exact finish 0 rfl
          (arrived_payload hp C I.1.1 e (sep e) away old ⟨good.2.1,good.2.2.2⟩ oldRead)
      | transit _ _ _ nz _ => exact (nz rfl).elim
    | succ k =>
      have A : Advance len (.back (k+1)) d := by
        cases E with
        | transit _ _ _ _ h => exact seen_advance hp h
      have post := (busy_start hp tail).2.1
      have rr := reverse_or_hold hp C e (sep e) op k I.1 old good oldRead
      dsimp only at rr
      split at rr
      · have idx : d=.back k := by
          cases A
          · have H : anyTag.D (project addr (step raw e) k) := rr.1.symm ▸ normal_reply old
            have h := quiet (k+1) k post (by have := good.1; omega) H
            omega
          · rfl
        exact finish k idx (.inr rr.1)
      · have idx : d=.back (k+1) := by
          cases A
          · rfl
          · have H : anyTag.D (project addr (step raw e) (k+1)) :=
                rr.elim (fun H => ⟨old,H⟩) (fun H => H.symm ▸ normal_reply old)
            have h := quiet k (k+1) post good.1 H
            omega
        exact finish (k+1) idx rr

theorem normal_origin {p q : Payload} (E : normal p=.reply q) (H : q.fault=0) :
    p.fault=0 ∧ p.opcode=q.opcode := by
  unfold normal at E
  split at E
  · cases E
    contradiction
  · split at E
    · cases E
      contradiction
    · cases E
      exact ⟨H,rfl⟩

/-- Receipt at the waiting source on the same raw return suffix
authenticates the normalized terminal D, even when intermediate old
D bytes were not in canonical form. -/
theorem from_arrival {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {op k : Nat} {w : List (Fin n)}
    (P : BusyOnly hp base (fun j => S.getD j fall) len op x (.back k) w (.back 0))
    (q : Payload) (healthy : q.fault=0) (nonacq : q.opcode.toNat≠acquire)
    (E : let y := BStarResetSchedule.run step x w
      let i := (S.getD 0 fall).1
      bind (longGeometry B (y i)) 0 (atSite (y i).long 0)=.reply q) :
    ∃ p, project (fun j => S.getD j fall) x k=.reply p ∧
      normal p=.reply q ∧ p.fault=0 ∧ p.opcode=q.opcode := by
  have I := BStarAcquireHistoryReturn.busy_end hp P
  have K := (root_header hp C I.1.1).2
  obtain ⟨v,V⟩ := I.2.1.2.1
  have V0 : atSite ((BStarResetSchedule.run step x w) (S.getD 0 fall).1).long 0=.reply v := by
    change atSite _ (S.getD 0 fall).2=.reply v at V
    rw [K] at V
    exact V
  have N : normal v=.reply q := by
    dsimp only at E
    exact (congrArg (bind _ 0) V0.symm).trans E
  obtain ⟨p,R,Q⟩ := backwards hp C sep P q healthy nonacq k 0 rfl rfl ⟨v,V,N⟩
  exact ⟨p,R,Q,normal_origin Q healthy⟩

theorem from_hit {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {op k : Nat} {w : List (Fin n)} {e : Fin n}
    (P : BusyOnly hp base (fun j => S.getD j fall) len op x (.back k) w (.back 0))
    (H : BStarNativeReceiptTape.Hit hp base (fun j => S.getD j fall) len
      (BStarResetSchedule.run step x w) e op)
    (lo : 13≤op) :
    ∃ p q, project (fun j => S.getD j fall) x k=.reply p ∧
      normal p=.reply q ∧ p.fault=0 ∧ q.opcode.toNat=op ∧ p.opcode=q.opcode := by
  obtain ⟨_,_,_,_,_,q,Q,F,Op⟩ := H
  have T : q.opcode.toNat≠acquire := by rw [Op]; unfold acquire; omega
  obtain ⟨p,A,D,R,S⟩ := from_arrival hp C sep P q F T Q
  exact ⟨p,q,A,D,R,Op,S⟩

open BStarNumericCarry BStarNumericReceipt BStarClearanceForward
open BStarNumericHealthy BStarNumericTerminal in
/-- Invert the actual selected terminal handler using a healthy
numeric returned D. No healthy-offer hypothesis is needed. -/
theorem joined_numeric_terminal (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (C : CommandClaim) (offer q : Payload) (K : C.source.occurrence.val=10)
    (hd : C.destination=none) :
    let g := Pair.map (longGeometry B) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let dst : Pair (BitVec LW) := Pair.map LargeSite.long (largePair B x)
    (C,.advance offer)∈actualOffers g raw → readK dst C.source=.reply q →
    Numeric q → Numeric offer ∧ offer.opcode=q.opcode ∧ q=output offer := by
  dsimp only
  intro sel R N
  let g := Pair.map (longGeometry B) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have valid : C.source=BStarLongClaims.R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true := by
    intro E _
    rw [E] at K
    contradiction
  have oldR := R
  change decode (readRaw _ C.source)=_ at R
  erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp x C.source valid] at R
  rw [terminal_finish g raw C offer hd sel,decode_encode] at R
  change finish (carried g raw C offer)=.reply q at R
  obtain ⟨v,Op,_⟩ := finish_origin _ _ R N
  have A : arrive (geometry g C.source.side) C.source.occurrence (carried g raw C offer)=
      .forward (carried g raw C offer) := by
    simp [arrive,numeric_gate _ _ _ v]
  obtain ⟨M,O,_⟩ := selected_health g raw C C.source offer (carried g raw C offer) A v
  have E := joined_terminal k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x C offer K hd sel M
  exact ⟨M,O.trans Op,Token.reply.inj (oldR.symm.trans E)⟩

/-- The actual matching numeric source Hit proves the health of the
selected old K10 offer, rather than taking it as an extra premise. -/
theorem numeric_selected_from_hit {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {op : Nat} {e door : Fin n} {ret : List (Fin n)}
    (P : BusyOnly hp base (fun j => S.getD j fall) len op (step x e) (.back len) ret (.back 0))
    (H : BStarNativeReceiptTape.Hit hp base (fun j => S.getD j fall) len
      (BStarResetSchedule.run step (step x e) ret) door op)
    (lo : 13≤op) (hi : op<408) (C : CommandClaim) (offer : Payload)
    (K : C.source.occurrence.val=10) (hd : C.destination=none)
    (addr : S.getD len fall=address e C.source)
    (sel : (C,.advance offer)∈actualOffers (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)) :
    Numeric offer ∧ offer.opcode.toNat=op ∧
    project (fun j => S.getD j fall) (step x e) len=.reply (output offer) := by
  obtain ⟨p,q,D,_,F,Q,O⟩ := from_hit hp chart sep P H lo
  have N : Numeric p := ⟨F,by rw [O,Q]; exact lo,by rw [O,Q]; exact hi⟩
  have raw := (new_read B x e (sep e) C.source).trans ((congrArg (atCursor (step x e)) addr).symm.trans D)
  obtain ⟨M,J,E⟩ := joined_numeric_terminal hp (x e,x (rightNeighbor e)) C offer p K hd sel raw N
  exact ⟨M,by rw [J,O,Q],D.trans (congrArg Token.reply E)⟩

end L4.BStarReplyBack
