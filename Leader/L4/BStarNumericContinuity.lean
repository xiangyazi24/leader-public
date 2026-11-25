import Leader.L4.BStarNumericCarry
import Leader.L4.BStarCommitNoPrior

namespace L4.BStarNumericContinuity
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

open BStarOwnerLaunchOrigin BStarAcquireHistorySample BStarClearanceForward
open BStarLongClaims BStarLongTransport BStarLongRouting BStarLongCommandData
open BStarLongEvents BStarResetQuiet BStarResetQuietTable BStarResetIdleRing
open BStarNumericCarry BStarLongCommand
theorem joined_slot_cases (k₁ k₂ t₂ J₁ J₂ r tune p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r tune p c₁)))
    (a : AtK) (f : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r tune p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let out : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    DoorSafe g raw a → readK out a=.forward f → f.fault=0 →
    avoids a (middle g raw) ∨
    ∃ C q offer, (C,.advance offer)∈actualOffers g raw ∧ C∈orderedCommands g ∧ C.destination=some a ∧
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
  · exact .inl M
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
          obtain ⟨v,H⟩ := BStarForwardProvenance.joined_hop k₁ k₂ t₂ J₁ J₂ r tune p c₁ hp x C d q f E act F hf
          exact .inr ⟨C,v,q,act,hc,E,H⟩


open BStarSeparatorQuiet BStarResetChartService




private theorem canonical_quiet (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (a : AtK) (p : Payload) (E : bound g (readK raw) a=.forward p)
    (H : Numeric p) (keep : a∉discarded g) (mid : avoids a (middle g raw)) :
    avoids a (routing g raw) := by
  intro w M W
  rw [routing_parts] at M
  rcases List.mem_append.mp M with h|h
  · rcases List.mem_append.mp h with h|h
    · rcases List.mem_append.mp h with h|h
      · obtain ⟨q,_,Q⟩ := List.mem_filterMap.mp h
        dsimp only at Q
        split at Q
        · rename_i bad
          have eq := (congrArg Prod.fst (Option.some.inj Q)).trans W
          change q=a at eq
          subst q
          simp [E,isFault,H.1] at bad
        · contradiction
      · obtain ⟨q,hq,Q⟩ := List.mem_map.mp h
        have eq := (congrArg Prod.fst Q).trans W
        change q=a at eq
        subst q
        exact keep hq
    · exact mid w h W
  · obtain ⟨q,_,Q⟩ := List.mem_filterMap.mp h
    split at Q
    · contradiction
    · split at Q
      · rename_i t V
        cases A : observe q (geometry g q.side) t <;>
          simp only [A,Option.map_some,Option.map_none] at Q
        · contradiction
        · have eq := (congrArg Prod.fst (Option.some.inj Q)).trans W
          change q=a at eq
          subst q
          change bound g (readK raw) a=.forward t at V
          rw [E] at V
          cases V
          have G := numeric_gate (geometry g a.side) a.occurrence p H
          simp [observe,G] at A
      · contradiction

#print axioms joined_slot_cases
#print axioms canonical_quiet

/-- A healthy outward cursor that stays on its index preserves the
whole old canonical numeric payload. Selection of a structural link
elsewhere does not count as movement, and an incoming overwrite is
excluded by the chart's unique old live forward. -/
theorem ring_stay {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (e : Fin n) (he : e≠rightNeighbor e) (op k : Nat)
    (W : Waiting hp base (S.getD 0 fall).1 op x)
    (G : Good anyTag len (project (fun j => S.getD j fall) x) (.out k))
    (clean : OutClean len (project (fun j => S.getD j fall) x) (.out k))
    (p q : Payload)
    (F : project (fun j => S.getD j fall) x k=.forward p)
    (H : Numeric p) (canonical : ∀ g j, BStarLongCommand.bind g j (.forward p)=.forward p)
    (V : project (fun j => S.getD j fall) (step x e) k=.forward q) (Q : q.fault=0) :
    p=q := by
  let addr := fun j => S.getD j fall
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let g := oldPair B x e
  have unique := BStarOwnerControlHistory.pointed_unique_forward _ len k G clean
  have active (a : AtK) (E : addr k=address e a) : p=q := by
    have dst := (new_read B x e he a).trans ((congrArg (atCursor (step x e)) E).symm)
    obtain ⟨keep,safe⟩ := (frames_any hp chart W.1 e (.out k) (by intro H; cases H) G W.2.1 W.2.2.1).safe
      k G.1 a E
    have old (j : Nat) (r : AtK) (eq : addr j=address e r) :
        readK raw r=project addr x j :=
      (old_read x e r).trans ((congrArg (atCursor x) eq).symm)
    rcases joined_slot_cases _ _ _ _ _ _ _ _ _ hp (x e,x (rightNeighbor e)) a q safe
        (dst.trans V) Q with mid|⟨K,u,offer,_,mem,des,oldF,_,_⟩
    · have bound_eq : bound g (readK raw) a=.forward p := by
        unfold bound
        rw [(old k a E).trans F]
        exact canonical _ _
      have eq := joined_silent _ _ _ _ _ _ _ _ _ hp (x e,x (rightNeighbor e)) a safe
        (canonical_quiet g raw a p bound_eq H keep mid)
      exact Token.forward.inj (((old k a E).trans F).symm.trans (eq.symm.trans (dst.trans V)))
    · have L := BStarAcquireReturn.link_shape g K a mem des
      have own : a∈K.slots := by simp [Claim.slots,des]
      rcases touches hp chart W.1 e k G.1 K a mem own E with D|T|U|⟨j,J,inc⟩
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
      · obtain ⟨_,Kt,d,memT,desT,srcT,dstT⟩ := inc
        have hit : a=d := BStarResetMarkAdapter.address_inj e he (E.symm.trans (J ▸ dstT))
        have eq := BStarAcquireIncidence.same_claim g K Kt a mem memT own (by simp [Claim.slots,desT,hit])
        subst Kt
        have R := (unique j (by omega)).mp ⟨u,(old j K.source srcT).symm.trans oldF⟩
        omega
  by_cases l : (addr k).1=e
  · exact active (L (addr k).2) (Prod.ext l rfl)
  · by_cases rr : (addr k).1=rightNeighbor e
    · exact active (R (addr k).2) (Prod.ext rr rfl)
    · exact Token.forward.inj (F.symm.trans ((idle_off_pair hp x e (addr k) l rr).symm.trans V))

#print axioms ring_stay

private theorem outgoing_back (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (p q : Payload)
    (F : (BStarLongOutgoing.execute g j x p).carried=.forward q) (H : Numeric q) :
    Numeric p := by
  unfold BStarLongOutgoing.execute at F
  dsimp only at F
  repeat' first
    | (change Token.forward p = .forward q at F; cases F; exact H)
    | (change fault false = .forward q at F; unfold fault at F; cases F; exact
        ((show (1 : BitVec 1)≠0 by decide) H.1).elim)
    | split at F
  cases F
  exact H

private theorem padding_back (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (a : AtK) (p q : Payload)
    (pad : C.source.occurrence.val≠1 ∨ (geometry g C.source.side).inside=false)
    (R : arrive (geometry g a.side) a.occurrence (carried g raw C p)=.forward q)
    (H : Numeric q) : Numeric p := by
  have carrier : Numeric (carried g raw C p) := by
    unfold arrive at R
    split at R <;> cases R <;> exact H
  unfold carried at carrier
  dsimp only at carrier
  rw [visit_padding _ _ _ _ pad] at carrier
  split at carrier
  · rename_i q E
    exact outgoing_back _ _ _ _ _ E carrier
  all_goals exact ((show (1 : BitVec 1)≠0 by decide) carrier.1).elim

/-- A numeric post-packet of an actual non-IN or non-K1 advance is
the same canonical old packet, including all argument bits. -/
theorem ring_padding {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (e : Fin n) (he : e≠rightNeighbor e) (op k : Nat) (hk : k<len)
    (W : Waiting hp base (S.getD 0 fall).1 op x)
    (G : Good anyTag len (project (fun j => S.getD j fall) x) (.out k))
    (clean : OutClean len (project (fun j => S.getD j fall) x) (.out k))
    (p q : Payload)
    (F : project (fun j => S.getD j fall) x k=.forward p)
    (canon : ∀ g j, BStarLongCommand.bind g j (.forward p)=.forward p)
    (V : project (fun j => S.getD j fall) (step x e) (k+1)=.forward q)
    (H : Numeric q)
    (pad : (S.getD k fall).2.val≠1 ∨ (longGeometry B (x (S.getD k fall).1)).inside=false) :
    p=q := by
  let addr := fun j => S.getD j fall
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let g := oldPair B x e
  obtain ⟨C,a,t,sel,dst,src,endEq⟩ := BStarNumericChronology.ring_departure hp chart e he op k hk W G clean q V H.1
  change addr k=address e C.source at src
  change addr (k+1)=address e a at endEq
  have hm : C∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,sel,rfl⟩
  have no := (BStarAcquireReturn.link_shape g C a hm dst).1
  have provided : C.source.occurrence.val≠1 ∨ (geometry g C.source.side).inside=false := by
    change (addr k).2.val≠1 ∨ (longGeometry B (x (addr k).1)).inside=false at pad
    rw [src] at pad
    have E (s : Side) : geometry g s=longGeometry B (x (site e s)) := by cases s <;> rfl
    rw [E]
    exact pad
  have safe : a=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true := by
    intro E Z
    have J : a.occurrence.val=0 := congrArg (fun z : AtK => z.occurrence.val) E
    have N := (BStarAcquireJoinedHop.k0_dest g C a hm dst J).2
    simp [Z] at N
  have Jraw := (move_lands g raw C t a dst sel (Ne.symm no)).2
  have D := (new_read B x e he a).trans ((congrArg (atCursor (step x e)) endEq).symm)
  have DL := D.trans V
  change decode (readRaw (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) a)=_ at DL
  erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp (x e,x (rightNeighbor e)) a safe,Jraw,decode_encode] at DL
  have Num := padding_back g raw C a t q provided DL H
  have Bnd := offer_exact g raw C t sel Num
  have orig := (old_read x e C.source).trans ((congrArg (atCursor x) src).symm.trans F)
  unfold bound at Bnd
  rw [orig,canon _ _] at Bnd
  have EQ := Token.forward.inj Bnd
  subst t
  have Epad := visit_padding (geometry g C.source.side) C.source.occurrence
      (atOld raw C.source) p provided
  have carry : carried g raw C p=p := by
    exact (carried_numeric g raw C p (Epad.symm ▸ Num)).trans (congrArg Prod.snd Epad)
  rw [carry] at DL
  have off := numeric_gate (geometry g a.side) a.occurrence p Num
  simp [arrive,off] at DL
  exact DL

#print axioms ring_padding

/-- Carry continuity over an exact busy segment with no significant
departures: arbitrary stay/exterior marks and actual padding hops
retain the entire canonical numeric packet. A healthy numeric end
authenticates all intermediate packets on the same outward history. -/
theorem busy_padding {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {op : Nat} {z d : Cursor} {w : List (Fin n)}
    (P : BusyOnly hp base (fun j => S.getD j fall) len op x z w d) :
    ∀ k l p q, z=.out k → d=.out l → l≤len →
    (∀ j, k≤j → j<l → (S.getD j fall).2.val≠1 ∨ (longGeometry B (base (S.getD j fall).1)).inside=false) →
    project (fun j => S.getD j fall) x k=.forward p → Numeric p →
    (∀ g j, BStarLongCommand.bind g j (.forward p)=.forward p) →
    project (fun j => S.getD j fall) (BStarResetSchedule.run step x w) l=.forward q → Numeric q →
    p=q := by
  induction P with
  | nil I =>
    intro k l p q K L _ _ F _ _ Q _
    have E := Cursor.out.inj (K.symm.trans L)
    subst l
    exact Token.forward.inj (F.symm.trans Q)
  | @cons x z d final e w I E tail ih =>
    intro k l p q Z D hl pad F num canon Q N
    subst z
    obtain ⟨k',Z'⟩ := busy_no_back_to_out hp tail ⟨l,D⟩
    subst d
    have A : Advance len (.out k) (.out k') := by
      cases E with
      | transit _ _ _ _ seen =>
        cases seen with
        | cons _ _ A _ rest => cases rest; exact A
    obtain ⟨j,hj,u,U,hu,opc⟩ := BStarOwnerLaunchOrigin.busy_origin hp chart sep tail l hl q Q N.1
    have next := busy_start hp tail
    have Ueq := (BStarOwnerControlHistory.pointed_unique_forward _ len k' next.2.1 next.2.2 j hj).mp ⟨u,U⟩
    subst j
    have Nu : Numeric u := by
      refine ⟨hu,?_,?_⟩ <;> rw [opc]
      · exact N.2.1
      · exact N.2.2
    have le : k'≤l := BStarCommitNoPrior.outward_mono hp tail k' l rfl D
    have P0 : k≤k' := by cases A <;> omega
    apply ih k' l p q rfl D hl (fun j J L => pad j (Nat.le_trans P0 J) L) _ num canon Q N
    have EE : p=u := by
      cases A with
      | stay => exact ring_stay hp chart e (sep e) op k I.1 I.2.1 I.2.2 p u F num canon U hu
      | forward =>
        have pp := pad k (Nat.le_refl k) (by omega)
        have inside : (longGeometry B (base (S.getD k fall).1)).inside =
            (longGeometry B (x (S.getD k fall).1)).inside :=
          congrArg (fun z : Bool × Bool × Bool => z.2.1) (I.1.1 _)
        rw [inside] at pp
        exact ring_padding hp chart e (sep e) op k (by omega) I.1 I.2.1 I.2.2 p u F canon U Nu pp
    exact EE.symm ▸ U

#print axioms busy_padding
end L4.BStarNumericContinuity
