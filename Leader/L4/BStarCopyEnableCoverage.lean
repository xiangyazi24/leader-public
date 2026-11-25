import Leader.L4.BStarCopyAttemptBand
import Leader.L4.BStarNumericChronology
import Leader.L4.BStarCopyLoadHistory
import Leader.L4.BStarNumericHealthy

namespace L4.BStarCopyEnableCoverage
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongArithmetic BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetMarkAdapter BStarOwnerLaunchOrigin
open BStarLongEvents BStarResetChartTouch BStarAcquireForwardTrace
open BStarLongCommandData BStarLongPrep BStarLongPackets BStarLongLiteral
open BStarNumericChronology BStarGeneratedOwner BStarCopyAttemptBand BStarGeneratedBandScan

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step
local notation "D" => Departure (n:=n) (k₁:=k₁) (k₂:=k₂) (t₂:=t₂) (J₁:=J₁)
  (J₂:=J₂) (r:=r) (c:=c) (p:=p) (c₁:=c₁)

theorem selected_enable (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (v : Payload) (sh : Sheet)
    (sel : (C,.advance v)∈actualOffers g raw)
    (good : v.fault=0) (op : v.opcode.toNat=9)
    (lane : sh∈prepSites (geometry g C.source.side) C.source.occurrence .enable) :
    ∃ a : BStarLongPrep.Offer, a.claim.op=.enable ∧
      a.claim.lane=⟨C.source.side,sh⟩ ∧ a∈(arbitration (round g raw).prep).1 := by
  let a : BStarLongPrep.Offer := ⟨⟨.enable,C.source,⟨C.source.side,sh⟩⟩,.empty⟩
  have G : (C,.advance v)∈gated g raw := by
    unfold actualOffers BStarLongGrant.run at sel
    obtain ⟨entry,hm,E⟩ := List.mem_map.mp sel
    obtain ⟨claim,action⟩ := entry
    have unchanged : (claim,action) = (C,.advance v) := by
      by_cases pos : claim.source.occurrence.val<3
      · cases action with
        | advance u =>
          simp only [BStarLongGrant.update,dif_pos pos] at E
          split at E
          · rename_i H
            have A := beq_iff_eq.mp (Bool.and_eq_true_iff.mp H).2
            have Q := (Prod.mk.inj E).2
            have opc := congrArg (fun t : Payload => t.opcode.toNat)
              (BStarLongCommand.Offer.advance.inj Q)
            unfold BStarLongGrant.capture BStarLongGrant.captureFields at opc
            split at opc <;> (simp only [A,op] at opc; contradiction)
          · exact E
        | _ => simpa only [BStarLongGrant.update,dif_pos pos] using E
      · simpa only [BStarLongGrant.update,dif_neg pos] using E
    rw [unchanged] at hm
    obtain ⟨entry,eIn,E⟩ := List.mem_map.mp hm
    obtain ⟨cl,act⟩ := entry
    cases act with
    | advance u =>
      simp only [cancel] at E
      split at E
      · cases E
        contradiction
      · cases E
        exact eIn
    | _ => cases E
  have off : a∈(round g raw).prep := by
    apply List.mem_flatMap.mpr
    refine ⟨(C,.advance v),G,?_⟩
    change a∈fieldOffers g raw C.source v
    have P : prepOf v.opcode.toNat=some .enable := by rw [op]; rfl
    simp only [fieldOffers,good,bne_self_eq_false,P]
    exact List.mem_map.mpr ⟨a.claim,List.mem_map.mpr ⟨sh,lane,rfl⟩,rfl⟩
  refine ⟨a,rfl,rfl,BStarCopyInjection.exclusive_winner a _ off ?_⟩
  intro b mem same
  have nd := List.pairwise_map.mp (BStarResetNoFault.prep_lanes_nodup g raw)
  generalize equation : (round g raw).prep = ls at mem off nd
  clear equation
  induction ls with
  | nil => cases mem
  | cons z tail ih =>
    obtain ⟨head,rest⟩ := List.pairwise_cons.mp nd
    rcases List.mem_cons.mp mem with rfl|bm
    · rcases List.mem_cons.mp off with rfl|am
      · rfl
      · exact (head a am same).elim
    · rcases List.mem_cons.mp off with rfl|am
      · exact (head b bm same.symm).elim
      · exact ih bm am rest

theorem record_split {base x : X} {addr : Nat→Pos n} {k len : Nat}
    {w : List (Fin n)} {ds : List D} (T : OutTape hp base addr x k w len ds)
    (d : D) (M : d∈ds) :
    ∃ pre post, w=pre++d.mark::post ∧ d.old=play x pre ∧
      (∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B d.old i) ∧
      Departure.Valid hp addr d := by
  induction T with
  | nil => simp at M
  | @stay x k e w l ds _ ih =>
    obtain ⟨pre,post,E,S,G,V⟩ := ih M
    exact ⟨e::pre,post,congrArg (List.cons e) E,S,G,V⟩
  | @hop x k e w l ds C a p frame V _ ih =>
    rcases List.mem_cons.mp M with eq|inTail
    · subst d
      exact ⟨[],w,rfl,rfl,frame,V⟩
    · obtain ⟨pre,post,E,S,G,V⟩ := ih inTail
      exact ⟨e::pre,post,congrArg (List.cons e) E,S,G,V⟩

open BStarClearanceDataChart BStarAcquireRailCoverage BStarAcquireAnchors

def enableOccurrence : Sheet → Fin 11
  | .ls => 0
  | .ld | .rd => 1
  | .rs => 2

theorem record_enable {base y : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) {w : List (Fin n)} {ds : List D}
    (T : OutTape hp base (fun j => S.getD j fall) y 0 w len ds)
    (health : ∀ d∈ds,d.offer.fault=0 ∧ d.offer.opcode.toNat=9)
    (i : Fin n) (sh : Sheet)
    (active : activeSheet (longGeometry B (base i)) sh=true)
    (own : dataOwner (oldH6 B base) i sh=o.val) :
    ∃ (pre : List (Fin n)) (e : Fin n) (post : List (Fin n)) (a : BStarLongPrep.Offer), w=pre++e::post ∧
      a.claim.op=.enable ∧ site e a.claim.lane.side=i ∧ a.claim.lane.occurrence=sh ∧
      a∈(arbitration (round (oldPair B (play y pre) e)
        (((play y pre) e).long,((play y pre) (rightNeighbor e)).long)).prep).1 := by
  let K := enableOccurrence sh
  have ac : BStarAcquireRailCoverage.active (longGeometry B (base i)) K=true := by
    cases sh <;> rfl
  have ow : commandOwner (oldH6 B base) i K=o.val := by
    cases sh <;> exact own
  obtain ⟨j,lim,R⟩ := List.mem_iff_getElem.mp (chart.cover (i,K) ac ow)
  have idx : S.getD j fall=(i,K) := by
    rwa [←List.getElem_eq_getD (h:=lim)]
  have bound : j<len := by
    have lens := chart.length
    apply Classical.byContradiction
    intro h
    have E : j=len := by omega
    rw [E,chart.terminal] at idx
    have Q := congrArg (fun u : Pos n => u.2.val) idx
    change 10=K.val at Q
    cases sh <;> simp [K,enableOccurrence] at Q
  have jmem : j∈ds.map Departure.index := by
    rw [(T.indices hp).2]
    simpa using List.mem_range.mpr bound
  obtain ⟨d,M,Kd⟩ := List.mem_map.mp jmem
  obtain ⟨pre,post,W,old,layout,V⟩ := record_split hp T d M
  obtain ⟨select,_,src,_⟩ := V
  have eq : (i,K)=address d.mark d.claim.source := idx.symm.trans (Kd ▸ src)
  have eqI : i=site d.mark d.claim.source.side :=
    congrArg Prod.fst eq
  have eqK : K=d.claim.source.occurrence :=
    congrArg Prod.snd eq
  have ins : (geometry (oldPair B d.old d.mark) d.claim.source.side).inside=
      (longGeometry B (base i)).inside := by
    have Q := congrArg (fun t : Bool×Bool×Bool => t.2.1) (layout i)
    rw [eqI]
    cases U : d.claim.source.side <;> (rw [eqI,U] at Q; exact Q.symm)
  have chosen : sh∈prepSites (geometry (oldPair B d.old d.mark) d.claim.source.side)
      d.claim.source.occurrence .enable := by
    rw [←eqK]
    cases sh <;> simp [K,enableOccurrence,prepSites,ins,activeSheet] at active ⊢
    · simp [active]
    · simp [active]
    · split <;> simp
  obtain ⟨a,A,Q,win⟩ := selected_enable (oldPair B d.old d.mark)
    ((d.old d.mark).long,(d.old (rightNeighbor d.mark)).long) d.claim d.offer sh select
    (health d M).1 (health d M).2 chosen
  refine ⟨pre,d.mark,post,a,W,A,?_,congrArg At.occurrence Q,?_⟩
  · rw [congrArg At.side Q]
    exact eqI.symm
  · rw [←old]
    exact win

open BStarLongTransport BStarClearanceForward BStarNumericConsecutive BStarLongRouting BStarResetRailRing BStarResetQuiet

private theorem outgoing_back (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (p q : Payload)
    (H : (BStarLongOutgoing.execute g j x p).carried=.forward q) :
    BStarForwardProvenance.Back p q := by
  intro F
  unfold BStarLongOutgoing.execute at H
  dsimp only at H
  repeat' first
    | (change (Token.forward p) = .forward q at H; cases H; exact ⟨F,rfl⟩)
    | (change fault false = .forward q at H; unfold fault at H; cases H; contradiction)
    | split at H
  cases H
  exact ⟨F,rfl⟩

private theorem visit_back (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (p : Payload) :
    BStarForwardProvenance.Back p (visit g j x p).2 := by
  unfold visit
  split
  · exact .refl _
  · split
    · exact .refl _
    · split
      · intro h
        contradiction
      · rename_i c _
        cases c <;> simp [physicalDigit,BStarForwardProvenance.Back] <;>
          split <;> simp

private theorem record_back {addr : Nat → Pos n} (d : D) (V : Departure.Valid hp addr d)
    (he : d.mark≠rightNeighbor d.mark) (q : Payload)
    (Q : project addr (step d.old d.mark) (d.index+1)=.forward q) (H : q.fault=0) :
    d.offer.fault=0 ∧ d.offer.opcode=q.opcode := by
  obtain ⟨sel,dst,_,endEq⟩ := V
  let x := d.old
  let e := d.mark
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have hm : d.claim∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,sel,rfl⟩
  have no := (BStarAcquireReturn.link_shape g d.claim d.destination hm dst).1
  have safe : d.destination=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true := by
    intro E Z
    have J : d.destination.occurrence.val=0 := congrArg (fun z : AtK => z.occurrence.val) E
    have N := (BStarAcquireJoinedHop.k0_dest g d.claim d.destination hm dst J).2
    simp [Z] at N
  have Jraw := (move_lands g raw d.claim d.offer d.destination dst sel (Ne.symm no)).2
  have E := (new_read B x e he d.destination).trans ((congrArg (atCursor (step x e)) endEq).symm)
  have DL := E.trans Q
  change decode (readRaw (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) d.destination)=_ at DL
  erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp (x e,x (rightNeighbor e)) d.destination safe,Jraw,decode_encode] at DL
  have carrier : (carried g raw d.claim d.offer).fault=0 ∧
      (carried g raw d.claim d.offer).opcode=q.opcode := by
    unfold arrive at DL
    split at DL <;> cases DL <;> exact ⟨H,rfl⟩
  unfold carried at carrier
  dsimp only at carrier
  split at carrier
  · rename_i u E
    obtain ⟨V,O⟩ := outgoing_back _ _ _ _ u E carrier.1
    obtain ⟨F,N⟩ := visit_back _ _ _ d.offer V
    exact ⟨F,N.trans (O.trans carrier.2)⟩
  all_goals exact ((show (1 : BitVec 1)≠0 by decide) carrier.1).elim

/-- Every selected departure on the completed outward PC9 tour is healthy:
reverse source and opcode custody from its actual terminal forward token. -/
theorem aligned_health {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {k l : Nat} {w : List (Fin n)} {ds : List D}
    (T : Aligned hp base (fun j => S.getD j fall) len 9 x k w l ds)
    (hl : l≤len) (pay : Payload)
    (F : project (fun j => S.getD j fall) (play x w) l=.forward pay)
    (good : pay.fault=0) (op : pay.opcode.toNat=9) :
    ∀ d∈ds,d.offer.fault=0 ∧ d.offer.opcode.toNat=9 := by
  induction T with
  | nil _ => simp
  | stay _ _ _ ih => exact ih hl F
  | @hop x k e w l ds C a u I E V T ih =>
    intro d M
    rcases List.mem_cons.mp M with L|R
    · subst d
      have b := Aligned.busy hp T
      have cur := busy_start hp b
      obtain ⟨j,hj,q,Q,hq,O⟩ := BStarOwnerLaunchOrigin.busy_origin hp chart sep b l hl pay F good
      have U := (BStarOwnerControlHistory.pointed_unique_forward _ len _
        cur.2.1 cur.2.2 j hj).mp ⟨q,Q⟩
      subst j
      obtain ⟨N,P⟩ := record_back hp ⟨k,x,e,C,a,u⟩ V (sep e) q Q hq
      exact ⟨N,(congrArg BitVec.toNat (P.trans O)).trans op⟩
    · exact ih hl F d R

/-- Genuine outward-to-K10 PC9 completion gives an actual winning
ENABLE mark for every active sheet of that owner, without a supplied
lane itinerary, cleanliness per mark, or prep-winner checklist. -/
theorem outward_enable {base y : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} (out : BusyOnly hp base (fun j => S.getD j fall) len 9 y (.out 0) w (.out len))
    (pay : Payload) (F : project (fun j => S.getD j fall) (play y w) len=.forward pay)
    (good : pay.fault=0) (op : pay.opcode.toNat=9)
    (i : Fin n) (sh : Sheet)
    (active : activeSheet (longGeometry B (base i)) sh=true)
    (own : dataOwner (oldH6 B base) i sh=o.val) :
    ∃ (pre : List (Fin n)) (e : Fin n) (post : List (Fin n)) (a : BStarLongPrep.Offer),
      w=pre++e::post ∧ a.claim.op=.enable ∧ site e a.claim.lane.side=i ∧
      a.claim.lane.occurrence=sh ∧ a∈(arbitration (round (oldPair B (play y pre) e)
        (((play y pre) e).long,((play y pre) (rightNeighbor e)).long)).prep).1 := by
  obtain ⟨ds,T⟩ := aligned_tape hp chart sep out 0 len pay rfl rfl (Nat.le_refl _) F good
  exact record_enable hp chart (T.to_tape hp) (aligned_health hp chart sep T (Nat.le_refl _) pay F good op)
    i sh active own

/-- On the same recovered attempt the resulting gates remain open
through the indicated later raw cut (e.g. ISSUE10/11). -/
theorem gates_of_outward {base y : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (lead tour tail : List (Fin n)) (m : Mode)
    (G : GeneratedOwner hp base (fun j => S.getD j fall) len y .idle (lead++tour++tail) m)
    (out : BusyOnly hp base (fun j => S.getD j fall) len 9 (play y lead) (.out 0) tour (.out len))
    (pay : Payload) (F : project (fun j => S.getD j fall) (play (play y lead) tour) len=.forward pay)
    (good : pay.fault=0) (op : pay.opcode.toNat=9)
    (valid : ∀ u v, tour++tail=u++v →
      (∀ k,BStarLongFixedRouting.Layout B base k=BStarLongFixedRouting.Layout B (play (play y lead) u) k) ∧
      Band (play (play y lead) u) (S.getD 0 fall).1)
    (i : Fin n) (sh : Sheet)
    (active : activeSheet (longGeometry B (base i)) sh=true)
    (own : dataOwner (oldH6 B base) i sh=o.val) :
    (readLane (Sheet.index sh) (play y (lead++tour++tail) i).long).gate=true := by
  obtain ⟨pre,e,post,a,W,ena,siteE,sheetE,win⟩ :=
    outward_enable hp chart sep out pay F good op i sh active own
  have WW : lead++tour++tail=(lead++pre)++e::(post++tail) := by rw [W]; simp [List.append_assoc]
  rw [WW]
  have win' : a∈(arbitration (round (oldPair B (play y (lead++pre)) e)
    (((play y (lead++pre)) e).long,((play y (lead++pre)) (rightNeighbor e)).long)).prep).1 := by
    simpa only [BStarResetSchedule.run_append] using win
  have U := enable_through_same_attempt hp chart sep (lead++pre) (post++tail) e a m (WW ▸ G) ena win'
  rw [siteE,sheetE] at U
  apply U own
  intro u v E
  have V : tour++tail=(pre++u)++v := by rw [W]; simp only [List.cons_append, List.append_assoc]; rw [←E]
  simpa only [BStarResetSchedule.run_append] using valid (pre++u) v V

end L4.BStarCopyEnableCoverage
