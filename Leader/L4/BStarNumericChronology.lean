import Leader.L4.BStarAcquireHistorySample
import Leader.L4.BStarLongKOne

namespace L4.BStarNumericChronology
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
theorem joined_slot_departure (k₁ k₂ t₂ J₁ J₂ r tune p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r tune p c₁)))
    (a : AtK) (f : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r tune p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let out : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    DoorSafe g raw a → readK out a=.forward f → f.fault=0 →
    (∃ q, readK raw a=.forward q ∧ q.fault=0 ∧ q.opcode=f.opcode) ∨
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
          obtain ⟨v,H⟩ := BStarForwardProvenance.joined_hop k₁ k₂ t₂ J₁ J₂ r tune p c₁ hp x C d q f E act F hf
          exact .inr ⟨C,v,q,act,hc,E,H⟩

open BStarSeparatorQuiet BStarResetChartService

/-- Each actual outward cursor increment of a healthy tour has a
unique relevant selected old advance. An observation or stutter
cannot make the empty next slot become a healthy forward. -/
theorem ring_departure {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (e : Fin n) (he : e≠rightNeighbor e) (op k : Nat) (hk : k<len)
    (W : Waiting hp base (S.getD 0 fall).1 op x)
    (G : Good anyTag len (project (fun j => S.getD j fall) x) (.out k))
    (clean : OutClean len (project (fun j => S.getD j fall) x) (.out k))
    (pay : Payload) (F : project (fun j => S.getD j fall) (step x e) (k+1)=.forward pay)
    (H : pay.fault=0) :
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    ∃ C a offer, (C,.advance offer)∈actualOffers g raw ∧ C.destination=some a ∧
      S.getD k fall=address e C.source ∧ S.getD (k+1) fall=address e a := by
  let addr := fun j => S.getD j fall
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let g := oldPair B x e
  have unique := BStarOwnerControlHistory.pointed_unique_forward _ len k G clean
  have no : ¬ anyTag.F (project addr x (k+1)) := fun f =>
    (show k+1≠k by omega) ((unique (k+1) hk).mp f)
  have active (a : AtK) (E : addr (k+1)=address e a) :
      ∃ C d offer, (C,.advance offer)∈actualOffers g raw ∧ C.destination=some d ∧
        addr k=address e C.source ∧ addr (k+1)=address e d := by
    have dst := (new_read B x e he a).trans ((congrArg (atCursor (step x e)) E).symm)
    have safe := ((frames_any hp chart W.1 e (.out k) (by intro H; cases H) G W.2.1 W.2.2.1).safe
      (k+1) hk a E).2
    have old (j : Nat) (r : AtK) (eq : addr j=address e r) :
        readK raw r=project addr x j :=
      (old_read x e r).trans ((congrArg (atCursor x) eq).symm)
    rcases joined_slot_departure k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e)) a pay safe
        (dst.trans F) H with ⟨q,Q,_,_⟩|⟨K,q,offer,sel,mem,des,Q,_,_⟩
    · exact (no ⟨q,(old _ _ E).symm.trans Q⟩).elim
    · have L := BStarAcquireReturn.link_shape g K a mem des
      have own : a∈K.slots := by simp [Claim.slots,des]
      rcases touches hp chart W.1 e (k+1) hk K a mem own E with D|T|U|⟨j,J,inc⟩
      · omega
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
        have p : j=k := by omega
        exact ⟨K,a,offer,sel,des,p ▸ srcT,E⟩
  by_cases l : (addr (k+1)).1=e
  · exact active (L (addr (k+1)).2) (Prod.ext l rfl)
  · by_cases rr : (addr (k+1)).1=rightNeighbor e
    · exact active (R (addr (k+1)).2) (Prod.ext rr rfl)
    · exact (no ⟨pay,(idle_off_pair hp x e (addr (k+1)) l rr).symm.trans F⟩).elim

/-- Literal chronological outward subtrace. The record at each
advancing index contains its actual old state, selected mark and offer. -/
structure Departure where
  index : Nat
  old : X
  mark : Fin n
  claim : CommandClaim
  destination : AtK
  offer : Payload

def Departure.Valid (addr : Nat → Pos n) (d : Departure (n:=n)
    (k₁:=k₁) (k₂:=k₂) (t₂:=t₂) (J₁:=J₁) (J₂:=J₂) (r:=r) (c:=c) (p:=p) (c₁:=c₁)) : Prop :=
  let x := d.old
  let e := d.mark
  let g := oldPair B x e
  let raw := ((x e).long,(x (rightNeighbor e)).long)
  (d.claim,.advance d.offer)∈actualOffers g raw ∧ d.claim.destination=some d.destination ∧
    addr d.index=address e d.claim.source ∧
    addr (d.index+1)=address e d.destination

inductive OutTape (base : X) (addr : Nat → Pos n) :
    X → Nat → List (Fin n) → Nat → List (Departure (n:=n)
      (k₁:=k₁) (k₂:=k₂) (t₂:=t₂) (J₁:=J₁) (J₂:=J₂) (r:=r) (c:=c) (p:=p) (c₁:=c₁)) → Prop
  | nil (x k) : OutTape base addr x k [] k []
  | stay {x k e w l ds} : OutTape base addr (step x e) k w l ds → OutTape base addr x k (e::w) l ds
  | hop {x k e w l ds C a p} :
      (∀ i, BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i) →
      Departure.Valid hp addr ⟨k,x,e,C,a,p⟩ →
      OutTape base addr (step x e) (k+1) w l ds →
      OutTape base addr x k (e::w) l (⟨k,x,e,C,a,p⟩::ds)

theorem OutTape.indices {base : X} {addr : Nat → Pos n} {x : X} {k w l ds}
    (P : OutTape hp base addr x k w l ds) : k≤l ∧ ds.map Departure.index=List.range' k (l-k) := by
  induction P with
  | nil => simp
  | stay _ ih => exact ih
  | @hop x k e w l ds C a p _ _ _ ih =>
    obtain ⟨H,E⟩ := ih
    constructor
    · omega
    · have Q : l-k=(l-(k+1))+1 := by omega
      simp only [List.map_cons,E,Q,List.range'_succ]

/-- Any successful outward segment ending with a healthy forward
extracts an actual old-offer itinerary, not just visits/observations.
The tape is kept intact; non-departure marks are recorded as stays. -/
theorem busy_tape {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {op : Nat} {z d : Cursor} {w : List (Fin n)}
    (P : BusyOnly hp base (fun j => S.getD j fall) len op x z w d) :
    ∀ k l pay, z=.out k → d=.out l → l≤len →
      project (fun j => S.getD j fall) (BStarResetSchedule.run step x w) l=.forward pay →
      pay.fault=0 → ∃ ds, OutTape hp base (fun j => S.getD j fall) x k w l ds := by
  induction P with
  | nil I =>
    intro k l _ Z D _ _ _
    have eq := Cursor.out.inj (Z.symm.trans D)
    subst l
    exact ⟨[],.nil _ _⟩
  | @cons x z d final e w I E tail ih =>
    intro k l pay Z D hie F H
    subst z
    obtain ⟨k',Z'⟩ := busy_no_back_to_out hp tail ⟨l,D⟩
    subst d
    have A : Advance len (.out k) (.out k') := by
      cases E with
      | transit _ _ _ _ seen =>
        cases seen with
        | cons _ _ A _ rest => cases rest; exact A
    obtain ⟨ds,T⟩ := ih k' l pay rfl D hie F H
    cases A with
    | stay => exact ⟨ds,.stay T⟩
    | forward =>
      have current := busy_start hp tail
      obtain ⟨j,hj,q,Q,hq,_⟩ := BStarOwnerLaunchOrigin.busy_origin hp C sep tail l hie pay F H
      have U := (BStarOwnerControlHistory.pointed_unique_forward _ len _ current.2.1 current.2.2 j hj).mp ⟨q,Q⟩
      subst j
      obtain ⟨K,a,offer,sel,hd,src,dst⟩ := ring_departure hp C e (sep e) op k
        (by have := current.2.1.1; omega) I.1 I.2.1 I.2.2 q Q hq
      exact ⟨_,.hop I.1.1 ⟨sel,hd,src,dst⟩ T⟩

theorem OutTape.path {base : X} {addr : Nat → Pos n} {x : X} {k w l ds}
    (P : OutTape hp base addr x k w l ds) :
    Path B base (addr k) (ds.map (fun d => addr d.index)) (addr l) := by
  induction P with
  | nil => exact .nil _
  | stay _ ih => exact ih
  | @hop x k e w l ds C a p same D _ ih =>
    obtain ⟨S,A,F,T⟩ := D
    have m : C∈orderedCommands (oldPair B x e) := by
      rw [←actualOffers_claims (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)]
      exact List.mem_map.mpr ⟨_,S,rfl⟩
    exact .cons ((edge_fixed B base x same _ _).mpr ⟨e,C,a,m,A,F,T⟩) ih

open BStarH6Ordinal BStarLongLiteral

private theorem kOne_edge {base : X} {u v : Pos n} (E : Edge B base u v)
    (H : u.2.val=1) :
    v.1=rightNeighbor u.1 ∧ (v.2.val=1 ↔ oldH6 B base v.1=false) := by
  obtain ⟨e,C,d,hs,hd,rfl,rfl⟩ := E
  have eq := center_of (oldPair B base e) C hs H
  subst C
  have A : d=R (if oldH6 B base (rightNeighbor e) then 2 else 1) := by
    exact (Option.some.inj hd).symm
  subst d
  cases W : oldH6 B base (rightNeighbor e) <;>
    simp [centerLink,link,L,R,site,oldPair,W]

noncomputable def digitAt (base : X) (hh : ∃ i,oldH6 B base i=true) (r : Nat)
    (u : Pos n) : List Nat :=
  if u.2.val=1 ∧ oldOrdinal B base hh u.1<r then [oldOrdinal B base hh u.1] else []

private noncomputable def remaining (base : X) (hh : ∃ i,oldH6 B base i=true) (r : Nat)
    (u : Pos n) : List Nat :=
  if u.2.val=0 then List.range r else
  if u.2.val=1 then List.range' (oldOrdinal B base hh u.1) (r-oldOrdinal B base hh u.1)
  else []

private theorem digit_transition {base : X} {hh : ∃ i,oldH6 B base i=true} {r : Nat}
    (notShort : ∀ i, oldH6 B base (rightNeighbor i)=true → r≤oldOrdinal B base hh i+1)
    {u v : Pos n} (E : Edge B base u v) :
    digitAt hp base hh r u ++ remaining hp base hh r v=remaining hp base hh r u := by
  have J := index_step E
  by_cases z : u.2.val=0
  ·
    unfold remaining digitAt
    simp only [z,if_true]
    by_cases V : v.2.val=0
    · simp [V]
    · have o : v.2.val=1 := by omega
      have O : oldOrdinal B base hh v.1=0 :=
        (ordinal_zero _ hh _).mpr (enter_header E (by omega) (by omega))
      simp [o,O,List.range_eq_range']
  · by_cases o : u.2.val=1
    · have nz : ¬v.2.val=0 := by omega
      obtain ⟨A,L⟩ := kOne_edge hp E o
      unfold digitAt remaining
      simp only [o,nz,if_false,if_true,true_and]
      by_cases q : v.2.val=1
      · have Z : oldOrdinal B base hh v.1=oldOrdinal B base hh u.1+1 := by
          rw [A]
          apply ordinal_body
          rw [←A]
          exact L.mp q
        rw [if_pos q,Z]
        by_cases I : oldOrdinal B base hh u.1<r
        · rw [if_pos I]
          have N : r-oldOrdinal B base hh u.1=(r-(oldOrdinal B base hh u.1+1))+1 := by omega
          rw [N,List.range'_succ]
          simp
        · have K₀ : r-oldOrdinal B base hh u.1=0 := by omega
          have K₁ : r-(oldOrdinal B base hh u.1+1)=0 := by omega
          simp [I,K₀,K₁]
      · have head : oldH6 B base (rightNeighbor u.1)=true := by
          rw [←A]
          cases F : oldH6 B base v.1
          · exact (q (L.mpr F)).elim
          · rfl
        have W := notShort u.1 head
        have R : r-oldOrdinal B base hh u.1=0 ∨ r-oldOrdinal B base hh u.1=1 := by omega
        rcases R with R|R
        · have I : ¬oldOrdinal B base hh u.1<r := by omega
          simp [q,R,I]
        · have I : oldOrdinal B base hh u.1<r := by omega
          simp [q,R,I,List.range'_succ]
    · have nz : ¬v.2.val=0 := by omega
      have no : ¬v.2.val=1 := by omega
      simp [digitAt,remaining,z,o,nz,no]

/-- A complete outward itinerary from K0 to K10 has exactly the
unclipped IN K1 ordinals 0,...,r−1. The not-short condition applies
only at a physical H6 seam; it permits any length of padding. -/
theorem path_digits {base : X} {hh : ∃ i,oldH6 B base i=true} {r : Nat}
    (notShort : ∀ i, oldH6 B base (rightNeighbor i)=true → r≤oldOrdinal B base hh i+1)
    {u v : Pos n} {ds : List (Pos n)} (P : Path B base u ds v)
    (A : u.2.val=0) (Z : v.2.val=10) :
    ds.flatMap (digitAt hp base hh r)=List.range r := by
  have H : ds.flatMap (digitAt hp base hh r) ++ remaining hp base hh r v =
      remaining hp base hh r u := by
    clear A Z
    induction P with
    | nil => rfl
    | cons E _ ih =>
      simp only [List.flatMap_cons,List.append_assoc,ih]
      exact digit_transition hp notShort E
  simpa [remaining,A,Z] using H

/-- An actual selected old K1 offer contributes its physical (not
cached, potentially clipped) digit ordinal iff the old initiator is IN. -/
noncomputable def actualDigit (base : X) (hh : ∃ i,oldH6 B base i=true)
    (d : Departure (n:=n) (k₁:=k₁) (k₂:=k₂) (t₂:=t₂) (J₁:=J₁) (J₂:=J₂)
      (r:=r) (c:=c) (p:=p) (c₁:=c₁)) : List Nat :=
  if d.claim.source.occurrence.val=1 ∧ (oldPair B d.old d.mark).1.inside=true
  then [oldOrdinal B base hh d.mark] else []

theorem OutTape.actual_digits {base : X} {hh : ∃ i,oldH6 B base i=true}
    {addr : Nat → Pos n} {x : X} {k w l ds} {width : Nat}
    (P : OutTape hp base addr x k w l ds)
    (flags : ∀ i, (longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<width)) :
    ds.flatMap (actualDigit hp base hh) =
      (ds.map (fun d => addr d.index)).flatMap (digitAt hp base hh width) := by
  induction P with
  | nil => rfl
  | stay _ ih => exact ih
  | @hop x k e w l ds C a p same V _ ih =>
    obtain ⟨sel,_,E,_⟩ := V
    simp only [List.map_cons,List.flatMap_cons,←ih]
    congr 1
    unfold actualDigit digitAt
    dsimp only
    rw [E]
    by_cases J : C.source.occurrence.val=1
    · have left : C.source=L 1 := by
        have D := BStarLongKOne.departure_geometry (oldPair B x e)
          ((x e).long,(x (rightNeighbor e)).long) C p sel J
        rw [D]
        split <;> rfl
      have I : (oldPair B x e).1.inside=(longGeometry B (base e)).inside :=
        (congrArg (fun z : Bool × Bool × Bool => z.2.1) (same e)).symm
      rw [I,flags e,left]
      simp only [decide_eq_true_eq]; rfl
    · change (if C.source.occurrence.val=1 ∧ _ then _ else []) =
        (if C.source.occurrence.val=1 ∧ _ then _ else [])
      simp [J]

/-- All and only significant old selected K1 departures, in the
order of the fixed physical tape, contribute the ordinal digit list. -/
theorem tape_digits {base : X} {hh : ∃ i,oldH6 B base i=true}
    {addr : Nat → Pos n} {x : X} {k w l ds} {width : Nat}
    (P : OutTape hp base addr x k w l ds)
    (flags : ∀ i, (longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<width))
    (notShort : ∀ i, oldH6 B base (rightNeighbor i)=true → width≤oldOrdinal B base hh i+1)
    (A : (addr k).2.val=0) (Z : (addr l).2.val=10) :
    ds.flatMap (actualDigit hp base hh)=List.range width := by
  rw [OutTape.actual_digits hp P flags]
  exact path_digits hp notShort (OutTape.path hp P) A Z

end L4.BStarNumericChronology
