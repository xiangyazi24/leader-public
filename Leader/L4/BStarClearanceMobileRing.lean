import Leader.L4.BStarClearanceMobileOwner
import Leader.L4.BStarClearanceMobileService
import Leader.L4.BStarLongFixedRouting
import Leader.L4.BStarAcquireRingFrame

namespace L4.BStarClearanceMobileRing
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongPackets
open BStarLongPrep BStarLongCommandData BStarCopyFIFO BStarCopyUpstreamCredit
open BStarClearanceMobile BStarClearanceMobileWeak BStarClearanceAggregate
open BStarLongFiberOwner BStarLongEvents BStarClearanceMobileOwner

private theorem slots_nodup (g : Pair LongGeometry) (rs : List (At Sheet)) (C : DataClaim)
    (h : C∈orderedData g rs) : C.slots.Nodup := by
  rcases selected_shape g rs C h with ⟨_,D⟩|⟨a,_,D,ne⟩
  · simp [Claim.slots,D]
  · simpa [Claim.slots,D] using ne

private theorem blocks_nodup (cs : List DataClaim)
    (pw : cs.Pairwise (fun a b => ∀ s∈b.slots, s∉a.slots))
    (nd : ∀ C∈cs, C.slots.Nodup) : (cs.map Claim.slots).flatten.Nodup := by
  induction cs with
  | nil => exact List.nodup_nil
  | cons C cs ih =>
    rw [List.map_cons,List.flatten_cons,List.nodup_append]
    have D := List.pairwise_cons.mp pw
    refine ⟨nd C List.mem_cons_self,ih D.2 (fun q h => nd q (List.mem_cons_of_mem _ h)),?_⟩
    intro a ha b hb E
    subst b
    obtain ⟨q,hq,hb⟩ := List.mem_flatten.mp hb
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hq
    exact D.1 k hk a hb ha

private theorem same_slots (g : Pair LongGeometry) (m w : Int) (rs : List (At Sheet))
    (C : DataClaim) (h : C∈orderedData g rs) (a : At Sheet) (ha : a∈C.slots) :
    pairOwner m w g.2.axes.h6 dataDispl a=pairOwner m w g.2.axes.h6 dataDispl C.source := by
  cases D : C.destination with
  | none =>
    have E : a=C.source := by simpa [Claim.slots,D] using ha
    rw [E]
  | some b =>
    have E : a=C.source ∨ a=b := by simpa [Claim.slots,D] using ha
    rcases E with rfl|rfl
    · rfl
    · exact (data_owner g m w rs C a h D).symm

theorem owner_strict (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (m w owner : Int)
    (d : At Sheet → Nat)
    (noDepart : ∀ C p, (C,BStarLongCommand.Offer.advance p)∈actualOffers g raw →
      pairOwner m w g.2.axes.h6 cmdDispl C.source≠owner)
    (gap : ∀ C∈ownerClaims g m w owner (reserved (round g raw).prep), ∀ a,
      C.destination=some a → d a<d C.source)
    (pays : ∃ C∈ownerClaims g m w owner (reserved (round g raw).prep),
      total (fun a => rank (d a) (post g raw a)) C.slots <
      total (fun a => rank (d a) (view raw a)) C.slots) :
    total (fun a => rank (d a) (post g raw a)) (ownerLanes g m w owner) <
      total (fun a => rank (d a) (view raw a)) (ownerLanes g m w owner) := by
  let rs := reserved (round g raw).prep
  let cs := ownerClaims g m w owner rs
  let slots := ownerLanes g m w owner
  let bs := cs.map Claim.slots
  have member (C : DataClaim) :
      C∈cs ↔ C∈orderedData g rs ∧ pairOwner m w g.2.axes.h6 dataDispl C.source=owner := by
    simp [cs,ownerClaims]
  have hm (a : At Sheet) :
      a∈slots ↔ pairOwner m w g.2.axes.h6 dataDispl a=owner := by
    simp [slots,ownerLanes,all_mem]
  have nd : slots.Nodup := all_nodup.filter _
  have bd : bs.flatten.Nodup := by
    apply blocks_nodup
    · exact (data_reservations g rs).1.filter _
    · exact fun C h => slots_nodup g rs C ((member C).mp h).1
  have sub : bs.flatten ⊆ slots := by
    intro a H
    obtain ⟨l,hl,ha⟩ := List.mem_flatten.mp H
    obtain ⟨C,hC,rfl⟩ := List.mem_map.mp hl
    have M := (member C).mp hC
    exact (hm a).mpr ((same_slots g m w rs C M.1 a ha).trans M.2)
  apply aggregate_lt _ _ slots (remainder slots bs) bs (chart_partition slots bs nd bd sub)
  · intro a ha
    have E : a∈slots ∧ a∉bs.flatten := by simpa [remainder] using ha
    have own := (hm a).mp E.1
    have noR : a∉rs := by
      intro h
      obtain ⟨C,p,hc,eq⟩ := reserved_owner_departure g m w raw a h
      exact noDepart C p hc (eq.trans own)
    have noK : ∀ C∈orderedData g rs, a∉C.slots := by
      intro C hc h
      have oc := (same_slots g m w rs C hc a h).symm.trans own
      apply E.2
      exact List.mem_flatten.mpr ⟨C.slots,List.mem_map.mpr ⟨C,(member C).mpr ⟨hc,oc⟩,rfl⟩,h⟩
    exact congrArg (rank (d a)) (quiet_lane g raw a noR noK)
  · intro l hl
    obtain ⟨C,hC,rfl⟩ := List.mem_map.mp hl
    have M := ((member C).mp hC).1
    rcases selected_shape g rs C M with ⟨K,E⟩|⟨a,K,E,ne⟩
    · have H : C=ending C.source := by cases C; simp_all [ending]
      simpa [total,Claim.slots,E] using terminal_weak g raw C.source (H ▸ M) (d C.source)
    · simpa [total,Claim.slots,E] using
        hop_gap g raw C.source a C rfl E K M ne (d C.source) (d a) (gap C hC a E)


  · obtain ⟨C,hC,H⟩ := pays
    exact ⟨C.slots,List.mem_map.mpr ⟨C,hC,rfl⟩,H⟩


open BStarH6WordChart hiding total
open BStarClearanceDataChart

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

/-- Inactive LD/RS have distance zero: irrelevant dormant mobile bits
cannot count as work or obstruct an active-empty characterization. -/
noncomputable def activeDistance (base : X) (hh : ∃ i, oldH6 B base i=true)
    (i : Fin n) (s : Sheet) : Nat :=
  if activeSheet (longGeometry B (base i)) s then distance (oldH6 B base) hh i s+1 else 0

noncomputable def siteRank (base : X) (hh : ∃ i, oldH6 B base i=true)
    (state : X) (o : Int) (i : Fin n) : Nat :=
  total (fun s : Sheet =>
    if dataOwner (oldH6 B base) i s=o then
      rank (activeDistance hp base hh i s) (readLane (Sheet.index s) (state i).long)
    else 0) [.ls,.ld,.rs,.rd]

noncomputable def ringRank (base : X) (hh : ∃ i, oldH6 B base i=true)
    (state : X) (o : Int) : Nat :=
  total (siteRank hp base hh state o) (List.finRange n)

private theorem filter_total {A : Type} (keep : A → Bool) (f : A → Nat) (xs : List A) :
    total f (xs.filter keep)=total (fun a => if keep a then f a else 0) xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases H : keep a
    · simp [H,total] at ih ⊢
      exact ih
    · simp [H,total] at ih ⊢
      exact ih

private theorem owner_pair (base : X) (e : Fin n) (a : At Sheet) :
    pairOwner (BStarH6WordChart.total (oldH6 B base)) (word (oldH6 B base) e)
      (oldH6 B base (rightNeighbor e)) dataDispl a =
    dataOwner (oldH6 B base) (site e a.side) a.occurrence :=
  (physical_pair_owner (oldH6 B base) e dataDispl a).symm

private theorem local_total (base state : X) (hh : ∃ i, oldH6 B base i=true)
    (o : Int) (e : Fin n) :
    let g := oldPair B base e
    let raw : Pair (BitVec LW) := ((state e).long,(state (rightNeighbor e)).long)
    let d := fun (a : At Sheet) => activeDistance hp base hh (site e a.side) a.occurrence
    total (fun a => rank (d a) (view raw a)) (ownerLanes g (BStarH6WordChart.total (oldH6 B base))
      (word (oldH6 B base) e) o) =
      siteRank hp base hh state o e+siteRank hp base hh state o (rightNeighbor e) := by
  dsimp only
  rw [ownerLanes,filter_total]
  have H (a : At Sheet) :
      pairOwner (BStarH6WordChart.total (oldH6 B base)) (word (oldH6 B base) e)
      (oldPair B base e).2.axes.h6 dataDispl a =
      dataOwner (oldH6 B base) (site e a.side) a.occurrence := owner_pair hp base e a
  simp only [H,decide_eq_true_eq]
  exact total_append _ [L Sheet.ls,L Sheet.ld,L Sheet.rs,L Sheet.rd] [R Sheet.ls,R Sheet.ld,R Sheet.rs,R Sheet.rd]

private def geo (h i l : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,h⟩,i,l,0,false⟩

private theorem active_claim (g : Pair LongGeometry) (rs : List (At Sheet))
    (C : DataClaim) (hc : C∈orderedData g rs) :
    activeSheet (BStarLongCommand.geometry g C.source.side) C.source.occurrence=true ∧
    ∀ a, C.destination=some a → activeSheet (BStarLongCommand.geometry g a.side) a.occurrence=true := by
  obtain ⟨x,y⟩ := g
  let A (g : Pair LongGeometry) (a : At Sheet) :=
    activeSheet (BStarLongCommand.geometry g a.side) a.occurrence
  let test (g : Pair LongGeometry) (C : DataClaim) := A g C.source && C.destination.all (A g)
  have P (I L H J : Bool) : (dataClaims (geo false I L,geo H J false)).all
      (test (geo false I L,geo H J false))=true := by
    cases I <;> cases L <;> cases H <;> cases J <;> decide +kernel
  have R := BStarLongFenceTopology.selected_data_raw (x,y) rs C hc
  change C∈dataClaims (geo false x.inside x.last,geo y.axes.h6 y.inside false) at R
  have Q := Bool.and_eq_true_iff.mp (List.all_eq_true.mp (P x.inside x.last y.axes.h6 y.inside) C R)
  constructor
  · cases z : C.source.side <;> simpa [A,z,BStarLongCommand.geometry,activeSheet,geo] using Q.1
  · intro a ha
    have H := Q.2
    rw [ha] at H
    cases z : a.side <;> simpa [A,z,BStarLongCommand.geometry,activeSheet,geo] using H

private theorem local_active (base : X) (hh : ∃ i, oldH6 B base i=true)
    (e : Fin n) (a : At Sheet)
    (h : activeSheet (BStarLongCommand.geometry (oldPair B base e) a.side) a.occurrence=true) :
    activeDistance hp base hh (site e a.side) a.occurrence =
      distance (oldH6 B base) hh (site e a.side) a.occurrence+1 := by
  have H : activeSheet (longGeometry B (base (site e a.side))) a.occurrence=true := by
    cases z : a.side <;> simpa [z,site,oldPair,BStarLongCommand.geometry] using h
  simp [activeDistance,H]

private theorem site_off (base x : X) (hh : ∃ i, oldH6 B base i=true) (o : Int)
    (e i : Fin n) (he : i≠e) (hr : i≠rightNeighbor e) :
    siteRank hp base hh (AllSizeS1Geometry.step B x e) o i=siteRank hp base hh x o i := by
  unfold siteRank
  rw [BStarAcquireRingFrame.unselected _ _ _ _ he hr]

private theorem ring_pays (base x : X) (hh : ∃ i, oldH6 B base i=true) (o : Int)
    (e : Fin n) (he : e≠rightNeighbor e)
    (cmp : let y := AllSizeS1Geometry.step B x e
      siteRank hp base hh y o e+siteRank hp base hh y o (rightNeighbor e) ≤
        siteRank hp base hh x o e+siteRank hp base hh x o (rightNeighbor e)) :
    ringRank hp base hh (AllSizeS1Geometry.step B x e) o≤ringRank hp base hh x o := by
  let s := [e,rightNeighbor e]
  let all := List.finRange n
  have N : [s].flatten.Nodup := by simp [s,he]
  have sub : [s].flatten ⊆ all := by intro a _; exact List.mem_finRange _
  have part := chart_partition all [s] (List.nodup_finRange n) N sub
  apply aggregate_le _ _ all _ [s] part
  · intro a ha
    have H := (show a∈all ∧ a∉s by simpa [remainder] using ha).2
    exact site_off hp base x hh o e a (fun h => H (by simp [s,h]))
      (fun h => H (by simp [s,h]))
  · intro z hz
    have E := List.mem_singleton.mp hz
    subst z
    simpa [s,total] using cmp

private theorem ring_strict (base x : X) (hh : ∃ i, oldH6 B base i=true) (o : Int)
    (e : Fin n) (he : e≠rightNeighbor e)
    (cmp : let y := AllSizeS1Geometry.step B x e
      siteRank hp base hh y o e+siteRank hp base hh y o (rightNeighbor e) <
        siteRank hp base hh x o e+siteRank hp base hh x o (rightNeighbor e)) :
    ringRank hp base hh (AllSizeS1Geometry.step B x e) o<ringRank hp base hh x o := by
  let s := [e,rightNeighbor e]
  let all := List.finRange n
  have N : [s].flatten.Nodup := by simp [s,he]
  have sub : [s].flatten ⊆ all := by intro a _; exact List.mem_finRange _
  have part := chart_partition all [s] (List.nodup_finRange n) N sub
  have P : total (siteRank hp base hh (AllSizeS1Geometry.step B x e) o) s <
      total (siteRank hp base hh x o) s := by simpa [s,total] using cmp
  apply aggregate_lt _ _ all _ [s] part
  · intro a ha
    have H := (show a∈all ∧ a∉s by simpa [remainder] using ha).2
    exact site_off hp base x hh o e a (fun h => H (by simp [s,h]))
      (fun h => H (by simp [s,h]))
  · intro a ha
    rw [List.mem_singleton.mp ha]
    exact Nat.le_of_lt P
  · exact ⟨s,List.mem_cons_self,P⟩


open BStarLongFixedRouting in
private theorem active_fixed (base x : X) (same : ∀ i,Layout B base i=Layout B x i)
    (e : Fin n) (a : At Sheet) :
    activeSheet (BStarLongCommand.geometry (oldPair B base e) a.side) a.occurrence =
      activeSheet (BStarLongCommand.geometry (oldPair B x e) a.side) a.occurrence := by
  have S (i : Fin n) : (longGeometry B (base i)).inside=(longGeometry B (x i)).inside :=
    congrArg (fun t : Bool × Bool × Bool => t.2.1) (same i)
  obtain ⟨s,j⟩ := a
  cases s <;> cases j <;> simp [activeSheet,BStarLongCommand.geometry,oldPair,S]

open BStarLongFixedRouting in
theorem ring_compare (base x : X) (hh : ∃ i,oldH6 B base i=true)
    (same : ∀ i,Layout B base i=Layout B x i)
    (o : Int) (e : Fin n) (he : e≠rightNeighbor e) :
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    let h := oldH6 B base
    let d := fun (a : At Sheet) => activeDistance hp base hh (site e a.side) a.occurrence
    let cs := ownerClaims g (BStarH6WordChart.total h) (word h e) o (reserved (round g raw).prep)
    (∀ C p, (C,BStarLongCommand.Offer.advance p)∈actualOffers g raw →
      physicalOwner h e cmdDispl C.source≠o) →
    ringRank hp base hh (AllSizeS1Geometry.step B x e) o≤ringRank hp base hh x o ∧
    ((∃ C∈cs, total (fun a => rank (d a) (post g raw a)) C.slots <
          total (fun a => rank (d a) (view raw a)) C.slots) →
      ringRank hp base hh (AllSizeS1Geometry.step B x e) o<ringRank hp base hh x o) := by
  dsimp only
  intro noDepart
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let h := oldH6 B base
  let d := fun (a : At Sheet) => activeDistance hp base hh (site e a.side) a.occurrence
  let y := AllSizeS1Geometry.step B x e
  let cs := ownerClaims g (BStarH6WordChart.total h) (word h e) o (reserved (round g raw).prep)
  let ls := ownerLanes g (BStarH6WordChart.total h) (word h e) o
  have heads : oldH6 B x=oldH6 B base := funext (fun i => (congrArg Prod.fst (same i)).symm)
  have R : g.2.axes.h6=h (rightNeighbor e) := congrFun heads (rightNeighbor e)
  have noD : ∀ C p, (C,BStarLongCommand.Offer.advance p)∈actualOffers g raw →
      pairOwner (BStarH6WordChart.total h) (word h e) g.2.axes.h6 cmdDispl C.source≠o := by
    intro C p H
    rw [R,←physical_pair_owner]
    exact noDepart C p H
  have gaps : ∀ C∈cs, ∀ a, C.destination=some a → d a<d C.source := by
    intro C hc a hd
    have H := (List.mem_filter.mp hc).1
    have A := active_claim g _ C H
    have T1 := local_active hp base hh e C.source ((active_fixed hp base x same e C.source).trans A.1)
    have T2 := local_active hp base hh e a ((active_fixed hp base x same e a).trans (A.2 a hd))
    change activeDistance hp base hh _ _ < activeDistance hp base hh _ _
    rw [T1,T2]
    have Hh : ∃ i,oldH6 B x i=true := heads.symm ▸ hh
    have E := hop_decreases B x Hh e _ C a H hd
    have distEq (u v : Fin n → Bool) (E : u=v)
        (U : ∃ i,u i=true) (V : ∃ i,v i=true) (j : Fin n) (s : Sheet) :
        distance u U j s=distance v V j s := by subst v; rfl
    rw [distEq _ _ heads Hh hh,distEq _ _ heads Hh hh] at E
    omega
  have total_at (z : X) :
      total (fun a => rank (d a) (view ((z e).long,(z (rightNeighbor e)).long) a)) ls =
      siteRank hp base hh z o e+siteRank hp base hh z o (rightNeighbor e) := by
    unfold ls ownerLanes
    change total _ ((allLanes.filter fun a =>
      decide (pairOwner (BStarH6WordChart.total h) (word h e) g.2.axes.h6 dataDispl a=o))) = _
    rw [R]
    exact local_total hp base z hh o e
  have pair : (Pair.map (fun q : LargeSite _ => q.long) (largePair B (x e,x (rightNeighbor e))) :
      Pair (BitVec LW)) = ((y e).long,(y (rightNeighbor e)).long) := by
    apply Prod.ext
    · simp [y,AllSizeS1Geometry.step,Pair.map] <;> rfl
    · simp [y,AllSizeS1Geometry.step,Pair.map,Ne.symm he] <;> rfl
  have Q := BStarClearanceMobileJoined.joined_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e))
  change view (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e))))=post g raw at Q
  erw [pair] at Q
  have Y := total_at y
  have Xold := total_at x
  erw [Q] at Y
  constructor
  · apply ring_pays hp base x hh o e he
    dsimp only
    rw [←Y,←Xold]
    exact owner_weak g raw _ _ o d noD gaps
  · intro pay
    apply ring_strict hp base x hh o e he
    dsimp only
    rw [←Y,←Xold]
    exact owner_strict g raw _ _ o d noD gaps pay


open BStarAcquireRailCoverage BStarClearanceRightmost in
/-- Nominating the owner-rightmost active mobile gives a strict
whole-ring mobile-rank decrease, unless an actual same-owner command
departs on that mark. The latter is exactly the higher-coordinate case. -/
theorem rightmost_service (x : X) (hh : ∃ i,oldH6 B x i=true) (o : Int)
    (distinct : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry B (x i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B x i; continuation g.1 g.2=true)
    (occupied : ∃ i s, activeSheet (longGeometry B (x i)) s=true ∧
      dataOwner (oldH6 B x) i s=o ∧ mobile x i s≠.empty) :
    ∃ e : Fin n,
      ringRank hp x hh (AllSizeS1Geometry.step B x e) o<ringRank hp x hh x o ∨
      ∃ C p, (C,BStarLongCommand.Offer.advance p)∈actualOffers (oldPair B x e)
        ((x e).long,(x (rightNeighbor e)).long) ∧
        physicalOwner (oldH6 B x) e cmdDispl C.source=o := by
  obtain ⟨e,C,nom,own,occ,vac,sel⟩ := nominate hp x hh o head cont occupied
  refine ⟨e,?_⟩
  rcases sel with H|H
  · let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    let d := fun (a : At Sheet) => activeDistance hp x hh (site e a.side) a.occurrence
    let edgeCharges := ∃ C p, (C,BStarLongCommand.Offer.advance p)∈actualOffers g raw ∧
        physicalOwner (oldH6 B x) e cmdDispl C.source=o
    by_cases J : edgeCharges
    · exact .inr J
    apply Or.inl
    have nd : ∀ C p, (C,BStarLongCommand.Offer.advance p)∈actualOffers g raw →
        physicalOwner (oldH6 B x) e cmdDispl C.source≠o :=
      fun C p H K => J ⟨C,p,H,K⟩
    have comp := ring_compare hp x x hh (fun _ => rfl) o e (distinct e) nd
    apply comp.2
    have M : C∈ownerClaims g (BStarH6WordChart.total (oldH6 B x)) (word (oldH6 B x) e)
        o (reserved (round g raw).prep) := by
      apply List.mem_filter.mpr
      refine ⟨H,?_⟩
      have O := (owner_pair hp x e C.source).trans own
      exact decide_eq_true O
    refine ⟨C,M,?_⟩
    have oc : (view raw C.source).mobile≠.empty :=
      fun E => occ ((pair_mobile hp x e C.source).1.symm.trans E)
    have A := active_claim g _ C H
    have Z := local_active hp x hh e C.source A.1
    have P : 0<d C.source := by simp [d,Z]
    rcases selected_shape g _ C H with ⟨K,E⟩|⟨a,K,E,ne⟩
    · have T : C=ending C.source := by cases C; simp_all [ending]
      have pay := terminal_charge g raw C.source (T ▸ H) oc (d C.source) P
      simpa [Claim.slots,E,total] using pay
    · have vc : (view raw a).mobile=.empty := (pair_mobile hp x e a).1.trans (vac a E)
      have Z' := local_active hp x hh e a (A.2 a E)
      have D : d a<d C.source := by
        change activeDistance hp x hh _ _ < activeDistance hp x hh _ _
        rw [Z,Z']
        exact Nat.succ_lt_succ (hop_decreases B x hh e _ C a H E)
      have W := vacant_hop_charge g raw C.source a C rfl E K H ne oc vc (d a)
      have L : (post g raw C.source).mobile=.empty := by
        apply Classical.byContradiction
        intro N
        simp [rank,mass,oc,vc,N] at W
        omega
      have Q := rank_le (d a) (post g raw a)
      have pay : rank (d C.source) (post g raw C.source)+rank (d a) (post g raw a) <
          rank (d C.source) (view raw C.source)+rank (d a) (view raw a) := by
        simp [rank,mass,oc,vc,L] at Q ⊢
        omega
      simpa [Claim.slots,E,total] using pay
  · exact .inr H


open BStarLongFixedRouting in
theorem rank_fixed (base x z : X) (hh : ∃ i,oldH6 B base i=true)
    (hx : ∃ i,oldH6 B x i=true) (same : ∀ i,Layout B base i=Layout B x i) (o : Int) :
    ringRank hp base hh z o=ringRank hp x hx z o := by
  have H : oldH6 B base=oldH6 B x := funext (fun i => congrArg Prod.fst (same i))
  have dis (h₁ h₂ : Fin n→Bool) (E : h₁=h₂)
      (H₁ : ∃ i,h₁ i=true) (H₂ : ∃ i,h₂ i=true) (i : Fin n) (s : Sheet) :
      distance h₁ H₁ i s=distance h₂ H₂ i s := by subst h₂; rfl
  have A (i : Fin n) (s : Sheet) :
      activeSheet (longGeometry B (base i)) s=activeSheet (longGeometry B (x i)) s :=
    active_fixed hp base x same i (L s)
  have D (i : Fin n) (s : Sheet) :
      activeDistance hp base hh i s=activeDistance hp x hx i s := by
    unfold activeDistance
    rw [A,dis _ _ H hh hx]
  unfold ringRank
  congr 1
  funext i
  unfold siteRank
  congr 1
  funext s
  rw [D,H]

open BStarAcquireRailCoverage BStarClearanceRightmost BStarLongFixedRouting in
theorem rightmost_fixed (base x : X) (hh : ∃ i,oldH6 B base i=true)
    (same : ∀ i,Layout B base i=Layout B x i) (o : Int)
    (distinct : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry B (x i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B x i; continuation g.1 g.2=true)
    (occupied : ∃ i s, activeSheet (longGeometry B (base i)) s=true ∧
      dataOwner (oldH6 B base) i s=o ∧ mobile x i s≠.empty) :
    ∃ e : Fin n,
      ringRank hp base hh (AllSizeS1Geometry.step B x e) o<ringRank hp base hh x o ∨
      ∃ C p, (C,BStarLongCommand.Offer.advance p)∈actualOffers (oldPair B x e)
        ((x e).long,(x (rightNeighbor e)).long) ∧
        physicalOwner (oldH6 B base) e cmdDispl C.source=o := by
  have H : oldH6 B base=oldH6 B x := funext (fun i => congrArg Prod.fst (same i))
  have hx : ∃ i,oldH6 B x i=true := H ▸ hh
  have occ : ∃ i s, activeSheet (longGeometry B (x i)) s=true ∧
      dataOwner (oldH6 B x) i s=o ∧ mobile x i s≠.empty := by
    obtain ⟨i,s,a,b,D⟩ := occupied
    have K := active_fixed hp base x same i (L s)
    change activeSheet (longGeometry B (base i)) s=activeSheet (longGeometry B (x i)) s at K
    exact ⟨i,s,K.symm.trans a,H ▸ b,D⟩
  obtain ⟨e,V⟩ := rightmost_service hp x hx o distinct head cont occ
  refine ⟨e,?_⟩
  rcases V with V|⟨C,p,sel,own⟩
  · apply Or.inl
    rw [rank_fixed hp base x _ hh hx same o,rank_fixed hp base x _ hh hx same o]
    exact V
  · exact .inr ⟨C,p,sel,H.symm ▸ own⟩


private theorem total_pos {A : Type} (f : A → Nat) (xs : List A) :
    0<total f xs ↔ ∃ a∈xs, 0<f a := by
  induction xs with
  | nil => simp [total]
  | cons a xs ih =>
    change 0<f a+total f xs ↔ _
    rw [Nat.add_pos_iff_pos_or_pos,ih]
    constructor
    · intro H
      rcases H with H|⟨b,hb,H⟩
      · exact ⟨a,List.mem_cons_self,H⟩
      · exact ⟨b,List.mem_cons_of_mem _ hb,H⟩
    · rintro ⟨b,hb,H⟩
      rcases List.mem_cons.mp hb with rfl|hb
      · exact .inl H
      · exact .inr ⟨b,hb,H⟩

open BStarClearanceRightmost in
theorem rank_positive (base x : X) (hh : ∃ i,oldH6 B base i=true) (o : Int) :
    0<ringRank hp base hh x o ↔
      ∃ i s, activeSheet (longGeometry B (base i)) s=true ∧
        dataOwner (oldH6 B base) i s=o ∧ mobile x i s≠.empty := by
  have P (i : Fin n) (s : Sheet) :
      0 < (if dataOwner (oldH6 B base) i s=o then
        rank (activeDistance hp base hh i s) (readLane (Sheet.index s) (x i).long)
      else 0) ↔
      activeSheet (longGeometry B (base i)) s=true ∧
      dataOwner (oldH6 B base) i s=o ∧ mobile x i s≠.empty := by
    by_cases H : dataOwner (oldH6 B base) i s=o
    · by_cases E : (readLane (Sheet.index s) (x i).long).mobile=.empty <;>
      cases A : activeSheet (longGeometry B (base i)) s <;>
        simp [H,A,rank,activeDistance,mobile,mass,E]
    · simp [H]
  unfold ringRank siteRank
  rw [total_pos]
  constructor
  · rintro ⟨i,_,hi⟩
    obtain ⟨s,_,hs⟩ := (total_pos _ _).mp hi
    exact ⟨i,s,(P i s).mp hs⟩
  · rintro ⟨i,s,h⟩
    refine ⟨i,List.mem_finRange _,(total_pos _ _).mpr ⟨s,?_,(P i s).mpr h⟩⟩
    cases s <;> decide

#print axioms ring_compare
#print axioms rightmost_fixed
#print axioms rank_positive
end L4.BStarClearanceMobileRing
