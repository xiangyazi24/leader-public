import Leader.L4.BStarClearanceMobileWeak
import Leader.L4.BStarClearanceAggregate

namespace L4.BStarClearanceMobileOwner
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongPackets
open BStarLongPrep BStarLongCommandData BStarCopyFIFO BStarCopyUpstreamCredit
open BStarClearanceMobile BStarClearanceMobileWeak BStarClearanceAggregate
open BStarLongFiberOwner BStarLongEvents

/-- Arbitrary chart distances are allowed: a mobile removed from the
source can contribute at most the strictly smaller destination distance. -/
theorem hop_gap (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (u v : At Sheet) (C : DataClaim)
    (hs : C.source=u) (hd : C.destination=some v) (hh : C.kind=.hop)
    (sel : C∈orderedData g (reserved (round g x).prep)) (ne : u≠v) (i j : Nat)
    (gap : j<i) :
    rank i (post g x u)+rank j (post g x v) ≤ rank i (view x u)+rank j (view x v) := by
  by_cases E : (view x u).mobile=.empty
  · unfold post
    rw [sender_exact g x u v C hs hd hh sel ne,
      BStarLongCopyFence.receiver_exact g x u v C hs hd hh sel ne]
    simp [hopEffects,E,typedLeaves]
  · by_cases G : ((view x u).gate && (view x v).gate)=true
    · by_cases V : (view x v).mobile=.empty
      · have A : (post g x u).mobile=.empty := by
          unfold post
          rw [sender_exact g x u v C hs hd hh sel ne]
          simp [hopEffects,E,V,G,typedLeaves,Leaf.put]
        have B := rank_le j (post g x v)
        have L : rank i (post g x u)=0 := by simp [rank,mass,A]
        have R : rank i (view x u)=i := by simp [rank,mass,E]
        omega
      · unfold post
        rw [sender_exact g x u v C hs hd hh sel ne,
          BStarLongCopyFence.receiver_exact g x u v C hs hd hh sel ne]
        simp [hopEffects,E,V,G,typedLeaves]
    · exact Nat.le_of_lt (closed_hop_charge g x u v C hs hd hh sel ne E
          (Bool.eq_false_iff.mpr G) i j (by omega))

def allLanes : List (At Sheet) :=
  [L .ls,L .ld,L .rs,L .rd,R .ls,R .ld,R .rs,R .rd]

theorem all_mem (a : At Sheet) : a∈allLanes := by
  obtain ⟨s,j⟩ := a
  cases s <;> cases j <;> decide

theorem all_nodup : allLanes.Nodup := by decide

private def validClaim (C : DataClaim) : Bool :=
  match C.kind,C.destination with
  | .ending,none => true
  | .hop,some a => decide (C.source≠a)
  | _,_ => false

private def geo (h i l : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,h⟩,i,l,0,false⟩

private theorem shapes (g : Pair LongGeometry) : (dataClaims g).all validClaim=true := by
  obtain ⟨x,y⟩ := g
  rw [show dataClaims (x,y)=dataClaims
    (geo false x.inside x.last,geo y.axes.h6 y.inside false) from rfl]
  generalize x.inside=xi
  generalize x.last=xl
  generalize y.axes.h6=yh
  generalize y.inside=yi
  cases xi <;> cases xl <;> cases yh <;> cases yi <;> decide +kernel

theorem selected_shape (g : Pair LongGeometry) (rs : List (At Sheet)) (C : DataClaim)
    (h : C∈orderedData g rs) :
    (C.kind=.ending ∧ C.destination=none) ∨
      ∃ a, C.kind=.hop ∧ C.destination=some a ∧ C.source≠a := by
  have T := List.all_eq_true.mp (shapes g) C (BStarLongFenceTopology.selected_data_raw g rs C h)
  cases H : C.kind <;> cases K : C.destination <;> simp [validClaim,H,K] at T ⊢
  exact T

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

def ownerLanes (g : Pair LongGeometry) (m w owner : Int) : List (At Sheet) :=
  allLanes.filter fun a => decide (pairOwner m w g.2.axes.h6 dataDispl a=owner)

def ownerClaims (g : Pair LongGeometry) (m w owner : Int) (rs : List (At Sheet)) : List DataClaim :=
  (orderedData g rs).filter fun C => decide (pairOwner m w g.2.axes.h6 dataDispl C.source=owner)

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

/-- Exact filtered owner-lane sum for the selected physical mark.
No same-owner command departure means no same-owner lane preparation.
All other selected disjoint blocks use their literal transport, and
quiet lanes have an exact frame. -/
theorem owner_weak (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (m w owner : Int)
    (d : At Sheet → Nat)
    (noDepart : ∀ C p, (C,BStarLongCommand.Offer.advance p)∈actualOffers g raw →
      pairOwner m w g.2.axes.h6 cmdDispl C.source≠owner)
    (gap : ∀ C∈ownerClaims g m w owner (reserved (round g raw).prep), ∀ a,
      C.destination=some a → d a<d C.source) :
    total (fun a => rank (d a) (post g raw a)) (ownerLanes g m w owner) ≤
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
  apply aggregate_le _ _ slots (remainder slots bs) bs (chart_partition slots bs nd bd sub)
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

/-- Wire the witnessed local mobile comparison to the complete physical
join. A separate verified command-rank aggregation may supply the
strict payment premise, in which case the surviving equal-forward
branch automatically has no same-owner prep. -/
theorem joined_owner_weak (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (m w owner : Int) (d : At Sheet → Nat) (beforeF afterF : Nat) :
    let b := BStarLongWork.bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    (∀ C p, (C,BStarLongCommand.Offer.advance p)∈actualOffers g raw →
      pairOwner m w g.2.axes.h6 cmdDispl C.source=owner → afterF<beforeF) →
    beforeF≤afterF →
    (∀ C∈ownerClaims g m w owner (reserved (round g raw).prep), ∀ a,
      C.destination=some a → d a<d C.source) →
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    total (fun a => rank (d a) (view y a)) (ownerLanes g m w owner) ≤
      total (fun a => rank (d a) (view raw a)) (ownerLanes g m w owner) := by
  dsimp only
  intro pays stable gap
  let b := BStarLongWork.bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
  change total (fun a => rank (d a) (view y a)) (ownerLanes g m w owner) ≤ _
  have J : view y=post g raw :=
    BStarClearanceMobileJoined.joined_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x
  rw [J]
  exact owner_weak g raw m w owner d (fun C p h own => (Nat.not_lt_of_ge stable) (pays C p h own)) gap

end L4.BStarClearanceMobileOwner
