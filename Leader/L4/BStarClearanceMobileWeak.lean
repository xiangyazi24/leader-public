import Leader.L4.BStarClearanceMobileJoined
import Leader.L4.BStarClearanceMobile
import Leader.L4.BStarClearancePrepOwner

namespace L4.BStarClearanceMobileWeak
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongPackets
open BStarLongPrep BStarLongCommandData BStarCopyFIFO BStarCopyUpstreamCredit
open BStarClearanceMobile

/-- Every actual selected hop with a one-unit owner distance drop is
weakly decreasing. BAD is occupied. Holds don't need vacancy; either
old empty sender or old occupied open receiver gives literal identity. -/
theorem hop_weak (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (u v : At Sheet) (c : DataClaim)
    (hs : c.source=u) (hd : c.destination=some v) (hh : c.kind=.hop)
    (sel : c∈orderedData g (reserved (round g x).prep)) (ne : u≠v) (d : Nat) :
    rank (d+1) (post g x u)+rank d (post g x v) ≤
      rank (d+1) (view x u)+rank d (view x v) := by
  by_cases E : (view x u).mobile=.empty
  · unfold post
    rw [sender_exact g x u v c hs hd hh sel ne,
      BStarLongCopyFence.receiver_exact g x u v c hs hd hh sel ne]
    simp [hopEffects,E,typedLeaves]
  · by_cases C : (view x u).gate && (view x v).gate
    · by_cases V : (view x v).mobile=.empty
      · exact Nat.le_of_lt (vacant_hop_charge g x u v c hs hd hh sel ne E V d)
      · have C' : ((view x u).gate && (view x v).gate)=true := C
        unfold post
        rw [sender_exact g x u v c hs hd hh sel ne,
          BStarLongCopyFence.receiver_exact g x u v c hs hd hh sel ne]
        simp [hopEffects,E,V,C',typedLeaves]
    · have C' : ((view x u).gate && (view x v).gate)=false := Bool.eq_false_iff.mpr C
      exact Nat.le_of_lt (closed_hop_charge g x u v c hs hd hh sel ne E C' (d+1) d (by omega))

theorem terminal_weak (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (s : At Sheet) (sel : ending s∈orderedData g (reserved (round g x).prep))
    (d : Nat) : rank d (post g x s)≤rank d (view x s) := by
  by_cases D : d=0
  · simp [rank,D]
  by_cases E : (view x s).mobile=.empty
  · rw [terminal_exact g x s sel]
    simp [endEffects,E,typedLeaves]
  · exact Nat.le_of_lt (terminal_charge g x s sel E d (by omega))

private theorem untouched_fold (old : At Sheet → Lane) (xs : List (At Sheet × Leaf))
    (a : At Sheet) (H : ∀ w∈xs, w.1≠a) :
    (xs.foldl update old) a=old a := by
  induction xs generalizing old with
  | nil => rfl
  | cons w ws ih =>
    rw [List.foldl_cons,ih _ (fun t ht => H t (List.mem_cons_of_mem _ ht))]
    simp [update,Ne.symm (H w List.mem_cons_self)]

/-- Neither automatic scratch/guard nor a quiet data slot can change
the old lane; disjointness from reservations and selected claims is
sufficient even if other lanes receive real prep. -/
theorem quiet_lane (g : Pair LongGeometry) (x : Pair (BitVec LW)) (a : At Sheet)
    (prep : a∉reserved (round g x).prep)
    (transport : ∀ C∈orderedData g (reserved (round g x).prep), a∉C.slots) :
    post g x a=view x a := by
  unfold post
  rw [BStarLongCommandData.round_transfer]
  apply untouched_fold
  rintro ⟨b,w⟩ hw E
  change b=a at E
  subst b
  simp only [BStarLongPrep.assignments,List.mem_append] at hw
  rcases hw with H|H
  · exact prep (prep_lane_reserved _ _ _ _ H)
  · obtain ⟨C,hC,H⟩ := List.mem_flatMap.mp H
    exact transport C hC (data_lane_claim _ _ _ _ _ H)

theorem joined_hop_weak (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (u v : At Sheet) (C : DataClaim) (hs : C.source=u) (hd : C.destination=some v)
    (hh : C.kind=.hop) (ne : u≠v) (d : Nat) :
    let b := BStarLongWork.bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    C∈orderedData g (reserved (round g raw).prep) →
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    rank (d+1) (view y u)+rank d (view y v) ≤
      rank (d+1) (view raw u)+rank d (view raw v) := by
  dsimp only
  intro H
  let b := BStarLongWork.bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
  change rank (d+1) (view y u)+rank d (view y v) ≤ _
  have J : view y=post g raw :=
    BStarClearanceMobileJoined.joined_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x
  rw [J]
  exact hop_weak g raw u v C hs hd hh H ne d


open BStarLongFiberOwner BStarH6WordChart BStarLongEvents in
/-- Every real reservation is caused by an actual forward departure of
the lane's owner, even when arbitration or prep emits a fault. This
does not require overlap with a routed data claim. -/
theorem reserved_owner_departure (g : Pair LongGeometry) (m w : Int) (x : Pair (BitVec LW))
    (s : At Sheet) (h : s∈reserved (round g x).prep) :
    ∃ c q, (c,.advance q)∈actualOffers g x ∧
      pairOwner m w g.2.axes.h6 cmdDispl c.source=pairOwner m w g.2.axes.h6 dataDispl s := by
  obtain ⟨c,p,op,hc,_,_,hside,hsite⟩ := BStarLongFenceTopology.reserved_from_old_advance g x s h
  obtain ⟨q,hq⟩ := BStarClearancePrepOwner.gated_still_departs g x c p hc
  have E : (⟨c.source.side,s.occurrence⟩ : At Sheet)=s := by
    cases s
    simp_all
  exact ⟨c,q,hq,(prep_owner g m w c.source op s.occurrence hsite).trans
    (congrArg (pairOwner m w _ dataDispl) E)⟩

theorem joined_quiet_lane (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (a : At Sheet) :
    let b := BStarLongWork.bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    a∉reserved (round g raw).prep →
    (∀ C∈orderedData g (reserved (round g raw).prep), a∉C.slots) →
    view (Pair.map LargeSite.long (largePair b x)) a=view raw a := by
  dsimp only
  intro H T
  let b := BStarLongWork.bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
  have J : view y=post g raw :=
    BStarClearanceMobileJoined.joined_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x
  exact (congrFun J a).trans (quiet_lane g raw a H T)

#print axioms hop_weak
#print axioms terminal_weak
#print axioms quiet_lane
#print axioms joined_hop_weak
#print axioms reserved_owner_departure
#print axioms joined_quiet_lane
end L4.BStarClearanceMobileWeak
