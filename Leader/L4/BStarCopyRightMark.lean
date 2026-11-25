import Leader.L4.BStarCopyRightStrip
import Leader.L4.BStarCopyOwnedFrozen

namespace L4.BStarCopyRightMark
open AllSizeProtocol BStarLongClaims BStarH6WordChart BStarLongPackets
open BStarLongPrep BStarLongCommandData BStarCopyRightStrip BStarTrace BStarLongWork

private def update (f : At Sheet → Lane) (p : At Sheet × Leaf) (s : At Sheet) : Lane :=
  if s=p.1 then p.2.put (f s) else f s

private theorem fold_away (A : List (At Sheet × Leaf)) (old : At Sheet → Lane)
    (s : At Sheet) (ha : ∀ a, (s,a)∉A) :
    (A.foldl update old) s=old s := by
  induction A generalizing old with
  | nil => rfl
  | cons a A ih =>
    have ne : s≠a.1 := fun H => ha a.2 (by cases a; simp_all)
    rw [List.foldl_cons,ih (update old a) (fun a h => ha a (List.mem_cons_of_mem _ h))]
    simp [update,ne]

/-- Full four-field frame, even for occupied/invalid mobiles. Competing
statement candidates and old data in other lanes are arbitrary. The
premise is about *emitted* old effects, not packet byte equality. -/
theorem patch_spectator (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (s : At Sheet)
    (np : s∉reserved (round g raw).prep)
    (nd : ∀ d∈orderedData g (reserved (round g raw).prep),
      ∀ a, (s,a)∉dataEffects g (view raw) d) :
    view (patchPair (patch g raw) raw) s=view raw s := by
  rw [BStarLongCommandData.round_transfer]
  apply fold_away
  intro a M
  rcases List.mem_append.mp M with M|M
  · exact np (prep_lane_reserved _ _ _ _ M)
  · obtain ⟨d,D,H⟩ := List.mem_flatMap.mp M
    exact nd d D a H

theorem spectator_off_slots (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (s : At Sheet)
    (np : s∉reserved (round g raw).prep)
    (nd : ∀ d∈orderedData g (reserved (round g raw).prep), s∉d.slots) :
    view (patchPair (patch g raw) raw) s=view raw s :=
  patch_spectator g raw s np <| fun d H a A => nd d H (data_lane_claim g _ d s a A)

theorem joined_spectator {k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat} (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (s : At Sheet) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw := Pair.map LargeSite.long x
    s∉reserved (round g raw).prep →
    (∀ d∈orderedData g (reserved (round g raw).prep),
      ∀ a, (s,a)∉dataEffects g (view raw) d) →
    view (Pair.map LargeSite.long (largePair b x)) s=view raw s := by
  dsimp only
  intro N D
  refine (congrFun (BStarClearanceMobileJoined.joined_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x) s).trans ?_
  exact patch_spectator _ _ s N D

/-- Both endpoints remain entirely unchanged if a selected nonempty
transfer waits on an occupied destination, or the old source is empty.
A disabled occupied-source offer is NOT a stutter: it drops the source.
Thus an all-word FIFO proof really needs persistent both-endpoint gates. -/
theorem hop_no_effect (g : Pair LongGeometry) (old : At Sheet → Lane) (u v : At Sheet)
    (H : (old u).mobile=.empty ∨
      (((old u).gate && (old v).gate)=true ∧ (old v).mobile≠.empty)) :
    dataEffects g old (hop u v)=[] := by
  rcases H with E|⟨E, F⟩
  · simp [dataEffects,hop,hopEffects,E]
  · by_cases X : (old u).mobile=.empty <;>
      simp [dataEffects,hop,hopEffects,X,E,F]

/-- Any physically adjacent pair of *upstream* addresses is a single
successive link at increasing strip indices. Includes wrapped strips;
the ring-closing edge cannot connect two upstream positions out of
order, since index zero (the retaining head) is not upstream. -/
theorem upstream_adjacent {n : Nat} (base : Fin n) {i j tail : Nat}
    (ip : 0<i) (jp : 0<j) (it : i≤tail) (jt : j≤tail) (tn : tail<n)
    (adj : rightNeighbor (addr base i)=addr base j) : j=i+1 := by
  rw [←addr_next] at adj
  have B : i+1≤n := by omega
  by_cases h : i+1=n
  · have E : addr base n=addr base 0 := by
      apply Fin.ext
      simp [addr,Nat.add_mod_right]
    rw [h,E] at adj
    have := addr_inj base (by omega : 0<n) (by omega : j<n) adj
    omega
  · exact (addr_inj base (by omega) (by omega) adj).symm

theorem selected_outgoing {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n→LargeSite a} {base : Fin n} {seam tail : Nat}
    (C : Strip b x base seam tail) (i : Nat) (it : i<tail)
    (rsv : List (At Sheet)) (d : DataClaim)
    (M : d∈orderedData (oldPair b x (addr base i)) rsv)
    (S : d.source=R (rail seam (i+1))) :
    d=hop (R (rail seam (i+1))) (L (rail seam i)) := by
  let g := oldPair b x (addr base i)
  have raw : d∈dataClaims g := BStarLongFenceTopology.selected_data_raw _ _ _ M
  have right := (addr_next base i).symm
  by_cases pad : i+1<seam
  · have H : g.2.axes.h6=false := by
      change oldH6 b x (rightNeighbor (addr base i))=false
      rw [right]; exact C.rd_noheader _ pad
    have q : i<seam := by omega
    simp only [rail,if_pos q,if_pos pad] at S ⊢
    exact (raw_rd_send_body _ _ H S).mp raw
  · have T : d.source=R .rs := by simpa only [rail,if_neg pad] using S
    have cases := (raw_rs_send _ _ T).mp raw
    by_cases atSeam : i+1=seam
    · have H : g.2.axes.h6=true := by
        change oldH6 b x (rightNeighbor (addr base i))=true
        rw [right,atSeam]; exact C.rs_header
      have q : i<seam := by omega
      simp only [rail,if_neg pad,if_pos q]
      rcases cases with ⟨_,_,E⟩|⟨N,_⟩
      · exact E
      · rw [H] at N
        contradiction
    · have H : g.2.axes.h6=false := by
        change oldH6 b x (rightNeighbor (addr base i))=false
        rw [right]; exact C.rs_nonheader _ (by omega) (by omega)
      have q : ¬i<seam := by omega
      simp only [rail,if_neg pad,if_neg q]
      rcases cases with ⟨N,_⟩|⟨_,_,_,_,E⟩
      · rw [H] at N
        contradiction
      · exact E

set_option maxHeartbeats 400000 in
/-- On an interior physical edge both strip slots have exactly one
possible selected data demand, with no other read/write aliases. Any
other simultaneous selected row (other lane or other owner) frames
the two slots. This includes the seam and all center padding. -/
theorem strip_pair_claim {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n→LargeSite a} {base : Fin n} {seam tail : Nat}
    (C : Strip b x base seam tail) (i : Nat) (it : i<tail)
    (rsv : List (At Sheet)) (d : DataClaim)
    (M : d∈orderedData (oldPair b x (addr base i)) rsv)
    (T : L (rail seam i)∈d.slots ∨ R (rail seam (i+1))∈d.slots) :
    d=hop (R (rail seam (i+1))) (L (rail seam i)) := by
  have raw := BStarLongFenceTopology.selected_data_raw _ _ _ M
  have l := no_left_send _ _ raw
  have rr := no_right_receive _ _ raw
  unfold Claim.slots at T
  cases D : d.destination with
  | none =>
    simp only [D,Option.toList_none,List.mem_cons,List.not_mem_nil,or_false] at T
    rcases T with T|T
    · by_cases h : i<seam
      · exact (l.1 (T.symm.trans (congrArg L (if_pos h)))).elim
      · exact (l.2 (T.symm.trans (congrArg L (if_neg h)))).elim
    · exact selected_outgoing C i it _ _ M T.symm
  | some dst =>
    simp only [D,Option.toList_some,List.mem_cons,List.not_mem_nil,or_false] at T
    rcases T with (T|T)|(T|T)
    · cases h : rail seam i with
      | ls => simp [rail] at h <;> split at h <;> contradiction
      | ld => simp [rail] at h <;> split at h <;> contradiction
      | rs => exact (l.2 (T.symm.trans (congrArg L h))).elim
      | rd => exact (l.1 (T.symm.trans (congrArg L h))).elim
    · exact selected_adjacent C i it _ _ M (D.trans (congrArg some T.symm))
    · exact selected_outgoing C i it _ _ M T.symm
    · cases h : rail seam (i+1) with
      | ls => simp [rail] at h <;> split at h <;> contradiction
      | ld => simp [rail] at h <;> split at h <;> contradiction
      | rs => exact (rr.2 (D.trans (congrArg some (T.symm.trans (congrArg R h))))).elim
      | rd => exact (rr.1 (D.trans (congrArg some (T.symm.trans (congrArg R h))))).elim

theorem strip_pair_frame {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
    (x : Fin n→LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (base : Fin n) (seam tail i : Nat) (it : i<tail)
    (C : Strip (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp) x base seam tail) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let edge := addr base i
    let xx := (x edge,x (rightNeighbor edge))
    let g := oldPair b x edge
    let raw := Pair.map LargeSite.long xx
    let rs := reserved (round g raw).prep
    let u := R (rail seam (i+1))
    let v := L (rail seam i)
    let h := hop u v
    (h∉orderedData g rs ∨ (view raw u).mobile=.empty ∨
      (((view raw u).gate && (view raw v).gate)=true ∧ (view raw v).mobile≠.empty)) →
    ∀ s, (s=u ∨ s=v) → s∉rs →
      view (Pair.map LargeSite.long (largePair b xx)) s=view raw s := by
  dsimp only
  intro quiet s S np
  apply joined_spectator hp _ s np
  intro d D a A
  have M := data_lane_claim _ _ _ _ _ A
  have TS : L (rail seam i)∈d.slots ∨ R (rail seam (i+1))∈d.slots := by
    rcases S with rfl|rfl
    · exact .inr M
    · exact .inl M
  have shape : d=hop (R (rail seam (i+1))) (L (rail seam i)) :=
    strip_pair_claim C i it _ d D TS
  subst d
  rcases quiet with no|blocked
  · exact no D
  · have Z := hop_no_effect (Pair.map (longGeometry (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp))
        (x (addr base i), x (rightNeighbor (addr base i)))) _ _ _ blocked
    rw [Z] at A
    exact List.not_mem_nil A

/-- Any reservation on either of the two strip slots suppresses the
entire adjacent data hop. The other slot is a full spectator if it
has no independent licensed reservation. -/
theorem strip_reserved_blocks {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n→LargeSite a} {base : Fin n} {seam i : Nat}
    (rs : List (At Sheet))
    (prep : L (rail seam i)∈rs ∨ R (rail seam (i+1))∈rs) :
    hop (R (rail seam (i+1))) (L (rail seam i))∉orderedData (oldPair b x (addr base i)) rs := by
  intro D
  have h := (data_reservations _ _).2 _ D
  rcases prep with P|P
  · exact h _ (by simp [Claim.slots,hop]) P
  · exact h _ (by simp [Claim.slots,hop]) P

theorem inject_or_no_reservation (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (s : At Sheet) (tracked : s.occurrence=.rd ∨ s.occurrence=.rs)
    (ownerCode : ∀ offer∈(arbitration (round g raw).prep).1, offer.claim.lane=s →
      ∃ pc, 10≤pc ∧ prepOf pc=some offer.claim.op) :
    s∉reserved (round g raw).prep ∨
      s.occurrence=.rs ∧ ∃ offer∈(arbitration (round g raw).prep).1,
        offer.claim.lane=s ∧ offer.claim.op=.inject ∧ offer.claim.origin.occurrence=2 := by
  classical
  by_cases Rsv : s∈reserved (round g raw).prep
  · obtain ⟨o,H,E⟩ := List.mem_map.mp Rsv
    obtain ⟨pc,P,K⟩ := ownerCode o H E
    have J : pc=10 ∧ o.claim.op=.inject := by
      unfold prepOf at K
      split at K <;> first | contradiction | omega | exact ⟨rfl,(Option.some.inj K).symm⟩
    obtain ⟨C,_,_,_,_,_,_,origin,_,T⟩ := BStarCopyOwnedFrozen.winner_origin g raw o H
    rw [E,J.2] at T
    have A : s.occurrence=.rs ∧ C.source.occurrence=2 := by
      simp only [prepSites] at T
      split at T
      · split at T
        · have Q : s.occurrence=.ls := by simpa using T
          rcases tracked with tr|tr <;> rw [Q] at tr <;> contradiction
        · split at T
          · exact ⟨by simpa using T,by assumption⟩
          · simp at T
      · simp at T
    exact .inr ⟨A.1,o,H,E,J.2,(congrArg At.occurrence origin).trans A.2⟩
  · exact .inl Rsv

theorem tail_claim_frame {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n→LargeSite a} {base : Fin n} {seam tail : Nat}
    (C : Strip b x base seam tail) (rs : List (At Sheet)) (d : DataClaim)
    (M : d∈orderedData (oldPair b x (addr base tail)) rs) :
    L (rail seam tail)∉d.slots := by
  intro T
  have raw := BStarLongFenceTopology.selected_data_raw _ _ _ M
  have q : ¬tail<seam := by have := C.seam_le_tail; omega
  unfold Claim.slots at T
  rcases List.mem_cons.mp T with E|E
  · simp only [rail,if_neg q] at E
    exact (no_left_send _ _ raw).2 E.symm
  · have D : d.destination=some (L (rail seam tail)) := by
      cases h : d.destination with
      | none => simp [h] at E
      | some s =>
        simp only [h,Option.toList_some,List.mem_singleton] at E
        rw [E]
    exact tail_no_ingress C d raw D

theorem joined_tail_frame {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
    (x : Fin n→LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (base : Fin n) (seam tail : Nat)
    (C : Strip (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp) x base seam tail) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let edge := addr base tail
    let xx := (x edge,x (rightNeighbor edge))
    let g := oldPair b x edge
    let raw := Pair.map LargeSite.long xx
    let s := L (rail seam tail)
    s∉reserved (round g raw).prep →
      view (Pair.map LargeSite.long (largePair b xx)) s=view raw s := by
  dsimp only
  intro Q
  apply joined_spectator hp _ _ Q
  intro d M a A
  exact tail_claim_frame C _ d M (data_lane_claim _ _ _ _ _ A)

theorem rightNeighbor_inj {n : Nat} {a b : Fin n}
    (h : rightNeighbor a=rightNeighbor b) : a=b := by
  have A := congrArg Fin.val h
  change (a.val+1)%n=(b.val+1)%n at A
  have X := a.isLt
  have Y := b.isLt
  by_cases p : a.val+1=n <;> by_cases q : b.val+1=n
  · exact Fin.ext (by omega)
  · rw [p,Nat.mod_self,Nat.mod_eq_of_lt (by omega : b.val+1<n)] at A
    omega
  · rw [q,Nat.mod_self,Nat.mod_eq_of_lt (by omega : a.val+1<n)] at A
    omega
  · rw [Nat.mod_eq_of_lt (by omega : a.val+1<n),
        Nat.mod_eq_of_lt (by omega : b.val+1<n)] at A
    exact Fin.ext (by omega)

/-- Every raw mark which touches an upstream position is uniquely one
of its incoming/outgoing geometric marks. This identifies the selected
pair without polling or skipping physical updates. -/
theorem incident {n : Nat} (base e : Fin n) (i : Nat) (ip : 0<i)
    (touch : addr base i=e ∨ addr base i=rightNeighbor e) :
    e=addr base i ∨ e=addr base (i-1) := by
  rcases touch with h|h
  · exact .inl h.symm
  · apply Or.inr
    apply rightNeighbor_inj
    have H := addr_next base (i-1)
    have J : i-1+1=i := by omega
    rwa [J,h] at H

theorem ring_exterior_frame {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
    (x : Fin n→LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (base e : Fin n) (i : Nat) (ip : 0<i)
    (non : e≠addr base i) (pred : e≠addr base (i-1)) :
    AllSizeS1Geometry.step (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp) x e (addr base i)=x (addr base i) := by
  have A : addr base i≠e := Ne.symm non
  have B : addr base i≠rightNeighbor e := fun H =>
    (incident base e i ip (.inr H)).elim non pred
  simp [AllSizeS1Geometry.step,A,B]

section JoinedRing
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "updateRing" => AllSizeS1Geometry.step (n:=n) B

theorem old_access (x : X) (e : Fin n) (a : At Sheet) :
    view ((x e).long,(x (rightNeighbor e)).long) a =
      readLane (Sheet.index a.occurrence) (x (site e a.side)).long := by
  obtain ⟨s,sh⟩ := a
  cases s <;> rfl

theorem new_access (x : X) (e : Fin n) (a : At Sheet) (sep : e≠rightNeighbor e) :
    view (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) a =
      readLane (Sheet.index a.occurrence) (updateRing x e (site e a.side)).long := by
  obtain ⟨s,sh⟩ := a
  cases s <;> simp [view,site,lane,BStarTrace.lane,Pair.map,AllSizeS1Geometry.step,Ne.symm sep]

/-- A selected interior mark frames every other upstream position at
the raw configuration level, including when actual Fin addresses wrap. -/
theorem ring_other_positions (x : X) (base : Fin n) (i j tail : Nat)
    (it : i<tail) (jpos : 0<j) (jt : j≤tail) (nT : tail<n)
    (a : j≠i) (b : j≠i+1) :
    updateRing x (addr base i) (addr base j)=x (addr base j) := by
  apply ring_exterior_frame hp x base (addr base i) j jpos
  · intro H
    exact a ((addr_inj base (by omega) (by omega) H).symm)
  · intro H
    have K := addr_inj base (by omega) (by omega) H
    omega

open BStarCopyFIFO BStarCopyUpstreamTags
def MobileMatches {Label : Type} (digits : Label→BitVec 36) (x : X)
    (base : Fin n) (seam tail : Nat) (label : Nat→Option Label) : Prop :=
  ∀ j, 0<j → j≤tail →
    (readLane (Sheet.index (rail seam j)) (x (addr base j)).long).mobile =
      encode digits (label j)

def swapTag {Label : Type} (label : Nat→Option Label) (i : Nat) (tag : Label)
    (j : Nat) : Option Label :=
  if j=i then some tag else if j=i+1 then none else label j

/-- Whole physical mark, not a reduced word: a selected ordinary
upstream hop updates *exactly* the two original tag positions and
frames every spectator. This works with arbitrary simultaneous
out-of-strip updates. The gates are explicit old premises. -/
theorem ring_transport {Label : Type} (digits : Label→BitVec 36) (tag : Label)
    (x : X) (base : Fin n) (seam tail i : Nat) (pos : 0<i) (it : i<tail)
    (C : Strip B x base seam tail) (d : DataClaim) (label : Nat→Option Label)
    (labels : MobileMatches digits x base seam tail label)
    (source : label (i+1)=some tag) (vacant : label i=none) :
    let edge := addr base i
    let raw : Pair (BitVec LW) := ((x edge).long,(x (rightNeighbor edge)).long)
    let g := oldPair B x edge
    let u := R (rail seam (i+1))
    let v := L (rail seam i)
    edge≠rightNeighbor edge →
    d∈orderedData g (reserved (round g raw).prep) →
    d.destination=some v →
    ((view raw u).gate && (view raw v).gate)=true →
    MobileMatches digits (updateRing x edge) base seam tail (swapTag label i tag) := by
  dsimp only
  intro sep M D G
  let edge := addr base i
  let u := R (rail seam (i+1))
  let v := L (rail seam i)
  have U : site edge u.side=addr base (i+1) := (addr_next base i).symm
  have V : site edge v.side=addr base i := rfl
  have donor := labels (i+1) (by omega) (by omega)
  have recv := labels i pos (by omega)
  rw [source] at donor
  rw [vacant] at recv
  have S : (view ((x edge).long,(x (rightNeighbor edge)).long) u).mobile =
      encode digits (some tag) := by rw [old_access,U]; exact donor
  have T : (view ((x edge).long,(x (rightNeighbor edge)).long) v).mobile =
      encode digits none := by rw [old_access,V]; exact recv
  have K := joined_strip_hop hp digits tag x base seam tail i pos it C d M D G S T
  have clear := K.1
  have gain := K.2.1
  change (view (Pair.map LargeSite.long (largePair B (x edge,x (rightNeighbor edge)))) u).mobile = _ at clear
  change (view (Pair.map LargeSite.long (largePair B (x edge,x (rightNeighbor edge)))) v).mobile = _ at gain
  rw [new_access hp x edge u sep,U] at clear
  rw [new_access hp x edge v sep,V] at gain
  intro j jp jt
  by_cases eq : j=i
  · subst j
    simp only [swapTag]
    exact gain
  · by_cases E : j=i+1
    · subst j
      simp only [swapTag,if_neg eq]
      exact clear
    · rw [ring_other_positions hp x base i j tail it jp jt C.tail_lt eq E]
      simpa [swapTag,eq,E] using labels j jp jt

end JoinedRing

/-- The actual ordered word exposed by an upstream mobile labeling;
index zero is reserved for the retaining boundary. -/
def stripWord {L : Type} (tail : Nat) (label : Nat→Option L) : List L :=
  (List.range' 1 tail).flatMap (fun j => (label j).toList)

private theorem flatMap_same {L : Type} (q : List Nat) (f g : Nat→List L)
    (same : ∀ i∈q, f i=g i) : q.flatMap f=q.flatMap g := by
  induction q with
  | nil => rfl
  | cons a q ih =>
    simp only [List.flatMap_cons]
    rw [same a (by simp),ih (fun i m => same i (List.mem_cons_of_mem _ m))]

theorem stripWord_swap {L : Type} (tail i : Nat) (ip : 0<i) (it : i<tail)
    (label : Nat→Option L) (tag : L)
    (source : label (i+1)=some tag) (vacant : label i=none) :
    stripWord tail (swapTag label i tag)=stripWord tail label := by
  let pre := List.range' 1 (i-1)
  let post := List.range' (i+2) (tail-(i+1))
  have ix : 1 + 1 * (i-1)=i := by omega
  have ll : i-1 + (tail-(i+1)+1+1)=tail := by omega
  have E : List.range' 1 tail=pre++i::(i+1)::post := by
    rw [←ll,←List.range'_append,ix,List.range'_succ,List.range'_succ]
  unfold stripWord
  rw [E]
  simp only [List.flatMap_append,List.flatMap_cons]
  have f (j : Nat) (h : j≠i) (k : j≠i+1) : swapTag label i tag j=label j := by
    simp [swapTag,h,k]
  have P := flatMap_same pre (fun j => (swapTag label i tag j).toList)
    (fun j => (label j).toList) (by
      intro j jP
      obtain ⟨q,Q,E⟩ := List.mem_range'.mp jP
      rw [f j (by omega) (by omega)])
  have Q := flatMap_same post (fun j => (swapTag label i tag j).toList)
    (fun j => (label j).toList) (by
      intro j jP
      obtain ⟨q,_,E⟩ := List.mem_range'.mp jP
      rw [f j (by omega) (by omega)])
  rw [P,Q,source,vacant]
  simp [swapTag]

end L4.BStarCopyRightMark
