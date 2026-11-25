import Leader.L4.BStarCopyFenceSaturation
import Leader.L4.BStarClearanceMobileJoined
import Leader.L4.BStarClearanceMobileOwner
import Leader.L4.BStarCopyOperand
import Leader.L4.BStarH6Ordinal

namespace L4.BStarCopyUpstreamTags
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongPackets BStarLongPrep
open BStarLongCommandData BStarCopyFIFO BStarCopyFenceSaturation BStarCopyMarkedLedger

/-- Ghost labels are stored per physical mobile, front to back (nearest
retaining receiver first). List addresses, not equal byte values,
determine which marked token moves. -/
def tags {L : Type} (u : List (Option L)) : List L := u.flatMap Option.toList

theorem tags_move {L : Type} (a : L) (pre post : List (Option L)) :
    tags (pre++some a::none::post)=tags (pre++none::some a::post) := by
  simp [tags]

theorem tags_new_tail {L : Type} (a : L) (pre post : List (Option L))
    (behindEmpty : tags post=[]) :
    tags (pre++some a::post)=tags (pre++none::post)++[a] := by
  have E : post.flatMap Option.toList=[] := behindEmpty
  simp [tags,E]

theorem tags_cross_head {L : Type} (a : L) (post : List (Option L)) :
    tags (some a::post)=a::tags (none::post) := rfl

private def geo (h i l : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,h⟩,i,l,0,false⟩

/-- Right-side center padding is an RD mobile on an OUT site, not a
retained digit. Every data arrival to an RD receiver comes from the
old right endpoint, while the recipient is old left; a header seam
changes RS→RD, but never changes which occurrence is old sender. -/
theorem right_rd_geometry (g : Pair LongGeometry) (rsv : List (At Sheet))
    (c : DataClaim) (dst : At Sheet)
    (chosen : c∈orderedData g rsv) (dest : c.destination=some dst) (D : dst.occurrence=.rd) :
    c.source.side=.right ∧ dst.side=.left ∧
    (if g.2.axes.h6 then c.source.occurrence=.rs else c.source.occurrence=.rd) ∧
    retains g dst = g.1.inside := by
  let test (b : Bool) (c : DataClaim) : Bool :=
    match c.destination with
    | none => true
    | some a => if a.occurrence=.rd then
        c.source.side==.right && a.side==.left &&
          (c.source.occurrence==(if b then .rs else .rd))
      else true
  have C (i l h j : Bool) :
      (dataClaims (geo false i l,geo h j false)).all (test h)=true := by
    cases i <;> cases l <;> cases h <;> cases j <;> decide +kernel
  obtain ⟨l,r⟩ := g
  have old := BStarLongFenceTopology.selected_data_raw (l,r) rsv c chosen
  change c∈dataClaims (geo false l.inside l.last,geo r.axes.h6 r.inside false) at old
  have Q := List.all_eq_true.mp (C l.inside l.last r.axes.h6 r.inside) c old
  unfold test at Q
  rw [dest] at Q
  dsimp only at Q
  rw [if_pos D] at Q
  simp only [Bool.and_eq_true,beq_iff_eq] at Q
  refine ⟨Q.1.1,Q.1.2,?_,?_⟩
  · cases H : r.axes.h6 <;> simpa [H] using Q.2
  · unfold retains
    rw [Q.1.2,D]
    simp

/-- Nonretaining selected HOP transfers the exact ghost label carried
by its old physical sender into the old vacant receiver. All equal
byte coincidences are irrelevant. -/
theorem nonretaining_tag_pair {L : Type} (digits : L→BitVec 36) (tag : L)
    (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (c : DataClaim) (u v : At Sheet)
    (source : c.source=u) (dst : c.destination=some v) (kind : c.kind=.hop)
    (chosen : c∈orderedData g (reserved (round g raw).prep)) (ne : u≠v)
    (notHeld : retains g v=false) (gates : ((view raw u).gate && (view raw v).gate)=true)
    (fromTag : (view raw u).mobile=encode digits (some tag))
    (vacant : (view raw v).mobile=encode digits none) :
    let out := view (patchPair (patch g raw) raw)
    (out u).mobile=encode digits none ∧
    (out v).mobile=encode digits (some tag) ∧
    (out v).retained=(view raw v).retained := by
  dsimp only
  rw [sender_exact g raw u v c source dst kind chosen ne,
    BStarLongCopyFence.receiver_exact g raw u v c source dst kind chosen ne]
  simp [hopEffects,fromTag,vacant,gates,notHeld,encode,typedLeaves,Leaf.put]

open BStarLongWork BStarH6WordChart
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- Actual full raw mark, including the non-COPY joined layers. -/
theorem nonretaining_tag_joined {L : Type} (digits : L→BitVec 36) (tag : L)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (cl : DataClaim) (u v : At Sheet)
    (source : cl.source=u) (dst : cl.destination=some v) (kind : cl.kind=.hop) :
    let g := Pair.map (longGeometry B) x
    let raw := Pair.map LargeSite.long x
    cl∈orderedData g (reserved (round g raw).prep) → u≠v →
    retains g v=false → ((view raw u).gate && (view raw v).gate)=true →
    (view raw u).mobile=encode digits (some tag) → (view raw v).mobile=encode digits none →
    let out := view (Pair.map LargeSite.long (largePair B x))
    (out u).mobile=encode digits none ∧
    (out v).mobile=encode digits (some tag) ∧
    (out v).retained=(view raw v).retained := by
  dsimp only
  intro sel ne ret gates input vacancy
  rw [BStarClearanceMobileJoined.joined_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x]
  exact nonretaining_tag_pair digits tag _ _ cl u v source dst kind sel ne ret gates input vacancy

#print axioms tags_move
#print axioms right_rd_geometry
#print axioms nonretaining_tag_joined

/-- Pure old-head credit. It comes from the existing exact ordered
ledger even when a release on this same mark is excluded. -/
theorem old_head_credit {L : Type} {plan : List L} {s : Ledger L} (tag : L) (u : List L)
    (P : OrderedPrefix plan s (tag::u)) :
    (s.cells 0).arrivals.length<s.release.released.length := by
  have H := congrArg List.length (ordered_prefix P).2
  simp only [List.length_append,List.length_cons] at H
  omega

/-- Boundary crossing: feeds the selected real retaining receiver the
old head tag (not an arbitrary label with the same bytes). The same
mark empties the actual upstream sender. -/
theorem physical_cross_head {L : Type} (digits : L→BitVec 36)
    {plan : List L} {s : Ledger L} (tag : L) (up : List L)
    (P : OrderedPrefix plan s (tag::up))
    (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (c : DataClaim) (u v : At Sheet)
    (src : c.source=u) (dst : c.destination=some v) (kind : c.kind=.hop)
    (chosen : c∈orderedData g (reserved (round g raw).prep)) (ne : u≠v)
    (retaining : retains g v=true) (gates : ((view raw u).gate && (view raw v).gate)=true)
    (oldTag : (view raw u).mobile=encode digits (some tag))
    (same : Compatible digits (s.cells 0) (view raw v)) (empty : (s.cells 0).mobile=none) :
    let post := view (patchPair (patch g raw) raw)
    OrderedPrefix plan (s.receiveFirst tag) up ∧
    (post u).mobile=encode digits none ∧
    Compatible digits ((s.receiveFirst tag).cells 0) (post v) := by
  dsimp only
  have credit := old_head_credit tag up P
  have carried := physical_first digits plan s (ordered_prefix P).1 tag g raw u v c src dst kind chosen
    ne retaining gates oldTag same empty credit
  have vacancy : (view raw v).mobile=.empty := by simpa [empty,encode] using same.1
  have sender := sender_exact g raw u v c src dst kind chosen ne
  have spent : (view (patchPair (patch g raw) raw) u).mobile=encode digits none := by
    rw [sender]
    simp [hopEffects,oldTag,vacancy,gates,encode,typedLeaves,Leaf.put]
  exact ⟨.mark P (.cross s up tag empty credit),spent,carried.2⟩

/-- In the physical view order, selected upstream hops swap a full
slot and its immediately preceding empty slot. This does not alter
the exact tag word; composing disjoint such moves is harmless. -/
theorem physical_inner_keeps_order {L : Type} (digits : L→BitVec 36)
    {plan : List L} {s : Ledger L} (tag : L) (pre post : List (Option L))
    (P : OrderedPrefix plan s (tags (pre++none::some tag::post)))
    (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (cl : DataClaim) (u v : At Sheet)
    (src : cl.source=u) (dst : cl.destination=some v) (kind : cl.kind=.hop)
    (chosen : cl∈orderedData g (reserved (round g raw).prep)) (ne : u≠v)
    (ret : retains g v=false) (gates : ((view raw u).gate && (view raw v).gate)=true)
    (oldTag : (view raw u).mobile=encode digits (some tag))
    (vacancy : (view raw v).mobile=encode digits none) :
    let out := view (patchPair (patch g raw) raw)
    OrderedPrefix plan s (tags (pre++some tag::none::post)) ∧
    (out u).mobile=encode digits none ∧ (out v).mobile=encode digits (some tag) := by
  have H := nonretaining_tag_pair digits tag g raw cl u v src dst kind chosen ne ret gates oldTag vacancy
  refine ⟨?_,H.1,H.2.1⟩
  rw [tags_move]
  exact P

#print axioms physical_cross_head
#print axioms physical_inner_keeps_order

/-- Actual old-right to old-left hop into right center OUT padding.
Outside RD never retains; it moves precisely the tagged old mobile,
whether the sender is old-right RS at the seam or old-right RD. -/
theorem right_padding_hop {L : Type} (digits : L→BitVec 36) (tag : L)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (cl : DataClaim) :
    let g := Pair.map (longGeometry B) x
    let raw := Pair.map LargeSite.long x
    cl∈orderedData g (reserved (round g raw).prep) → cl.destination=some (BStarLongClaims.L .rd) →
    g.1.inside=false →
    ((view raw cl.source).gate && (view raw (BStarLongClaims.L .rd)).gate)=true →
    (view raw cl.source).mobile=encode digits (some tag) →
    (view raw (BStarLongClaims.L .rd)).mobile=encode digits none →
    let out := view (Pair.map LargeSite.long (largePair B x))
    (out cl.source).mobile=encode digits none ∧
    (out (BStarLongClaims.L .rd)).mobile=encode digits (some tag) ∧
    (out (BStarLongClaims.L .rd)).retained=(view raw (BStarLongClaims.L .rd)).retained := by
  dsimp only
  intro sel D out gate sender target
  let g := Pair.map (longGeometry B) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let dst := BStarLongClaims.L Sheet.rd
  have Q := right_rd_geometry g _ cl dst sel D rfl
  have shape : cl.kind=.hop ∧ cl.source≠dst := by
    rcases BStarClearanceMobileOwner.selected_shape g (reserved (round g raw).prep) cl sel with
      ⟨_,bad⟩ | ⟨a,k,H,ne⟩
    · rw [D] at bad; contradiction
    · have E := Option.some.inj (D.symm.trans H)
      subst a
      exact ⟨k,ne⟩
  have notRet : retains g dst=false := Q.2.2.2.trans out
  exact nonretaining_tag_joined hp digits tag x cl _ dst rfl D shape.1 sel shape.2
    notRet gate sender target

#print axioms right_padding_hop

/-- The selected old upstream source position receives the exact frozen
packet, whose label is the next issued occurrence. Its insertion is at
the tail of the word if all physically behind positions are vacant. -/
theorem physical_inject_tail {L : Type} (digits : L→BitVec 36)
    {plan : List L} {s : Ledger L} (tag : L) (todo : List L)
    (front behind : List (Option L))
    (P : OrderedPrefix plan s (tags (front++none::behind)))
    (behindEmpty : tags behind=[]) (next : s.release.pending=tag::todo)
    (x : X) (e : Fin n) (sep : e≠rightNeighbor e) (sd : Side) (rev : Bool)
    (chosen : BStarCopyInjection.injection sd rev∈
      (arbitration (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep).1) :
    let i := site e sd
    let ln := Sheet.index (BStarCopyInjection.sourceLane rev)
    (readLane ln (x i).long).gate=true →
    (readLane ln (x i).long).frozen=.data (digits tag) →
    (readLane ln (x i).long).mobile=.empty →
    let out := readLane ln (step x e i).long
    OrderedPrefix plan (s.releaseOne tag todo) (tags (front++some tag::behind)) ∧
      out.mobile=encode digits (some tag) ∧ out.frozen=encode digits none := by
  dsimp only
  intro gate frozen empty
  have H := BStarCopyOperand.ring_inject hp x e sep sd rev (digits tag) chosen gate frozen empty
  rw [tags_new_tail _ _ _ behindEmpty]
  exact ⟨.mark P (.issue s _ tag todo next),congrArg Lane.mobile H,congrArg Lane.frozen H⟩

#print axioms physical_inject_tail

private theorem old_site_view (x : X) (e : Fin n) (a : At Sheet) :
    view ((x e).long,(x (rightNeighbor e)).long) a=
      readLane (Sheet.index a.occurrence) (x (site e a.side)).long := by
  obtain ⟨s,sh⟩ := a
  cases s <;> rfl

private theorem new_site_view (x : X) (e : Fin n) (a : At Sheet) (sep : e≠rightNeighbor e) :
    view (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) a=
      readLane (Sheet.index a.occurrence) (step x e (site e a.side)).long := by
  obtain ⟨s,sh⟩ := a
  cases s <;> simp [view,site,lane,BStarTrace.lane,Pair.map,AllSizeS1Geometry.step,Ne.symm sep]

/-- Boundary on the complete actual ring mark, not a projection of the
upstream input inferred by packet-byte equality. -/
theorem ring_cross_head {L : Type} (digits : L→BitVec 36)
    {plan : List L} {s : Ledger L} (tag : L) (up : List L)
    (P : OrderedPrefix plan s (tag::up))
    (x : X) (e : Fin n) (sep : e≠rightNeighbor e) (cl : DataClaim) (v : At Sheet) :
    let u := cl.source
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    let atPos := fun (z : X) (a : At Sheet) => readLane (Sheet.index a.occurrence) (z (site e a.side)).long
    cl.destination=some v → cl.kind=.hop →
    cl∈orderedData g (reserved (round g raw).prep) → u≠v →
    retains g v=true → ((atPos x u).gate && (atPos x v).gate)=true →
    (atPos x u).mobile=encode digits (some tag) →
    Compatible digits (s.cells 0) (atPos x v) → (s.cells 0).mobile=none →
    OrderedPrefix plan (s.receiveFirst tag) up ∧
    (atPos (step x e) u).mobile=encode digits none ∧
    Compatible digits ((s.receiveFirst tag).cells 0) (atPos (step x e) v) := by
  dsimp only
  intro dest kind sel ne ret gates fromLabel matched empty
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have G : ((view raw cl.source).gate && (view raw v).gate)=true := by
    rw [old_site_view x e cl.source,old_site_view x e v]
    exact gates
  have A : (view raw cl.source).mobile=encode digits (some tag) := by
    rw [old_site_view x e cl.source]; exact fromLabel
  have M : Compatible digits (s.cells 0) (view raw v) := by
    rw [old_site_view x e v]; exact matched
  obtain ⟨advance,src,dst⟩ := physical_cross_head digits tag up P g raw cl cl.source v
    rfl dest kind sel ne ret G A M empty
  have H := BStarClearanceMobileJoined.joined_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (x e,x (rightNeighbor e))
  have uEq := (new_site_view hp x e cl.source sep).symm.trans (congrFun H cl.source)
  have vEq := (new_site_view hp x e v sep).symm.trans (congrFun H v)
  rw [uEq,vEq]
  exact ⟨advance,src,dst⟩

#print axioms ring_cross_head

open BStarH6Ordinal

/-- A non-seam selected RD-to-RD move across the right center padding
is one adjacent ordinal step toward the retaining boundary. In
particular the OUT slots cannot permute the ghost stream. -/
theorem rd_padding_ordinal (x : X) (hh : ∃ i,oldH6 B x i=true) (e : Fin n)
    (rsv : List (At Sheet)) (cl : DataClaim)
    (chosen : cl∈orderedData (oldPair B x e) rsv)
    (dest : cl.destination=some (BStarLongClaims.L .rd))
    (body : oldH6 B x (rightNeighbor e)=false) :
    cl.source=BStarLongClaims.R .rd ∧
    ordinal (oldH6 B x) hh (site e cl.source.side) =
      ordinal (oldH6 B x) hh e+1 := by
  have Q := right_rd_geometry (oldPair B x e) rsv cl (BStarLongClaims.L .rd) chosen dest rfl
  have source : cl.source=BStarLongClaims.R .rd := by
    have h := Q.2.2.1
    change (if oldH6 B x (rightNeighbor e) then cl.source.occurrence=.rs else cl.source.occurrence=.rd) at h
    simp only [body,Bool.false_eq_true,if_false] at h
    generalize E : cl.source=z at Q h ⊢
    obtain ⟨sd,sh⟩ := z
    have A : sd=.right := Q.1
    have H : sh=.rd := h
    subst sd; subst sh; rfl
  refine ⟨source,?_⟩
  rw [source]
  exact ordinal_body _ hh e body

#print axioms rd_padding_ordinal
end L4.BStarCopyUpstreamTags
