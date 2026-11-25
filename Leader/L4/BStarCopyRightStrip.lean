import Leader.L4.BStarCopyUpstreamTags

namespace L4.BStarCopyRightStrip
open AllSizeProtocol BStarLongClaims BStarH6WordChart BStarLongPackets

/-- Right-copy body moves left on RD even through OUT padding. The only
RD seam ingress comes from the following header's RS. -/
theorem raw_rd_receive (g : Pair LongGeometry) (d : DataClaim)
    (dest : d.destination=some (L .rd)) :
    d∈dataClaims g ↔
      (g.2.axes.h6=false ∧ d=hop (R .rd) (L .rd)) ∨
      (g.2.axes.h6=true ∧ g.2.inside=true ∧ d=hop (R .rs) (L .rd)) := by
  unfold dataClaims
  cases H : g.2.axes.h6 <;> cases I : g.2.inside <;>
    cases J : g.1.inside <;> cases K : ends g.1 <;>
    simp [H,I,J,K,hop,ending] <;> grind [L,R]

/-- On a nonheader site RD has no local terminal: every selected use as
a sender is its unique one-site move left. -/
theorem raw_rd_send_body (g : Pair LongGeometry) (d : DataClaim)
    (hs : g.2.axes.h6=false) (src : d.source=R .rd) :
    d∈dataClaims g ↔ d=hop (R .rd) (L .rd) := by
  cases I : g.1.inside <;> cases J : g.2.inside <;> cases K : ends g.1 <;>
    simp [dataClaims,hs,I,J,K,hop,ending] <;> grind [L,R]

/-- RS receives only within the next sector's INSIDE run, and never
receives across LAST. The last INSIDE RS is the true upstream tail,
regardless of the amount of center padding in the preceding sector. -/
theorem raw_rs_receive (g : Pair LongGeometry) (d : DataClaim)
    (dest : d.destination=some (L .rs)) :
    d∈dataClaims g ↔
      g.2.axes.h6=false ∧ g.1.inside=true ∧ g.2.inside=true ∧
      ends g.1=false ∧ d=hop (R .rs) (L .rs) := by
  unfold dataClaims
  cases H : g.2.axes.h6 <;> cases I : g.2.inside <;>
    cases J : g.1.inside <;> cases K : ends g.1 <;>
    simp [H,I,J,K,hop,ending] <;> grind [L,R]


/-- The header's RS turns onto RD across the seam; other RS positions
continuously move left on RS. There is no destructive RS end row. -/
theorem raw_rs_send (g : Pair LongGeometry) (d : DataClaim) (src : d.source=R .rs) :
    d∈dataClaims g ↔
      (g.2.axes.h6=true ∧ g.2.inside=true ∧ d=hop (R .rs) (L .rd)) ∨
      (g.2.axes.h6=false ∧ g.1.inside=true ∧ g.2.inside=true ∧
        ends g.1=false ∧ d=hop (R .rs) (L .rs)) := by
  unfold dataClaims
  cases H : g.2.axes.h6 <;> cases I : g.2.inside <;>
    cases J : g.1.inside <;> cases K : ends g.1 <;>
    simp [H,I,J,K,hop,ending] <;> grind [L,R]

theorem no_right_receive (g : Pair LongGeometry) (d : DataClaim)
    (chosen : d∈dataClaims g) :
    d.destination≠some (R .rd) ∧ d.destination≠some (R .rs) := by
  unfold dataClaims at chosen
  cases H : g.2.axes.h6 <;> cases I : g.2.inside <;>
    cases J : g.1.inside <;> cases K : ends g.1 <;>
    simp [H,I,J,K,hop,ending] at chosen <;>
    grind [L,R,hop,ending]

theorem no_left_send (g : Pair LongGeometry) (d : DataClaim)
    (chosen : d∈dataClaims g) : d.source≠L .rd ∧ d.source≠L .rs := by
  unfold dataClaims at chosen
  cases H : g.2.axes.h6 <;> cases I : g.2.inside <;>
    cases J : g.1.inside <;> cases K : ends g.1 <;>
    simp [H,I,J,K,hop,ending] at chosen <;>
    grind [L,R,hop,ending]

/-- Address measured from the FIRST destination digit of this right
copy, increasing upstream. Consecutive addresses may wrap. -/
def addr {n : Nat} (base : Fin n) (i : Nat) : Fin n :=
  ⟨(base.val+i)%n, Nat.mod_lt _ (Nat.zero_lt_of_lt base.isLt)⟩

theorem addr_next {n : Nat} (base : Fin n) (i : Nat) :
    addr base (i+1)=rightNeighbor (addr base i) := by
  apply Fin.ext
  simp only [addr, rightNeighbor]
  rw [Nat.mod_add_mod, Nat.add_assoc]

theorem addr_inj {n : Nat} (base : Fin n) {i j : Nat}
    (hi : i<n) (hj : j<n) (h : addr base i=addr base j) : i=j := by
  have h' := congrArg Fin.val h
  change (base.val+i)%n=(base.val+j)%n at h'
  have A := Nat.mod_add_div (base.val+i) n
  have B := Nat.mod_add_div (base.val+j) n
  have ni : (base.val+i)/n<2 := by
    apply (Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt base.isLt)).2
    have := base.isLt
    omega
  have nj : (base.val+j)/n<2 := by
    apply (Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt base.isLt)).2
    have := base.isLt
    omega
  generalize (base.val+i)/n=qi at A ni
  generalize (base.val+j)/n=qj at B nj
  have U : qi=0 ∨ qi=1 := by omega
  have V : qj=0 ∨ qj=1 := by omega
  rcases U with U|U <;> rcases V with V|V <;> rw [U] at A <;> rw [V] at B <;> omega

def rail (seam i : Nat) : Sheet := if i<seam then .rd else .rs

/-- Snapshot geometry of the physical right stream. Coordinate 0 is
the final INSIDE RD of destination owner. RD coordinates 1..seam−1
are the entire OUT run. Coordinate seam is the next header's inside
RS, then the next owner's full INSIDE RS through its LAST. The head
may be immediately before the seam. `tail` is an inclusive index. -/
structure Strip {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x : Fin n→LargeSite a) (base : Fin n) (seam tail : Nat) : Prop where
  seam_pos : 0<seam
  seam_le_tail : seam≤tail
  tail_lt : tail<n
  head_in : (longGeometry b (x (addr base 0))).inside=true
  rd_noheader : ∀ i<seam, oldH6 b x (addr base i)=false
  pads_out : ∀ i, 0<i → i<seam → (longGeometry b (x (addr base i))).inside=false
  rs_header : oldH6 b x (addr base seam)=true
  rs_nonheader : ∀ i, seam<i → i≤tail → oldH6 b x (addr base i)=false
  rs_in : ∀ i, seam≤i → i≤tail → (longGeometry b (x (addr base i))).inside=true
  rs_nonlast : ∀ i, seam≤i → i<tail → ends (longGeometry b (x (addr base i)))=false
  tail_last : ends (longGeometry b (x (addr base tail)))=true

/-- At each non-tail position there is exactly one raw incoming
claim on the edge joining it to the next strip position. This
statement is before prep reservations; those may suppress a move
but cannot change direction, duplicate, or skip a position. -/
theorem raw_incoming {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n→LargeSite a} {base : Fin n} {seam tail : Nat}
    (C : Strip b x base seam tail) (i : Nat) (it : i<tail) (d : DataClaim)
    (D : d.destination=some (L (rail seam i))) :
    d∈dataClaims (oldPair b x (addr base i)) ↔
      d=hop (R (rail seam (i+1))) (L (rail seam i)) := by
  let g := oldPair b x (addr base i)
  change d∈dataClaims g ↔ _
  have right : rightNeighbor (addr base i)=addr base (i+1) := (addr_next base i).symm
  by_cases pad : i+1<seam
  · have H : g.2.axes.h6=false := by
      change oldH6 b x (rightNeighbor (addr base i))=false
      rw [right]; exact C.rd_noheader _ pad
    have q : i<seam := by omega
    simp only [rail,if_pos q,if_pos pad] at D ⊢
    rw [raw_rd_receive g d D,H]
    simp
  · by_cases atSeam : i+1=seam
    · have H : g.2.axes.h6=true := by
        change oldH6 b x (rightNeighbor (addr base i))=true
        rw [right,atSeam]; exact C.rs_header
      have I : g.2.inside=true := by
        change (longGeometry b (x (rightNeighbor (addr base i)))).inside=true
        rw [right,atSeam]; exact C.rs_in _ (by omega) C.seam_le_tail
      have q : i<seam := by omega
      simp only [rail,if_pos q,if_neg pad] at D ⊢
      rw [raw_rd_receive g d D,H,I]
      simp
    · have H : g.2.axes.h6=false := by
        change oldH6 b x (rightNeighbor (addr base i))=false
        rw [right]; exact C.rs_nonheader _ (by omega) (by omega)
      have I : g.2.inside=true := by
        change (longGeometry b (x (rightNeighbor (addr base i)))).inside=true
        rw [right]; exact C.rs_in _ (by omega) (by omega)
      have J : g.1.inside=true := C.rs_in _ (by omega) (by omega)
      have K : ends g.1=false := C.rs_nonlast _ (by omega) it
      have q : ¬ i<seam := by omega
      simp only [rail,if_neg q,if_neg pad] at D ⊢
      rw [raw_rs_receive g d D,H,I,J,K]
      simp

/-- No exterior incoming data row at the tail. This exclusion checks
LAST's real handling, and is independent of reservations or payload. -/
theorem tail_no_ingress {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n→LargeSite a} {base : Fin n} {seam tail : Nat}
    (C : Strip b x base seam tail) (d : DataClaim)
    (M : d∈dataClaims (oldPair b x (addr base tail))) :
    d.destination≠some (L (rail seam tail)) := by
  intro D
  have q : ¬tail<seam := by have := C.seam_le_tail; omega
  simp only [rail,if_neg q] at D
  have H := (raw_rs_receive _ _ D).mp M
  have T : ends (oldPair b x (addr base tail)).1=true := C.tail_last
  rw [T] at H
  exact Bool.noConfusion H.2.2.2.1

#print axioms raw_incoming
#print axioms tail_no_ingress

open BStarH6Ordinal

theorem address_ordinal_run {n : Nat} (base : Fin n)
    (h : Fin n→Bool) (hh : ∃ z,h z=true)
    (start len : Nat)
    (body : ∀ j, 0<j → j≤len → h (addr base (start+j))=false) :
    ∀ j≤len, ordinal h hh (addr base (start+j)) =
      ordinal h hh (addr base start)+j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    intro hj
    have H := body (j+1) (by omega) hj
    rw [show start+(j+1)=(start+j)+1 by omega,addr_next,
      ordinal_body h hh _ (by rwa [←addr_next,Nat.add_assoc]),ih (by omega)]
    omega

/-- Construct the strip from a real settled ordinal layout. The two
header premises say that `seam` is the next header and its digit run
reaches its actual last position before any further header. No
packet fields, tags, or ghost writer assumptions enter this chart. -/
theorem of_ordinal_layout {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n→LargeSite a} (base : Fin n) (seam r : Nat)
    (hr : 1<r) (hs : 0<seam) (bound : seam+r-1<n)
    (hh : ∃ z,oldH6 b x z=true)
    (first : oldOrdinal b x hh (addr base 0)=r-1)
    (noPadHead : ∀ i, 0<i → i<seam → oldH6 b x (addr base i)=false)
    (nextHead : oldH6 b x (addr base seam)=true)
    (noNewHead : ∀ j, 0<j → j<r → oldH6 b x (addr base (seam+j))=false)
    (layout : ∀ z, (longGeometry b (x z)).inside=decide (oldOrdinal b x hh z<r) ∧
      (longGeometry b (x z)).last=decide (oldOrdinal b x hh z+1=r)) :
    Strip b x base seam (seam+r-1) := by
  have A : ∀ i<seam, oldOrdinal b x hh (addr base i)=r-1+i := by
    intro i hi
    have R := address_ordinal_run base (oldH6 b x) hh 0 (seam-1)
      (by intro j H J; simpa only [Nat.zero_add] using noPadHead j H (by omega))
      i (by omega)
    change oldOrdinal b x hh (addr base (0+i)) = oldOrdinal b x hh (addr base 0)+i at R
    simpa only [Nat.zero_add, first] using R
  have R : ∀ j<r, oldOrdinal b x hh (addr base (seam+j))=j := by
    intro j hj
    have F : oldOrdinal b x hh (addr base seam)=0 :=
      (ordinal_zero _ hh _).mpr nextHead
    have G := address_ordinal_run base (oldH6 b x) hh seam (r-1)
      (fun j H J => noNewHead j H (by omega)) j (by omega)
    change oldOrdinal b x hh (addr base (seam+j)) = oldOrdinal b x hh (addr base seam)+j at G
    simpa only [F,Nat.zero_add] using G
  have V : ∀ i, seam≤i → i≤seam+r-1 →
      oldOrdinal b x hh (addr base i)=i-seam := by
    intro i hs ht
    have E : seam+(i-seam)=i := by omega
    simpa only [E] using R (i-seam) (by omega)
  refine ⟨hs, by omega, bound, ?_, ?_, ?_, nextHead, ?_, ?_, ?_, ?_⟩
  · rw [(layout _).1,first]
    exact decide_eq_true (by omega)
  · intro i hi
    by_cases z : i=0
    · subst i
      cases H : oldH6 b x (addr base 0)
      · rfl
      · have K : oldOrdinal b x hh (addr base 0)=0 := (ordinal_zero _ hh _).mpr H
        omega
    · exact noPadHead i (by omega) hi
  · intro i pos lt
    rw [(layout _).1,A _ lt]
    exact decide_eq_false (by omega)
  · intro i hs ht
    have E : seam+(i-seam)=i := by omega
    simpa only [E] using noNewHead (i-seam) (by omega) (by omega)
  · intro i hs ht
    rw [(layout _).1,V i hs ht]
    exact decide_eq_true (by omega)
  · intro i hs ht
    unfold ends
    rw [(layout _).2,V i hs (by omega)]
    simp [show ¬ i - seam + 1 = r by omega]
  · unfold ends
    rw [(layout _).1,(layout _).2,V _ (by omega) (by omega)]
    simp [show seam + r - 1 - seam < r by omega,show seam + r - 1 - seam + 1 = r by omega]

#print axioms of_ordinal_layout

theorem retains_iff_head {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n→LargeSite a} {base : Fin n} {seam tail : Nat}
    (C : Strip b x base seam tail) (i : Nat) :
    retains (oldPair b x (addr base i)) (L (rail seam i)) = decide (i=0) := by
  by_cases h : i=0
  · subst i
    simp [rail,C.seam_pos,retains,L,show
      (oldPair b x (addr base 0)).1.inside=true from C.head_in]
  · by_cases j : i<seam
    · simp [rail,j,retains,L,h,show (oldPair b x (addr base i)).1.inside=false
        from C.pads_out _ (by omega) j]
    · simp [rail,j,retains,L,h]

theorem selected_adjacent {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n→LargeSite a} {base : Fin n} {seam tail : Nat}
    (C : Strip b x base seam tail) (i : Nat) (it : i<tail)
    (rsv : List (At Sheet)) (d : DataClaim)
    (M : d∈orderedData (oldPair b x (addr base i)) rsv)
    (D : d.destination=some (L (rail seam i))) :
    d=hop (R (rail seam (i+1))) (L (rail seam i)) :=
  (raw_incoming C i it d D).mp (BStarLongFenceTopology.selected_data_raw _ _ _ M)

open BStarTrace BStarLongWork BStarLongCommandData BStarLongPrep BStarCopyUpstreamTags BStarCopyMarkedLedger BStarCopyFIFO

/-- A selected healthy internal move in the actual joined row (including
RS→RD at the seam) moves exactly the old tracked byte to the frontward
adjacent position. At position zero use the retaining head theorem
instead. Arguments are old slot fingerprints, not equality-based tag
reconstruction from the new packet. -/
theorem joined_strip_hop {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
    {Label : Type} (digits : Label→BitVec 36) (tag : Label)
    (x : Fin n→LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (base : Fin n) (seam tail i : Nat) (pos : 0<i) (it : i<tail)
    (C : Strip (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp) x base seam tail)
    (d : DataClaim) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let edge := addr base i
    let xx := (x edge,x (rightNeighbor edge))
    let raw := Pair.map LargeSite.long xx
    let g := oldPair b x edge
    let u := R (rail seam (i+1))
    let v := L (rail seam i)
    d∈orderedData g (reserved (round g raw).prep) →
    d.destination=some v →
    ((view raw u).gate && (view raw v).gate)=true →
    (view raw u).mobile=encode digits (some tag) →
    (view raw v).mobile=encode digits none →
    let out := view (Pair.map LargeSite.long (largePair b xx))
    (out u).mobile=encode digits none ∧
    (out v).mobile=encode digits (some tag) ∧
    (out v).retained=(view raw v).retained := by
  dsimp only
  intro M D G U V
  have E := selected_adjacent C i it _ d M D
  subst d
  apply nonretaining_tag_joined hp digits tag _ _ _ _ rfl rfl rfl M
  · intro H
    have T := congrArg At.side H
    contradiction
  · change retains (oldPair _ x (addr base i)) (L (rail seam i)) = false
    rw [retains_iff_head C i]
    exact decide_eq_false (by omega)
  · exact G
  · exact U
  · exact V

#print axioms joined_strip_hop
end L4.BStarCopyRightStrip
