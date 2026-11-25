import Leader.L4.BStarCopyRightStrip
import Leader.L4.BStarFenceReceiverChart

namespace L4.BStarCopyLeftStrip
open AllSizeProtocol BStarLongClaims BStarH6WordChart BStarLongPackets
open BStarH6Ordinal BStarAcquireAnchors BStarAcquireLiteralChain BStarLongFiberOwner
open BStarCopyRightStrip (addr addr_next address_ordinal_run)

/-- The forward-travelling LS rail extends through padding. Its only
splice is LS→LD into the next INSIDE H6 header. LD does not traverse
the destination sector's padding. -/
theorem raw_ld_receive (g : Pair LongGeometry) (d : DataClaim)
    (dest : d.destination=some (R .ld)) :
    d∈dataClaims g ↔
      (g.2.axes.h6=true ∧ g.2.inside=true ∧ d=hop (L .ls) (R .ld)) ∨
      (g.2.axes.h6=false ∧ g.1.inside=true ∧ g.2.inside=true ∧
        ends g.1=false ∧ d=hop (L .ld) (R .ld)) := by
  unfold dataClaims
  cases H : g.2.axes.h6 <;> cases I : g.2.inside <;>
    cases J : g.1.inside <;> cases K : ends g.1 <;>
    simp [H,I,J,K,hop,ending] <;> grind [L,R]

theorem raw_ls_receive (g : Pair LongGeometry) (d : DataClaim)
    (dest : d.destination=some (R .ls)) :
    d∈dataClaims g ↔ g.2.axes.h6=false ∧ d=hop (L .ls) (R .ls) := by
  unfold dataClaims
  cases H : g.2.axes.h6 <;> cases I : g.2.inside <;>
    cases J : g.1.inside <;> cases K : ends g.1 <;>
    simp [H,I,J,K,hop,ending] <;> grind [L,R]

theorem raw_ld_terminal (g : Pair LongGeometry) (d : DataClaim)
    (last : ends g.1=true) (src : d.source=L .ld) :
    d∈dataClaims g ↔ d=ending (L .ld) := by
  unfold dataClaims
  cases H : g.2.axes.h6 <;> cases I : g.2.inside <;>
    cases J : g.1.inside <;>
    simp [H,I,J,last,hop,ending] <;> grind [L,R]

theorem no_left_receive (g : Pair LongGeometry) (d : DataClaim) (M : d∈dataClaims g) :
    d.destination≠some (L .ls) ∧ d.destination≠some (L .ld) := by
  unfold dataClaims at M
  cases H : g.2.axes.h6 <;> cases I : g.2.inside <;>
    cases J : g.1.inside <;> cases K : ends g.1 <;>
    simp [H,I,J,K,hop,ending] at M <;> grind [L,R]

def rail (seam i : Nat) : Sheet := if i<seam then .ls else .ld

def position {n : Nat} (base : Fin n) (seam i : Nat) : Fin n × Sheet :=
  (addr base i,rail seam i)

/-- Travel order starts at the source LS header, then the entire LS
word (including its padding), then exactly the destination's inside LD.
Wrap can revisit a site, but not the same physical sheet address. -/
structure Strip {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x : Fin n → LargeSite a) (base : Fin n) (seam width : Nat) : Prop where
  seam_pos : 0<seam
  seam_le : seam≤n
  width_pos : 0<width
  width_le : width≤n
  source_header : oldH6 b x base=true
  ls_body : ∀ i,0<i → i<seam → oldH6 b x (addr base i)=false
  dest_header : oldH6 b x (addr base seam)=true
  ld_body : ∀ i,seam<i → i<seam+width → oldH6 b x (addr base i)=false
  ld_in : ∀ i,seam≤i → i<seam+width → (longGeometry b (x (addr base i))).inside=true
  ld_before_last : ∀ i,seam≤i → i+1<seam+width → ends (longGeometry b (x (addr base i)))=false
  last : ends (longGeometry b (x (addr base (seam+width-1))))=true

theorem raw_hop {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n → LargeSite a} {base : Fin n} {seam width : Nat}
    (C : Strip b x base seam width) (i : Nat) (hi : i+1<seam+width) (d : DataClaim)
    (D : d.destination=some (R (rail seam (i+1)))) :
    d∈dataClaims (oldPair b x (addr base i)) ↔
      d=hop (L (rail seam i)) (R (rail seam (i+1))) := by
  let g := oldPair b x (addr base i)
  change d∈dataClaims g ↔ _
  have right : rightNeighbor (addr base i)=addr base (i+1) := (addr_next base i).symm
  by_cases ls : i+1<seam
  · have H : g.2.axes.h6=false := by
      change oldH6 b x (rightNeighbor (addr base i))=false
      rw [right]; exact C.ls_body _ (by omega) ls
    have a0 : i<seam := by omega
    simp only [rail,if_pos ls,if_pos a0] at D ⊢
    rw [raw_ls_receive _ _ D,H]
    simp
  · have lin : g.2.inside=true := by
      change (longGeometry b (x (rightNeighbor (addr base i)))).inside=true
      rw [right]; exact C.ld_in _ (by omega) hi
    by_cases h : i+1=seam
    · have H : g.2.axes.h6=true := by
        change oldH6 b x (rightNeighbor (addr base i))=true
        rw [right,h]; exact C.dest_header
      have a0 : i<seam := by omega
      simp only [rail,if_neg ls,if_pos a0] at D ⊢
      rw [raw_ld_receive _ _ D,H,lin]
      simp
    · have H : g.2.axes.h6=false := by
        change oldH6 b x (rightNeighbor (addr base i))=false
        rw [right]; exact C.ld_body _ (by omega) hi
      have A : seam≤i := by omega
      have I : g.1.inside=true := C.ld_in _ A (by omega)
      have K : ends g.1=false := C.ld_before_last _ A hi
      simp only [rail,if_neg ls,if_neg (Nat.not_lt_of_ge A)] at D ⊢
      rw [raw_ld_receive _ _ D,H,I,lin,K]
      simp

theorem selected_hop {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n → LargeSite a} {base : Fin n} {seam width : Nat}
    (C : Strip b x base seam width) (i : Nat) (hi : i+1<seam+width)
    (rsv : List (At Sheet)) (d : DataClaim)
    (M : d∈orderedData (oldPair b x (addr base i)) rsv)
    (D : d.destination=some (R (rail seam (i+1)))) :
    d=hop (L (rail seam i)) (R (rail seam (i+1))) :=
  (raw_hop C i hi d D).mp (BStarLongFenceTopology.selected_data_raw _ _ _ M)

theorem retains_at_hop {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n → LargeSite a} {base : Fin n} {seam width : Nat}
    (C : Strip b x base seam width) (i : Nat) (hi : i+1<seam+width) :
    retains (oldPair b x (addr base i)) (R (rail seam (i+1))) = decide (seam≤i+1) := by
  by_cases W : seam≤i+1
  · have I : (oldPair b x (addr base i)).2.inside=true := by
      change (longGeometry b (x (rightNeighbor (addr base i)))).inside=true
      rw [←addr_next]
      exact C.ld_in _ W hi
    simp [retains,R,rail,Nat.not_lt_of_ge W,I,W]
  · simp [retains,R,rail,Nat.lt_of_not_ge W,W]

open BStarFenceReceiverChart (digitFrom)
open BStarTrace BStarLongWork BStarAcquireVisitOrder BStarResetChartTouch

private theorem addr_zero {n : Nat} (base : Fin n) : addr base 0=base :=
  Fin.ext (Nat.mod_eq_of_lt base.isLt)

theorem addr_from {n : Nat} (base : Fin n) (seam d : Nat) :
    addr base (seam+d)=digitFrom (addr base seam) d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [show seam+(d+1)=seam+d+1 by omega,addr_next,ih]
    rfl

private theorem next_header {n : Nat} (h : Fin n → Bool) (base : Fin n)
    (H : h base=true) :
    ∃ seam, 0<seam ∧ seam≤n ∧ h (addr base seam)=true ∧
      ∀ i,0<i → i<seam → h (addr base i)=false := by
  have N : h (addr base n)=true := by
    have E : addr base n=base := by
      apply Fin.ext
      change (base.val+n)%n=base.val
      rw [Nat.add_mod_right,Nat.mod_eq_of_lt base.isLt]
    rwa [E]
  have pick (d : Nat) (pos : 0<d) (D : h (addr base d)=true) :
      ∃ seam,0<seam ∧ seam≤d ∧ h (addr base seam)=true ∧
        ∀ i,0<i → i<seam → h (addr base i)=false := by
    induction d using Nat.strongRecOn with
    | ind d ih =>
      by_cases any : ∃ i,0<i ∧ i<d ∧ h (addr base i)=true
      · obtain ⟨i,I,J,P⟩ := any
        obtain ⟨s,A,B,C,E⟩ := ih i J I P
        exact ⟨s,A,by omega,C,E⟩
      · refine ⟨d,pos,Nat.le_refl _,D,?_⟩
        intro i I J
        cases P : h (addr base i)
        · rfl
        · exact (any ⟨i,I,J,P⟩).elim
  exact pick n (by have := base.isLt; omega) N

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

/-- Actual settled chart, not externally supplied seam: the first
next H6 is the chart's K10. COPY's last LD is consequently the
same ordinal receiver selected by the accepted FENCE lemma. -/
theorem of_chart {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) {width : Nat} (hw : 0<width)
    (flags : ∀ i, (longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<width) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=width))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → width≤oldOrdinal B base hh j+1) :
    let root := (S.getD 0 fall).1
    let dest := (S.getD len fall).1
    ∃ seam, Strip B base root seam width ∧ addr root seam=dest ∧
      addr root (seam+width-1)=digitFrom dest (width-1) ∧
      ∀ d, d<width → oldOrdinal B base hh (addr root (seam+d))=d := by
  dsimp only
  let h := oldH6 B base
  let root := (S.getD 0 fall).1
  obtain ⟨H,O,_⟩ := endpoint_spec h hh o 0
  rw [←C.root] at H O
  change h root=true at H
  change commandOwner h root 0=o.val at O
  obtain ⟨seam,hs,hn,E,between⟩ := next_header h root H
  have W : ∀ j<seam, word h (addr root j)=word h root := by
    intro j
    induction j with
    | zero => intro _; rw [addr_zero]
    | succ j ih =>
      intro J
      have T := right_word h (addr root j)
      rw [←addr_next,between (j+1) (by omega) J] at T
      simp only [Bool.toNat_false,Int.natCast_zero,Int.add_zero] at T
      obtain ⟨a,b⟩ := word_range h (addr root j) hh
      rw [Int.emod_eq_of_lt a b] at T
      exact T.trans (ih (by omega))
  have N : word h (addr root seam)=(word h root+1)%(total h : Int) := by
    have T := right_word h (addr root (seam-1))
    have Q : seam-1+1=seam := by omega
    rw [←addr_next,Q,E,W (seam-1) (by omega)] at T
    exact T
  have D : commandOwner h (addr root seam) 10=o.val := by
    change ((word h (addr root seam)-1)%(total h : Int))=o.val
    change (word h root-0)%(total h : Int)=o.val at O
    rw [N,Int.emod_sub_emod,show word h root+1-1=word h root by omega]
    simpa only [Int.sub_zero] using O
  have dest := (endpoint_spec h hh o 10).2.2 _ E D
  have loc : addr root seam=(S.getD len fall).1 := by
    rw [C.terminal]
    exact congrArg Prod.fst dest
  have ord (d : Nat) (hd : d<width) : oldOrdinal B base hh (addr root (seam+d))=d := by
    rw [addr_from]
    exact (BStarFenceReceiverChart.digit_from hp E width notShort d hd).1
  have wn : width≤n := by
    have T := (ordinal_spec h hh (addr root (seam+(width-1)))).1
    change oldOrdinal B base hh (addr root (seam+(width-1)))<n at T
    rw [ord _ (by omega)] at T
    omega
  have end_eq : addr root (seam+width-1)=digitFrom (S.getD len fall).1 (width-1) := by
    rw [show seam+width-1=seam+(width-1) by omega,addr_from,loc]
  refine ⟨seam,⟨hs,hn,hw,wn,H,between,E,?_,?_,?_,?_⟩,loc,end_eq,ord⟩
  · intro i lo hi
    have A : oldOrdinal B base hh (addr root i)=i-seam := by
      have T := ord (i-seam) (by omega)
      rwa [show seam+(i-seam)=i by omega] at T
    cases Z : oldH6 B base (addr root i)
    · rfl
    · have K : oldOrdinal B base hh (addr root i)=0 := (ordinal_zero _ hh _).mpr Z
      omega
  · intro i lo hi
    have T := ord (i-seam) (by omega)
    rw [show seam+(i-seam)=i by omega] at T
    rw [(flags _).1,T]
    exact decide_eq_true (by omega)
  · intro i lo hi
    have T := ord (i-seam) (by omega)
    rw [show seam+(i-seam)=i by omega] at T
    unfold ends
    rw [(flags _).2,T]
    simp [show i-seam+1≠width by omega]
  · have T := ord (width-1) (by omega)
    rw [show seam+(width-1)=seam+width-1 by omega] at T
    unfold ends
    rw [(flags _).1,(flags _).2,T]
    simp [show width-1<width by omega,show width-1+1=width by omega]

/-- A wrap can revisit a physical site only on a different lane. -/
theorem position_injective {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n → LargeSite a} {base : Fin n} {seam width : Nat}
    (C : Strip b x base seam width) {i j : Nat} (I : i<seam+width) (J : j<seam+width)
    (E : position base seam i=position base seam j) : i=j := by
  have siteEq : addr base i=addr base j := congrArg Prod.fst E
  have laneEq : rail seam i=rail seam j := congrArg Prod.snd E
  by_cases hi : i<seam <;> by_cases hj : j<seam
  · exact BStarCopyRightStrip.addr_inj base
      (Nat.lt_of_lt_of_le hi C.seam_le) (Nat.lt_of_lt_of_le hj C.seam_le) siteEq
  · simp [rail,hi,hj] at laneEq
  · simp [rail,hi,hj] at laneEq
  · let d := addr base seam
    have A (k : Nat) : addr base (seam+k)=addr d k := by
      exact (addr_from base seam k).trans (by simpa only [addr_zero,Nat.zero_add] using (addr_from d 0 k).symm)
    have si : seam+(i-seam)=i := by omega
    have sj : seam+(j-seam)=j := by omega
    have Q : addr d (i-seam)=addr d (j-seam) := by
      rw [←A,←A,si,sj,siteEq]
    have wn := C.width_le
    have eq := BStarCopyRightStrip.addr_inj d (by omega : i-seam<n) (by omega : j-seam<n) Q
    omega

/-- No exterior hop can insert a mobile into source LS at the first
header. Prep/injection on that lane is a separate selected mechanism. -/
theorem source_no_ingress {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n → LargeSite a} {base : Fin n} {seam width : Nat}
    (C : Strip b x base seam width) (e : Fin n) (rsv : List (At Sheet))
    (d : DataClaim) (M : d∈orderedData (oldPair b x e) rsv) (s : Side)
    (A : site e s=base) : d.destination≠some ⟨s,.ls⟩ := by
  intro D
  have raw := BStarLongFenceTopology.selected_data_raw _ _ _ M
  cases s with
  | left => exact (no_left_receive _ _ raw).1 D
  | right =>
    have T := (raw_ls_receive _ _ D).mp raw
    change rightNeighbor e=base at A
    have H : (oldPair b x e).2.axes.h6=true := by change oldH6 b x (rightNeighbor e)=true; rw [A]; exact C.source_header
    rw [H] at T
    exact Bool.noConfusion T.1

theorem selected_tail {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n → LargeSite a} {base : Fin n} {seam width : Nat}
    (C : Strip b x base seam width) (rsv : List (At Sheet)) (d : DataClaim)
    (M : d∈orderedData (oldPair b x (addr base (seam+width-1))) rsv)
    (D : d.source=L .ld) :
    d=ending (L .ld) :=
  (raw_ld_terminal _ _ C.last D).mp (BStarLongFenceTopology.selected_data_raw _ _ _ M)

#print axioms position_injective
#print axioms source_no_ingress
#print axioms selected_tail
#print axioms of_chart
#print axioms raw_hop
#print axioms retains_at_hop
end L4.BStarCopyLeftStrip
