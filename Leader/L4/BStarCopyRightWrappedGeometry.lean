import Leader.L4.BStarCopyRightActualWitness
import Leader.L4.BStarCopyLeftStrip

namespace L4.BStarCopyRightWrappedGeometry
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongCommand
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetChartTouch BStarCopyRightStrip BStarCopyRightRetained
open BStarFenceReceiverChart BStarClearanceDataChart
open BStarLongFiberOwner BStarAcquireAnchors

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

private theorem zero_addr {n : Nat} (a : Fin n) : addr a 0=a :=
  Fin.ext (Nat.mod_eq_of_lt a.isLt)

private theorem add_addr {n : Nat} (a : Fin n) (i j : Nat) :
    addr (addr a i) j=addr a (i+j) := by
  calc
    addr (addr a i) j = digitFrom (addr a i) j := by
      have E := BStarCopyLeftStrip.addr_from (addr a i) 0 j
      rw [Nat.zero_add,zero_addr] at E
      exact E
    _ = addr a (i+j) := (BStarCopyLeftStrip.addr_from a i j).symm

structure WrappedStrip {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x : Fin n→LargeSite a) (base : Fin n) (seam tail : Nat) : Prop where
  seam_pos : 0<seam
  seam_le_tail : seam≤tail
  tail_le : tail≤n
  head_in : (longGeometry b (x (addr base 0))).inside=true
  rd_noheader : ∀ i, 0<i → i<seam → oldH6 b x (addr base i)=false
  pads_out : ∀ i, 0<i → i<seam → (longGeometry b (x (addr base i))).inside=false
  rs_header : oldH6 b x (addr base seam)=true
  rs_nonheader : ∀ i, seam<i → i≤tail → oldH6 b x (addr base i)=false
  rs_in : ∀ i, seam≤i → i≤tail → (longGeometry b (x (addr base i))).inside=true
  rs_nonlast : ∀ i, seam≤i → i<tail → ends (longGeometry b (x (addr base i)))=false
  tail_last : ends (longGeometry b (x (addr base tail)))=true

private theorem first_next {n : Nat} (h : Fin n→Bool) (root : Fin n)
    (H0 : h root=true) :
    ∃ d,0<d ∧ d≤n ∧ h (addr root d)=true ∧
      ∀ j,0<j → j<d → h (addr root j)=false := by
  have zpos : 0<n := Nat.zero_lt_of_lt root.isLt
  have A : addr root n=root := by
    apply Fin.ext
    change (root.val+n)%n=root.val
    rw [Nat.add_mod_right,Nat.mod_eq_of_lt root.isLt]
  have H (d : Nat) (pos : 0<d) (D : h (addr root d)=true) :
      ∃ next,0<next ∧ next≤d ∧ h (addr root next)=true ∧
        ∀ j,0<j → j<next → h (addr root j)=false := by
    induction d using Nat.strongRecOn with
    | ind d ih =>
      by_cases any : ∃ j,0<j ∧ j<d ∧ h (addr root j)=true
      · obtain ⟨j,P,L,R⟩ := any
        obtain ⟨next,A,Q,S,T⟩ := ih j L P R
        exact ⟨next,A,by omega,S,T⟩
      · refine ⟨d,pos,Nat.le_refl _,D,?_⟩
        intro j P L
        cases K : h (addr root j)
        · rfl
        · exact (any ⟨j,P,L,K⟩).elim
  exact H n zpos (A.symm ▸ H0)

theorem wrapped_raw_incoming {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n→LargeSite a} {base : Fin n} {seam tail : Nat}
    (C : WrappedStrip b x base seam tail) (i : Nat) (it : i<tail) (d : DataClaim)
    (D : d.destination=some (L (rail seam i))) :
    d∈dataClaims (oldPair b x (addr base i)) ↔
      d=hop (R (rail seam (i+1))) (L (rail seam i)) := by
  let g := oldPair b x (addr base i)
  change d∈dataClaims g ↔ _
  have right : rightNeighbor (addr base i)=addr base (i+1) := (addr_next base i).symm
  by_cases pad : i+1<seam
  · have H : g.2.axes.h6=false := by
      change oldH6 b x (rightNeighbor (addr base i))=false
      rw [right]; exact C.rd_noheader _ (by omega) pad
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
theorem wrapped_tail_no_ingress {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n→LargeSite a} {base : Fin n} {seam tail : Nat}
    (C : WrappedStrip b x base seam tail) (d : DataClaim)
    (M : d∈dataClaims (oldPair b x (addr base tail))) :
    d.destination≠some (L (rail seam tail)) := by
  intro D
  have q : ¬tail<seam := by have := C.seam_le_tail; omega
  simp only [rail,if_neg q] at D
  have H := (raw_rs_receive _ _ D).mp M
  have T : ends (oldPair b x (addr base tail)).1=true := C.tail_last
  rw [T] at H
  exact Bool.noConfusion H.2.2.2.1

/-- Actual right geometry without either false site-injectivity
premise: a full wrap is retained as two distinct typed occurrences,
and coordinate zero may be the H6 header when width is one. -/
theorem wrapped_of_chart {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) {width : Nat} (hw : 0<width)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<width) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=width))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → width≤oldOrdinal B base hh i+1)
    :
    let root := (S.getD len fall).1
    ∃ a seam tail, Dest B base root width ∧ WrappedStrip B base a seam tail ∧
      addr a 0=addr root (width-1) ∧ tail+1=seam+width ∧
      dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val := by
  dsimp only
  let root := (S.getD len fall).1
  have H := (endpoint_spec (oldH6 B base) hh o 10)
  rw [←chart.terminal] at H
  have rootH : oldH6 B base root=true := H.1
  have rootO : commandOwner (oldH6 B base) root 10=o.val := H.2.1
  obtain ⟨d,dp,dn,next,mid⟩ := first_next (oldH6 B base) root rootH
  have dist : ∀ j<d,oldOrdinal B base hh (addr root j)=j := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [zero_addr]
      exact (ordinal_zero _ hh root).mpr rootH
    | succ j ih =>
      intro L
      have J := ordinal_body (oldH6 B base) hh (addr root j) (by
        rw [←addr_next]
        exact mid (j+1) (by omega) L)
      change oldOrdinal B base hh (rightNeighbor (addr root j))=oldOrdinal B base hh (addr root j)+1 at J
      rw [←addr_next,ih (by omega)] at J
      exact J
  have dw : width≤d := by
    have N : oldH6 B base (rightNeighbor (addr root (d-1)))=true := by
      rw [←addr_next,show d-1+1=d by omega]
      exact next
    have Q := notShort _ N
    rw [dist _ (by omega)] at Q
    omega
  let a := addr root (width-1)
  let seam := d-(width-1)
  have se : width-1+seam=d := by dsimp [seam]; omega
  have sp : 0<seam := by dsimp [seam]; omega
  have sr : addr a seam=addr root d := by rw [show a=addr root (width-1) from rfl,add_addr,se]
  have after (i : Nat) (L : seam≤i) (U : i≤d) :
      oldOrdinal B base hh (addr a i)=i-seam := by
    have R := digit_from hp next width notShort (i-seam) (by omega)
    rw [←sr,←BStarCopyLeftStrip.addr_from,show seam+(i-seam)=i by omega] at R
    exact R.1
  have before (i : Nat) (L : i<seam) :
      oldOrdinal B base hh (addr a i)=width-1+i := by
    rw [show a=addr root (width-1) from rfl,add_addr]
    exact dist _ (by omega)
  have D : Dest B base root width := by
    refine ⟨by omega,by omega,?_,?_,?_⟩
    · rw [zero_addr]; exact rootH
    · intro j P L
      exact mid _ P (by omega)
    · intro j L
      rw [(flags _).1,dist _ (by omega)]
      exact decide_eq_true L
  have U : WrappedStrip B base a seam d := by
    refine ⟨sp,by omega,dn,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [(flags _).1,before 0 sp]
      exact decide_eq_true (by omega)
    · intro i P L
      rw [show a=addr root (width-1) from rfl,add_addr]
      exact mid _ (by omega) (by omega)
    · intro i P L
      rw [(flags _).1,before i L]
      exact decide_eq_false (by omega)
    · rwa [sr]
    · intro i P L
      cases e : oldH6 B base (addr a i)
      · rfl
      · have zero := (ordinal_zero _ hh _).mpr e
        change oldOrdinal B base hh (addr a i)=0 at zero
        rw [after i (by omega) L] at zero
        omega
    · intro i P L
      rw [(flags _).1,after i P L]
      exact decide_eq_true (by omega)
    · intro i P L
      unfold ends
      rw [(flags _).2,after i P (by omega)]
      simp [show i-seam+1≠width by omega]
    · unfold ends
      rw [(flags _).1,(flags _).2,after d (by omega) (Nat.le_refl _)]
      simp [show d-seam<width by omega,show d-seam+1=width by omega]
  refine ⟨a,seam,d,D,U,zero_addr _,by omega,?_⟩
  have wordSame := (digit_from hp rootH width notShort (width-1) (by omega)).2
  have aa : a=digitFrom root (width-1) := by
    have T := BStarCopyLeftStrip.addr_from root 0 (width-1)
    rw [Nat.zero_add,zero_addr] at T
    exact T
  rw [←aa] at wordSame
  rw [zero_addr,show rail seam 0=.rd from if_pos sp]
  unfold dataOwner
  rw [show word (oldH6 B base) a=word (oldH6 B base) root from wordSame]
  exact rootO

private theorem addr_full {n : Nat} (a : Fin n) : addr a n=addr a 0 := by
  apply Fin.ext
  change (a.val+n)%n=(a.val+0)%n
  rw [Nat.add_mod_right,Nat.add_zero]

/-- Upstream coordinates 1..tail remain site-injective even on the
full wrap. The only possible site alias with index 0 is index n. -/
theorem upstream_addr_inj {n : Nat} (a : Fin n) {i j : Nat}
    (ip : 0<i) (jp : 0<j) (I : i≤n) (J : j≤n)
    (E : addr a i=addr a j) : i=j := by
  by_cases H : i=n
  · subst i
    by_cases K : j=n
    · exact K.symm
    · rw [addr_full] at E
      have A := addr_inj a (Nat.zero_lt_of_lt a.isLt) (by omega) E
      omega
  · by_cases K : j=n
    · subst j
      rw [addr_full] at E
      have A := addr_inj a (by omega) (Nat.zero_lt_of_lt a.isLt) E
      omega
    · exact addr_inj a (by omega) (by omega) E

/-- Typed strip address is injective, including full ring wrap. -/
theorem typed_inj {aP : LargeParams} {b : LargeRows aP} {x : Fin n→LargeSite aP} {a : Fin n} {seam tail : Nat}
    (C : WrappedStrip b x a seam tail)
    {i j : Nat} (I : i≤tail) (J : j≤tail)
    (E : (addr a i,rail seam i)=(addr a j,rail seam j)) : i=j := by
  have sites := congrArg Prod.fst E
  have sheets := congrArg Prod.snd E
  have bound := C.tail_le
  have pos := C.seam_pos
  by_cases iz : i=0
  · subst i
    by_cases jn : j=n
    · subst j
      simp [rail,pos,show ¬ n<seam by have := C.seam_le_tail; omega] at sheets
    · exact addr_inj a (Nat.zero_lt_of_lt a.isLt) (by omega) sites
  · by_cases jz : j=0
    · subst j
      by_cases ine : i=n
      · subst i
        simp [rail,pos,show ¬ n<seam by have := C.seam_le_tail; omega] at sheets
      · exact addr_inj a (by omega) (Nat.zero_lt_of_lt a.isLt) sites
    · exact upstream_addr_inj a (by omega) (by omega) (by omega) (by omega) sites

theorem sole_header_tail {base : X} {root a : Fin n} {width seam tail : Nat}
    (only : ∀ i,oldH6 B base i=true → i=root)
    (C : WrappedStrip B base a seam tail) (join : addr a 0=addr root (width-1))
    (size : tail+1=seam+width) (hw : 0<width) : tail=n := by
  have bound := C.tail_le
  by_cases H : tail=n
  · exact H
  exfalso
  rw [zero_addr] at join
  have E := only _ C.rs_header
  rw [join,add_addr] at E
  have J := addr_inj root (i:=width-1+seam) (j:=0)
    (by omega) (Nat.zero_lt_of_lt root.isLt) (E.trans (zero_addr _).symm)
  have pos := C.seam_pos
  omega

/-- On the ingress mark the two aliased end slots are both on the
left. Tail RS is neither the source nor the destination of any
literal data claim, even when ingress RD advances simultaneously. -/
theorem wrapped_tail_untouched_ingress (x : X) (a : Fin n) (seam : Nat)
    (C : WrappedStrip B x a seam n)
    (d : DataClaim) (D : d∈dataClaims (oldPair B x (addr a 0))) :
    L .rs∉d.slots := by
  have rr : rail seam n=.rs := if_neg (Nat.not_lt_of_ge C.seam_le_tail)
  have N := congrArg (oldPair B x) (addr_full a)
  have noDest := wrapped_tail_no_ingress C d (N.symm ▸ D)
  rw [rr] at noDest
  have noSource := (no_left_send _ d D).2
  intro M
  change L .rs∈d.source :: d.destination.toList at M
  rcases List.mem_cons.mp M with source | dest
  · exact noSource source.symm
  · cases H : d.destination with
    | none => simp [H] at dest
    | some e => simp only [H,Option.toList_some,List.mem_singleton] at dest
                exact noDest (H.trans (congrArg some dest.symm))

#print axioms typed_inj
#print axioms sole_header_tail
#print axioms wrapped_tail_untouched_ingress
#print axioms wrapped_of_chart
end L4.BStarCopyRightWrappedGeometry
