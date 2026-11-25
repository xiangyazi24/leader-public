import Leader.L4.WidthOrdinalSpan
import Leader.L4.ShortChartOwnership
import Leader.L4.ShortResetWatch
import Leader.L4.ShortReadCaptureGeometry

namespace L4.ReportChartPartition
open AllSizeProtocol BStarH6Ordinal WidthOrdinalSpan ShortLayerGeometry ShortResetChart
open ShortResetCycle ShortChartOwnership

theorem ordinal_at_offset {n : Nat} {h : Fin n → Bool} (hh : ∃ q,h q=true)
    {r : Fin n} {d : Nat} (R : h r=true) (G : Gap h r d) (k : Nat) (K : k<d) :
    ordinal h hh (nextAt r k)=k := by
  have H : First h (nextAt r k) k := by
    constructor
    · have E := back_nextAt_add r 0 k
      rw [Nat.zero_add] at E
      rw [E]
      exact R
    · intro j J
      have E := back_nextAt_add r (k-j) j
      rw [show k-j+j=k by omega] at E
      rw [E]
      exact G.interior _ (by omega) (by omega)
  exact first_unique _ _ (ordinal_spec _ hh _).2 H

theorem ordinal_inside_gap {n : Nat} {h : Fin n → Bool} (hh : ∃ q,h q=true)
    (i : Fin n) {d : Nat} (G : Gap h (back i (ordinal h hh i)) d) :
    ordinal h hh i<d := by
  let k := ordinal h hh i
  let r := back i k
  have X : nextAt r k=i := nextAt_back i k
  apply Nat.lt_of_not_ge
  intro D
  have Z := back_nextAt_add r d (k-d)
  rw [show d+(k-d)=k by omega,X] at Z
  have B := (ordinal_spec h hh i).2.2 (k-d) (by have := G.positive; omega)
  rw [Z,G.atEnd] at B
  contradiction

private theorem predecessor_gap {n B : Nat} {h : Fin n → Bool}
    (hh : ∃ q,h q=true) (S : ∀ q,h q=true → ∃ d≤B,Gap h q d)
    (r : Fin n) (R : h r=true) : ∃ p d, h p=true ∧ d≤B ∧ Gap h p d ∧ nextAt p d=r := by
  let q := RearTrace.predecessor r
  have e : rightNeighbor q=r := RearTrace.right_predecessor r
  have rr : h (rightNeighbor q)=true := e.symm ▸ R
  obtain ⟨P,G⟩ := last_gap h hh q rr
  let p := back q (ordinal h hh q)
  let d := ordinal h hh q+1
  obtain ⟨b,T,F⟩ := S p P
  have J := gap_unique G F
  have X : nextAt p d=r := by
    change rightNeighbor (nextAt p (ordinal h hh q))=r
    rw [nextAt_back,e]
  rw [←J] at T
  exact ⟨p,d,P,T,G,X⟩

/-- Three-word chart coverage is per (physical site, lane), not per site.
Same-cell uniqueness is independent of the choice of successor witnesses. -/
theorem chart_cell_cover {n B : Nat} {h : Fin n → Bool} (hh : ∃ q,h q=true)
    (room : 3*B<n) (S : ∀ q,h q=true → ∃ d≤B,Gap h q d)
    (i : Fin n) (port : Fin 3) :
    ∃ (C : Chart h) (k : Nat), C.L≤3*B ∧ k<C.L ∧ cell C k=(i,port) := by
  let k := ordinal h hh i
  let r := back i k
  have R : h r=true := (ordinal_spec h hh i).2.1
  have X : nextAt r k=i := nextAt_back i k
  obtain ⟨a,A,F⟩ := S r R
  obtain ⟨b,Bb,G⟩ := S _ F.atEnd
  obtain ⟨c,Cc,I⟩ := S _ G.atEnd
  have K : k<a := ordinal_inside_gap hh i F
  have pa := F.positive
  have pb := G.positive
  have pc := I.positive
  rcases (show port.val=0 ∨ port.val=1 ∨ port.val=2 by have := port.isLt; omega) with p|p|p
  · let C := chart_of_three R F G I (by omega)
    refine ⟨C,k,by change a+b+c≤3*B; omega,by change k<a+b+c; omega,Prod.ext X ?_⟩
    apply Fin.ext
    change (lane a b k).val=port.val
    simp [lane,K,p]
  · obtain ⟨l,d,L,D,Q,V⟩ := predecessor_gap hh S r R
    have pd := Q.positive
    have F' : Gap h (nextAt l d) a := V.symm ▸ F
    have G' : Gap h (nextAt (nextAt l d) a) b := by rw [V]; exact G
    let C := chart_of_three L Q F' G' (by omega)
    refine ⟨C,d+k,by change d+a+b≤3*B; omega,by change d+k<d+a+b; omega,Prod.ext ?_ ?_⟩
    · change nextAt l (d+k)=i
      rw [nextAt_add,V,X]
    · apply Fin.ext
      change (lane d a (d+k)).val=port.val
      simp [lane,p,show ¬d+k<d by omega,show d+k<d+a by omega]
  · obtain ⟨l,d,L,D,Q,V⟩ := predecessor_gap hh S r R
    obtain ⟨u,e,U,E,P,W⟩ := predecessor_gap hh S l L
    have pd := Q.positive
    have pe := P.positive
    have Q' : Gap h (nextAt u e) d := W.symm ▸ Q
    have F' : Gap h (nextAt (nextAt u e) d) a := by rw [W,V]; exact F
    let C := chart_of_three U P Q' F' (by omega)
    refine ⟨C,e+d+k,by change e+d+a≤3*B; omega,by change e+d+k<e+d+a; omega,Prod.ext ?_ ?_⟩
    · change nextAt u (e+d+k)=i
      rw [nextAt_add,nextAt_add,W,V,X]
    · apply Fin.ext
      change (lane e d (e+d+k)).val=port.val
      simp [lane,p,show ¬e+d+k<e by omega,show ¬e+d+k<e+d by omega]

theorem chart_cell_partition {n B : Nat} {h : Fin n → Bool}
    (hh : ∃ q,h q=true) (room : 3*B<n) (S : ∀ q,h q=true → ∃ d≤B,Gap h q d)
    (i : Fin n) (port : Fin 3) :
    ∃ (C : Chart h) (k : Nat), C.L≤3*B ∧ k<C.L ∧ cell C k=(i,port) ∧
      ∀ (D : Chart h) j, j<D.L → cell D j=(i,port) → D.root=C.root ∧ j=k := by
  obtain ⟨C,k,L,K,J⟩ := chart_cell_cover hh room S i port
  exact ⟨C,k,L,K,J,fun D j V P=>same_cell_owner D C j k V K (P.trans J.symm)⟩

/-- The literal saturated cache still distinguishes every digit offset
below the configured cap. In particular offset 2 is unique if cap≥3. -/
theorem cached_digit_exact {n : Nat} {h : Fin n → Bool} (hh : ∃ q,h q=true)
    {r : Fin n} {d cap : Nat} (R : h r=true) (G : Gap h r d)
    (k j : Nat) (K : k<d) (J : j<cap) :
    min cap (ordinal h hh (nextAt r k))=j ↔ k=j := by
  rw [ordinal_at_offset hh R G k K]
  omega

#print axioms ordinal_at_offset
#print axioms chart_cell_cover
#print axioms chart_cell_partition
#print axioms cached_digit_exact
end L4.ReportChartPartition

namespace L4.ReportChartPartition
open AllSizeProtocol BStarH6Ordinal WidthOrdinalSpan ShortLayerGeometry ShortResetChart
open ShortResetCycle ShortChartOwnership ShortResetWatch

def wordStart (a b : Nat) (j : Fin 3) : Nat :=
  if j=0 then 0 else if j=1 then a else a+b

def wordSize (a b c : Nat) (j : Fin 3) : Nat :=
  if j=0 then a else if j=1 then b else c

/-- Affine chart coordinates within each literal lane-word, even for
a chart crossing the physical wrap. -/
theorem chart_word_geometry {n : Nat} {h : Fin n → Bool} (hh : ∃ q,h q=true)
    {r : Fin n} {a b c : Nat} (R : h r=true)
    (F : Gap h r a) (G : Gap h (nextAt r a) b)
    (I : Gap h (nextAt (nextAt r a) b) c) (room : a+b+c<n)
    (j : Fin 3) (p : Nat) (P : p<wordSize a b c j) :
    let C := chart_of_three R F G I room
    let k := wordStart a b j+p
    k<C.L ∧ C.route.port k=j ∧ ordinal h hh (nextAt C.root k)=p := by
  dsimp only
  have aP := F.positive
  have bP := G.positive
  have cP := I.positive
  have J : j=0 ∨ j=1 ∨ j=2 := by
    have jP := j.isLt
    rcases (show j.val=0 ∨ j.val=1 ∨ j.val=2 by omega) with H|H|H
    · exact .inl (Fin.ext H)
    · exact .inr (.inl (Fin.ext H))
    · exact .inr (.inr (Fin.ext H))
  rcases J with rfl|rfl|rfl
  · change p<a at P
    change 0+p<a+b+c ∧ lane a b (0+p)=0 ∧ ordinal h hh (nextAt r (0+p))=p
    exact ⟨by omega,by simp [lane,P],by simpa only [Nat.zero_add] using ordinal_at_offset hh R F p P⟩
  · change p<b at P
    change a+p<a+b+c ∧ lane a b (a+p)=1 ∧ ordinal h hh (nextAt r (a+p))=p
    refine ⟨by omega,by simp [lane,show ¬a+p<a by omega,show a+p<a+b by omega],?_⟩
    rw [nextAt_add]
    exact ordinal_at_offset hh F.atEnd G p P
  · change p<c at P
    change a+b+p<a+b+c ∧ lane a b (a+b+p)=2 ∧ ordinal h hh (nextAt r (a+b+p))=p
    refine ⟨by omega,by simp [lane,show ¬a+b+p<a by omega,show ¬a+b+p<a+b by omega],?_⟩
    rw [nextAt_add,nextAt_add]
    exact ordinal_at_offset hh G.atEnd I p P

theorem chart_word_decompose {a b c : Nat}
    (k : Nat) (K : k<a+b+c) :
    ∃ p : Nat, p<wordSize a b c (lane a b k) ∧ k=wordStart a b (lane a b k)+p := by
  by_cases P : k<a
  · exact ⟨k,by simp [lane,P,wordSize],by simp [lane,P,wordStart]⟩
  · by_cases Q : k<a+b
    · refine ⟨k-a,?_,?_⟩ <;> simp [lane,P,Q,wordStart,wordSize] <;> omega
    · refine ⟨k-(a+b),?_,?_⟩ <;> simp [lane,P,Q,wordStart,wordSize] <;> omega

/-- Any requested radius digit below cap and below each word length
appears once in its own lane. Offset two and lane one give the unique
report gate, when those hypotheses hold for digit 2. -/
theorem chart_unique_digit {n : Nat} {h : Fin n → Bool} (hh : ∃ q,h q=true)
    {r : Fin n} {a b c cap : Nat} (R : h r=true)
    (F : Gap h r a) (G : Gap h (nextAt r a) b)
    (I : Gap h (nextAt (nextAt r a) b) c) (room : a+b+c<n)
    (j : Fin 3) (d : Nat) (D : d<cap) (P : d<wordSize a b c j) :
    let C := chart_of_three R F G I room
    let picked := wordStart a b j+d
    picked<C.L ∧ ∀ k, k<C.L →
      (C.route.port k=j ∧ min cap (ordinal h hh (nextAt C.root k))=d ↔ k=picked) := by
  dsimp only
  let C := chart_of_three R F G I room
  have Hit := chart_word_geometry hh R F G I room j d P
  refine ⟨Hit.1,?_⟩
  intro k K
  constructor
  · intro ⟨J,O⟩
    change lane a b k=j at J
    obtain ⟨v,V,W⟩ := chart_word_decompose (a:=a) (b:=b) (c:=c) k K
    rw [J] at V W
    have Geometry := (chart_word_geometry hh R F G I room j v V).2.2
    change min cap (ordinal h hh (nextAt C.root k))=d at O
    rw [W,Geometry] at O
    have H : v=d := by omega
    exact W.trans (congrArg (wordStart a b j + ·) H)
  · rintro rfl
    exact ⟨Hit.2.1,by rw [Hit.2.2]; omega⟩

theorem report_gate_at_middle_plus_two {n : Nat} {h : Fin n → Bool}
    (hh : ∃ q,h q=true) {r : Fin n} {a b c cap : Nat} (R : h r=true)
    (F : Gap h r a) (G : Gap h (nextAt r a) b)
    (I : Gap h (nextAt (nextAt r a) b) c) (room : a+b+c<n)
    (Cap : 2<cap) (Middle : 2<b) :
    let C := chart_of_three R F G I room
    a+2<C.L ∧ ∀ k, k<C.L →
      (C.route.port k=1 ∧ min cap (ordinal h hh (nextAt C.root k))=2 ↔ k=a+2) :=
  chart_unique_digit hh R F G I room 1 2 Cap Middle

theorem door_not_outgoing {n : Nat} {h : Fin n → Bool} (C : Chart h)
    (k : Nat) (K : k<C.L) : RearTrace.predecessor C.root≠nextAt C.root k := by
  intro E
  have R : nextAt C.root (k+1)=nextAt C.root 0 :=
    (congrArg rightNeighbor E).symm.trans (RearTrace.right_predecessor C.root)
  have X := nextAt_injective_under C.root (k+1) 0
    (by have := C.length_lt; omega) (by have := C.length_lt; omega) R
  omega

#print axioms chart_word_geometry
#print axioms chart_unique_digit
#print axioms report_gate_at_middle_plus_two
#print axioms door_not_outgoing
end L4.ReportChartPartition

namespace L4.ReportChartPartition
open ShortResetCycle ShortLayerGeometry ShortChartOwnership ShortResetChart ShortReadCaptureGeometry

/-- For any fixed choice of one correctly rooted chart per selected
header, every (site,port) is contained in exactly one chosen chart. -/
theorem fixed_charts_partition {n B : Nat} {h : Fin n → Bool}
    (hh : ∃ q,h q=true) (room : 3*B<n) (S : ∀ q,h q=true → ∃ d≤B,Gap h q d)
    (pick : {r : Fin n // h r=true} → Chart h)
    (root : ∀ r, (pick r).root=r.val) (site : Fin n) (port : Fin 3) :
    ∃ (r : {r : Fin n // h r=true}) (k : Nat),
      k<(pick r).L ∧ cell (pick r) k=(site,port) ∧
      ∀ (u : {r : Fin n // h r=true}) j,
        j<(pick u).L → cell (pick u) j=(site,port) → u=r ∧ j=k := by
  obtain ⟨C,k,_,K,Ck⟩ := chart_cell_cover hh room S site port
  let r : {r : Fin n // h r=true} := ⟨C.root,C.rootHeader⟩
  have E : (pick r).root=C.root := root r
  obtain ⟨L,P⟩ := chart_unique (pick r) C E
  have V : k<(pick r).L := L.symm ▸ K
  have Ck' : cell (pick r) k=(site,port) := by
    refine (Prod.ext ?_ (P k V)).trans Ck
    change nextAt (pick r).root k=nextAt C.root k
    rw [E]
  refine ⟨r,k,V,Ck',?_⟩
  intro u j J T
  obtain ⟨A,D⟩ := same_cell_owner (pick u) (pick r) j k J V (T.trans Ck'.symm)
  exact ⟨Subtype.ext ((root u).symm.trans (A.trans (root r))),D⟩

#print axioms fixed_charts_partition
end L4.ReportChartPartition
