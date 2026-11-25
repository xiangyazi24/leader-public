import Leader.L4.ShortGateChart
namespace L4.ShortChartOwnership
open AllSizeProtocol MISByteCodec PhysicalCustody PhysicalCustody.H1
open ShortResetChart ShortResetCycle ShortResetMIS1Ring ShortResetForwardH2
open ShortResetRow ShortGateChart

/-- The physical site and MIS1 lane of a fixed chart cell. -/
def cell {n : Nat} {h : Fin n→Bool} (C : Chart h) (i : Nat) : Fin n × Fin 3 :=
  (nextAt C.root i,C.route.port i)

theorem right_injective {n : Nat} {u v : Fin n} (E : rightNeighbor u=rightNeighbor v) :
    u=v := by
  simpa only [RearTrace.predecessor_right] using congrArg RearTrace.predecessor E

theorem destination_unique_predecessor (b : Bool) (j k p : Fin 3)
    (A : destination b j=some p) (B : destination b k=some p) : j=k := by
  cases b
  · exact (Option.some.inj A).trans (Option.some.inj B).symm
  · unfold destination at A B
    simp only [if_true] at A B
    split at A
    · split at B
      · have V := congrArg Fin.val ((Option.some.inj A).trans (Option.some.inj B).symm)
        apply Fin.ext
        change j.val+1=k.val+1 at V
        omega
      · contradiction
    · contradiction

theorem destination_ne_root (j : Fin 3) : destination true j ≠ some 0 := by
  intro K
  change (if h : j.val+1<3 then some (⟨j.val+1,h⟩ : Fin 3) else none)=some 0 at K
  split at K
  · have V := congrArg Fin.val (Option.some.inj K)
    change j.val+1=0 at V
    omega
  · contradiction

private theorem root_not_positive {n : Nat} {h : Fin n→Bool} (C D : Chart h) (j : Nat)
    (J : j+1<D.L) (E : cell C 0=cell D (j+1)) : False := by
  have X : C.root=rightNeighbor (nextAt D.root j) := congrArg Prod.fst E
  have S : C.route.port 0=D.route.port (j+1) := congrArg Prod.snd E
  have S0 : C.route.port 0=0 := C.rootPort
  have H : h (rightNeighbor (nextAt D.root j))=true := by rw [←X]; exact C.rootHeader
  have live := D.route.live j J
  change destination (h (rightNeighbor (nextAt D.root j))) (D.route.port j) = some (D.route.port (j+1)) at live
  rw [H,←S,S0] at live
  exact destination_ne_root _ live

private theorem cell_previous {n : Nat} {h : Fin n→Bool} (C D : Chart h) (i j : Nat)
    (I : i+1<C.L) (J : j+1<D.L) (E : cell C (i+1)=cell D (j+1)) :
    cell C i=cell D j := by
  have X : rightNeighbor (nextAt C.root i)=rightNeighbor (nextAt D.root j) := congrArg Prod.fst E
  have S : C.route.port (i+1)=D.route.port (j+1) := congrArg Prod.snd E
  have LC := C.route.live i I
  have LD := D.route.live j J
  change destination (h (rightNeighbor (nextAt C.root i))) (C.route.port i)=some (C.route.port (i+1)) at LC
  change destination (h (rightNeighbor (nextAt D.root j))) (D.route.port j)=some (D.route.port (j+1)) at LD
  rw [X,S] at LC
  exact Prod.ext (right_injective X) (destination_unique_predecessor _ _ _ _ LC LD)

/-- Equal physical rails have equal root owner and equal index whenever
both indices are valid, including charts crossing the cyclic seam. -/
theorem same_cell_owner {n : Nat} {h : Fin n→Bool} (C D : Chart h)
    (i j : Nat) (I : i<C.L) (J : j<D.L) (E : cell C i=cell D j) :
    C.root=D.root ∧ i=j := by
  induction i generalizing j with
  | zero =>
    cases j with
    | zero => exact ⟨congrArg Prod.fst E,rfl⟩
    | succ j => exact (root_not_positive C D j J E).elim
  | succ i ih =>
    cases j with
    | zero => exact (root_not_positive D C i I E.symm).elim
    | succ j =>
      have H := ih j (by omega) (by omega) (cell_previous C D i j I J E)
      exact ⟨H.1,congrArg Nat.succ H.2⟩

theorem distinct_owners_disjoint {n : Nat} {h : Fin n→Bool} (C D : Chart h)
    (roots : C.root≠D.root) (i j : Nat) (I : i<C.L) (J : j<D.L) :
    cell C i≠cell D j :=
  fun E=>roots (same_cell_owner C D i j I J E).1

theorem frozen_raw_owner {s n : Nat} {h : Fin n→Bool} (C D : Chart h) (x : Raw s n)
    (i j : Nat) (I : i<C.L) (J : j<D.L) (E : cell C i=cell D j)
    (frozen : ∀ q, header x q=h q) :
    C.root=D.root ∧ i=j ∧ header x C.root=true := by
  obtain ⟨R,S⟩ := same_cell_owner C D i j I J E
  exact ⟨R,S,(frozen C.root).trans C.rootHeader⟩

#print axioms same_cell_owner
#print axioms distinct_owners_disjoint
#print axioms frozen_raw_owner

private theorem incoming_near_selected {s n : Nat} (x : Raw s n)
    (H : rawMaximal x) (v : Fin n) :
    ∃ r : Fin n, ∃ d : Nat, 0<d ∧ d≤3 ∧ header x r=true ∧ nextAt r d=v ∧
      ∀ k, 0<k → k<d → header x (nextAt r k)=false := by
  let u := incoming v
  let t := incoming u
  let r := incoming t
  have uv : rightNeighbor u=v := incoming_spec v
  have tu : rightNeighbor t=u := incoming_spec u
  have rt : rightNeighbor r=t := incoming_spec t
  by_cases U : header x u=true
  · exact ⟨u,1,by omega,by omega,U,uv,fun _ _ _=>by omega⟩
  by_cases T : header x t=true
  · refine ⟨t,2,by omega,by omega,T,?_,?_⟩
    · change rightNeighbor (rightNeighbor t)=v
      rw [tu,uv]
    · intro k K B
      have E : k=1 := by omega
      subst k
      change header x (rightNeighbor t)=false
      rw [tu]
      exact Bool.eq_false_iff.mpr U
  have R : header x r=true := by
    have Z := H.2 t
    change header x r=true ∨ header x t=true ∨ header x (rightNeighbor t)=true at Z
    rw [tu] at Z
    exact Z.resolve_right (fun H=>H.elim T U)
  refine ⟨r,3,by omega,by omega,R,?_,?_⟩
  · change rightNeighbor (rightNeighbor (rightNeighbor r))=v
    rw [rt,tu,uv]
  · intro k K B
    have E : k=1 ∨ k=2 := by omega
    rcases E with E|E
    · subst k
      change header x (rightNeighbor r)=false
      rw [rt]
      exact Bool.eq_false_iff.mpr T
    · subst k
      change header x (rightNeighbor (rightNeighbor r))=false
      rw [rt,tu]
      exact Bool.eq_false_iff.mpr U

def Covered {n : Nat} (h : Fin n→Bool) (v : Fin n) (j : Fin 3) : Prop :=
  ∃ C : Chart h, ∃ i, i<C.L ∧ cell C i=(v,j)

theorem cover_step {n : Nat} {h : Fin n→Bool} {u : Fin n} {j k : Fin 3}
    (C : Covered h u j) (D : destination (h (rightNeighbor u)) j=some k) :
    Covered h (rightNeighbor u) k := by
  obtain ⟨c,i,I,E⟩ := C
  have A : nextAt c.root i=u := congrArg Prod.fst E
  have B : c.route.port i=j := congrArg Prod.snd E
  have R := c.dst i I
  change destination (h (rightNeighbor (nextAt c.root i))) (c.route.port i) =
    if i+1<c.L then some (c.route.port (i+1)) else none at R
  rw [A,B,D] at R
  split at R
  · exact ⟨c,i+1,by assumption,Prod.ext (congrArg rightNeighbor A) (Option.some.inj R).symm⟩
  · contradiction

private theorem cover_nonheaders {n : Nat} {h : Fin n→Bool} {r : Fin n} {j : Fin 3}
    (C : Covered h r j) (d : Nat)
    (H : ∀ k, 0<k → k≤d → h (nextAt r k)=false) :
    Covered h (nextAt r d) j := by
  induction d with
  | zero => exact C
  | succ d ih =>
    have prev := ih (fun k K L=>H k K (by omega))
    apply cover_step prev
    change destination (h (nextAt r (d+1))) j=some j
    rw [H _ (by omega) (by omega)]
    rfl

private theorem cover_headers {s n : Nat} (x : Raw s n) (M : rawMaximal x)
    (N : 9<n) (j : Nat) (J : j<3) :
    ∀ v, header x v=true → Covered (header x) v ⟨j,J⟩ := by
  induction j with
  | zero =>
    intro v V
    obtain ⟨C,R,_⟩ := chart_exists_gate x M v V N
    exact ⟨C,0,C.positive,Prod.ext R C.rootPort⟩
  | succ j ih =>
    intro v V
    obtain ⟨r,d,D,_,R,B,G⟩ := incoming_near_selected x M v
    have P : j<3 := by omega
    have PP := cover_nonheaders (ih P r R) (d-1)
      (fun k K L=>G k K (by omega))
    have F : rightNeighbor (nextAt r (d-1))=v := by
      change nextAt r (d-1+1)=v
      rwa [show d-1+1=d by omega]
    have Z : destination (header x (rightNeighbor (nextAt r (d-1)))) ⟨j,P⟩=
        some (⟨j+1,J⟩ : Fin 3) := by rw [F,V]; simp only [destination,if_true,dif_pos J]
    simpa only [F] using cover_step PP Z

/-- All three physical lanes of every site have an owner chart on a
maximal H1 ring of size greater than nine. No clean H2 byte is needed. -/
theorem every_lane_covered {s n : Nat} (x : Raw s n) (M : rawMaximal x)
    (N : 9<n) (v : Fin n) (j : Fin 3) : Covered (header x) v j := by
  obtain ⟨j,J⟩ := j
  by_cases V : header x v=true
  · exact cover_headers x M N j J v V
  · obtain ⟨r,d,D,_,R,B,G⟩ := incoming_near_selected x M v
    have X : ∀ k, 0<k → k≤d → header x (nextAt r k)=false := by
      intro k K L
      by_cases E : k=d
      · subst k; rw [B]; exact Bool.eq_false_iff.mpr V
      · exact G k K (by omega)
    simpa only [B] using cover_nonheaders (cover_headers x M N j J r R) d X

#print axioms every_lane_covered

/-- The first selected successor of a chart root is its center. More
precisely the chart contains this successor in its lane 1, and contains
the intervening nonheaders in lane 0. -/
theorem next_center {s n : Nat} (x : Raw s n) (M : rawMaximal x)
    (C : Chart (header x)) :
    ∃ g, (g=2 ∨ g=3) ∧ g<C.L ∧
      header x (nextAt C.root g)=true ∧ C.route.port g=1 ∧
      ∀ k, 0<k → k<g → header x (nextAt C.root k)=false := by
  obtain ⟨g,G,H,B⟩ := gap M C.root C.rootHeader
  change header x (nextAt C.root g)=true at H
  change ∀ k, 0<k → k<g → header x (nextAt C.root k)=false at B
  have before (i : Nat) (I : i<g) : i<C.L ∧ C.route.port i=0 := by
    induction i with
    | zero => exact ⟨C.positive,C.rootPort⟩
    | succ i ih =>
      obtain ⟨L,P⟩ := ih (by omega)
      have K := C.dst i L
      change destination (header x (nextAt C.root (i+1))) (C.route.port i)=
        if i+1<C.L then some (C.route.port (i+1)) else none at K
      rw [B _ (by omega) I,P] at K
      change some (0 : Fin 3) = (if i+1<C.L then some (C.route.port (i+1)) else none) at K
      split at K
      · exact ⟨by assumption,(Option.some.inj K).symm⟩
      · contradiction
  have G0 : 0<g := by omega
  obtain ⟨I,Z⟩ := before (g-1) (by omega)
  have K := C.dst (g-1) I
  change destination (header x (nextAt C.root (g-1+1))) (C.route.port (g-1)) =
    if g-1+1<C.L then some (C.route.port (g-1+1)) else none at K
  rw [show g-1+1=g by omega,H,Z] at K
  change some (1 : Fin 3) = (if g<C.L then some (C.route.port g) else none) at K
  split at K
  · exact ⟨g,G,by assumption,H,(Option.some.inj K).symm,B⟩
  · contradiction

/-- No different owner chart shares the center lane of this root. -/
theorem next_center_owner {s n : Nat} (x : Raw s n) (M : rawMaximal x)
    (C : Chart (header x)) :
    ∃ g, (g=2 ∨ g=3) ∧ g<C.L ∧ header x (nextAt C.root g)=true ∧
      ∀ D : Chart (header x), ∀ i, i<D.L →
        cell D i=(nextAt C.root g,1) → D.root=C.root ∧ i=g := by
  obtain ⟨g,G,I,H,P,_⟩ := next_center x M C
  refine ⟨g,G,I,H,?_⟩
  intro D i J E
  have V : cell C g=(nextAt C.root g,1) := Prod.ext rfl P
  exact same_cell_owner D C i g J I (E.trans V.symm)

#print axioms next_center
#print axioms next_center_owner
end L4.ShortChartOwnership
