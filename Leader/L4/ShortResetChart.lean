import Leader.L4.PhysicalCustodyH2Ready
import Leader.L4.ShortResetRow

namespace L4.ShortResetChart
open AllSizeProtocol AllSizeS1Geometry PhysicalCustody PhysicalCustody.H1

def nextAt {n : Nat} (r : Fin n) : Nat → Fin n
  | 0 => r
  | i+1 => rightNeighbor (nextAt r i)

theorem nextAt_add {n : Nat} (r : Fin n) (i j : Nat) :
    nextAt r (i+j)=nextAt (nextAt r i) j := by
  induction j with
  | zero => rfl
  | succ j ih => exact congrArg rightNeighbor ih

theorem nextAt_val {n : Nat} (r : Fin n) (i : Nat) :
    (nextAt r i).val=(r.val+i)%n := by
  induction i with
  | zero => exact (Nat.mod_eq_of_lt r.isLt).symm
  | succ i ih =>
    change ((nextAt r i).val+1)%n=(r.val+i+1)%n
    rw [ih, Nat.mod_add_mod]

theorem nextAt_injective_under {n : Nat} (r : Fin n) (i j : Nat)
    (I : i<n) (J : j<n) (E : nextAt r i=nextAt r j) : i=j := by
  have V := congrArg Fin.val E
  rw [nextAt_val,nextAt_val] at V
  have A : r.val+i<2*n := by have := r.isLt; omega
  have B : r.val+j<2*n := by have := r.isLt; omega
  by_cases L : r.val+i<n
  · rw [Nat.mod_eq_of_lt L] at V
    by_cases M : r.val+j<n
    · rw [Nat.mod_eq_of_lt M] at V; omega
    · rw [Nat.mod_eq_sub_mod (by omega : n≤r.val+j), Nat.mod_eq_of_lt (by omega)] at V
      omega
  · rw [Nat.mod_eq_sub_mod (by omega : n≤r.val+i), Nat.mod_eq_of_lt (by omega)] at V
    by_cases M : r.val+j<n
    · rw [Nat.mod_eq_of_lt M] at V; omega
    · rw [Nat.mod_eq_sub_mod (by omega : n≤r.val+j), Nat.mod_eq_of_lt (by omega)] at V
      omega

private theorem incoming_next {n : Nat} (i : Fin n) : incoming (rightNeighbor i)=i := by
  apply Fin.ext
  unfold incoming
  have hi := i.isLt
  have V : (rightNeighbor i).val=(i.val+1)%n := rfl
  by_cases h : i.val+1<n
  · rw [Nat.mod_eq_of_lt h] at V
    simp [V]
  · have h' : i.val+1=n := by omega
    rw [h',Nat.mod_self] at V
    simp [V]
    omega

theorem gap {s n : Nat} {x : Raw s n} (A : rawMaximal x) (r : Fin n)
    (R : header (x r)=true) :
    ∃ d : Nat, (d=2 ∨ d=3) ∧ header (x (nextAt r d))=true ∧
      ∀ k : Nat, 0<k → k<d → header (x (nextAt r k))=false := by
  have noAdj (i : Fin n) (a : header (x i)=true) :
      header (x (rightNeighbor i))=false := by
    cases b : header (x (rightNeighbor i))
    · rfl
    · exact False.elim (A.1.2 i i.isLt ⟨a,b⟩)
  have U := noAdj r R
  by_cases B : header (x (nextAt r 2))=true
  · refine ⟨2,Or.inl rfl,B,?_⟩
    intro k p q
    have : k=1 := by omega
    simpa [this,nextAt] using U
  · have C : header (x (nextAt r 2))=false := Bool.eq_false_iff.mpr B
    have D := A.2 (nextAt r 2)
    change header (x (incoming (rightNeighbor (rightNeighbor r))))=true ∨
      header (x (nextAt r 2))=true ∨ header (x (nextAt r 3))=true at D
    rw [incoming_next] at D
    have E : header (x (nextAt r 3))=true := by simpa [U,C] using D
    refine ⟨3,Or.inr rfl,E,?_⟩
    intro k p q
    have t : k=1 ∨ k=2 := by omega
    rcases t with h|h
    · subst k; exact U
    · subst k; exact C

/-- Short MIS rail chart before the terminal edge. The physical H1-selected
sites, not the H2/MIS1-selected sites, set the boundary for the MIS1 sheet. -/
def lane (a b k : Nat) : Fin 3 :=
  if k<a then 0 else if k<a+b then 1 else 2

theorem three_gaps {s n : Nat} {x : Raw s n} (A : rawMaximal x) (r : Fin n)
    (R : header (x r)=true) :
    ∃ a b c : Nat,
      (a=2 ∨ a=3) ∧ (b=2 ∨ b=3) ∧ (c=2 ∨ c=3) ∧
      ∀ k : Nat, 0<k → k≤a+b+c → (
        header (x (nextAt r k))=true ↔ k=a ∨ k=a+b ∨ k=a+b+c) := by
  obtain ⟨a,Aa,Ha,Ga⟩ := gap A r R
  obtain ⟨b,Bb,Hb,Gb⟩ := gap A (nextAt r a) Ha
  obtain ⟨c,Cc,Hc,Gc⟩ := gap A (nextAt (nextAt r a) b) Hb
  refine ⟨a,b,c,Aa,Bb,Cc,?_⟩
  intro k K L
  by_cases ka : k<a
  · rw [Ga k K ka]
    simp only [Bool.false_eq_true, false_iff]
    rcases Bb with eq|eq <;> omega
  by_cases ea : k=a
  · subst k
    simp [Ha]
  by_cases kb : k<a+b
  · have kx : k=a+(k-a) := by omega
    rw [show nextAt r k=nextAt (nextAt r a) (k-a) by rw [←nextAt_add,←kx]]
    rw [Gb (k-a) (by omega) (by omega)]
    simp only [Bool.false_eq_true, false_iff]
    omega
  by_cases eb : k=a+b
  · subst k
    rw [nextAt_add]
    simp [Hb]
  by_cases kc : k<a+b+c
  · have kx : k=a+b+(k-(a+b)) := by omega
    rw [show nextAt r k=nextAt (nextAt (nextAt r a) b) (k-(a+b)) by
      rw [←nextAt_add,←nextAt_add,←Nat.add_assoc,←kx]]
    rw [Gc (k-(a+b)) (by omega) (by omega)]
    simp only [Bool.false_eq_true, false_iff]
    omega
  · have h : k=a+b+c := by omega
    subst k
    rw [nextAt_add,nextAt_add]
    simp [Hc]

theorem destination_chart {s n : Nat} {x : Raw s n} (A : rawMaximal x) (r : Fin n)
    (R : header (x r)=true) (N : 9<n) :
    ∃ a b c : Nat, (a=2 ∨ a=3) ∧ (b=2 ∨ b=3) ∧ (c=2 ∨ c=3) ∧
      lane a b 0=0 ∧ lane a b (a+b+c-1)=2 ∧
      (∀ k : Nat, k+1<a+b+c →
        ShortResetRow.destination (header (x (rightNeighbor (nextAt r k)))) (lane a b k)
          =some (lane a b (k+1))) ∧
      ShortResetRow.destination (header (x (rightNeighbor (nextAt r (a+b+c-1)))))
        (lane a b (a+b+c-1))=none ∧
      ∀ i j : Nat, i≤a+b+c → j≤a+b+c → nextAt r i=nextAt r j → i=j := by
  obtain ⟨a,b,c,Aa,Bb,Cc,H⟩ := three_gaps A r R
  have Ap : 0<a := by omega
  have Bp : 0<b := by omega
  have Cp : 0<c := by omega
  have L : a+b+c<n := by omega
  have fin : lane a b (a+b+c-1)=2 := by
    unfold lane
    rw [if_neg (by omega),if_neg (by omega)]
  refine ⟨a,b,c,Aa,Bb,Cc,by simp [lane,Ap],fin,?_,?_,?_⟩
  · intro k K
    change ShortResetRow.destination (header (x (nextAt r (k+1)))) (lane a b k)=some (lane a b (k+1))
    by_cases P : k+1=a
    · have T := (H (k+1) (by omega) (by omega)).mpr (Or.inl P)
      have u : k<a := by omega
      have v : k+1<a+b := by omega
      have w : ¬ k+1<a := by omega
      simp [ShortResetRow.destination,T,lane,u,v,w]
    by_cases Q : k+1=a+b
    · have T := (H (k+1) (by omega) (by omega)).mpr (Or.inr (Or.inl Q))
      have u : ¬ k<a := by omega
      have v : k<a+b := by omega
      have w : ¬ k+1<a := by omega
      have z : ¬ k+1<a+b := by omega
      simp [ShortResetRow.destination,T,lane,u,v,w,z]
    have T : header (x (nextAt r (k+1)))=false :=
      Bool.eq_false_iff.mpr (fun h => by have F := (H (k+1) (by omega) (by omega)).mp h; omega)
    have I : (k<a)=(k+1<a) := propext (by omega)
    have J : (k<a+b)=(k+1<a+b) := propext (by omega)
    simp [ShortResetRow.destination,T,lane]
    split <;> rename_i e
    · simp [←I,e]
    · simp [←I,e,←J]
  · have e : a+b+c-1+1=a+b+c := by omega
    change ShortResetRow.destination (header (x (nextAt r (a+b+c-1+1)))) (lane a b (a+b+c-1))=none
    rw [e,fin,(H _ (by omega) (by omega)).mpr (Or.inr (Or.inr rfl))]
    rfl
  · intro i j I J E
    exact nextAt_injective_under r i j (by omega) (by omega) E

/-- Physical H1 selectors are constant throughout the actual sampled tape,
so the route chart is state independent once H2Ready has been reached. -/
theorem header_run {s n : Nat} (N : 5≤n) (x : Raw s n) (A : rawMaximal x)
    (w : List (Fin n)) :
    rawMaximal (rawRun x w) ∧ ∀ i, header (rawRun x w i)=header (x i) := by
  induction w generalizing x with
  | nil => exact ⟨A,fun _=>rfl⟩
  | cons e w ih =>
    have F := ih (rawNext s x e) (raw_h1_maximal_closed N x e A)
    exact ⟨F.1,fun i=>(F.2 i).trans (raw_h1_selected_frozen N x e i A)⟩

theorem ready_run {s n : Nat} (N : 5≤n) (x : Raw s n) (A : H2Ready x)
    (w : List (Fin n)) : H2Ready (rawRun x w) := by
  induction w generalizing x with
  | nil => exact A
  | cons e w ih => exact ih (rawNext s x e) (h2_ready_closed N x e A)

/-- Gate K1 is found only at distance a along this owner's three-lane
route; the second H1 boundary uses K2, and the last is terminal. -/
theorem first_boundary_is_only_gate {s n : Nat} {x : Raw s n} (P : H2Ready x)
    (r : Fin n) (R : header (x r)=true) (N : 5≤n) :
    ∃ a b c : Nat, (a=2 ∨ a=3) ∧ (b=2 ∨ b=3) ∧ (c=2 ∨ c=3) ∧
      ∀ (w : List (Fin n)) (k : Nat), k<a+b+c →
        (MISByteCodec.atGate
          (header (rawRun x w (nextAt r k)))
          (rawRun x w (nextAt r k)).mis1
          (lane a b k)=true ↔ k=a) := by
  obtain ⟨a,b,c,Aa,Bb,Cc,C⟩ := three_gaps P.1 r R
  refine ⟨a,b,c,Aa,Bb,Cc,?_⟩
  intro w k K
  rw [h2_ready_gate (ready_run N x P w), (header_run N x P.1 w).2]
  constructor
  · intro H
    have p : ¬ k<a := by intro J; simpa [lane,J] using H.1
    have q : k<a+b := by
      by_cases J : k<a+b
      · exact J
      · simpa [lane,p,J] using H.1
    have E := (C k (by omega) (by omega)).mp H.2
    omega
  · intro H
    subst k
    have p : a<a+b := by omega
    exact ⟨by simp [lane,p],(C a (by omega) (by omega)).mpr (Or.inl rfl)⟩

end L4.ShortResetChart
