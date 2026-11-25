import Leader.L4.ShortResetChart
import Leader.L4.ShortNORCover

namespace L4.PhysicalH1Neighbors
open AllSizeProtocol AllSizeS1Geometry PhysicalCustody PhysicalCustody.H1 ShortResetChart

abbrev Sites {n : Nat} (h : Fin n → Bool) := {i : Fin n // h i = true}

private theorem next_inj {n : Nat} {a b : Fin n}
    (E : rightNeighbor a = rightNeighbor b) : a = b := by
  have F := congrArg Fin.val E
  change (a.val+1)%n=(b.val+1)%n at F
  have A := a.isLt
  have B := b.isLt
  apply Fin.ext
  by_cases U : a.val+1<n
  · rw [Nat.mod_eq_of_lt U] at F
    by_cases V : b.val+1<n
    · rw [Nat.mod_eq_of_lt V] at F; omega
    · rw [show b.val+1=n by omega,Nat.mod_self] at F; omega
  · rw [show a.val+1=n by omega,Nat.mod_self] at F
    by_cases V : b.val+1<n
    · rw [Nat.mod_eq_of_lt V] at F; omega
    · omega

private theorem left_right {n : Nat} (i : Fin n) :
    incoming (rightNeighbor i)=i :=
  next_inj (incoming_spec (rightNeighbor i))

private theorem not_adjacent {s n : Nat} {x : Raw s n} (A : rawMaximal x)
    (i : Fin n) (I : header (x i)=true) : header (x (rightNeighbor i))=false := by
  cases E : header (x (rightNeighbor i))
  · rfl
  · exact False.elim (A.1.2 i i.isLt ⟨I,E⟩)

def rightDist {n : Nat} (h : Fin n → Bool) (i : Fin n) : Nat :=
  if h (nextAt i 2) then 2 else 3

theorem rightDist_eq_gap {n : Nat} {h : Fin n → Bool}
    {i : Fin n} {d : Nat} (D : d=2 ∨ d=3)
    (H : h (nextAt i d)=true) (clear : ∀ k, 0<k → k<d → h (nextAt i k)=false) :
    rightDist h i=d := by
  rcases D with rfl|rfl
  · simp [rightDist,H]
  · simp [rightDist,clear 2 (by decide) (by decide)]

theorem rightDist_header {s n : Nat} {x : Raw s n} (A : rawMaximal x)
    (i : Sites (fun e => header (x e))) :
    header (x (nextAt i.val (rightDist (fun e=>header (x e)) i.val)))=true := by
  obtain ⟨d,D,H,C⟩ := gap A i.val i.property
  rw [rightDist_eq_gap D H C]
  exact H

def right {s n : Nat} {x : Raw s n} (A : rawMaximal x)
    (i : Sites (fun e => header (x e))) : Sites (fun e=>header (x e)) :=
  ⟨nextAt i.val (rightDist (fun e=>header (x e)) i.val), rightDist_header A i⟩

theorem right_injective {s n : Nat} {x : Raw s n} (A : rawMaximal x)
    {i j : Sites (fun e=>header (x e))} (E : right A i=right A j) : i=j := by
  have S := congrArg Subtype.val E
  change nextAt i.val (rightDist _ i.val)=nextAt j.val (rightDist _ j.val) at S
  apply Subtype.ext
  unfold rightDist at S
  split at S <;> split at S <;>
    simp only [nextAt] at S
  · exact next_inj (next_inj S)
  · have F := next_inj (next_inj S)
    have B := not_adjacent A j.val j.property
    rw [← F,(show header (x i.val)=true from i.property)] at B
    contradiction
  · have F := next_inj (next_inj S)
    have B := not_adjacent A i.val i.property
    rw [F,(show header (x j.val)=true from j.property)] at B
    contradiction
  · exact next_inj (next_inj (next_inj S))

private theorem next_two_incoming {n : Nat} (i : Fin n) :
    nextAt (incoming (incoming i)) 2=i := by
  simp [nextAt,incoming_spec]

private theorem next_three_incoming {n : Nat} (i : Fin n) :
    nextAt (incoming (incoming (incoming i))) 3=i := by
  simp [nextAt,incoming_spec]

def leftAt {n : Nat} (h : Fin n → Bool) (i : Fin n) : Fin n :=
  let p := incoming (incoming i)
  if h p then p else incoming p

theorem leftAt_header {s n : Nat} {x : Raw s n} (A : rawMaximal x)
    (i : Sites (fun e=>header (x e))) :
    header (x (leftAt (fun e=>header (x e)) i.val))=true := by
  unfold leftAt
  dsimp only
  let p := incoming (incoming i.val)
  change header (x (if header (x p)=true then p else incoming p))=true
  by_cases P : header (x p)=true
  · simpa only [if_pos P] using P
  · have near : header (x (incoming i.val))=false := by
      cases D : header (x (incoming i.val))
      · rfl
      · have B := not_adjacent A (incoming i.val) D
        rw [incoming_spec,(show header (x i.val)=true from i.property)] at B
        contradiction
    have H := A.2 p
    change header (x (incoming p))=true ∨ header (x p)=true ∨ header (x (rightNeighbor p))=true at H
    rw [show rightNeighbor p=incoming i.val from incoming_spec _] at H
    simpa [P,near] using H

def left {s n : Nat} {x : Raw s n} (A : rawMaximal x)
    (i : Sites (fun e=>header (x e))) : Sites (fun e=>header (x e)) :=
  ⟨leftAt (fun e=>header (x e)) i.val, leftAt_header A i⟩

theorem right_left {s n : Nat} {x : Raw s n} (A : rawMaximal x)
    (i : Sites (fun e=>header (x e))) : right A (left A i)=i := by
  let p := incoming (incoming i.val)
  have H : header (x i.val)=true := i.property
  have L : (left A i).val=(if header (x p) then p else incoming p) := rfl
  apply Subtype.ext
  change nextAt (left A i).val (rightDist (fun e=>header (x e)) (left A i).val)=i.val
  rw [L]
  by_cases P : header (x p)=true
  · rw [if_pos P]
    have E : nextAt p 2=i.val := next_two_incoming i.val
    simp [rightDist,E,H]
  · rw [if_neg P]
    have near : header (x (incoming i.val))=false := by
      cases D : header (x (incoming i.val))
      · rfl
      · have B := not_adjacent A (incoming i.val) D
        rw [incoming_spec,H] at B
        contradiction
    have E : nextAt (incoming p) 2=incoming i.val := by simp [p,nextAt,incoming_spec]
    rw [show rightDist (fun e=>header (x e)) (incoming p)=3 by simp [rightDist,E,near]]
    exact next_three_incoming i.val

theorem right_surjective {s n : Nat} {x : Raw s n} (A : rawMaximal x)
    (i : Sites (fun e=>header (x e))) :
    ∃ j : Sites (fun e=>header (x e)), right A j=i :=
  ⟨left A i,right_left A i⟩

theorem right_noLoop {s n : Nat} {x : Raw s n} (A : rawMaximal x) (N : 3<n)
    (i : Sites (fun e=>header (x e))) :
    right A i≠i := by
  intro E
  have S := congrArg Subtype.val E
  change nextAt i.val (rightDist _ i.val)=nextAt i.val 0 at S
  unfold rightDist at S
  split at S
  · have F := nextAt_injective_under i.val 2 0 (by omega) (by omega) S
    omega
  · have F := nextAt_injective_under i.val 3 0 N (by omega) S
    omega

/-- Actual cyclic selected-H1 neighbours, skipping the one or two unselected
physical sites between consecutive headers. -/
def ring {s n : Nat} {x : Raw s n} (A : rawMaximal x) (N : 3<n) :
    ShortNORCover.Ring (Sites (fun e=>header (x e))) where
  left := left A
  right := right A
  lr i := right_injective A (right_left A (right A i))
  rl := right_left A
  noLoop := right_noLoop A N

/-- Use the same fixed selected-site alphabet on every raw state in the H1
fiber. Only the old header mask, not the MIS1 data, enters either map. -/
def fixedRing {s n : Nat} {x : Raw s n} {h : Fin n → Bool}
    (A : rawMaximal x) (N : 3<n) (heads : ∀ e, header (x e)=h e) :
    ShortNORCover.Ring (Sites h) :=
  have eq : (fun e=>header (x e))=h := funext heads
  eq ▸ ring A N

theorem fixedRing_right {s n : Nat} {x : Raw s n} {h : Fin n → Bool}
    (A : rawMaximal x) (N : 3<n) (heads : ∀ e, header (x e)=h e) (i : Sites h) :
    ((fixedRing A N heads).right i).val=nextAt i.val (rightDist h i.val) := by
  have eq : h=(fun e=>header (x e)) := (funext heads).symm
  subst h
  rfl

theorem fixedRing_left {s n : Nat} {x : Raw s n} {h : Fin n → Bool}
    (A : rawMaximal x) (N : 3<n) (heads : ∀ e, header (x e)=h e) (i : Sites h) :
    ((fixedRing A N heads).left i).val=leftAt h i.val := by
  have eq : h=(fun e=>header (x e)) := (funext heads).symm
  subst h
  rfl

/-- If the first two chronological H1 gaps from the owner root have sizes
a,b, the READ at the root/first/second headers is precisely a read at the
left/center/right of its publication centre. -/
theorem read_sites {s n a b : Nat} {x : Raw s n} {h : Fin n → Bool}
    (A : rawMaximal x) (N : 3<n) (heads : ∀ e, header (x e)=h e)
    (i : Sites h) (G1 : a=2 ∨ a=3) (G2 : b=2 ∨ b=3)
    (H1 : h (nextAt i.val a)=true) (H2 : h (nextAt i.val (a+b))=true)
    (C1 : ∀ k, 0<k → k<a → h (nextAt i.val k)=false)
    (C2 : ∀ k, a<k → k<a+b → h (nextAt i.val k)=false) :
    let R := fixedRing A N heads
    let center : Sites h := ⟨nextAt i.val a,H1⟩
    R.left center=i ∧ (R.right center).val=nextAt i.val (a+b) := by
  dsimp only
  let R := fixedRing A N heads
  let j : Sites h := ⟨nextAt i.val a,H1⟩
  have K : R.right i=j := by
    apply Subtype.ext
    rw [fixedRing_right,rightDist_eq_gap G1 H1 C1]
  constructor
  · change R.left j=i
    rw [←K,R.lr]
  · change (R.right j).val=_
    rw [fixedRing_right]
    have D : rightDist h j.val=b := by
      apply rightDist_eq_gap G2
      · change h (nextAt (nextAt i.val a) b)=true
        rwa [← nextAt_add]
      · intro k pos short
        change h (nextAt (nextAt i.val a) k)=false
        rw [← nextAt_add]
        exact C2 _ (by omega) (by omega)
    rw [D]
    exact (nextAt_add i.val a b).symm

/-- Discharge the gap premises from raw maximality in the fixed fiber.
This is intentionally geometric: it does not assert that a packet holding
three bits actually visited these sites or retained its grants. -/
theorem actual_read_sites {s n : Nat} {x : Raw s n} {h : Fin n → Bool}
    (A : rawMaximal x) (N : 3<n) (heads : ∀ e, header (x e)=h e)
    (i : Sites h) :
    ∃ a b : Nat, (a=2 ∨ a=3) ∧ (b=2 ∨ b=3) ∧
      ∃ center : Sites h, center.val=nextAt i.val a ∧
        (fixedRing A N heads).left center=i ∧
        ((fixedRing A N heads).right center).val=nextAt i.val (a+b) := by
  have H : header (x i.val)=true := (heads i.val).trans i.property
  obtain ⟨a,b,c,Ga,Gb,Gc,Z⟩ := three_gaps A i.val H
  have Z' (k : Nat) (P : 0<k) (B : k≤a+b+c) :
      h (nextAt i.val k)=true ↔ k=a ∨ k=a+b ∨ k=a+b+c := by
    rw [←heads]
    exact Z k P B
  have A' := (Z' a (by omega) (by omega)).mpr (.inl rfl)
  have B' := (Z' (a+b) (by omega) (by omega)).mpr (.inr (.inl rfl))
  have CA : ∀ k, 0<k → k<a → h (nextAt i.val k)=false := by
    intro k P Q
    apply Bool.eq_false_iff.mpr
    intro Y
    have G := (Z' k P (by omega)).mp Y
    omega
  have CB : ∀ k, a<k → k<a+b → h (nextAt i.val k)=false := by
    intro k P Q
    apply Bool.eq_false_iff.mpr
    intro Y
    have G := (Z' k (by omega) (by omega)).mp Y
    omega
  exact ⟨a,b,Ga,Gb,⟨nextAt i.val a,A'⟩,rfl,read_sites A N heads i Ga Gb A' B' CA CB⟩

end L4.PhysicalH1Neighbors
