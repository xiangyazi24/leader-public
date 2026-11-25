import Leader.L4.ShortLayerGeometry
import Leader.L4.ShortReadCaptureGeometry
import Leader.L4.PhysicalShortSheet
import Leader.L4.PhysicalCustodyH2Ready

namespace L4.ShortMIS2Cap
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open PhysicalShortSheet AllSizeS1Geometry BStarH6Ordinal PhysicalCustody.H1
abbrev size : Nat := 2^32+8

/-- Alternating physical H1 and alternating selected-bank bits on the H1
subring. This is an independent literal witness. -/
def x : Raw 6 size := fun i =>
  ⟨if i.val%2=0 then 4 else 0,
    BitVec.ofNat 96 ((if i.val%2=1 then 2^94+2^93 else 0) +
      (if i.val%4=0 then 2^88 else 0)),
    0,0,0,0,0,0,0,0⟩

theorem advice_correct : ell (ell size)=6 := by decide

theorem mask_exact (i : Fin size) : mask .mis2 x i=decide (i.val%4=0) := by
  unfold mask eligible oldHeaders x
  by_cases H : i.val%2=0 <;> by_cases J : i.val%4=0 <;> simp only [H,J,if_true,if_false]
  · decide
  · decide
  · omega
  · have P : i.val%2=1 := by omega
    rw [if_pos P]
    decide

private theorem header_x (i : Fin size) : header (x i)=decide (i.val%2=0) := by
  unfold header x
  by_cases h : i.val%2=0 <;> simp [h] <;> decide

private theorem role_x (i : Fin size) : PhysicalMIS.role ((projection x) i)=0 := by
  unfold projection x
  by_cases h : i.val%2=0 <;> simp [h] <;> decide

private theorem nextParity (i : Fin size) :
    (rightNeighbor i).val%2 = 1-i.val%2 := by
  have I := i.isLt
  change ((i.val+1)%size)%2=1-i.val%2
  by_cases H : i.val+1<size
  · rw [Nat.mod_eq_of_lt H]
    omega
  · have W : i.val+1=size := by omega
    rw [W,Nat.mod_self]
    have Q : i.val%2=1 := by
      have V : i.val = 4294967303 := Nat.add_right_cancel W
      rw [V]
    simp [Q]

private theorem x_maximal : rawMaximal x := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro i
    constructor
    · intro H
      rw [role_x] at H
      contradiction
    · intro H
      rw [role_x] at H
      contradiction
  · intro i _ bad
    change header (x i)=true ∧ header (x (rightNeighbor i))=true at bad
    simp only [header_x,decide_eq_true_eq,nextParity] at bad
    omega
  · intro i
    change _ ∨ header (x i)=true ∨ header (x (rightNeighbor i))=true
    by_cases h : i.val%2=0
    · exact Or.inr (Or.inl (by simp [header_x,h]))
    · have w : i.val%2=1 := by omega
      exact Or.inr (Or.inr (by simp [header_x,nextParity,w]))

private theorem off_succ_x (i : Fin size) :
    AllSizeS1Geometry.off (x i)=i.val%2 ∧
    successor (x i) = BitVec.ofNat 1 (i.val%2) := by
  have P : i.val%2=0 ∨ i.val%2=1 := by omega
  by_cases J : i.val%4=0
  · have H : i.val%2=0 := by omega
    have T : ¬i.val%2=1 := by omega
    rw [H]
    simp only [AllSizeS1Geometry.off,successor,x,T,J,if_true,if_false]
    decide
  · rcases P with H|H
    · have T : ¬i.val%2=1 := by omega
      rw [H]
      simp only [AllSizeS1Geometry.off,successor,x,T,J,if_false]
      decide
    · rw [H]
      simp only [AllSizeS1Geometry.off,successor,x,H,J,if_true,if_false]
      decide

theorem ready : H2Ready x := by
  have hh : ∃ j,header (x j)=true := ⟨0,by decide⟩
  refine ⟨x_maximal,hh,?_⟩
  intro i
  have of := off_succ_x i
  constructor
  · rw [of.1]
    by_cases h : i.val%2=0
    · have hi : header (x i)=true := by simp [header_x,h]
      rw [(ordinal_zero _ hh i).mpr hi,h]
      rfl
    · have w : i.val%2=1 := by omega
      let prev := BStarH6Ordinal.back i 1
      have Prev : prev.val=i.val-1 := by
        change (((i.val : Int)-1) % (size : Int)).toNat=i.val-1
        rw [Int.emod_eq_of_lt (by omega) (by omega)]
        omega
      have prevH : header (x prev)=true := by simp [header_x,Prev]; omega
      have F : First (fun j=>header (x j)) i 1 := by
        refine ⟨prevH,?_⟩
        intro j bound
        have J : j=0 := by omega
        subst j
        rw [back_zero]
        change header (x i)=false
        rw [header_x]
        simp [h]
      rw [first_unique _ _ (ordinal_spec _ hh i).2 F,w]
      rfl
  · rw [of.2,header_x,nextParity]
    by_cases h : i.val%2=0
    · simp [h]
    · have w : i.val%2=1 := by omega
      simp [w]

def root : Fin size := 0

private theorem gap4 (r : Fin size) (R : mask .mis2 x r=true) :
    Gap (mask .mis2 x) r 4 := by
  rw [mask_exact,decide_eq_true_eq] at R
  refine ⟨by decide,?_,?_⟩
  · rw [mask_exact,decide_eq_true_eq,nextAt_val]
    have Q : r.val < size := r.isLt
    by_cases H : r.val+4<size
    · rw [Nat.mod_eq_of_lt H]; omega
    · have A : r.val+4=size := by change r.val < 4294967304 at Q; change ¬ r.val+4 < 4294967304 at H; change r.val+4=4294967304; omega
      rw [A,Nat.mod_self]
  · intro k K L
    rw [mask_exact,nextAt_val]
    have Q : r.val < size := r.isLt
    have H : r.val+k<size := by change r.val < 4294967304 at Q; change r.val+k<4294967304; omega
    rw [Nat.mod_eq_of_lt H]
    exact decide_eq_false (by omega)

theorem every_mis2_chart_has_length12 (C : Chart (mask .mis2 x)) : C.L=12 := by
  have F := gap4 C.root C.rootHeader
  have G := gap4 _ F.atEnd
  have H := gap4 _ G.atEnd
  let D := chart_of_three C.rootHeader F G H (by decide)
  exact (ShortReadCaptureGeometry.chart_unique C D rfl).1

theorem mis2_chart_exists : ∃ C : Chart (mask .mis2 x), C.root=root ∧ C.L=12 := by
  have R : mask .mis2 x root=true := by rw [mask_exact]; decide
  have F := gap4 root R
  have G := gap4 _ F.atEnd
  have H := gap4 _ G.atEnd
  exact ⟨chart_of_three R F G H (by decide),rfl,rfl⟩

end L4.ShortMIS2Cap
