import Leader.L4.BStarBiasedLift

namespace L4.BStarCycleCosetInit

def next {m : Nat} (i : Fin m) : Fin m :=
  ⟨(i.val+1)%m, Nat.mod_lt _ (by have := i.isLt; omega)⟩

private def sumDelta (d : Nat → Int) : Nat → Int
  | 0 => 0
  | k+1 => sumDelta d k + d k

private theorem sumDelta_bounds (d : Nat → Int) (m : Nat)
    (H : ∀ k, k<m → -1 ≤ d k ∧ d k ≤ 1) :
    ∀ k, k≤m → -(k:Int) ≤ sumDelta d k ∧ sumDelta d k ≤ (k:Int) := by
  intro k
  induction k with
  | zero => simp [sumDelta]
  | succ k ih =>
    intro hm
    have a := ih (by omega)
    have b := H k (by omega)
    simp only [sumDelta]
    omega

private theorem mod_add_congr {P a b c : Int} (h : a%P=b%P) :
    (a+c)%P=(b+c)%P := by
  rw [Int.add_emod a, Int.add_emod b, h]

/-- Integrate the signed unit differences once around a cycle.
Only residues must match, not the absolute representatives of the clocks. -/
theorem exists_coherent (m P : Nat) (hm : 0<m) (small : m<P)
    (tick : Fin m → Nat)
    (edge : ∀ i, ∃ d : Int, -1≤d ∧ d≤1 ∧
      ((tick i : Int)+d)%(P:Int)=(tick (next i) : Int)%(P:Int)) :
    ∃ time : Fin m → Nat, (∀ i, (time i)%P=(tick i)%P) ∧
      ∀ i, time i ≤ time (next i)+1 ∧ time (next i) ≤ time i+1 := by
  classical
  let atN (k : Nat) : Fin m := ⟨k%m, Nat.mod_lt _ hm⟩
  let t (k : Nat) : Int := (tick (atN k) : Int)
  let d (k : Nat) : Int := Classical.choose (edge (atN k))
  have spec (k : Nat) := Classical.choose_spec (edge (atN k))
  have succN (k : Nat) : next (atN k)=atN (k+1) := by
    apply Fin.ext
    change (k%m+1)%m=(k+1)%m
    rw [Nat.mod_add_mod]
  have edgeN (k : Nat) : (t k+d k)%(P:Int)=t (k+1)%(P:Int) := by
    have H : (t k+d k)%(P:Int)=(tick (next (atN k)) : Int)%(P:Int) := (spec k).2.2
    rwa [succN k] at H
  have residue (k : Nat) : (t 0+sumDelta d k)%(P:Int)=t k%(P:Int) := by
    induction k with
    | zero => simp [sumDelta]
    | succ k ih =>
      rw [sumDelta, ←Int.add_assoc, mod_add_congr (c:=d k) ih, edgeN]
  have atEnd : atN m=atN 0 := Fin.ext (by simp [atN])
  have totalMod := residue m
  have T : t m=t 0 := congrArg (fun i : Fin m => (tick i : Int)) atEnd
  rw [T] at totalMod
  have zmod : (sumDelta d m)%(P:Int)=0 := by
    have A := mod_add_congr (c:=-(t 0)) totalMod
    rw [show t 0 + sumDelta d m + -t 0 = sumDelta d m by omega,
      show t 0 + -t 0 = 0 by omega, Int.zero_emod] at A
    exact A
  have bd := sumDelta_bounds d m (fun k _=>⟨(spec k).1,(spec k).2.1⟩)
  have closed : sumDelta d m=0 := by
    have step := Int.emod_add_mul_ediv (sumDelta d m) (P:Int)
    rw [zmod, Int.zero_add] at step
    have B := bd m (Nat.le_refl _)
    have Pm : (m:Int)<P := by exact_mod_cast small
    have P0 : (0:Int)<P := by omega
    let q := sumDelta d m / (P:Int)
    change (P:Int)*q=sumDelta d m at step
    by_cases hp : 0<q
    · have C := Int.mul_le_mul_of_nonneg_left (show 1≤q by omega) (Int.le_of_lt P0)
      rw [Int.mul_one,step] at C
      omega
    · by_cases hn : q<0
      · have C := Int.mul_le_mul_of_nonneg_left (show q≤-1 by omega) (Int.le_of_lt P0)
        rw [Int.mul_neg,Int.mul_one,step] at C
        omega
      · have H : q=0 := by omega
        simp [H] at step
        exact step.symm
  let lifted (k : Nat) : Int := (P:Int) + t 0 + sumDelta d k
  have nonneg (k : Nat) (hk : k≤m) : 0≤lifted k := by
    have B := bd k hk
    have T0 : 0≤t 0 := Int.natCast_nonneg _
    have Pm : (m:Int)<P := by exact_mod_cast small
    unfold lifted
    omega
  let time (i : Fin m) : Nat := (lifted i.val).toNat
  have repr (i : Fin m) : (time i : Int)=lifted i.val :=
    Int.toNat_of_nonneg (nonneg i.val (Nat.le_of_lt i.isLt))
  have atSelf (i : Fin m) : atN i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  refine ⟨time, ?_, ?_⟩
  · intro i
    have A : lifted i.val%(P:Int)=t i.val%(P:Int) := by
      unfold lifted
      rw [Int.add_assoc, Int.add_emod, Int.emod_self, Int.zero_add, Int.emod_emod]
      exact residue i.val
    rw [←repr i] at A
    change (time i : Int)%(P:Int)=(tick (atN i.val) : Int)%(P:Int) at A
    rw [atSelf i, ←Int.natCast_emod, ←Int.natCast_emod] at A
    exact_mod_cast A
  · intro i
    have W : lifted (next i).val=lifted (i.val+1) := by
      by_cases H : i.val+1<m
      · exact congrArg lifted (Nat.mod_eq_of_lt H)
      · have E : i.val+1=m := by have := i.isLt; omega
        change lifted ((i.val+1)%m)=lifted (i.val+1)
        rw [E,Nat.mod_self]
        simp [lifted,sumDelta,closed]
    have V : lifted (i.val+1)=lifted i.val+d i.val := by
      simp only [lifted,sumDelta,Int.add_assoc]
    have R := (spec i.val).1
    have S := (spec i.val).2.1
    have Q := repr (next i)
    have Z := repr i
    rw [W,V,←Z] at Q
    have dl : -1≤d i.val := R
    have du : d i.val≤1 := S
    omega

#print axioms exists_coherent
end L4.BStarCycleCosetInit
