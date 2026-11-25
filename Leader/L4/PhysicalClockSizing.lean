import Leader.L4.Height.ProductionBlockInterface
import Leader.L4.Compiler.NativeSpec

namespace L4.PhysicalClockDisplay
open AllSizeProtocol PhysicalCustody BStarH6WordChart
open L4.Compiler.Native

theorem radius_lower {s : Nat} (hs : 6≤s) : 63≤radWidth s := by
  have H := Nat.pow_le_pow_right (n:=2) (by decide) hs
  change 64≤2^s at H
  unfold radWidth
  omega

private theorem exponent_room (t : Nat) : t+18≤2^(t+5) := by
  induction t with
  | zero => decide
  | succ t ih =>
    have H : 2^(t+5+1)=2^(t+5)*2 := Nat.pow_succ _ _
    rw [show t+1+5=t+5+1 by omega,H]
    omega

/-- The large advice band implies the production size guard, without
assuming it independently at the display/all-size interface. -/
theorem room_of_advice {s n : Nat} (hs : 6≤s) (ha : s=ell (ell n)) :
    3*1024*radWidth s<n := by
  have minAdv : 2^(s-1)<ell n := by
    by_cases h : 2^(s-1)<ell n
    · exact h
    have L := (ell_le_iff (ell n) (s-1)).mpr (by omega : ell n≤2^(s-1))
    omega
  have powBound : s+12≤2^(s-1) := by
    obtain ⟨t,E⟩ := Nat.exists_eq_add_of_le hs
    have A : 6+t-1=t+5 := by omega
    rw [E,A]
    have H := exponent_room t
    omega
  have big : 2^(s+12)<n := by
    by_cases H : 2^(s+12)<n
    · exact H
    have L := (ell_le_iff n (s+12)).mpr (by omega : n≤2^(s+12))
    omega
  have cap : 3*1024*radWidth s≤2^(s+12) := by
    unfold radWidth
    rw [Nat.pow_add]
    change 3072*(2^s-1)≤2^s*4096
    omega
  omega

private theorem half_formula {r : Nat} (hr : 2≤r) :
    modulus r = 256 * heightMod r ∧ modulus r/2=128*heightMod r := by
  have A : r=(r-2)+2 := by omega
  have E : 16^r=16^(r-2)*256 := by
    calc
      16^r = 16^((r-2)+2) := congrArg (fun x : Nat => 16^x) A
      _ = _ := Nat.pow_add 16 _ _
  unfold modulus heightMod
  rw [E]
  omega

/-- Both the exact half period and the stronger display-height bound. -/
theorem production_clock_bounds {s n : Nat} {x : Raw s n} (g : CustodyWitness x)
    (hs : 6≤s) (ha : s=ell (ell n)) :
    let r := radWidth s
    let P := modulus r/2
    5≤r ∧ modulus r=2*P ∧ 0<P ∧ 32∣P ∧
    total (oldH6 (rows s) g.base)<P ∧ total (oldH6 (rows s) g.base)<heightMod r := by
  let r := radWidth s
  let H := heightMod r
  have r63 : 63≤r := radius_lower hs
  obtain ⟨full,half⟩ := half_formula (r:=r) (by omega)
  have Hpos : 0<H := Nat.pow_pos (by decide)
  have q : ell n≤2^s := ha ▸ power_of_ell (ell n)
  have r1 : r+1=2^s := by
    change 2^s-1+1=2^s
    have z : 0<2^s := Nat.two_pow_pos _
    omega
  have nBound : n≤2^(r+1) := by
    apply Nat.le_trans (power_of_ell n)
    apply Nat.pow_le_pow_right (by decide)
    rwa [r1]
  have height : H=2^(4*(r-2)) := by
    unfold H heightMod
    rw [Nat.pow_mul]
  have nLt : n<H := Nat.lt_of_le_of_lt nBound (height.symm ▸
    Nat.pow_lt_pow_right (by decide : 1<2) (by omega : r+1<4*(r-2)))
  have pack := g.packed
  have owners : total (oldH6 (rows s) g.base)≤n := by
    exact Nat.le_trans (Nat.le_mul_of_pos_right _ (by omega : 0<r)) pack
  change 5≤r ∧ modulus r=2*(modulus r/2) ∧ 0<modulus r/2 ∧
    32∣modulus r/2 ∧ total (oldH6 (rows s) g.base)<modulus r/2 ∧
    total (oldH6 (rows s) g.base)<H
  refine ⟨by omega,by rw [half,full]; omega,by rw [half]; omega,?_,?_,by omega⟩
  · refine ⟨4*H,?_⟩
    rw [half]
    change 128*H=32*(4*H)
    omega
  · rw [half]
    omega

end L4.PhysicalClockDisplay
