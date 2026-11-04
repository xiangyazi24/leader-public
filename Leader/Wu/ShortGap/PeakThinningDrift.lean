import Init.Data.Nat.Lemmas

namespace PeakConcurrentThinningBatch

set_option autoImplicit false

/-- Core-only finite sum, avoiding any Mathlib/Std summation API. -/
def natSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + natSum xs

theorem natSum_map_mul_left (a : Nat) :
    ∀ xs : List Nat,
      natSum (xs.map (fun x => a * x)) = a * natSum xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change a * x + natSum (xs.map (fun y => a * y)) =
        a * (x + natSum xs)
      rw [ih, Nat.mul_add]

/-- One uniform finite-tree round: `q` equiprobable children. -/
structure UniformNatRound (q : Nat) where
  next : Nat → List Nat
  arity : ∀ z, (next z).length = q
  cost : Nat → Nat

/-- Division-free Bellman form mirroring the repository certificate. -/
def NatBellmanSuperSolution {q : Nat}
    (P : UniformNatRound q) (phi : Nat → Nat) : Prop :=
  phi 0 = 0 ∧
  ∀ z,
    q * P.cost z + natSum ((P.next z).map phi) ≤ q * phi z

/-- `8*A*z`: for the protocol, `A = c₁*n*h`, hence `K = 8*c₁`. -/
def linearPhi (A z : Nat) : Nat := (8 * A) * z

private theorem one_add_seven_mul (x : Nat) :
    x + 7 * x = 8 * x := by
  calc
    x + 7 * x = 7 * x + x := Nat.add_comm _ _
    _ = 8 * x := (Nat.succ_mul 7 x).symm

/--
`hdrift` is the division-free uniform-tree encoding of
`E[Z' | Z=z] ≤ 7z/8`:

    8 * Σ_child Z' ≤ 7 * q * z.

If a round costs at most `A*z`, then `8*A*z` pays that round plus the
expected residual potential. No logarithmic potential is needed.
-/
theorem linearPhi_bellman
    {q A : Nat} (P : UniformNatRound q)
    (hcost : ∀ z, P.cost z ≤ A * z)
    (hdrift : ∀ z,
      8 * natSum (P.next z) ≤ 7 * (q * z)) :
    NatBellmanSuperSolution P (linearPhi A) := by
  refine ⟨rfl, ?_⟩
  intro z
  have hc : q * P.cost z ≤ q * (A * z) :=
    Nat.mul_le_mul_left q (hcost z)
  have hd :
      A * (8 * natSum (P.next z)) ≤ A * (7 * (q * z)) :=
    Nat.mul_le_mul_left A (hdrift z)
  have hs :
      natSum ((P.next z).map (linearPhi A)) =
        A * (8 * natSum (P.next z)) := by
    change natSum ((P.next z).map (fun x => (8 * A) * x)) =
      A * (8 * natSum (P.next z))
    rw [natSum_map_mul_left]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [hs]
  calc
    q * P.cost z + A * (8 * natSum (P.next z)) ≤
        q * (A * z) + A * (8 * natSum (P.next z)) :=
      Nat.add_le_add_right hc _
    _ ≤ q * (A * z) + A * (7 * (q * z)) :=
      Nat.add_le_add_left hd _
    _ = A * (q * z) + A * (7 * (q * z)) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ = A * ((q * z) + 7 * (q * z)) :=
      (Nat.mul_add A (q * z) (7 * (q * z))).symm
    _ = A * (8 * (q * z)) := by
      rw [one_add_seven_mul]
    _ = q * linearPhi A z := by
      simp [linearPhi, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Protocol-shaped specialization: `Phi(z)=8*c₁*n*h*z`. -/
def protocolPhi (c1 n h z : Nat) : Nat :=
  linearPhi (c1 * n * h) z

theorem protocolPhi_bellman
    {q c1 n h : Nat} (P : UniformNatRound q)
    (hcost : ∀ z, P.cost z ≤ (c1 * n * h) * z)
    (hdrift : ∀ z,
      8 * natSum (P.next z) ≤ 7 * (q * z)) :
    NatBellmanSuperSolution P (protocolPhi c1 n h) := by
  have hphi : protocolPhi c1 n h = linearPhi (c1 * n * h) := by
    funext z
    rfl
  rw [hphi]
  exact linearPhi_bellman (P := P) hcost hdrift

end PeakConcurrentThinningBatch

#print axioms PeakConcurrentThinningBatch.linearPhi_bellman
#print axioms PeakConcurrentThinningBatch.protocolPhi_bellman
