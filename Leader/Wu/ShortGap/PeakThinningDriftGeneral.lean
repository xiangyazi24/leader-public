import Leader.Wu.ShortGap.PeakThinningDrift


namespace PeakConcurrentThinningBatch


set_option autoImplicit false


/-- `c * A * z`: the linear Bellman potential for a `1 / c` thinning drift. -/
def linearPhiC (c A z : Nat) : Nat := c * A * z


/--
Division-free uniform-tree encoding of


    E[Z' | Z = z] ≤ ((c - 1) / c) * z.


The hypothesis is the direct generalization of the `8/7` form used by
`linearPhi_bellman`:


    c * Σ_child Z' ≤ (c - 1) * q * z.


If one round costs at most `A * z`, then `c * A * z` pays the round plus
all expected residual potential.
-/
theorem linearPhiC_bellman
    {q c A : Nat} (P : UniformNatRound q)
    (hc : 1 ≤ c)
    (hcost : ∀ z, P.cost z ≤ A * z)
    (hdrift : ∀ z,
      c * natSum (P.next z) ≤ (c - 1) * (q * z)) :
    NatBellmanSuperSolution P (linearPhiC c A) := by
  refine ⟨rfl, ?_⟩
  intro z
  change
    q * P.cost z +
        natSum ((P.next z).map (fun x => (c * A) * x)) ≤
      q * ((c * A) * z)
  rw [natSum_map_mul_left]
  have hcost' :
      q * P.cost z ≤ q * (A * z) :=
    Nat.mul_le_mul_left q (hcost z)
  have hdrift' :
      A * (c * natSum (P.next z)) ≤
        A * ((c - 1) * (q * z)) :=
    Nat.mul_le_mul_left A (hdrift z)
  have hres :
      (c * A) * natSum (P.next z) ≤
        A * ((c - 1) * (q * z)) := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hdrift'
  have hpred : 1 + (c - 1) = c := by
    calc
      1 + (c - 1) = (c - 1) + 1 := Nat.add_comm _ _
      _ = c := Nat.sub_add_cancel hc
  calc
    q * P.cost z + (c * A) * natSum (P.next z)
        ≤ q * (A * z) + A * ((c - 1) * (q * z)) :=
      Nat.add_le_add hcost' hres
    _ = A * (q * z) + A * ((c - 1) * (q * z)) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ = A * ((q * z) + (c - 1) * (q * z)) :=
      (Nat.mul_add A (q * z) ((c - 1) * (q * z))).symm
    _ = A * ((1 + (c - 1)) * (q * z)) := by
      rw [Nat.add_mul, Nat.one_mul]
    _ = A * (c * (q * z)) := by
      rw [hpred]
    _ = q * ((c * A) * z) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]


/--
The imported `linearPhi_bellman` certificate is exactly the `c := 8`
instance of `linearPhiC_bellman`.
-/
theorem linearPhi_bellman_from_C
    {q A : Nat} (P : UniformNatRound q)
    (hcost : ∀ z, P.cost z ≤ A * z)
    (hdrift : ∀ z,
      8 * natSum (P.next z) ≤ 7 * (q * z)) :
    NatBellmanSuperSolution P (linearPhi A) := by
  have hphi : linearPhi A = linearPhiC 8 A := by
    funext z
    rfl
  rw [hphi]
  exact linearPhiC_bellman (c := 8) (P := P)
    (hc := by decide)
    (hcost := hcost)
    (hdrift := by
      intro z
      simpa using hdrift z)


/-- The cycle-packing `1/12` potential. -/
def protocolPhi12 (c1 n h z : Nat) : Nat :=
  12 * (c1 * n * h) * z


/--
Protocol specialization with thinning constant `c = 12` and
`A = c1 * n * h`.
-/
theorem protocolPhiC_bellman
    {q c1 n h : Nat} (P : UniformNatRound q)
    (hcost : ∀ z, P.cost z ≤ (c1 * n * h) * z)
    (hdrift : ∀ z,
      12 * natSum (P.next z) ≤ 11 * (q * z)) :
    NatBellmanSuperSolution P (protocolPhi12 c1 n h) := by
  have hphi :
      protocolPhi12 c1 n h = linearPhiC 12 (c1 * n * h) := by
    funext z
    rfl
  rw [hphi]
  exact linearPhiC_bellman (c := 12) (P := P)
    (hc := by decide)
    (hcost := hcost)
    (hdrift := by
      intro z
      simpa using hdrift z)


/--
Since `Φ(z0) = 12 * (c1 * n * h) * z0`, an initial bound `z0 ≤ m0`
gives the explicit thinning-total certificate


    Φ(z0) ≤ 12 * c1 * n * h * m0.
-/
theorem thinning_total_le
    (c1 n h z0 m0 : Nat)
    (hz0 : z0 ≤ m0) :
    protocolPhi12 c1 n h z0 ≤ 12 * c1 * n * h * m0 := by
  have hmono :
      (12 * (c1 * n * h)) * z0 ≤
        (12 * (c1 * n * h)) * m0 :=
    Nat.mul_le_mul_left (12 * (c1 * n * h)) hz0
  simpa only [protocolPhi12, Nat.mul_assoc] using hmono


end PeakConcurrentThinningBatch


#print axioms PeakConcurrentThinningBatch.linearPhiC_bellman
#print axioms PeakConcurrentThinningBatch.linearPhi_bellman_from_C
#print axioms PeakConcurrentThinningBatch.protocolPhiC_bellman
#print axioms PeakConcurrentThinningBatch.thinning_total_le
