import Leader.PPL.PsiAtLeastN.CDLClosed
import Leader.PPL.Safety.SPLWhiteCorrectness

/-!
# The Theorem-1 safe target when `psi ≥ n` (F.1b, parts a and b)

Paper Theorem 1 says P_PL "reaches a safe configuration".  For `psi < n`
the proved target is `S_PL`.  For `psi ≥ n` (one segment, `ζ = 1`) the
Lemma-18 argument fails and a closed non-`S_PL` class exists (ERRATA S3.14),
so the target is widened to

  `Theorem1SafeTarget ring C :=
     SPL ring C ∨ (segmentCount n psi = 1 ∧ ∃ root, CDLAt ring root C)`.

With one segment, `SPLAt root` is `CDLAt root` plus "no risky token" (the
interior-pair clause ranges over `Fin (1 - 2) = Fin 0`), so on `ζ = 1` the
target is exactly "rooted `C_DL` at some root"
(`theorem1SafeTarget_iff_cdl_of_single_segment`).  No token clause is needed:
`CDLAt` alone is closed when `ζ = 1` (`cdlAt_step_closed_of_single_segment`).

Results (for every `n ≥ 3`, `psi ≥ 2`, `kappa`; no `psi` window):

* (a) `theorem1SafeTargetAt_step_closed`: the rooted target is closed under
  every interaction, with the same root; hence
  `theorem1SafeTarget_closedPred`.
* (b) `theorem1SafeTarget_isSafe`: every configuration in the target is safe
  in the `PopulationProtocol.IsSafe … PPL.Safety.SPL.output` sense (exactly
  one leader, and every agent's output is constant along every run).
-/

namespace PPL.PsiAtLeastN

open PPL.Safety.SPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-- Rooted safe target: `S_PL` at `root`, or (single segment) rooted `C_DL`
at `root`. -/
def Theorem1SafeTargetAt {n psi kappa : Nat} (ring : DirectedRing n)
    (root : Fin n) (C : Config n psi kappa) : Prop :=
  Or (SPLAt ring root C)
    (And (segmentCount n psi = 1) (CDLAt ring root C))

/-- The Theorem-1 safe target: `S_PL`, or (single segment) rooted `C_DL` at
some root. -/
def Theorem1SafeTarget {n psi kappa : Nat} (ring : DirectedRing n)
    (C : Config n psi kappa) : Prop :=
  Or (SPL ring C)
    (And (segmentCount n psi = 1)
      (Exists fun root : Fin n => CDLAt ring root C))

/-- The target is the existential closure of the rooted target. -/
theorem theorem1SafeTarget_iff_exists_at
    {n psi kappa : Nat} (ring : DirectedRing n)
    (C : Config n psi kappa) :
    Theorem1SafeTarget ring C ↔
      Exists fun root : Fin n => Theorem1SafeTargetAt ring root C := by
  constructor
  · intro h
    rcases h with ⟨root, hroot⟩ | ⟨hseg, root, hroot⟩
    · exact ⟨root, Or.inl hroot⟩
    · exact ⟨root, Or.inr ⟨hseg, hroot⟩⟩
  · intro h
    rcases h with ⟨root, hroot | ⟨hseg, hcdl⟩⟩
    · exact Or.inl ⟨root, hroot⟩
    · exact Or.inr ⟨hseg, root, hcdl⟩

/-- With one segment the target is exactly rooted `C_DL` at some root. -/
theorem theorem1SafeTarget_iff_cdl_of_single_segment
    {n psi kappa : Nat} (hseg : segmentCount n psi = 1)
    (ring : DirectedRing n) (C : Config n psi kappa) :
    Theorem1SafeTarget ring C ↔
      Exists fun root : Fin n => CDLAt ring root C := by
  constructor
  · intro h
    rcases h with ⟨root, hroot⟩ | ⟨_, hcdl⟩
    · exact ⟨root, hroot.1⟩
    · exact hcdl
  · intro h
    exact Or.inr ⟨hseg, h⟩

/-- Both disjuncts pin the leader set to `{root}`. -/
theorem theorem1SafeTargetAt_unique_root
    {n psi kappa : Nat} {ring : DirectedRing n} {root : Fin n}
    {C : Config n psi kappa} (h : Theorem1SafeTargetAt ring root C) :
    forall i : Fin n, (C i).leader = true ↔ i = root := by
  rcases h with hspl | ⟨_, hcdl⟩
  · exact hspl.1.2.1
  · exact hcdl.2.1

/-- **(a) Closure, rooted.**  One interaction keeps the rooted target with
the same root: the `S_PL` disjunct by Lemma 14 (`splAt_closed`), the
single-segment `C_DL` disjunct by `cdlAt_step_closed_of_single_segment`. -/
theorem theorem1SafeTargetAt_step_closed
    {n psi kappa : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) (e : Fin n)
    (h : Theorem1SafeTargetAt ring root C) :
    Theorem1SafeTargetAt ring root
      (PopulationProtocol.step (PPL.protocol psi kappa) ring C e) := by
  rcases h with hspl | ⟨hseg, hcdl⟩
  · exact Or.inl
      (splAt_closed splLocalStepProp_proved hn3 hpsi ring root C e hspl)
  · exact Or.inr
      ⟨hseg,
        cdlAt_step_closed_of_single_segment hn3 hpsi hseg ring root C e hcdl⟩

/-- Closed-predicate form of the rooted closure. -/
theorem theorem1SafeTargetAt_closedPred
    {n psi kappa : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n) :
    PopulationProtocol.ClosedPred (PPL.protocol psi kappa) ring
      (Theorem1SafeTargetAt ring root) := by
  intro C hC C' hstep
  rcases hstep with ⟨e, rfl⟩
  exact theorem1SafeTargetAt_step_closed hn3 hpsi ring root C e hC

/-- **(a) Closure.**  `Theorem1SafeTarget` is closed under every interaction,
for all `n ≥ 3`, `psi ≥ 2`, `kappa`. -/
theorem theorem1SafeTarget_closedPred
    {n psi kappa : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred (PPL.protocol psi kappa) ring
      (Theorem1SafeTarget ring) := by
  intro C hC C' hstep
  rw [theorem1SafeTarget_iff_exists_at] at hC ⊢
  rcases hC with ⟨root, hroot⟩
  exact ⟨root, theorem1SafeTargetAt_closedPred hn3 hpsi ring root C hroot C' hstep⟩

/-- **(b) Safety.**  Every configuration in the safe target has exactly one
leader, and along every run from it every agent's output (its leader bit)
never changes.  Same proof as `splAt_isSafe`, with the closed rooted target
in place of `SPLAt`. -/
theorem theorem1SafeTarget_isSafe
    {n psi kappa : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (C : Config n psi kappa)
    (hC : Theorem1SafeTarget ring C) :
    PopulationProtocol.IsSafe (PPL.protocol psi kappa) ring C
      PPL.Safety.SPL.output := by
  rw [theorem1SafeTarget_iff_exists_at] at hC
  rcases hC with ⟨root, hroot⟩
  have huniq := theorem1SafeTargetAt_unique_root hroot
  refine And.intro ?_ ?_
  · refine ⟨root, ?_, ?_⟩
    · have hr : (C root).leader = true := (huniq root).2 rfl
      simpa [output, PPL.protocol] using hr
    · intro j hj
      have hj' : (C j).leader = true := by
        simpa [output, PPL.protocol] using hj
      exact (huniq j).1 hj'
  · intro C' hr i
    have hC' : Theorem1SafeTargetAt ring root C' :=
      PopulationProtocol.ClosedPred.reachable
        (theorem1SafeTargetAt_closedPred hn3 hpsi ring root) hroot hr
    have huniq' := theorem1SafeTargetAt_unique_root hC'
    change (C' i).leader = (C i).leader
    cases h0 : (C i).leader with
    | false =>
        cases h1 : (C' i).leader with
        | false => rfl
        | true =>
            have ht : (C i).leader = true := (huniq i).2 ((huniq' i).1 h1)
            simp [h0] at ht
    | true =>
        cases h1 : (C' i).leader with
        | false =>
            have ht : (C' i).leader = true := (huniq' i).2 ((huniq i).1 h0)
            simp [h1] at ht
        | true => rfl

/-- On `3 ≤ n ≤ psi`, the safe target is closed and safe, and it is exactly
rooted `C_DL` at some root. -/
theorem theorem1SafeTarget_psi_ge_n
    {n psi kappa : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi) (hge : n ≤ psi)
    (ring : DirectedRing n) :
    And
      (PopulationProtocol.ClosedPred (PPL.protocol psi kappa) ring
        (Theorem1SafeTarget ring))
      (And
        (forall C : Config n psi kappa,
          Theorem1SafeTarget ring C ->
            PopulationProtocol.IsSafe (PPL.protocol psi kappa) ring C
              PPL.Safety.SPL.output)
        (forall C : Config n psi kappa,
          Theorem1SafeTarget ring C ↔
            Exists fun root : Fin n => CDLAt ring root C)) :=
  ⟨theorem1SafeTarget_closedPred hn3 hpsi ring,
    fun C hC => theorem1SafeTarget_isSafe hn3 hpsi ring C hC,
    fun C =>
      theorem1SafeTarget_iff_cdl_of_single_segment
        (segmentCount_eq_one_of_le (by omega) hge) ring C⟩

end PPL.PsiAtLeastN

#print axioms PPL.PsiAtLeastN.theorem1SafeTarget_iff_cdl_of_single_segment
#print axioms PPL.PsiAtLeastN.theorem1SafeTargetAt_step_closed
#print axioms PPL.PsiAtLeastN.theorem1SafeTarget_closedPred
#print axioms PPL.PsiAtLeastN.theorem1SafeTarget_isSafe
#print axioms PPL.PsiAtLeastN.theorem1SafeTarget_psi_ge_n
