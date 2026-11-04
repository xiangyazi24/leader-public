import Leader.Wu.Splice.PhysicalHoldTable
import Leader.Wu.Splice.ComposedEvents

set_option autoImplicit false

namespace B9SpliceTableV10f

open Q11593SpliceControllerDesign
  B9SpliceControllerR1Table
  B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3
  B9SpliceControllerR1TableV6
  B9SpliceControllerR1TableV7
  B9SpliceTableV10d
  B9SpliceTableV10e
  B9SpliceComposedEvents

variable {n psi kappa tau width : Nat}

/-- V10f is V10e with a genuine HOLD on the stutter branch whenever the
left endpoint is an already-pending predecessor. -/
def rowV10f
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau :=
  let q := rowV10d hpsi hwidth hle l r
  if hq : q = (l, r) then
    if hp : role l.carrier = .predecessorArmed ∧ l.carrier.repairPending = true then
      (l, r)
    else
      rowV10e hpsi hwidth hle l r
  else
    q

/-- Pointwise ring step using `rowV10f`, with the same self-edge convention as
`stepV10e`. -/
def stepV10f
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    R1ConfigV6 n psi kappa tau :=
  if hself : ring.rightNeighbor e = e then
    C
  else
    let w := rowV10f hpsi hwidth hle (C e) (C (ring.rightNeighbor e))
    fun i =>
      if i = e then w.1
      else if i = ring.rightNeighbor e then w.2
      else C i

theorem rowV10f_eq_rowV10e_of_not_pendingLeft
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hnp : ¬ (role l.carrier = .predecessorArmed ∧ l.carrier.repairPending = true)) :
    rowV10f hpsi hwidth hle l r = rowV10e hpsi hwidth hle l r := by
  unfold rowV10f rowV10e
  dsimp only
  by_cases hq : rowV10d hpsi hwidth hle l r = (l, r)
  · simp [hq, hnp]
  · simp [hq]

theorem stepV10f_eq_stepV10e_of_shapeClear
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hclear : ShapeClear C) :
    stepV10f hpsi hwidth hle ring C e =
      stepV10e hpsi hwidth hle ring C e := by
  have hnp : ¬ (role (C e).carrier = .predecessorArmed ∧
      (C e).carrier.repairPending = true) := by
    intro h
    have hf := hclear.2 e h.1
    rw [hf] at h
    exact Bool.noConfusion h.2
  have hrow := rowV10f_eq_rowV10e_of_not_pendingLeft hpsi hwidth hle
    (C e) (C (ring.rightNeighbor e)) hnp
  by_cases hself : ring.rightNeighbor e = e
  · simp [stepV10f, stepV10e, hself]
  · simp [stepV10f, stepV10e, hself, hrow]

theorem stepV10f_pendingLeft_hold
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hq : rowV10d hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) =
      (C e, C (ring.rightNeighbor e)))
    (hrole : role (C e).carrier = .predecessorArmed)
    (hpending : (C e).carrier.repairPending = true) :
    stepV10f hpsi hwidth hle ring C e = C := by
  unfold stepV10f
  by_cases hself : ring.rightNeighbor e = e
  · simp [hself]
  · simp only [hself, ↓reduceDIte]
    have hrow : rowV10f hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) =
        (C e, C (ring.rightNeighbor e)) := by
      unfold rowV10f
      dsimp only
      simp [hq, hrole, hpending]
    rw [hrow]
    funext i
    by_cases hie : i = e
    · subst hie
      simp
    · by_cases hij : i = ring.rightNeighbor e
      · subst hij
        simp [hie]
      · simp [hie, hij]

theorem stepV10f_preserves_spliceSafeV7_shapeClear
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hclear : ShapeClear C)
    (hleaderless : B9SpliceV10eAssembly.Leaderless C)
    (hS : SpliceSafeV7 hpsi ring C) :
    SpliceSafeV7 hpsi ring (stepV10f hpsi hwidth hle ring C e) := by
  rw [stepV10f_eq_stepV10e_of_shapeClear hpsi hwidth hle ring C e hclear]
  exact B9SpliceV10eAssembly.stepV10e_preserves_spliceSafeV7_leaderless_final
    hpsi hwidth hle ring C e hleaderless hS

end B9SpliceTableV10f
