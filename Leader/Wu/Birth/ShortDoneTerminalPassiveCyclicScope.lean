import Leader.Wu.Birth.ShortDoneTerminalPassiveFirstCapClosed
import Leader.Wu.Birth.ShortWaitTerminalEntryMassWitness

namespace BirthShortDoneTerminalPassiveScopeAudit

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLExpiringComparisonRepair
open BirthWaitPassive BirthShortWait
open BirthShortWaitTerminalEntryRepair
open BirthShortDoneTerminalPassiveR1 BirthShortDoneTerminalPassiveR3
open BirthShortDoneTerminalPassiveR4

set_option autoImplicit false
set_option pp.structureInstances false

variable {psi kappa tau n : Nat}

/-- Arithmetic leaf copied from the existing private SubProtocol proof. -/
private theorem dvd_of_add_mod_eq (a n psi : Nat) (hpsi : 0 < psi)
    (ha : a < psi) (h : (a + n) % psi = a) : psi ∣ n := by
  suffices n % psi = 0 by exact Nat.dvd_of_mod_eq_zero this
  have h2 := Nat.add_mod a n psi
  rw [h, Nat.mod_eq_of_lt ha] at h2
  have h3 : n % psi < psi := Nat.mod_lt _ hpsi
  by_cases hcase : a + n % psi < psi
  · rw [Nat.mod_eq_of_lt hcase] at h2
    omega
  · have hge : psi ≤ a + n % psi := by omega
    have hsub : a + n % psi - psi < psi := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsub] at h2
    omega

/-- R4's global consecutive-label predicate can exist only when `psi ∣ n`.
The requested `n ≥ 2`, `psi ≥ 2` premises are stated explicitly, although the
underlying arithmetic only needs positivity. -/
theorem hostCyclic_dvd (hn : 2 ≤ n) (hpsi2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : BirthShortDoneTerminalPassiveR4.FullConfig n psi kappa tau)
    (hcyc : HostCyclic (by omega : 0 < psi) ring C) :
    psi ∣ n := by
  have hn0 : 0 < n := by omega
  have hpsi : 0 < psi := by omega
  let g : Nat → Nat := fun k =>
    (raw (C ⟨k % n, Nat.mod_lt _ hn0⟩)).label.val
  have hg_step : ∀ k, g (k + 1) = (g k + 1) % psi := by
    intro k
    show
      (raw (C ⟨(k + 1) % n, _⟩)).label.val =
        ((raw (C ⟨k % n, _⟩)).label.val + 1) % psi
    have h := hcyc ⟨k % n, Nat.mod_lt _ hn0⟩
    simp [DirectedRing.rightNeighbor] at h
    exact congrArg Fin.val h
  have hg_ind : ∀ k, g k = (g 0 + k) % psi := by
    intro k
    induction k with
    | zero =>
        show
          (raw (C ⟨0, hn0⟩)).label.val =
            (raw (C ⟨0, hn0⟩)).label.val % psi
        exact
          (Nat.mod_eq_of_lt (raw (C ⟨0, hn0⟩)).label.isLt).symm
    | succ k ih =>
        rw [hg_step, ih,
          Nat.add_mod ((g 0 + k) % psi) 1 psi, Nat.mod_mod,
          ← Nat.add_mod (g 0 + k) 1 psi]
        congr 1
  have hg_n : g n = g 0 := by
    show
      (raw (C ⟨n % n, _⟩)).label.val =
        (raw (C ⟨0 % n, _⟩)).label.val
    simp [Nat.mod_self]
  have hg_n' := hg_ind n
  rw [hg_n] at hg_n'
  exact dvd_of_add_mod_eq _ _ _ hpsi
    (raw (C ⟨0, hn0⟩)).label.isLt hg_n'.symm

/-- Concrete scope consequence: the R4 global ruler premise is impossible at
`n = 3, psi = 2`. This is only a predicate impossibility, not a protocol one. -/
theorem no_hostCyclic_n3_psi2 (kappa tau : Nat) (ring : DirectedRing 3)
    (C : BirthShortDoneTerminalPassiveR4.FullConfig 3 2 kappa tau) :
    ¬ HostCyclic (by decide : 0 < 2) ring C := by
  intro h
  have hd := hostCyclic_dvd
    (n := 3) (psi := 2) (kappa := kappa) (tau := tau)
    (by decide) (by decide) ring C h
  exact (by decide : ¬ (2 ∣ 3)) hd

set_option maxRecDepth 32768 in
/-- The accepted local WAIT-entry mass witness at the same `n = 3, psi = 2`
remains valid: only the two line labels are required. -/
theorem width2_n3_wait_mass_witness :
    3 ^ 6 ≤
      8 * BirthShortWaitTerminalEntryMass.entryNumerator
        (by decide : 2 ≤ 2) (by decide : 2 ≤ 2)
        (by decide : 2 < 3) 2
        BirthShortWaitTerminalEntryMassAudit.dirty3 6 := by
  simpa using BirthShortWaitTerminalEntryMassAudit.dirty3_mass

/-- Smallest full-host localization interface: only the current actual edge is
required to be passive and consecutively labelled. All other sites and labels
are unconstrained. Choosing `e` at the short-line boundary makes the boundary
condition explicit rather than global. -/
structure LocalPassiveEdge2 (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : BirthShortDoneTerminalPassiveR4.FullConfig n psi kappa tau)
    (e : Fin n) : Prop where
  left : Passive (raw (C e))
  right : Passive (raw (C (ring.rightNeighbor e)))
  consecutive :
    (raw (C (ring.rightNeighbor e))).label =
      ⟨((raw (C e)).label.val + 1) % psi, Nat.mod_lt _ hpsi⟩

/-- Earliest reusable localized TerminalHost row. No `HostPassive` or
`HostCyclic` premise is used; the theorem talks only about the actual scheduled
pair and the actual repaired pre-cap test. -/
theorem local_row2_preCap (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (kappa tau : Nat) (ring : DirectedRing n)
    (C : BirthShortDoneTerminalPassiveR4.FullConfig n psi kappa tau)
    (e : Fin n) (hloc : LocalPassiveEdge2 hpsi ring C e)
    (hpre : RowPreCap2 hpsi h2 kappa ring C e) :
    let q := BirthShortDoneTerminalHost.row
      hpsi (by decide : 0 < 2) h2
      (C e) (C (ring.rightNeighbor e))
    RowProjection2 hpsi h2 kappa tau ring C e ∧
      Passive (raw q.1) ∧ Passive (raw q.2) := by
  let a := registers (raw (C e))
  let b := registers (raw (C (ring.rightNeighbor e)))
  have hla : raw (C e) = cell a := by
    change raw (C e) = cell (registers (raw (C e)))
    exact hloc.left.1
  have hrb : raw (C (ring.rightNeighbor e)) = cell b := by
    change raw (C (ring.rightNeighbor e)) =
      cell (registers (raw (C (ring.rightNeighbor e))))
    exact hloc.right.1
  have hwa : a.wait = true := by
    simpa [a, registers] using hloc.left.2.1
  have hwb : b.wait = true := by
    simpa [b, registers] using hloc.right.2.1
  have hab : b.label =
      ⟨(a.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
    simpa [a, b, registers] using hloc.consecutive
  have hpRaw : PreCapEntry2 hpsi h2 kappa
      (raw (C e)) (raw (C (ring.rightNeighbor e))) :=
    (rowPreCap2_iff hpsi h2 kappa tau ring C e).1 hpre
  have hpCell : PreCapEntry2 hpsi h2 kappa (cell a) (cell b) := by
    rw [← hla, ← hrb]
    exact hpRaw
  let w := waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa
    (cell a) (cell b)
  let q := BirthShortDoneTerminalHost.row
    hpsi (by decide : 0 < 2) h2
    (C e) (C (ring.rightNeighbor e))
  have hrow :=
    BirthShortDoneTerminalPassiveR3.full_terminal_row2_preCap
      hpsi h2 kappa tau (C e) (C (ring.rightNeighbor e))
      a b hla hrb hwa hwb hab hpCell
  change
    clock (raw q.1) = clock w.1 ∧
    clock (raw q.2) = clock w.2 ∧
    Passive (raw q.1) ∧ Passive (raw q.2) at hrow
  have hproj : RowProjection2 hpsi h2 kappa tau ring C e := by
    unfold RowProjection2
    rw [hla, hrb]
    change
      clock (raw q.1) = clock w.1 ∧
      clock (raw q.2) = clock w.2
    exact ⟨hrow.1, hrow.2.1⟩
  exact ⟨hproj, hrow.2.2.1, hrow.2.2.2⟩

#print axioms BirthShortDoneTerminalPassiveScopeAudit.hostCyclic_dvd
#print axioms BirthShortDoneTerminalPassiveScopeAudit.no_hostCyclic_n3_psi2
#print axioms BirthShortDoneTerminalPassiveScopeAudit.width2_n3_wait_mass_witness
#print axioms BirthShortDoneTerminalPassiveScopeAudit.local_row2_preCap

end BirthShortDoneTerminalPassiveScopeAudit
