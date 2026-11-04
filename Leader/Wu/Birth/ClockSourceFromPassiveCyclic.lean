import Leader.Wu.Birth.ShortDoneTerminalPassiveLocalTripleRotation

namespace BirthPhaseClockSourceAudit

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open BirthWaitPassive
open BirthShortDoneTerminalPassiveR1
  BirthShortDoneTerminalPassiveR4
  BirthShortDoneTerminalPassiveLocal3Rotation

set_option autoImplicit false

variable {psi kappa tau n : Nat}

abbrev FC (n psi kappa tau : Nat) :=
  BirthShortDoneTerminalPassiveR4.FullConfig n psi kappa tau

theorem localLine3At_of_hostPassive_hostCyclic_zero
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (hpass : HostPassive C)
    (hcyc : HostCyclic hpsi ring C)
    (anchor : Fin n)
    (hzero : (raw (C anchor)).label.val = 0) :
    LocalLine3At hpsi hn ring anchor C := by
  have h1 := congrArg Fin.val (hcyc anchor)
  change
    (raw (C (ring.rightNeighbor anchor))).label.val =
      ((raw (C anchor)).label.val + 1) % psi at h1
  have hone :
      (raw (C (ring.rightNeighbor anchor))).label.val = 1 := by
    rw [hzero] at h1
    simpa [Nat.mod_eq_of_lt (by omega : 1 < psi)] using h1
  have hnext := hcyc (ring.rightNeighbor anchor)
  have h2val := congrArg Fin.val hnext
  change
    (raw (C (ring.rightNeighbor
      (ring.rightNeighbor anchor)))).label.val =
      ((raw (C (ring.rightNeighbor anchor))).label.val + 1) % psi at h2val
  rw [hone] at h2val
  refine {
    pass0 := hpass anchor
    pass1 := hpass (ring.rightNeighbor anchor)
    pass2 := hpass (ring.rightNeighbor (ring.rightNeighbor anchor))
    lab0 := hzero
    lab1 := hone
    lab2 := ?_ }
  simpa using h2val

end BirthPhaseClockSourceAudit

#print axioms BirthPhaseClockSourceAudit.localLine3At_of_hostPassive_hostCyclic_zero
