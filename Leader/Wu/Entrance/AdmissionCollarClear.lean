import Leader.Wu.Entrance.WriterAdmissionResetEcho

set_option autoImplicit false
set_option Elab.async false

namespace B6EntranceAdmissionR1

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open B6LocalReverseFill
open B6EntranceV2 B6EntranceV3
open B6EntranceEnvelopeFrame
open B6EntranceAdmissionV3

variable {n psi : Nat}
variable {ring : DirectedRing n}

/-- Residual physical handoff required at the start of the eventual R1
writer-admission word: every envelope collar site is reset/echo clear. -/
def R1CollarClearAtEntry
    (X : Workspace ring psi)
    (C : PConfig n (Phys psi psi (16 * psi))) : Prop :=
  EnvelopeBoundaryResetEchoClear
    (fun q : Phys psi psi (16 * psi) => q) X C

/-- Exact collar conjunct that the successful R1 endpoint must supply to
`HostWriterAdmissionV3`. -/
def R1CollarClearAtAdmission
    (X : Workspace ring psi)
    (D : PConfig n (Phys psi psi (16 * psi))) : Prop :=
  EnvelopeBoundaryResetEchoClear
    (fun q : Phys psi psi (16 * psi) => q) X D

/-- A core-internal R1 word leaves every site outside the core literally
unchanged.  This is stronger than a reset/echo frame and needs no leaderless
hypothesis. -/
theorem r1_core_internal_collar_site_unchanged
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (X : Workspace ring psi)
    (C : PConfig n (Phys psi psi (16 * psi)))
    (w : List (Fin n))
    (hCore : InternalWord X.core.J w)
    (i : Fin n) (hiCore : support X.core.J i = false) :
    runHost
        (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
        ring w C i = C i := by
  exact B6EntranceV2.runHost_outside
    (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
    ring X.core.J i hiCore w C hCore

theorem r1CollarClearAtAdmission_of_entry
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (X : Workspace ring psi)
    (C : PConfig n (Phys psi psi (16 * psi)))
    (w : List (Fin n))
    (hCore : InternalWord X.core.J w)
    (hEntry : R1CollarClearAtEntry X C) :
    R1CollarClearAtAdmission X
      (runHost
        (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
        ring w C) := by
  unfold R1CollarClearAtAdmission EnvelopeBoundaryResetEchoClear
  intro i hiEnv hiCore
  have hsame := r1_core_internal_collar_site_unchanged
    hpsi h2 X C w hCore i hiCore
  rw [hsame]
  exact hEntry i hiEnv hiCore

/-- Successful-target constructor for the eventual R1 admission producer.
The old writer fact plus the residual entry collar premise and core-internality
are exactly enough for the strengthened V3 admission target. -/
theorem r1_writerAdmissionV3_target_of_entry
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (WP : WriterProtected ring psi (Phys psi psi (16 * psi)))
    (X : Workspace ring psi)
    (C : PConfig n (Phys psi psi (16 * psi)))
    (w : List (Fin n))
    (hCore : InternalWord X.core.J w)
    (hEntry : R1CollarClearAtEntry X C)
    (hWriter :
      WriterAt WP X
        (runHost
          (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
          ring w C)) :
    WriterAt WP X
        (runHost
          (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
          ring w C) ∧
      EnvelopeBoundaryResetEchoClear
        (fun q : Phys psi psi (16 * psi) => q) X
        (runHost
          (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
          ring w C) := by
  exact ⟨hWriter,
    r1CollarClearAtAdmission_of_entry
      hpsi h2 X C w hCore hEntry⟩


