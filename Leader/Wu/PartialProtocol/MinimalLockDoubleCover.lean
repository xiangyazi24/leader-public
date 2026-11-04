import Leader.Wu.PartialProtocol.LockOriginIndistinguishable
import Leader.Wu.Safety.StaticDoubleCoverNoGo

/-!
# Fixed-protocol double-cover obstruction for the minimal lock

This file instantiates the generic static-certificate double-cover theorem at
the accepted one-bit minimal-lock protocol.  The certificate is the lock bit;
an edge is protected exactly when both endpoint locks are true.  On such an
edge the accepted transition is exact identity, so both certificates and both
outputs are preserved.

The theorem fixes one `PopulationProtocol` before mentioning either ring size.
Consequently its state type, transition, and output map are literally the same
on the length-`n` word and its length-`2*n` repetition.  A ring-indexed family
such as `EpochAgentState n psi kappa`, with `slot : Fin n`, does not satisfy
that premise: replacing `n` by `2*n` changes `Q` itself.  Thus the conclusion
does not apply to the factor-`n` protected epoch.

No bad-reachability premise is assumed.  The two leaders are constructed
by copying the verified one-leader word, protection is copied edge by edge,
and non-uniqueness of every reachable future follows from proved pointwise
output stability.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialStaticDoubleCoverSol

open PPLL PPLLResearchFormulation
open PPartialMinimalLockRepairSol
open PPLLStaticDoubleCoverNoGo

set_option autoImplicit false

variable {n psi kappa tau : Nat}

/-! ## The lock bit as a static local certificate -/

/-- A protected edge has two true lock certificates. -/
def minimalLockStaticCertificate
    (hpsi : psi > 0) (kappa tau : Nat) :
    StaticProtectedEdgeCertificate
      (P_partialMinimalLockProtocol hpsi kappa tau) where
  Cert := Bool
  cert := fun s => s.2
  edgeOK := fun left right => left = true ∧ right = true
  preserves := by
    intro l r hprotected
    have hpair := P_partialMinimalLock_eq_self_of_locked
      hpsi kappa tau l r hprotected.1 hprotected.2
    change
      let q := P_partialMinimalLock hpsi kappa tau l r
      ((q.1.2 = l.2 ∧
          (P_partialMinimalLockProtocol hpsi kappa tau).output q.1 =
            (P_partialMinimalLockProtocol hpsi kappa tau).output l) ∧
        (q.2.2 = r.2 ∧
          (P_partialMinimalLockProtocol hpsi kappa tau).output q.2 =
            (P_partialMinimalLockProtocol hpsi kappa tau).output r))
    simp [hpair]

/-- Static protection for this certificate is closed on every nonempty ring. -/
theorem minimalLockStaticProtected_closed
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred
      (P_partialMinimalLockProtocol hpsi kappa tau) ring
      (StaticProtectedConfig
        (P_partialMinimalLockProtocol hpsi kappa tau)
        (minimalLockStaticCertificate hpsi kappa tau) ring) :=
  staticProtected_closed
    (P_partialMinimalLockProtocol hpsi kappa tau)
    (minimalLockStaticCertificate hpsi kappa tau) ring

/-! ## A protected one-leader cyclic word -/

/-- The accepted all-locked witness satisfies every local certificate edge. -/
theorem minimalLockWitness_staticProtected
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) :
    StaticProtectedConfig
      (P_partialMinimalLockProtocol hpsi kappa tau)
      (minimalLockStaticCertificate hpsi kappa tau) ring
      (minimalLockWitness (n := n) hpsi kappa tau) := by
  intro e
  exact ⟨rfl, rfl⟩

/-- The same protected word has exactly one leader output. -/
theorem minimalLockWitness_unique
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) :
    UniqueLeaderOutput
      (P_partialMinimalLockProtocol hpsi kappa tau)
      n (minimalLockWitness (n := n) hpsi kappa tau)
      isLeaderOutput :=
  (minimalLockLegit_inhabited hpsi kappa tau ring).2

/-- Package the accepted witness as the generic theorem's cyclic word. -/
def minimalLockProtectedWord
    (hpsi : psi > 0) (kappa tau : Nat)
    (hn : n > 0) :
    OneLeaderProtectedWord
      (P_partialMinimalLockProtocol hpsi kappa tau)
      (minimalLockStaticCertificate hpsi kappa tau)
      isLeaderOutput n where
  hn := hn
  config := minimalLockWitness (n := n) hpsi kappa tau
  hprotected := minimalLockWitness_staticProtected
    hpsi kappa tau (cycleRing hn)
  hunique := minimalLockWitness_unique
    hpsi kappa tau (cycleRing hn)

/-! ## Repetition produces a closed two-leader obstruction -/

/-- Strongest scoped obstruction: repeating the protected one-leader word
twice produces a protected two-leader configuration whose output vector is
stable and whose every reachable future is non-unique.  All four conclusions
are derived; none is a premise. -/
theorem minimalLock_static_double_cover_no_go
    (hpsi : psi > 0) (kappa tau : Nat) (hn : n > 0) :
    let P := P_partialMinimalLockProtocol hpsi kappa tau
    let S := minimalLockStaticCertificate hpsi kappa tau
    let w := minimalLockProtectedWord hpsi kappa tau hn
    let D := doubleCoverConfig P hn w.config
    StaticProtectedConfig P S (doubleRing hn) D ∧
      HasTwoLeaderOutputs P isLeaderOutput D ∧
      OutputStableFrom P (doubleRing hn) D ∧
      ∀ C' : P.Configuration (2 * n),
        PopulationProtocol.Reachable P (doubleRing hn) D C' →
        ¬UniqueLeaderOutput P (2 * n) C' isLeaderOutput := by
  exact static_double_cover_no_go
    (P_partialMinimalLockProtocol hpsi kappa tau)
    (minimalLockStaticCertificate hpsi kappa tau)
    isLeaderOutput
    (minimalLockProtectedWord hpsi kappa tau hn)

/-- Therefore the repeated word cannot reach any Definition-1 safe
configuration of the same fixed protocol on the doubled ring. -/
theorem minimalLock_double_cover_cannot_reach_safe
    (hpsi : psi > 0) (kappa tau : Nat) (hn : n > 0) :
    let P := P_partialMinimalLockProtocol hpsi kappa tau
    let w := minimalLockProtectedWord hpsi kappa tau hn
    let D := doubleCoverConfig P hn w.config
    ¬∃ C' : P.Configuration (2 * n),
        PopulationProtocol.Reachable P (doubleRing hn) D C' ∧
        PopulationProtocol.IsSafe P (doubleRing hn) C' isLeaderOutput := by
  dsimp only
  let P := P_partialMinimalLockProtocol hpsi kappa tau
  let S := minimalLockStaticCertificate hpsi kappa tau
  let w := minimalLockProtectedWord hpsi kappa tau hn
  let D := doubleCoverConfig P hn w.config
  have hnoGo := minimalLock_static_double_cover_no_go
    hpsi kappa tau hn
  intro hex
  rcases hex with ⟨C', hreach, hsafe⟩
  have hnever :
      ¬UniqueLeaderOutput P (2 * n) C' isLeaderOutput :=
    hnoGo.2.2.2 C' hreach
  exact hnever hsafe.1

end PPartialStaticDoubleCoverSol
end PPLLCompleteMultiLeaderCleanup
