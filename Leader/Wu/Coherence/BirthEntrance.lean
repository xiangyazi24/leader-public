import Leader.Wu.Coherence.OpenEntrance
import Leader.Wu.Birth.CheckChainRing
import Leader.Wu.Birth.CheckPermitRepairLeaf

set_option autoImplicit false

namespace R2CoherenceV31BirthEntrance

variable {n ψ κ τ : Nat}

/-- Strongest producer-facing entrance the current B6/R1 first-birth proof
supports: the initial ready train, the literal R1 train
word, neutral V3.1 initialization and the produced leader.  It deliberately says
nothing about pre-existing equal cells and does not include admitted geometry. -/
def BirthEntranceV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C0 : BirthCheckPermitRepairLeaf.FC n ψ κ τ)
    (C : R2CoherenceV31.FC n ψ κ τ) : Prop :=
  ∃ s : Fin n,
    (∀ k, k < ψ →
      BirthCheckChainR1Ring.ReadyCell k
        (C0 (BirthCheckChainR1Ring.cell ring s k))) ∧
    (∀ i : Fin n,
      (C i).phys.base =
        ((BirthCheckChainR1Ring.trainRequests ring s ψ).foldl
          (BirthCheckPermitRepairLeaf.step1 hψ h2 ring) C0) i) ∧
    R2CoherenceV31Entrance.AllOpenV31 C ∧
    R2CoherenceV31Entrance.HasLeaderV31 C

end R2CoherenceV31BirthEntrance
