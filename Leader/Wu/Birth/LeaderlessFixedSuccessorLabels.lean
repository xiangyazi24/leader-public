import Leader.Wu.Birth.LeaderlessFixedLabelFrames
import Leader.Wu.Protocol.EliminateLabelFrame

set_option autoImplicit false
set_option Elab.async false

namespace ZZF3Closed

open PPLL PPLLRepair

/-!
# F3, unconditional

`ZZF3Skeleton.leaderless_edgewiseFixed_forces_successor_labels` carried one
hypothesis, `hEliminate`.  `ZZEliminateFrame` discharges it, so the conclusion
holds outright: in a configuration with no leader anywhere, being fixed on
every edge forces the labels to increase by one around the ring.
-/

theorem leaderless_edgewiseFixed_forces_successor_labels
    {n psi : Nat} (hpsi : 0 < psi) (kappa : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState psi)
    (hfixed : ZZF3Skeleton.EdgewiseFixed ring
      (PPLLRepair.ppllNoBulletSignalCollision hpsi kappa) C)
    (hlead : ∀ i : Fin n, (C i).leader = false) :
    ∀ e : Fin n,
      (C (ring.rightNeighbor e)).label.val =
        ((C e).label.val + 1) % psi :=
  ZZF3Skeleton.leaderless_edgewiseFixed_forces_successor_labels
    hpsi kappa ring C
    (fun a b => ZZEliminateFrame.eliminateLeadersNoCollision_labels_eq hpsi a b)
    hfixed hlead

#print axioms leaderless_edgewiseFixed_forces_successor_labels

end ZZF3Closed
