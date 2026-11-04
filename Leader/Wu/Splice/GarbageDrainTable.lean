import Leader.Wu.Splice.ZeroRefreshBlockMass
import Leader.Wu.Splice.OrphanToFence
import Leader.Wu.Splice.LiveSelectorNoGo

set_option autoImplicit false

/-! # V10d: the V10c table with three garbage-draining rows in front

`LDR-BIRTH-B9-LIVE-SELECTOR-REFUTED` showed the V10c one-service bridge is false because the
orphan reserved-front branch is a literal stutter, and `LDR-BIRTH-B9-SCRUB-UNSAFE` showed the
naive scrub (clearControlV6 on the front) breaks SpliceSafeV7.  The rows below use the V7 host
fence instead: every one of them is proved to preserve SpliceSafeV7 in `B9OrphanToFence`, and
every one of them strictly lowers `controllerPotentialV6`. -/

namespace B9SpliceTableV10d

open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceV10cLiveness B9SpliceBlockDrainMass B9OrphanToFence

variable {n psi width kappa tau : Nat}

instance instDecOrphanVictimGuard (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (OrphanVictimGuard l r) := by
  unfold OrphanVictimGuard; infer_instance

instance instDecOwnedPendingVictimGuard (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (OwnedPendingVictimGuard l r) := by
  unfold OwnedPendingVictimGuard; infer_instance

instance instDecOwnerlessPendingPredGuard (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (OwnerlessPendingPredGuard l r) := by
  unfold OwnerlessPendingPredGuard; infer_instance

/-- The four garbage-draining rows placed above V10c. -/
def rowV10d (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau :=
  if OrphanReservedFrontGuardV3 l.carrier r.carrier then (l, fenceV6 r)
  else if OrphanVictimGuard l r then (l, clearControlV6 r)
  else if OwnedPendingVictimGuard l r then (fenceV6 l, fenceV6 r)
  else if OwnerlessPendingPredGuard l r then (fenceV6 l, clearControlV6 r)
  else rowV10c hpsi hwidth hle l r

def stepV10d (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    R1ConfigV6 n psi kappa tau :=
  let j := ring.rightNeighbor e
  if j = e then C else
    let q := rowV10d hpsi hwidth hle (C e) (C j)
    fun i => if i = e then q.1 else if i = j then q.2 else C i

def ControllerProductiveServiceV10d
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) : Prop :=
  controllerPotentialV6 (stepV10d hpsi hwidth hle ring C e) < controllerPotentialV6 C \/
    RolesClearV7 (stepV10d hpsi hwidth hle ring C e)

/-! ## Local weights of the three rows (weights from controllerWeightV6). -/

theorem fence_weight (u : R1AgentStateV6 psi kappa tau) : controllerWeightV6 (fenceV6 u) = 1 := rfl
theorem clear_weight (u : R1AgentStateV6 psi kappa tau) : controllerWeightV6 (clearControlV6 u) = 0 := rfl

theorem reservedFront_weight (u : R1AgentStateV6 psi kappa tau)
    (h : ReservedFrontHoldGuard u.carrier) : 6 <= controllerWeightV6 u := by
  unfold controllerWeightV6
  rw [h.1, h.2]
  cases u.acquireTicket <;> decide

theorem pendingVictim_weight (u : R1AgentStateV6 psi kappa tau)
    (h1 : role u.carrier = .victimArmed) (h2 : u.carrier.repairPending = true) :
    5 <= controllerWeightV6 u := by
  unfold controllerWeightV6
  rw [h1, h2]
  cases u.acquireTicket <;> decide

theorem settledPred_weight (u : R1AgentStateV6 psi kappa tau)
    (h1 : role u.carrier = .predecessorArmed) (h2 : u.carrier.repairPending = false) :
    3 <= controllerWeightV6 u := by
  unfold controllerWeightV6
  rw [h1, h2]
  cases u.acquireTicket <;> decide

theorem pendingPred_weight (u : R1AgentStateV6 psi kappa tau)
    (h1 : role u.carrier = .predecessorArmed) (h2 : u.carrier.repairPending = true) :
    4 <= controllerWeightV6 u := by
  unfold controllerWeightV6
  rw [h1, h2]
  cases u.acquireTicket <;> decide

/-! ## One-index sum accounting -/

private theorem ofFn_sum_le_of_le {m : Nat} (f g : Fin m -> Nat) (hfg : forall i, f i <= g i) :
    (List.ofFn f).sum <= (List.ofFn g).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
      exact Nat.add_le_add (hfg 0) (ih (fun i => f i.succ) (fun i => g i.succ) (fun i => hfg i.succ))

/-- Pointwise `f <= g` away from one index `a` gives `sum f + g a <= sum g + f a`. -/
theorem ofFn_sum_split {m : Nat} (f g : Fin m -> Nat) (a : Fin m)
    (hle : forall i, i ≠ a -> f i <= g i) :
    (List.ofFn f).sum + g a <= (List.ofFn g).sum + f a := by
  induction m with
  | zero => exact Fin.elim0 a
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
      by_cases hz : a = 0
      · subst hz
        have ht := ofFn_sum_le_of_le (fun i : Fin m => f i.succ) (fun i => g i.succ)
          (fun i => hle i.succ (Fin.succ_ne_zero i))
        omega
      · have hz' : a.val ≠ 0 := fun h => hz (Fin.ext h)
        let p : Fin m := ⟨a.val - 1, by have hc := a.isLt; omega⟩
        have hs : p.succ = a := Fin.ext (by simp [p]; omega)
        have ht := ih (fun i : Fin m => f i.succ) (fun i => g i.succ) p
          (fun i hi => hle i.succ (fun h => hi (by rw [<- hs] at h; exact Fin.succ_inj.mp h)))
        have h0 := hle 0 (Ne.symm hz)
        simp only [hs] at ht
        omega

/-! ## Step shape: each branch is one of the proved configuration writers. -/

section StepShape

variable (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
  (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)

theorem stepV10d_of_orphanFront (hne : ring.rightNeighbor e ≠ e)
    (h : OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier) :
    stepV10d hpsi hwidth hle ring C e = orphanToFenceAt ring C e := by
  funext i
  simp only [stepV10d, rowV10d, orphanToFenceAt, hne, if_false, h, if_true]
  by_cases hi : i = e
  · subst hi; simp [Ne.symm hne]
  · simp [hi]

theorem stepV10d_of_orphanVictim (hne : ring.rightNeighbor e ≠ e)
    (h1 : ¬ OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier)
    (h : OrphanVictimGuard (C e) (C (ring.rightNeighbor e))) :
    stepV10d hpsi hwidth hle ring C e = orphanVictimClearAt ring C e := by
  funext i
  simp only [stepV10d, rowV10d, orphanVictimClearAt, hne, if_false, h1, h, if_true]
  by_cases hi : i = e
  · subst hi; simp [Ne.symm hne]
  · simp [hi]

theorem stepV10d_of_ownedVictim (hne : ring.rightNeighbor e ≠ e)
    (h1 : ¬ OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier)
    (h2 : ¬ OrphanVictimGuard (C e) (C (ring.rightNeighbor e)))
    (h : OwnedPendingVictimGuard (C e) (C (ring.rightNeighbor e))) :
    stepV10d hpsi hwidth hle ring C e = fenceFenceAt ring C e := by
  funext i
  simp only [stepV10d, rowV10d, fenceFenceAt, hne, if_false, h1, h2, h, if_true]

theorem stepV10d_of_ownerless (hne : ring.rightNeighbor e ≠ e)
    (h1 : ¬ OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier)
    (h2 : ¬ OrphanVictimGuard (C e) (C (ring.rightNeighbor e)))
    (h2b : ¬ OwnedPendingVictimGuard (C e) (C (ring.rightNeighbor e)))
    (h : OwnerlessPendingPredGuard (C e) (C (ring.rightNeighbor e))) :
    stepV10d hpsi hwidth hle ring C e = fenceClearAt ring C e := by
  funext i
  simp only [stepV10d, rowV10d, fenceClearAt, hne, if_false, h1, h2, h2b, h, if_true]

theorem stepV10d_of_none (hne : ring.rightNeighbor e ≠ e)
    (h1 : ¬ OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier)
    (h2 : ¬ OrphanVictimGuard (C e) (C (ring.rightNeighbor e)))
    (h2b : ¬ OwnedPendingVictimGuard (C e) (C (ring.rightNeighbor e)))
    (h3 : ¬ OwnerlessPendingPredGuard (C e) (C (ring.rightNeighbor e))) :
    stepV10d hpsi hwidth hle ring C e = stepV10c hpsi hwidth hle ring C e := by
  funext i
  simp only [stepV10d, rowV10d, stepV10c, hne, if_false, h1, h2, h2b, h3]

theorem stepV10d_self (hne : ring.rightNeighbor e = e) :
    stepV10d hpsi hwidth hle ring C e = C := by
  simp [stepV10d, hne]

/-- Whole-step safety of V10d, relative to whole-step safety of the V10c remainder. -/
theorem stepV10d_preserves_spliceSafeV7
    (hV10c : ∀ (D : R1ConfigV6 n psi kappa tau) (f : Fin n), SpliceSafeV7 hpsi ring D →
      SpliceSafeV7 hpsi ring (stepV10c hpsi hwidth hle ring D f))
    (hS : SpliceSafeV7 hpsi ring C) :
    SpliceSafeV7 hpsi ring (stepV10d hpsi hwidth hle ring C e) := by
  by_cases hne : ring.rightNeighbor e = e
  · rw [stepV10d_self hpsi hwidth hle ring C e hne]; exact hS
  by_cases h1 : OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier
  · rw [stepV10d_of_orphanFront hpsi hwidth hle ring C e hne h1]
    exact orphanToFence_preserves_spliceSafeV7 hpsi ring C e hS h1
  by_cases h2 : OrphanVictimGuard (C e) (C (ring.rightNeighbor e))
  · rw [stepV10d_of_orphanVictim hpsi hwidth hle ring C e hne h1 h2]
    exact orphanVictimClear_preserves_spliceSafeV7 hpsi ring C e hS h2
  by_cases h2b : OwnedPendingVictimGuard (C e) (C (ring.rightNeighbor e))
  · rw [stepV10d_of_ownedVictim hpsi hwidth hle ring C e hne h1 h2 h2b]
    exact fenceFence_preserves_spliceSafeV7 hpsi ring C e hne hS h2b
  by_cases h3 : OwnerlessPendingPredGuard (C e) (C (ring.rightNeighbor e))
  · rw [stepV10d_of_ownerless hpsi hwidth hle ring C e hne h1 h2 h2b h3]
    exact fenceClear_preserves_spliceSafeV7 hpsi ring C e hne hS h3
  · rw [stepV10d_of_none hpsi hwidth hle ring C e hne h1 h2 h2b h3]
    exact hV10c C e hS

/-! ## Potential drops of the three rows at configuration level -/

theorem orphanToFence_potential_drop
    (h : OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier) :
    controllerPotentialV6 (orphanToFenceAt ring C e) + 5 <= controllerPotentialV6 C := by
  have hs := ofFn_sum_split (fun i => controllerWeightV6 (orphanToFenceAt ring C e i))
    (fun i => controllerWeightV6 (C i)) (ring.rightNeighbor e)
    (fun i hi => by simp [orphanToFenceAt, hi])
  have hj : controllerWeightV6 (orphanToFenceAt ring C e (ring.rightNeighbor e)) = 1 := by
    simp [orphanToFenceAt, fence_weight]
  have hw := reservedFront_weight (C (ring.rightNeighbor e)) h.1
  unfold controllerPotentialV6
  simp only [hj] at hs
  omega

theorem orphanVictimClear_potential_drop
    (h : OrphanVictimGuard (C e) (C (ring.rightNeighbor e))) :
    controllerPotentialV6 (orphanVictimClearAt ring C e) + 5 <= controllerPotentialV6 C := by
  have hs := ofFn_sum_split (fun i => controllerWeightV6 (orphanVictimClearAt ring C e i))
    (fun i => controllerWeightV6 (C i)) (ring.rightNeighbor e)
    (fun i hi => by simp [orphanVictimClearAt, hi])
  have hj : controllerWeightV6 (orphanVictimClearAt ring C e (ring.rightNeighbor e)) = 0 := by
    simp [orphanVictimClearAt, clear_weight]
  have hw := pendingVictim_weight (C (ring.rightNeighbor e)) h.1 h.2.1
  unfold controllerPotentialV6
  simp only [hj] at hs
  omega

theorem fenceFence_potential_drop (hne : ring.rightNeighbor e ≠ e)
    (h : OwnedPendingVictimGuard (C e) (C (ring.rightNeighbor e))) :
    controllerPotentialV6 (fenceFenceAt ring C e) + 6 <= controllerPotentialV6 C := by
  -- the fence at the right endpoint alone is orphanToFenceAt
  have hs1 := ofFn_sum_split (fun i => controllerWeightV6 (orphanToFenceAt ring C e i))
    (fun i => controllerWeightV6 (C i)) (ring.rightNeighbor e)
    (fun i hi => by simp [orphanToFenceAt, hi])
  have hj : controllerWeightV6 (orphanToFenceAt ring C e (ring.rightNeighbor e)) = 1 := by
    simp [orphanToFenceAt, fence_weight]
  have hwr := pendingVictim_weight (C (ring.rightNeighbor e)) h.2.2.1 h.2.2.2
  have hs2 := ofFn_sum_split (fun i => controllerWeightV6 (fenceFenceAt ring C e i))
    (fun i => controllerWeightV6 (orphanToFenceAt ring C e i)) e
    (fun i hi => by simp [fenceFenceAt, orphanToFenceAt, hi])
  have he : controllerWeightV6 (fenceFenceAt ring C e e) = 1 := by
    simp [fenceFenceAt, fence_weight]
  have he' : controllerWeightV6 (orphanToFenceAt ring C e e) = controllerWeightV6 (C e) := by
    simp [orphanToFenceAt, Ne.symm hne]
  have hwl := settledPred_weight (C e) h.1 h.2.1
  unfold controllerPotentialV6
  simp only [hj] at hs1
  simp only [he, he'] at hs2
  omega

theorem fenceClear_potential_drop (hne : ring.rightNeighbor e ≠ e)
    (h : OwnerlessPendingPredGuard (C e) (C (ring.rightNeighbor e))) :
    controllerPotentialV6 (fenceClearAt ring C e) + 3 <= controllerPotentialV6 C := by
  -- first the clear at the right endpoint alone
  have hs1 := ofFn_sum_split (fun i => controllerWeightV6 (orphanVictimClearAt ring C e i))
    (fun i => controllerWeightV6 (C i)) (ring.rightNeighbor e)
    (fun i hi => by simp [orphanVictimClearAt, hi])
  have hj : controllerWeightV6 (orphanVictimClearAt ring C e (ring.rightNeighbor e)) = 0 := by
    simp [orphanVictimClearAt, clear_weight]
  have hw := pendingPred_weight (C (ring.rightNeighbor e)) h.2.1 h.2.2
  -- then the fence at the left endpoint, on top of the cleared configuration
  have hs2 := ofFn_sum_split (fun i => controllerWeightV6 (fenceClearAt ring C e i))
    (fun i => controllerWeightV6 (orphanVictimClearAt ring C e i)) e
    (fun i hi => by simp [fenceClearAt, orphanVictimClearAt, hi])
  have he : controllerWeightV6 (fenceClearAt ring C e e) = 1 := by
    simp [fenceClearAt, fence_weight]
  have he' : controllerWeightV6 (orphanVictimClearAt ring C e e) = controllerWeightV6 (C e) := by
    simp [orphanVictimClearAt, Ne.symm hne]
  unfold controllerPotentialV6
  simp only [hj] at hs1
  simp only [he, he'] at hs2
  omega

/-- Every one of the four new rows is an immediate controller drop. -/
theorem productive_of_orphanFront (hne : ring.rightNeighbor e ≠ e)
    (h : OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier) :
    ControllerProductiveServiceV10d hpsi hwidth hle ring C e := by
  left
  rw [stepV10d_of_orphanFront hpsi hwidth hle ring C e hne h]
  have := orphanToFence_potential_drop ring C e h
  omega

theorem productive_of_orphanVictim (hne : ring.rightNeighbor e ≠ e)
    (h1 : ¬ OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier)
    (h : OrphanVictimGuard (C e) (C (ring.rightNeighbor e))) :
    ControllerProductiveServiceV10d hpsi hwidth hle ring C e := by
  left
  rw [stepV10d_of_orphanVictim hpsi hwidth hle ring C e hne h1 h]
  have := orphanVictimClear_potential_drop ring C e h
  omega

theorem productive_of_ownedVictim (hne : ring.rightNeighbor e ≠ e)
    (h1 : ¬ OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier)
    (h2 : ¬ OrphanVictimGuard (C e) (C (ring.rightNeighbor e)))
    (h : OwnedPendingVictimGuard (C e) (C (ring.rightNeighbor e))) :
    ControllerProductiveServiceV10d hpsi hwidth hle ring C e := by
  left
  rw [stepV10d_of_ownedVictim hpsi hwidth hle ring C e hne h1 h2 h]
  have := fenceFence_potential_drop ring C e hne h
  omega

theorem productive_of_ownerless (hne : ring.rightNeighbor e ≠ e)
    (h1 : ¬ OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier)
    (h2 : ¬ OrphanVictimGuard (C e) (C (ring.rightNeighbor e)))
    (h2b : ¬ OwnedPendingVictimGuard (C e) (C (ring.rightNeighbor e)))
    (h : OwnerlessPendingPredGuard (C e) (C (ring.rightNeighbor e))) :
    ControllerProductiveServiceV10d hpsi hwidth hle ring C e := by
  left
  rw [stepV10d_of_ownerless hpsi hwidth hle ring C e hne h1 h2 h2b h]
  have := fenceClear_potential_drop ring C e hne h
  omega

end StepShape

/-! ## The live-selector refutation fixture is productive under V10d -/

section BadC

open B9SpliceLiveSelector

private theorem hOne : 0 < 1 := by decide
private theorem hTwo : 0 < 2 := by decide
private theorem hOneTwo : 1 <= 2 := by decide
private def ring4 : DirectedRing 4 := ⟨by decide⟩

/-- Edge 0 of `badC`, which stuttered under every V10c service, now fences the orphan
reserved front at site 1 and drops the controller potential. -/
theorem badC_productive_edge_V10d :
    ControllerProductiveServiceV10d hTwo hOne hOneTwo ring4 badC 0 :=
  productive_of_orphanFront hTwo hOne hOneTwo ring4 badC 0 (by decide) bad_hold_census.1

theorem badC_live_V10d : LiveNonClearV10c hTwo ring4 badC :=
  ⟨bad_safe, bad_not_clear⟩

end BadC

end B9SpliceTableV10d
