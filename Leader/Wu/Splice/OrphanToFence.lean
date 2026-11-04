import Leader.Wu.Splice.FenceHandoffTable

set_option autoImplicit false

namespace B9OrphanToFence

open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7

variable {n psi kappa tau : Nat}

/-- Turn a cell into the V7 host fence: role none, no pending repair, ticket set. -/
def fenceV6 (u : R1AgentStateV6 psi kappa tau) : R1AgentStateV6 psi kappa tau :=
  setTicketV6 (setControlV6 u .none false) true

/-- The proposed B9 row: on an orphan reserved front `(l, r)` the front becomes a fence. -/
def orphanToFenceAt (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    R1ConfigV6 n psi kappa tau :=
  fun i => if i = ring.rightNeighbor e then fenceV6 (C (ring.rightNeighbor e)) else C i

theorem rightNeighbor_inj (ring : DirectedRing n) {i e : Fin n}
    (h : ring.rightNeighbor i = ring.rightNeighbor e) : i = e := by
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  have hi := i.isLt
  have he := e.isLt
  apply Fin.ext
  rcases Nat.lt_or_ge (i.val + 1) n with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at hv
    rcases Nat.lt_or_ge (e.val + 1) n with h2 | h2
    · rw [Nat.mod_eq_of_lt h2] at hv; omega
    · have : e.val + 1 = n := by omega
      rw [this, Nat.mod_self] at hv; omega
  · have hin : i.val + 1 = n := by omega
    rw [hin, Nat.mod_self] at hv
    rcases Nat.lt_or_ge (e.val + 1) n with h2 | h2
    · rw [Nat.mod_eq_of_lt h2] at hv; omega
    · omega

theorem fence_shape (u : R1AgentStateV6 psi kappa tau) : HostFenceShapeV7 (fenceV6 u) :=
  ⟨rfl, rfl, rfl⟩

theorem fence_base (u : R1AgentStateV6 psi kappa tau) :
    (fenceV6 u).carrier.splice.base = u.carrier.splice.base := rfl

theorem at_j (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    orphanToFenceAt ring C e (ring.rightNeighbor e) = fenceV6 (C (ring.rightNeighbor e)) := by
  simp [orphanToFenceAt]

theorem at_other (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n)
    (h : i ≠ ring.rightNeighbor e) : orphanToFenceAt ring C e i = C i := by
  simp [orphanToFenceAt, h]

/-- The physical base of every cell is unchanged. -/
theorem base_eq (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n) :
    (orphanToFenceAt ring C e i).carrier.splice.base = (C i).carrier.splice.base := by
  unfold orphanToFenceAt
  split
  · rename_i h; subst h; rfl
  · rfl

/-- Prepared dangers depend on the physical base only. -/
theorem dangerAt_iff (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e e' : Fin n) :
    PreparedDangerAt hpsi ring (projectV6 (orphanToFenceAt ring C e)) e' ↔
      PreparedDangerAt hpsi ring (projectV6 C) e' := by
  unfold PreparedDangerAt PreparedBarrierAt preparedR1 prepared projectSpliceConfig projectV6
  dsimp only
  rw [base_eq, base_eq]

theorem orphanToFence_preserves_spliceSafeV7
    (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hS : SpliceSafeV7 hpsi ring C)
    (hO : OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier) :
    SpliceSafeV7 hpsi ring (orphanToFenceAt ring C e) := by
  have hfront : role (C (ring.rightNeighbor e)).carrier = .front := hO.1.1
  have hnotpred : role (C e).carrier ≠ .predecessorArmed := hO.2
  refine ⟨?_, ?_, ?_⟩
  · -- every prepared danger stays protected
    intro e' hd
    by_cases h1 : e' = ring.rightNeighbor e
    · right
      rw [h1, at_j]
      exact fence_shape _
    · have hd0 := (dangerAt_iff hpsi ring C e e').1 hd
      have hp := hS.1 e' hd0
      by_cases h2 : ring.rightNeighbor e' = ring.rightNeighbor e
      · -- e' = e: the right endpoint became the fence
        have hee : e' = e := rightNeighbor_inj ring h2
        subst hee
        rcases hp with hv | hf
        · left
          unfold R1ProtectedSpliceEdgeV3 at hv ⊢
          simp only [projectV6] at hv ⊢
          rw [at_other ring C e' e' h1, at_j]
          rcases hv with h1' | h2' | h3'
          · exact Or.inl h1'
          · exact absurd h2'.1 (by rw [hfront]; decide)
          · exact absurd h3'.1 hnotpred
        · right
          rw [at_other ring C e' e' h1]
          exact hf
      · -- neither endpoint changed
        unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3 at hp ⊢
        simp only [projectV6] at hp ⊢
        rw [at_other ring C e e' h1, at_other ring C e _ h2]
        exact hp
  · -- ticket shape
    intro i
    by_cases h1 : i = ring.rightNeighbor e
    · rw [h1, at_j]
      intro _
      exact Or.inr (fence_shape _)
    · rw [at_other ring C e i h1]
      exact hS.2.1 i
  · -- pending predecessors keep a reserved, unticketed front
    intro i hr hp
    by_cases h1 : i = ring.rightNeighbor e
    · rw [h1, at_j] at hr
      have hnone : role (fenceV6 (C (ring.rightNeighbor e))).carrier = .none := rfl
      rw [hnone] at hr
      exact absurd hr (by decide)
    · rw [at_other ring C e i h1] at hr hp
      by_cases h2 : ring.rightNeighbor i = ring.rightNeighbor e
      · have hie : i = e := rightNeighbor_inj ring h2
        subst hie
        exact absurd hr hnotpred
      · rw [at_other ring C e _ h2]
        exact hS.2.2 i hr hp


/-! ## Second garbage class: an orphan pending victim (never produced by the table,
but possible as initial garbage).  A pending victim protects nothing on its right;
on its left it protects `(l, r)` only when `l` is a settled predecessor.  So when
`l` is not a settled predecessor the victim can be cleared outright. -/

def OrphanVictimGuard (l r : R1AgentStateV6 psi kappa tau) : Prop :=
  role r.carrier = .victimArmed ∧ r.carrier.repairPending = true ∧
    ¬ (role l.carrier = .predecessorArmed ∧ l.carrier.repairPending = false)

def orphanVictimClearAt (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    R1ConfigV6 n psi kappa tau :=
  fun i => if i = ring.rightNeighbor e then clearControlV6 (C (ring.rightNeighbor e)) else C i

theorem vc_at_j (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    orphanVictimClearAt ring C e (ring.rightNeighbor e) = clearControlV6 (C (ring.rightNeighbor e)) := by
  simp [orphanVictimClearAt]

theorem vc_at_other (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n)
    (h : i ≠ ring.rightNeighbor e) : orphanVictimClearAt ring C e i = C i := by
  simp [orphanVictimClearAt, h]

theorem vc_base_eq (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n) :
    (orphanVictimClearAt ring C e i).carrier.splice.base = (C i).carrier.splice.base := by
  unfold orphanVictimClearAt
  split
  · rename_i h; subst h; rfl
  · rfl

theorem vc_dangerAt_iff (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e e' : Fin n) :
    PreparedDangerAt hpsi ring (projectV6 (orphanVictimClearAt ring C e)) e' ↔
      PreparedDangerAt hpsi ring (projectV6 C) e' := by
  unfold PreparedDangerAt PreparedBarrierAt preparedR1 prepared projectSpliceConfig projectV6
  dsimp only
  rw [vc_base_eq, vc_base_eq]

theorem clearControl_role (u : R1AgentStateV6 psi kappa tau) :
    role (clearControlV6 u).carrier = .none := rfl
theorem clearControl_pending (u : R1AgentStateV6 psi kappa tau) :
    (clearControlV6 u).carrier.repairPending = false := rfl
theorem clearControl_ticket (u : R1AgentStateV6 psi kappa tau) :
    (clearControlV6 u).acquireTicket = false := rfl

theorem orphanVictimClear_preserves_spliceSafeV7
    (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hS : SpliceSafeV7 hpsi ring C)
    (hO : OrphanVictimGuard (C e) (C (ring.rightNeighbor e))) :
    SpliceSafeV7 hpsi ring (orphanVictimClearAt ring C e) := by
  have hvictim : role (C (ring.rightNeighbor e)).carrier = .victimArmed := hO.1
  have hnotowner := hO.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro e' hd
    have hd0 := (vc_dangerAt_iff hpsi ring C e e').1 hd
    have hp := hS.1 e' hd0
    by_cases h1 : e' = ring.rightNeighbor e
    · -- the cleared victim is the left endpoint: it protected nothing there
      subst h1
      rcases hp with hv | hf
      · unfold R1ProtectedSpliceEdgeV3 at hv
        simp only [projectV6] at hv
        rcases hv with h1' | h2' | h3'
        · exact absurd h1'.1 (by rw [hvictim]; decide)
        · left
          unfold R1ProtectedSpliceEdgeV3
          simp only [projectV6]
          rw [vc_at_j]
          by_cases hself : ring.rightNeighbor (ring.rightNeighbor e) = ring.rightNeighbor e
          · rw [hself, vc_at_j]
            exact absurd h2'.1 (by rw [hself, hvictim]; decide)
          · rw [vc_at_other ring C e _ hself]
            exact Or.inr (Or.inl h2')
        · exact absurd h3'.1 (by rw [hvictim]; decide)
      · unfold HostFenceShapeV7 at hf
        exact absurd hf.1 (by rw [hvictim]; decide)
    · by_cases h2 : ring.rightNeighbor e' = ring.rightNeighbor e
      · have hee : e' = e := rightNeighbor_inj ring h2
        subst hee
        rcases hp with hv | hf
        · left
          unfold R1ProtectedSpliceEdgeV3 at hv ⊢
          simp only [projectV6] at hv ⊢
          rw [vc_at_other ring C e' e' h1, vc_at_j]
          rcases hv with h1' | h2' | h3'
          · exact Or.inl h1'
          · exact absurd h2'.1 (by rw [hvictim]; decide)
          · exact absurd ⟨h3'.1, h3'.2.1⟩ hnotowner
        · right
          rw [vc_at_other ring C e' e' h1]
          exact hf
      · unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3 at hp ⊢
        simp only [projectV6] at hp ⊢
        rw [vc_at_other ring C e e' h1, vc_at_other ring C e _ h2]
        exact hp
  · intro i
    by_cases h1 : i = ring.rightNeighbor e
    · rw [h1, vc_at_j]
      intro ht
      rw [clearControl_ticket] at ht
      exact absurd ht (by decide)
    · rw [vc_at_other ring C e i h1]
      exact hS.2.1 i
  · intro i hr hp
    by_cases h1 : i = ring.rightNeighbor e
    · rw [h1, vc_at_j, clearControl_role] at hr
      exact absurd hr (by decide)
    · rw [vc_at_other ring C e i h1] at hr hp
      by_cases h2 : ring.rightNeighbor i = ring.rightNeighbor e
      · have hie : i = e := rightNeighbor_inj ring h2
        subst hie
        have hb := hS.2.2 i hr hp
        exact absurd hb.1.1 (by rw [hvictim]; decide)
      · rw [vc_at_other ring C e _ h2]
        exact hS.2.2 i hr hp


/-! ## Third garbage class: a pending predecessor whose left neighbour is neutral.
It protects its incoming edge (disjunct 2), so it cannot be erased; instead the
neutral left cell becomes a fence (protecting that edge) and the predecessor is
settled (keeping the outgoing edge protected through disjunct 3 when its front
is reserved). -/

def OwnerlessPendingPredGuard (l r : R1AgentStateV6 psi kappa tau) : Prop :=
  role l.carrier = .none ∧ role r.carrier = .predecessorArmed ∧ r.carrier.repairPending = true

def settleV6 (u : R1AgentStateV6 psi kappa tau) : R1AgentStateV6 psi kappa tau :=
  setControlV6 u .predecessorArmed false

def fenceSettleAt (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    R1ConfigV6 n psi kappa tau :=
  fun i => if i = e then fenceV6 (C e)
    else if i = ring.rightNeighbor e then settleV6 (C (ring.rightNeighbor e)) else C i

theorem fs_at_e (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    fenceSettleAt ring C e e = fenceV6 (C e) := by simp [fenceSettleAt]

theorem fs_at_j (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    fenceSettleAt ring C e (ring.rightNeighbor e) = settleV6 (C (ring.rightNeighbor e)) := by
  simp [fenceSettleAt, hne]

theorem fs_at_other (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n)
    (h1 : i ≠ e) (h2 : i ≠ ring.rightNeighbor e) : fenceSettleAt ring C e i = C i := by
  simp [fenceSettleAt, h1, h2]

theorem fs_base_eq (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n) :
    (fenceSettleAt ring C e i).carrier.splice.base = (C i).carrier.splice.base := by
  unfold fenceSettleAt
  split
  · rename_i h; subst h; rfl
  · split
    · rename_i h; subst h; rfl
    · rfl

theorem fs_dangerAt_iff (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e e' : Fin n) :
    PreparedDangerAt hpsi ring (projectV6 (fenceSettleAt ring C e)) e' ↔
      PreparedDangerAt hpsi ring (projectV6 C) e' := by
  unfold PreparedDangerAt PreparedBarrierAt preparedR1 prepared projectSpliceConfig projectV6
  dsimp only
  rw [fs_base_eq, fs_base_eq]

theorem settle_role (u : R1AgentStateV6 psi kappa tau) :
    role (settleV6 u).carrier = .predecessorArmed := rfl
theorem settle_pending (u : R1AgentStateV6 psi kappa tau) :
    (settleV6 u).carrier.repairPending = false := rfl
theorem settle_ticket (u : R1AgentStateV6 psi kappa tau) :
    (settleV6 u).acquireTicket = false := rfl

theorem fenceSettle_preserves_spliceSafeV7
    (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hS : SpliceSafeV7 hpsi ring C)
    (hO : OwnerlessPendingPredGuard (C e) (C (ring.rightNeighbor e))) :
    SpliceSafeV7 hpsi ring (fenceSettleAt ring C e) := by
  have hlnone : role (C e).carrier = .none := hO.1
  have hrpred : role (C (ring.rightNeighbor e)).carrier = .predecessorArmed := hO.2.1
  have hrpend : (C (ring.rightNeighbor e)).carrier.repairPending = true := hO.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro e' hd
    have hd0 := (fs_dangerAt_iff hpsi ring C e e').1 hd
    have hp := hS.1 e' hd0
    by_cases h1 : e' = e
    · right
      rw [h1, fs_at_e]
      exact fence_shape _
    · by_cases h2 : e' = ring.rightNeighbor e
      · -- edge out of the settled predecessor
        subst h2
        rcases hp with hv | hf
        · unfold R1ProtectedSpliceEdgeV3 at hv
          simp only [projectV6] at hv
          rcases hv with h1' | h2' | h3'
          · exact absurd h1'.1 (by rw [hrpred]; decide)
          · by_cases h3 : ring.rightNeighbor (ring.rightNeighbor e) = e
            · rw [h3] at h2'
              exact absurd h2'.1 (by rw [hlnone]; decide)
            · left
              unfold R1ProtectedSpliceEdgeV3
              simp only [projectV6]
              have h5 : ring.rightNeighbor (ring.rightNeighbor e) ≠ ring.rightNeighbor e :=
                fun h => hne (rightNeighbor_inj ring h)
              rw [fs_at_j ring C e hne, fs_at_other ring C e _ h3 h5]
              exact Or.inr (Or.inl h2')
          · exact absurd h3'.2.1 (by rw [hrpend]; decide)
        · unfold HostFenceShapeV7 at hf
          exact absurd hf.1 (by rw [hrpred]; decide)
      · by_cases h3 : ring.rightNeighbor e' = e
        · -- edge into the fence: its left endpoint is unchanged and the old
          -- protection could only come from that endpoint
          rcases hp with hv | hf
          · left
            unfold R1ProtectedSpliceEdgeV3 at hv ⊢
            simp only [projectV6] at hv ⊢
            rw [fs_at_other ring C e e' h1 h2, h3, fs_at_e]
            rcases hv with h1' | h2' | h3'
            · exact Or.inl h1'
            · rw [h3] at h2'
              exact absurd h2'.1 (by rw [hlnone]; decide)
            · rw [h3] at h3'
              rcases h3'.2.2 with h4 | h4 | h4
              · exact absurd h4.1 (by rw [hlnone]; decide)
              · exact absurd h4.1 (by rw [hlnone]; decide)
              · exact absurd h4.1 (by rw [hlnone]; decide)
          · right
            rw [fs_at_other ring C e e' h1 h2]
            exact hf
        · by_cases h4 : ring.rightNeighbor e' = ring.rightNeighbor e
          · exact absurd (rightNeighbor_inj ring h4) h1
          · unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3 at hp ⊢
            simp only [projectV6] at hp ⊢
            rw [fs_at_other ring C e e' h1 h2, fs_at_other ring C e _ h3 h4]
            exact hp
  · intro i
    by_cases h1 : i = e
    · rw [h1, fs_at_e]; intro _; exact Or.inr (fence_shape _)
    · by_cases h2 : i = ring.rightNeighbor e
      · rw [h2, fs_at_j ring C e hne]
        intro ht
        rw [settle_ticket] at ht
        exact absurd ht (by decide)
      · rw [fs_at_other ring C e i h1 h2]
        exact hS.2.1 i
  · intro i hr hp
    by_cases h1 : i = e
    · rw [h1, fs_at_e] at hr
      have : role (fenceV6 (C e)).carrier = .none := rfl
      rw [this] at hr
      exact absurd hr (by decide)
    · by_cases h2 : i = ring.rightNeighbor e
      · rw [h2, fs_at_j ring C e hne, settle_pending] at hp
        exact absurd hp (by decide)
      · rw [fs_at_other ring C e i h1 h2] at hr hp
        by_cases h3 : ring.rightNeighbor i = e
        · have hb := hS.2.2 i hr hp
          rw [h3] at hb
          exact absurd hb.1.1 (by rw [hlnone]; decide)
        · by_cases h4 : ring.rightNeighbor i = ring.rightNeighbor e
          · exact absurd (rightNeighbor_inj ring h4) h1
          · rw [fs_at_other ring C e _ h3 h4]
            exact hS.2.2 i hr hp

/-! ## Ownerless pending predecessor, immediate-drop variant: fence the left host, clear the
predecessor.  The predecessor's reserved front (its right neighbour, by ProvenanceSafeV7)
becomes an orphan reserved front, which the orphan-front row then fences. -/

def fenceClearAt (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    R1ConfigV6 n psi kappa tau :=
  fun i => if i = e then fenceV6 (C e)
    else if i = ring.rightNeighbor e then clearControlV6 (C (ring.rightNeighbor e)) else C i

theorem fc_at_e (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    fenceClearAt ring C e e = fenceV6 (C e) := by simp [fenceClearAt]

theorem fc_at_j (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    fenceClearAt ring C e (ring.rightNeighbor e) = clearControlV6 (C (ring.rightNeighbor e)) := by
  simp [fenceClearAt, hne]

theorem fc_at_other (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n)
    (h1 : i ≠ e) (h2 : i ≠ ring.rightNeighbor e) : fenceClearAt ring C e i = C i := by
  simp [fenceClearAt, h1, h2]

theorem fc_base_eq (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n) :
    (fenceClearAt ring C e i).carrier.splice.base = (C i).carrier.splice.base := by
  unfold fenceClearAt
  split
  · rename_i h; subst h; rfl
  · split
    · rename_i h; subst h; rfl
    · rfl

theorem fc_dangerAt_iff (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e e' : Fin n) :
    PreparedDangerAt hpsi ring (projectV6 (fenceClearAt ring C e)) e' ↔
      PreparedDangerAt hpsi ring (projectV6 C) e' := by
  unfold PreparedDangerAt PreparedBarrierAt preparedR1 prepared projectSpliceConfig projectV6
  dsimp only
  rw [fc_base_eq, fc_base_eq]

theorem clear_role (u : R1AgentStateV6 psi kappa tau) :
    role (clearControlV6 u).carrier = .none := rfl
theorem clear_pending (u : R1AgentStateV6 psi kappa tau) :
    (clearControlV6 u).carrier.repairPending = false := rfl
theorem clear_ticket (u : R1AgentStateV6 psi kappa tau) :
    (clearControlV6 u).acquireTicket = false := rfl

theorem fenceClear_preserves_spliceSafeV7
    (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hS : SpliceSafeV7 hpsi ring C)
    (hO : OwnerlessPendingPredGuard (C e) (C (ring.rightNeighbor e))) :
    SpliceSafeV7 hpsi ring (fenceClearAt ring C e) := by
  have hlnone : role (C e).carrier = .none := hO.1
  have hrpred : role (C (ring.rightNeighbor e)).carrier = .predecessorArmed := hO.2.1
  have hrpend : (C (ring.rightNeighbor e)).carrier.repairPending = true := hO.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro e' hd
    have hd0 := (fc_dangerAt_iff hpsi ring C e e').1 hd
    have hp := hS.1 e' hd0
    by_cases h1 : e' = e
    · right
      rw [h1, fc_at_e]
      exact fence_shape _
    · by_cases h2 : e' = ring.rightNeighbor e
      · -- edge out of the settled predecessor
        subst h2
        rcases hp with hv | hf
        · unfold R1ProtectedSpliceEdgeV3 at hv
          simp only [projectV6] at hv
          rcases hv with h1' | h2' | h3'
          · exact absurd h1'.1 (by rw [hrpred]; decide)
          · by_cases h3 : ring.rightNeighbor (ring.rightNeighbor e) = e
            · rw [h3] at h2'
              exact absurd h2'.1 (by rw [hlnone]; decide)
            · left
              unfold R1ProtectedSpliceEdgeV3
              simp only [projectV6]
              have h5 : ring.rightNeighbor (ring.rightNeighbor e) ≠ ring.rightNeighbor e :=
                fun h => hne (rightNeighbor_inj ring h)
              rw [fc_at_j ring C e hne, fc_at_other ring C e _ h3 h5]
              exact Or.inr (Or.inl h2')
          · exact absurd h3'.2.1 (by rw [hrpend]; decide)
        · unfold HostFenceShapeV7 at hf
          exact absurd hf.1 (by rw [hrpred]; decide)
      · by_cases h3 : ring.rightNeighbor e' = e
        · -- edge into the fence: its left endpoint is unchanged and the old
          -- protection could only come from that endpoint
          rcases hp with hv | hf
          · left
            unfold R1ProtectedSpliceEdgeV3 at hv ⊢
            simp only [projectV6] at hv ⊢
            rw [fc_at_other ring C e e' h1 h2, h3, fc_at_e]
            rcases hv with h1' | h2' | h3'
            · exact Or.inl h1'
            · rw [h3] at h2'
              exact absurd h2'.1 (by rw [hlnone]; decide)
            · rw [h3] at h3'
              rcases h3'.2.2 with h4 | h4 | h4
              · exact absurd h4.1 (by rw [hlnone]; decide)
              · exact absurd h4.1 (by rw [hlnone]; decide)
              · exact absurd h4.1 (by rw [hlnone]; decide)
          · right
            rw [fc_at_other ring C e e' h1 h2]
            exact hf
        · by_cases h4 : ring.rightNeighbor e' = ring.rightNeighbor e
          · exact absurd (rightNeighbor_inj ring h4) h1
          · unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3 at hp ⊢
            simp only [projectV6] at hp ⊢
            rw [fc_at_other ring C e e' h1 h2, fc_at_other ring C e _ h3 h4]
            exact hp
  · intro i
    by_cases h1 : i = e
    · rw [h1, fc_at_e]; intro _; exact Or.inr (fence_shape _)
    · by_cases h2 : i = ring.rightNeighbor e
      · rw [h2, fc_at_j ring C e hne]
        intro ht
        rw [clear_ticket] at ht
        exact absurd ht (by decide)
      · rw [fc_at_other ring C e i h1 h2]
        exact hS.2.1 i
  · intro i hr hp
    by_cases h1 : i = e
    · rw [h1, fc_at_e] at hr
      have : role (fenceV6 (C e)).carrier = .none := rfl
      rw [this] at hr
      exact absurd hr (by decide)
    · by_cases h2 : i = ring.rightNeighbor e
      · rw [h2, fc_at_j ring C e hne, clear_pending] at hp
        exact absurd hp (by decide)
      · rw [fc_at_other ring C e i h1 h2] at hr hp
        by_cases h3 : ring.rightNeighbor i = e
        · have hb := hS.2.2 i hr hp
          rw [h3] at hb
          exact absurd hb.1.1 (by rw [hlnone]; decide)
        · by_cases h4 : ring.rightNeighbor i = ring.rightNeighbor e
          · exact absurd (rightNeighbor_inj ring h4) h1
          · rw [fc_at_other ring C e _ h3 h4]
            exact hS.2.2 i hr hp


/-! ## Owned pending victim: a settled predecessor whose right neighbour is a pending victim.
The pair is stuck in MoveSeekHold forever (the V6 abort clears only the ticket); both cells
become host fences. -/

def OwnedPendingVictimGuard (l r : R1AgentStateV6 psi kappa tau) : Prop :=
  role l.carrier = .predecessorArmed ∧ l.carrier.repairPending = false ∧
    role r.carrier = .victimArmed ∧ r.carrier.repairPending = true

def fenceFenceAt (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    R1ConfigV6 n psi kappa tau :=
  fun i => if i = e then fenceV6 (C e)
    else if i = ring.rightNeighbor e then fenceV6 (C (ring.rightNeighbor e)) else C i

theorem ff_at_e (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    fenceFenceAt ring C e e = fenceV6 (C e) := by simp [fenceFenceAt]

theorem ff_at_j (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    fenceFenceAt ring C e (ring.rightNeighbor e) = fenceV6 (C (ring.rightNeighbor e)) := by
  simp [fenceFenceAt, hne]

theorem ff_at_other (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n)
    (h1 : i ≠ e) (h2 : i ≠ ring.rightNeighbor e) : fenceFenceAt ring C e i = C i := by
  simp [fenceFenceAt, h1, h2]

theorem ff_base_eq (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n) :
    (fenceFenceAt ring C e i).carrier.splice.base = (C i).carrier.splice.base := by
  unfold fenceFenceAt
  split
  · rename_i h; subst h; rfl
  · split
    · rename_i h; subst h; rfl
    · rfl

theorem ff_dangerAt_iff (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e e' : Fin n) :
    PreparedDangerAt hpsi ring (projectV6 (fenceFenceAt ring C e)) e' ↔
      PreparedDangerAt hpsi ring (projectV6 C) e' := by
  unfold PreparedDangerAt PreparedBarrierAt preparedR1 prepared projectSpliceConfig projectV6
  dsimp only
  rw [ff_base_eq, ff_base_eq]

theorem fenceFence_preserves_spliceSafeV7
    (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hS : SpliceSafeV7 hpsi ring C)
    (hO : OwnedPendingVictimGuard (C e) (C (ring.rightNeighbor e))) :
    SpliceSafeV7 hpsi ring (fenceFenceAt ring C e) := by
  have hlpred : role (C e).carrier = .predecessorArmed := hO.1
  have hlset : (C e).carrier.repairPending = false := hO.2.1
  have hrvic : role (C (ring.rightNeighbor e)).carrier = .victimArmed := hO.2.2.1
  refine ⟨?_, ?_, ?_⟩
  · intro e' hd
    have hd0 := (ff_dangerAt_iff hpsi ring C e e').1 hd
    have hp := hS.1 e' hd0
    by_cases h1 : e' = e
    · right
      rw [h1, ff_at_e]
      exact fence_shape _
    · by_cases h2 : e' = ring.rightNeighbor e
      · right
        rw [h2, ff_at_j ring C e hne]
        exact fence_shape _
      · by_cases h3 : ring.rightNeighbor e' = e
        · -- edge into the left fence: the old protection could only come from its left endpoint
          rcases hp with hv | hf
          · left
            unfold R1ProtectedSpliceEdgeV3 at hv ⊢
            simp only [projectV6] at hv ⊢
            rw [ff_at_other ring C e e' h1 h2, h3, ff_at_e]
            rcases hv with h1' | h2' | h3'
            · exact Or.inl h1'
            · rw [h3] at h2'
              exact absurd h2'.2 (by rw [hlset]; decide)
            · rw [h3] at h3'
              rcases h3'.2.2 with h4 | h4 | h4
              · exact absurd h4.1 (by rw [hlpred]; decide)
              · exact absurd h4.1 (by rw [hlpred]; decide)
              · exact absurd h4.2 (by rw [hlset]; decide)
          · right
            rw [ff_at_other ring C e e' h1 h2]
            exact hf
        · by_cases h4 : ring.rightNeighbor e' = ring.rightNeighbor e
          · exact absurd (rightNeighbor_inj ring h4) h1
          · unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3 at hp ⊢
            simp only [projectV6] at hp ⊢
            rw [ff_at_other ring C e e' h1 h2, ff_at_other ring C e _ h3 h4]
            exact hp
  · intro i
    by_cases h1 : i = e
    · rw [h1, ff_at_e]; intro _; exact Or.inr (fence_shape _)
    · by_cases h2 : i = ring.rightNeighbor e
      · rw [h2, ff_at_j ring C e hne]; intro _; exact Or.inr (fence_shape _)
      · rw [ff_at_other ring C e i h1 h2]
        exact hS.2.1 i
  · intro i hr hp
    by_cases h1 : i = e
    · rw [h1, ff_at_e] at hr
      have : role (fenceV6 (C e)).carrier = .none := rfl
      rw [this] at hr
      exact absurd hr (by decide)
    · by_cases h2 : i = ring.rightNeighbor e
      · rw [h2, ff_at_j ring C e hne] at hr
        have : role (fenceV6 (C (ring.rightNeighbor e))).carrier = .none := rfl
        rw [this] at hr
        exact absurd hr (by decide)
      · rw [ff_at_other ring C e i h1 h2] at hr hp
        by_cases h3 : ring.rightNeighbor i = e
        · have hb := hS.2.2 i hr hp
          rw [h3] at hb
          exact absurd hb.1.1 (by rw [hlpred]; decide)
        · by_cases h4 : ring.rightNeighbor i = ring.rightNeighbor e
          · have hb := hS.2.2 i hr hp
            rw [h4] at hb
            exact absurd hb.1.1 (by rw [hrvic]; decide)
          · rw [ff_at_other ring C e _ h3 h4]
            exact hS.2.2 i hr hp


/-! ## Certificate-free right endpoints can be cleared.
Covers the V6 scrub rows that the fence and reservation HOLDs preempt: a non-pending victim
or front, and a malformed pending mark with role none. -/

def CertFreeV7 (r : R1AgentStateV6 psi kappa tau) : Prop :=
  ¬ ReservedFrontHoldGuard r.carrier ∧ role r.carrier ≠ .predecessorArmed ∧
    ¬ (role r.carrier = .victimArmed ∧ r.carrier.repairPending = true) ∧ ¬ HostFenceShapeV7 r

theorem certFreeClear_preserves_spliceSafeV7
    (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hS : SpliceSafeV7 hpsi ring C)
    (hF : CertFreeV7 (C (ring.rightNeighbor e))) :
    SpliceSafeV7 hpsi ring (orphanVictimClearAt ring C e) := by
  obtain ⟨hnf, hnp, hnv, hnfence⟩ := hF
  refine ⟨?_, ?_, ?_⟩
  · intro e' hd
    have hd0 := (vc_dangerAt_iff hpsi ring C e e').1 hd
    have hp := hS.1 e' hd0
    by_cases h1 : e' = ring.rightNeighbor e
    · subst h1
      rcases hp with hv | hf
      · unfold R1ProtectedSpliceEdgeV3 at hv
        simp only [projectV6] at hv
        rcases hv with h1' | h2' | h3'
        · exact absurd h1' hnf
        · left
          unfold R1ProtectedSpliceEdgeV3
          simp only [projectV6]
          rw [vc_at_j]
          by_cases hself : ring.rightNeighbor (ring.rightNeighbor e) = ring.rightNeighbor e
          · rw [hself] at h2'
            exact absurd h2'.1 hnp
          · rw [vc_at_other ring C e _ hself]
            exact Or.inr (Or.inl h2')
        · exact absurd h3'.1 hnp
      · exact absurd hf hnfence
    · by_cases h2 : ring.rightNeighbor e' = ring.rightNeighbor e
      · have hee : e' = e := rightNeighbor_inj ring h2
        subst hee
        rcases hp with hv | hf
        · left
          unfold R1ProtectedSpliceEdgeV3 at hv ⊢
          simp only [projectV6] at hv ⊢
          rw [vc_at_other ring C e' e' h1, vc_at_j]
          rcases hv with h1' | h2' | h3'
          · exact Or.inl h1'
          · exact absurd h2'.1 hnp
          · rcases h3'.2.2 with h4 | h4 | h4
            · exact absurd h4 hnf
            · exact absurd h4 hnv
            · exact absurd h4.1 hnp
        · right
          rw [vc_at_other ring C e' e' h1]
          exact hf
      · unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3 at hp ⊢
        simp only [projectV6] at hp ⊢
        rw [vc_at_other ring C e e' h1, vc_at_other ring C e _ h2]
        exact hp
  · intro i
    by_cases h1 : i = ring.rightNeighbor e
    · rw [h1, vc_at_j]
      intro ht
      rw [clearControl_ticket] at ht
      exact absurd ht (by decide)
    · rw [vc_at_other ring C e i h1]
      exact hS.2.1 i
  · intro i hr hp
    by_cases h1 : i = ring.rightNeighbor e
    · rw [h1, vc_at_j, clearControl_role] at hr
      exact absurd hr (by decide)
    · rw [vc_at_other ring C e i h1] at hr hp
      by_cases h2 : ring.rightNeighbor i = ring.rightNeighbor e
      · have hie : i = e := rightNeighbor_inj ring h2
        subst hie
        have hb := hS.2.2 i hr hp
        exact absurd hb.1 hnf
      · rw [vc_at_other ring C e _ h2]
        exact hS.2.2 i hr hp

end B9OrphanToFence
