import Leader.Wu.Splice.HostFenceTable
import Leader.Wu.Splice.OrphanToFence
import Leader.Wu.Splice.PhysicalHoldBirthSafe

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9SpliceLeaderlessSeamAbort

open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9OrphanToFence B9SpliceV10ePhysicalHoldNoBirth

variable {n psi width kappa tau : Nat}

/-- Leaderless MOVE-SEEK seam: both physical endpoints are followers. -/
def LeaderlessSeamAbortGuard
    (hpsi : 0 < psi) (_hwidth : 0 < width) (_hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) : Prop :=
  MoveSeekGuardV3 hpsi l.carrier r.carrier /\
    l.carrier.splice.base.core.core.leader = false /\
    r.carrier.splice.base.core.core.leader = false

/-- Execute the ordinary physical row, discard all old controller provenance,
and turn each follower output into a host fence.  A leader output is merely
controller-cleared. -/
def leaderlessSeamAbortWriteV6
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau :=
  let q := ordinaryRow hpsi hwidth hle l.carrier r.carrier
  let l0 : R1AgentStateV6 psi kappa tau := ⟨q.1, false⟩
  let r0 : R1AgentStateV6 psi kappa tau := ⟨q.2, false⟩
  (if q.1.splice.base.core.core.leader = false then
      fenceV6 l0
    else
      clearControlV6 l0,
   if q.2.splice.base.core.core.leader = false then
      fenceV6 r0
    else
      clearControlV6 r0)

/-- Configuration-level two-cell writer. -/
def abortAt
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    R1ConfigV6 n psi kappa tau :=
  let q := leaderlessSeamAbortWriteV6
    hpsi hwidth hle (C e) (C (ring.rightNeighbor e))
  fun i =>
    if i = e then q.1
    else if i = ring.rightNeighbor e then q.2
    else C i

/-- Potential fact requested for the row, stated without proof. -/
def LeaderlessSeamAbortWeightFact
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) : Prop :=
  let q := leaderlessSeamAbortWriteV6 hpsi hwidth hle l r
  controllerWeightV6 q.1 <= 1 /\ controllerWeightV6 q.2 <= 1

/-! ## Writer/configuration frame -/

theorem abortAt_e
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    abortAt hpsi hwidth hle ring C e e =
      (leaderlessSeamAbortWriteV6 hpsi hwidth hle
        (C e) (C (ring.rightNeighbor e))).1 := by
  simp [abortAt]

theorem abortAt_j
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    abortAt hpsi hwidth hle ring C e (ring.rightNeighbor e) =
      (leaderlessSeamAbortWriteV6 hpsi hwidth hle
        (C e) (C (ring.rightNeighbor e))).2 := by
  simp [abortAt, hne]

theorem abortAt_other
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e i : Fin n) (hie : i ≠ e) (hij : i ≠ ring.rightNeighbor e) :
    abortAt hpsi hwidth hle ring C e i = C i := by
  simp [abortAt, hie, hij]

theorem abortWrite_left_base
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    (leaderlessSeamAbortWriteV6 hpsi hwidth hle l r).1.carrier.splice.base =
      (BirthShortDoneTerminalHost.row hpsi hwidth hle
        l.carrier.splice.base r.carrier.splice.base).1 := by
  unfold leaderlessSeamAbortWriteV6 ordinaryRow
  dsimp only
  split <;> rfl

theorem abortWrite_right_base
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    (leaderlessSeamAbortWriteV6 hpsi hwidth hle l r).2.carrier.splice.base =
      (BirthShortDoneTerminalHost.row hpsi hwidth hle
        l.carrier.splice.base r.carrier.splice.base).2 := by
  unfold leaderlessSeamAbortWriteV6 ordinaryRow
  dsimp only
  split <;> rfl

theorem abortWrite_left_neutral
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    role (leaderlessSeamAbortWriteV6 hpsi hwidth hle l r).1.carrier = .none /\
      (leaderlessSeamAbortWriteV6 hpsi hwidth hle l r).1.carrier.repairPending = false := by
  unfold leaderlessSeamAbortWriteV6
  dsimp only
  split <;> exact ⟨rfl, rfl⟩

theorem abortWrite_right_neutral
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    role (leaderlessSeamAbortWriteV6 hpsi hwidth hle l r).2.carrier = .none /\
      (leaderlessSeamAbortWriteV6 hpsi hwidth hle l r).2.carrier.repairPending = false := by
  unfold leaderlessSeamAbortWriteV6
  dsimp only
  split <;> exact ⟨rfl, rfl⟩

theorem abortWrite_left_ticketShape
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    TicketShapeV7 (leaderlessSeamAbortWriteV6 hpsi hwidth hle l r).1 := by
  unfold TicketShapeV7
  unfold leaderlessSeamAbortWriteV6
  dsimp only
  split
  · intro _
    exact Or.inr (fence_shape _)
  · intro ht
    change (false : Bool) = true at ht
    exact False.elim ((by decide : (false : Bool) ≠ true) ht)

theorem abortWrite_right_ticketShape
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    TicketShapeV7 (leaderlessSeamAbortWriteV6 hpsi hwidth hle l r).2 := by
  unfold TicketShapeV7
  unfold leaderlessSeamAbortWriteV6
  dsimp only
  split
  · intro _
    exact Or.inr (fence_shape _)
  · intro ht
    change (false : Bool) = true at ht
    exact False.elim ((by decide : (false : Bool) ≠ true) ht)

theorem abortWrite_left_fence_of_follower
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hf : (leaderlessSeamAbortWriteV6 hpsi hwidth hle l r).1.carrier.splice.base.core.core.leader = false) :
    HostFenceShapeV7 (leaderlessSeamAbortWriteV6 hpsi hwidth hle l r).1 := by
  have hb := abortWrite_left_base hpsi hwidth hle l r
  have hp :
      (BirthShortDoneTerminalHost.row hpsi hwidth hle
        l.carrier.splice.base r.carrier.splice.base).1.core.core.leader = false :=
    (congrArg
      (fun b : ExpiringAgentState psi kappa tau => b.core.core.leader) hb).symm.trans hf
  unfold leaderlessSeamAbortWriteV6
  dsimp only
  have hq :
      (ordinaryRow hpsi hwidth hle l.carrier r.carrier).1.splice.base.core.core.leader = false := by
    unfold ordinaryRow; exact hp
  rw [if_pos hq]
  exact fence_shape _

theorem abortWrite_right_fence_of_follower
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hf : (leaderlessSeamAbortWriteV6 hpsi hwidth hle l r).2.carrier.splice.base.core.core.leader = false) :
    HostFenceShapeV7 (leaderlessSeamAbortWriteV6 hpsi hwidth hle l r).2 := by
  have hb := abortWrite_right_base hpsi hwidth hle l r
  have hp :
      (BirthShortDoneTerminalHost.row hpsi hwidth hle
        l.carrier.splice.base r.carrier.splice.base).2.core.core.leader = false :=
    (congrArg
      (fun b : ExpiringAgentState psi kappa tau => b.core.core.leader) hb).symm.trans hf
  unfold leaderlessSeamAbortWriteV6
  dsimp only
  have hq :
      (ordinaryRow hpsi hwidth hle l.carrier r.carrier).2.splice.base.core.core.leader = false := by
    unfold ordinaryRow; exact hp
  rw [if_pos hq]
  exact fence_shape _

theorem danger_congr_carrier_at
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C D : R1ConfigV6 n psi kappa tau) (x : Fin n)
    (hL : (D x).carrier = (C x).carrier)
    (hR : (D (ring.rightNeighbor x)).carrier =
      (C (ring.rightNeighbor x)).carrier) :
    PreparedDangerAt hpsi ring (projectV6 D) x <->
      PreparedDangerAt hpsi ring (projectV6 C) x := by
  unfold PreparedDangerAt PreparedBarrierAt projectSpliceConfig projectV6
  dsimp only
  rw [hL, hR]

/-! ## Preservation -/

theorem abort_preserves_spliceSafeV7
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hlead : forall i, (C i).carrier.splice.base.core.core.leader = false)
    (hS : SpliceSafeV7 hpsi ring C)
    (hne : ring.rightNeighbor e ≠ e)
    (hG : LeaderlessSeamAbortGuard hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e))) :
    SpliceSafeV7 hpsi ring (abortAt hpsi hwidth hle ring C e) := by
  let j := ring.rightNeighbor e
  let D := abortAt hpsi hwidth hle ring C e
  let w := leaderlessSeamAbortWriteV6 hpsi hwidth hle (C e) (C j)
  have hG' : LeaderlessSeamAbortGuard hpsi hwidth hle (C e) (C j) := by
    simpa only [j] using hG
  have hePred : role (C e).carrier = .predecessorArmed := hG'.1.1
  have hePend : (C e).carrier.repairPending = false := hG'.1.2.1
  have heLeader : (C e).carrier.splice.base.core.core.leader = false := hG'.2.1
  have hDe : D e = w.1 := by
    simpa only [D, w, j] using
      (abortAt_e hpsi hwidth hle ring C e)
  have hDj : D j = w.2 := by
    simpa only [D, w, j] using
      (abortAt_j hpsi hwidth hle ring C e hne)
  have hDother : forall i, i ≠ e -> i ≠ j -> D i = C i := by
    intro i hie hij
    simpa only [D, j] using
      (abortAt_other hpsi hwidth hle ring C e i hie
        (by simpa only [j] using hij))
  have hleftBase := abortWrite_left_base
    hpsi hwidth hle (C e) (C j)
  have hleftFrame :=
    B9SpliceV10ePhysicalHoldBirth.left_follower_label_frame
      hpsi hwidth hle
      (C e).carrier.splice.base (C j).carrier.splice.base heLeader
  have hleftLabel :
      (D e).carrier.splice.base.core.core.label =
        (C e).carrier.splice.base.core.core.label := by
    calc
      (D e).carrier.splice.base.core.core.label =
          w.1.carrier.splice.base.core.core.label :=
        congrArg
          (fun u : R1AgentStateV6 psi kappa tau =>
            u.carrier.splice.base.core.core.label) hDe
      _ =
          (BirthShortDoneTerminalHost.row hpsi hwidth hle
            (C e).carrier.splice.base (C j).carrier.splice.base).1.core.core.label :=
        congrArg
          (fun b : ExpiringAgentState psi kappa tau => b.core.core.label)
          hleftBase
      _ = (C e).carrier.splice.base.core.core.label := hleftFrame
  refine ⟨?_, ?_, ?_⟩
  · intro x hdx
    have hd := (danger_iff_physical hpsi ring D x).1 hdx
    by_cases hxe : x = e
    · subst x
      have hwFollower :
          w.1.carrier.splice.base.core.core.leader = false :=
        (congrArg
          (fun u : R1AgentStateV6 psi kappa tau =>
            u.carrier.splice.base.core.core.leader) hDe).symm.trans hd.1
      right
      rw [abortAt_e hpsi hwidth hle ring C e]
      simpa only [w] using
        (abortWrite_left_fence_of_follower
          hpsi hwidth hle (C e) (C j) hwFollower)
    · by_cases hxj : x = j
      · subst x
        have hwFollower :
            w.2.carrier.splice.base.core.core.leader = false :=
          (congrArg
            (fun u : R1AgentStateV6 psi kappa tau =>
              u.carrier.splice.base.core.core.leader) hDj).symm.trans hd.1
        right
        rw [abortAt_j hpsi hwidth hle ring C e hne]
        simpa only [w] using
          (abortWrite_right_fence_of_follower
            hpsi hwidth hle (C e) (C j) hwFollower)
      · have hDx : D x = C x := hDother x hxe hxj
        by_cases hye : ring.rightNeighbor x = e
        · have hxLabel :
              (D x).carrier.splice.base.core.core.label =
                (C x).carrier.splice.base.core.core.label :=
            congrArg
              (fun u : R1AgentStateV6 psi kappa tau =>
                u.carrier.splice.base.core.core.label) hDx
          have hdbar :
              (D e).carrier.splice.base.core.core.label ≠
                ⟨((D x).carrier.splice.base.core.core.label.val + 1) % psi,
                  Nat.mod_lt _ hpsi⟩ := by
            have hh := hd.2.2
            rw [hye] at hh
            exact hh
          have hbar :
              (C e).carrier.splice.base.core.core.label ≠
                ⟨((C x).carrier.splice.base.core.core.label.val + 1) % psi,
                  Nat.mod_lt _ hpsi⟩ := by
            intro hh
            apply hdbar
            calc
              (D e).carrier.splice.base.core.core.label =
                  (C e).carrier.splice.base.core.core.label := hleftLabel
              _ =
                  ⟨((C x).carrier.splice.base.core.core.label.val + 1) % psi,
                    Nat.mod_lt _ hpsi⟩ := hh
              _ =
                  ⟨((D x).carrier.splice.base.core.core.label.val + 1) % psi,
                    Nat.mod_lt _ hpsi⟩ :=
                congrArg
                  (fun a : Fin psi =>
                    (⟨(a.val + 1) % psi, Nat.mod_lt _ hpsi⟩ : Fin psi))
                  hxLabel.symm
          have hrightLeader :
              (C (ring.rightNeighbor x)).carrier.splice.base.core.core.leader = false := by
            rw [hye]
            exact heLeader
          have hd0 : PreparedDangerAt hpsi ring (projectV6 C) x :=
            (danger_iff_physical hpsi ring C x).2
              ⟨hlead x, hrightLeader,
                (by simpa only [hye] using hbar)⟩
          have hp0 := hS.1 x hd0
          change R1ProtectedSpliceEdgeV3 ring (projectV6 C) x \/
            HostFenceShapeV7 (C x) at hp0
          rcases hp0 with hv | hf
          · unfold R1ProtectedSpliceEdgeV3 at hv
            simp only [projectV6] at hv
            rcases hv with hleft | hright | hthird
            · left
              unfold R1ProtectedSpliceEdgeV3
              simp only [projectV6]
              left
              rw [abortAt_other hpsi hwidth hle ring C e x hxe hxj]
              exact hleft
            · rw [hye] at hright
              exact absurd hright.2 (by rw [hePend]; decide)
            · rw [hye] at hthird
              rcases hthird.2.2 with hfront | hvictim | hpred
              · exact absurd hfront.1 (by rw [hePred]; decide)
              · exact absurd hvictim.1 (by rw [hePred]; decide)
              · exact absurd hpred.2 (by rw [hePend]; decide)
          · right
            rw [abortAt_other hpsi hwidth hle ring C e x hxe hxj]
            exact hf
        · have hyj : ring.rightNeighbor x ≠ j := by
            intro hh
            apply hxe
            apply rightNeighbor_inj ring
            simpa only [j] using hh
          have hDy : D (ring.rightNeighbor x) = C (ring.rightNeighbor x) :=
            hDother (ring.rightNeighbor x) hye hyj
          have hL : (D x).carrier = (C x).carrier :=
            congrArg
              (fun u : R1AgentStateV6 psi kappa tau => u.carrier) hDx
          have hR :
              (D (ring.rightNeighbor x)).carrier =
                (C (ring.rightNeighbor x)).carrier :=
            congrArg
              (fun u : R1AgentStateV6 psi kappa tau => u.carrier) hDy
          have hd0 :=
            (danger_congr_carrier_at hpsi ring C D x hL hR).1 hdx
          have hp0 := hS.1 x hd0
          unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3 at hp0 ⊢
          simp only [projectV6] at hp0 ⊢
          rw [abortAt_other hpsi hwidth hle ring C e x hxe hxj,
            abortAt_other hpsi hwidth hle ring C e (ring.rightNeighbor x) hye hyj]
          exact hp0
  · intro i
    by_cases hie : i = e
    · subst i
      rw [abortAt_e hpsi hwidth hle ring C e]
      simpa only [w] using
        (abortWrite_left_ticketShape hpsi hwidth hle (C e) (C j))
    · by_cases hij : i = j
      · subst i
        rw [abortAt_j hpsi hwidth hle ring C e hne]
        simpa only [w] using
          (abortWrite_right_ticketShape hpsi hwidth hle (C e) (C j))
      · rw [abortAt_other hpsi hwidth hle ring C e i hie hij]
        exact hS.2.1 i
  · intro i hr hp
    by_cases hie : i = e
    · subst i
      rw [abortAt_e hpsi hwidth hle ring C e] at hr
      have hn := abortWrite_left_neutral hpsi hwidth hle (C e) (C j)
      exact absurd hr (by rw [hn.1]; decide)
    · by_cases hij : i = j
      · subst i
        rw [abortAt_j hpsi hwidth hle ring C e hne] at hr
        have hn := abortWrite_right_neutral hpsi hwidth hle (C e) (C j)
        exact absurd hr (by rw [hn.1]; decide)
      · rw [abortAt_other hpsi hwidth hle ring C e i hie hij] at hr hp
        have hold := hS.2.2 i hr hp
        by_cases hye : ring.rightNeighbor i = e
        · have hres : ReservedFrontHoldGuard (C e).carrier := by
            simpa only [hye] using hold.1
          exact absurd hres.1 (by rw [hePred]; decide)
        · by_cases hyj : ring.rightNeighbor i = j
          · have hie' : i = e := by
              apply rightNeighbor_inj ring
              simpa only [j] using hyj
            exact (hie hie').elim
          · rw [abortAt_other hpsi hwidth hle ring C e (ring.rightNeighbor i) hye hyj]
            exact hold

end B9SpliceLeaderlessSeamAbort
