import Leader.Wu.PartialProtocol.CollisionReset

/-!
# Zero-state serialized seal sweep

This module audits the transition-only proposal against the
accepted factor-four carrier.  The proposed `sealBit` is exactly the outer
Boolean of `SweepResetState`; no field is added.  The bit can be reused only by
giving its unsealed modes private overlay semantics.  Consequently this is a
separately named transition, not a definitional refinement of the accepted
unsealed `P_partialSweepReset` branch.

In the controlled all-sealed region, a sealed leader followed by a sealed
follower launches an unsealed anchor/probe pair.  The follower probe moves
clockwise through sealed followers, clears a sealed leader when it encounters
one, and reseals itself and the anchor when it returns.  Every unlisted pair is
identity.  Physical state is framed except for the already defined
`clearMinimalLockLeader` operation at an authenticated probe/leader collision.

Two theorem boundaries are proved.  First, every all-sealed unique-leader
configuration is Definition-1 safe under every schedule, although the literal
all-sealed predicate is not closed.  Second, a serialized clockwise word of
exact length `n` clears every leader except a chosen source, provided the
source is initially sealed and its successor is a follower.  This includes
all separated multi-leader configurations.  No universal fair-scheduler
convergence claim is made; concurrent sweeps remain outside the theorem.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepOverlaySol

open PPLL PPLLResearchFormulation
  PPLLNoCheckBirthConditionTwoGeometry
open PPLLStaticDoubleCoverNoGo
open PPartialMinimalLockRepairSol
open PPartialDynamicSweepLockSol
open PPartialDynamicSweepResetSol

set_option autoImplicit false

variable {n psi kappa tau : Nat}

/-! ## Exact carrier and executable overlay -/

/-- No new state: this is exactly the accepted factor-four carrier. -/
abbrev SealSweepState (psi kappa tau : Nat) :=
  SweepResetState psi kappa tau

abbrev SealSweepConfig (n psi kappa tau : Nat) :=
  Fin n → SealSweepState psi kappa tau

/-- The private five-case overlay.  The Boolean tuple is
`(leftLeader,leftClosed,rightLeader,rightClosed)`. -/
def P_partialSealSweep
    (l r : SealSweepState psi kappa tau) :
    SealSweepState psi kappa tau × SealSweepState psi kappa tau :=
  match sweepLockLeader l, l.2, sweepLockLeader r, r.2 with
  | true, true, true, true =>
      ((l.1, true), (clearMinimalLockLeader r.1, true))
  | true, true, false, true =>
      ((l.1, false), (r.1, false))
  | false, false, false, true =>
      ((l.1, true), (r.1, false))
  | false, false, true, true =>
      ((l.1, true), (clearMinimalLockLeader r.1, false))
  | false, false, true, false =>
      ((l.1, true), (r.1, true))
  | _, _, _, _ => (l, r)

/-- Packaged protocol.  Output ignores the commandeered control bit. -/
def P_partialSealSweepProtocol
    (psi kappa tau : Nat) : PopulationProtocol where
  Q := SealSweepState psi kappa tau
  Y := LeaderOutput
  transition := P_partialSealSweep
  output := fun s =>
    if sweepLockLeader s then LeaderOutput.leader
    else LeaderOutput.follower

/-- Physical bounded-domain closure is inherited from the unchanged carrier. -/
theorem P_partialSealSweep_output_inProtocolDomain
    (l r : SealSweepState psi kappa tau) :
    let q := P_partialSealSweep l r
    q.1.1.1.core.erase.core.inProtocolDomain kappa ∧
      q.2.1.1.core.erase.core.inProtocolDomain kappa := by
  let q := P_partialSealSweep l r
  exact ⟨q.1.1.1.core.core.erase_inProtocolDomain,
    q.2.1.1.core.core.erase_inProtocolDomain⟩

theorem P_partialSealSweep_launch
    (l r : SealSweepState psi kappa tau)
    (hl : sweepLockLeader l = true) (hlc : l.2 = true)
    (hr : sweepLockLeader r = false) (hrc : r.2 = true) :
    P_partialSealSweep l r =
      ((l.1, false), (r.1, false)) := by
  simp [P_partialSealSweep, hl, hlc, hr, hrc]

theorem P_partialSealSweep_advance
    (l r : SealSweepState psi kappa tau)
    (hl : sweepLockLeader l = false) (hlc : l.2 = false)
    (hr : sweepLockLeader r = false) (hrc : r.2 = true) :
    P_partialSealSweep l r =
      ((l.1, true), (r.1, false)) := by
  simp [P_partialSealSweep, hl, hlc, hr, hrc]

theorem P_partialSealSweep_collision
    (l r : SealSweepState psi kappa tau)
    (hl : sweepLockLeader l = false) (hlc : l.2 = false)
    (hr : sweepLockLeader r = true) (hrc : r.2 = true) :
    P_partialSealSweep l r =
      ((l.1, true), (clearMinimalLockLeader r.1, false)) := by
  simp [P_partialSealSweep, hl, hlc, hr, hrc]

theorem P_partialSealSweep_return
    (l r : SealSweepState psi kappa tau)
    (hl : sweepLockLeader l = false) (hlc : l.2 = false)
    (hr : sweepLockLeader r = true) (hrc : r.2 = false) :
    P_partialSealSweep l r =
      ((l.1, true), (r.1, true)) := by
  simp [P_partialSealSweep, hl, hlc, hr, hrc]

theorem P_partialSealSweep_twoClosedLeaders
    (l r : SealSweepState psi kappa tau)
    (hl : sweepLockLeader l = true) (hlc : l.2 = true)
    (hr : sweepLockLeader r = true) (hrc : r.2 = true) :
    P_partialSealSweep l r =
      ((l.1, true), (clearMinimalLockLeader r.1, true)) := by
  simp [P_partialSealSweep, hl, hlc, hr, hrc]

/-- A closed follower initiator is inert against every responder. -/
theorem P_partialSealSweep_eq_self_of_leftClosedFollower
    (l r : SealSweepState psi kappa tau)
    (hl : sweepLockLeader l = false) (hlc : l.2 = true) :
    P_partialSealSweep l r = (l, r) := by
  cases hr : sweepLockLeader r <;> cases hrc : r.2 <;>
    simp [P_partialSealSweep, hl, hlc, hr, hrc]

/-- An unclosed leader initiator is inert against every responder. -/
theorem P_partialSealSweep_eq_self_of_leftOpenLeader
    (l r : SealSweepState psi kappa tau)
    (hl : sweepLockLeader l = true) (hlc : l.2 = false) :
    P_partialSealSweep l r = (l, r) := by
  cases hr : sweepLockLeader r <;> cases hrc : r.2 <;>
    simp [P_partialSealSweep, hl, hlc, hr, hrc]

private theorem sealSweep_step_eq_of_pair_eq
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau) (e : Fin n)
    (hpair : P_partialSealSweep (C e) (C (ring.rightNeighbor e)) =
      (C e, C (ring.rightNeighbor e))) :
    localStep ring P_partialSealSweep C e = C := by
  funext i
  by_cases hie : i = e
  · subst i
    simp [localStep, hpair]
  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      simp [localStep, hie, hpair]
    · simp [localStep, hie, hij, hpair]

/-! ## Exact local wave effects -/

theorem sealSweep_localStep_launch
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SealSweepConfig n psi kappa tau) (e : Fin n)
    (hl : sweepLockLeader (C e) = true)
    (hlc : (C e).2 = true)
    (hr : sweepLockLeader (C (ring.rightNeighbor e)) = false)
    (hrc : (C (ring.rightNeighbor e)).2 = true) :
    let D := localStep ring P_partialSealSweep C e
    D e = ((C e).1, false) ∧
      D (ring.rightNeighbor e) =
        ((C (ring.rightNeighbor e)).1, false) ∧
      ∀ i : Fin n, i ≠ e → i ≠ ring.rightNeighbor e →
        D i = C i := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  have hpair : P_partialSealSweep (C e) (C j) =
      (((C e).1, false), ((C j).1, false)) :=
    P_partialSealSweep_launch (C e) (C j)
      hl hlc (by simpa [j] using hr) (by simpa [j] using hrc)
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simp [localStep, j, hpair]
  · simp [localStep, j, hpair, hje]
  · intro i hie hij
    simp [localStep, j, hpair, hie, hij]

/-- A genuine follower probe crosses either kind of closed responder.  The
old probe is closed and the responder becomes a follower probe. -/
theorem sealSweep_localStep_probe_closed
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SealSweepConfig n psi kappa tau) (e : Fin n)
    (hl : sweepLockLeader (C e) = false)
    (hlc : (C e).2 = false)
    (hrc : (C (ring.rightNeighbor e)).2 = true) :
    let D := localStep ring P_partialSealSweep C e
    D e = ((C e).1, true) ∧
      (D (ring.rightNeighbor e)).2 = false ∧
      sweepLockLeader (D (ring.rightNeighbor e)) = false ∧
      ∀ i : Fin n, i ≠ e → i ≠ ring.rightNeighbor e →
        D i = C i := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  cases hr : sweepLockLeader (C j) with
  | false =>
      have hpair : P_partialSealSweep (C e) (C j) =
          (((C e).1, true), ((C j).1, false)) :=
        P_partialSealSweep_advance (C e) (C j)
          hl hlc hr (by simpa [j] using hrc)
      dsimp only
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [localStep, j, hpair]
      · simp [localStep, j, hpair, hje]
      · simpa [localStep, j, hpair, hje, sweepLockLeader] using hr
      · intro i hie hij
        simp [localStep, j, hpair, hie, hij]
  | true =>
      have hpair : P_partialSealSweep (C e) (C j) =
          (((C e).1, true),
            (clearMinimalLockLeader (C j).1, false)) :=
        P_partialSealSweep_collision (C e) (C j)
          hl hlc hr (by simpa [j] using hrc)
      dsimp only
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [localStep, j, hpair]
      · simp [localStep, j, hpair, hje]
      · simp [localStep, j, hpair, hje, sweepLockLeader]
      · intro i hie hij
        simp [localStep, j, hpair, hie, hij]

theorem sealSweep_localStep_return
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SealSweepConfig n psi kappa tau) (e : Fin n)
    (hl : sweepLockLeader (C e) = false)
    (hlc : (C e).2 = false)
    (hr : sweepLockLeader (C (ring.rightNeighbor e)) = true)
    (hrc : (C (ring.rightNeighbor e)).2 = false) :
    let D := localStep ring P_partialSealSweep C e
    D e = ((C e).1, true) ∧
      D (ring.rightNeighbor e) =
        ((C (ring.rightNeighbor e)).1, true) ∧
      ∀ i : Fin n, i ≠ e → i ≠ ring.rightNeighbor e →
        D i = C i := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  have hpair : P_partialSealSweep (C e) (C j) =
      (((C e).1, true), ((C j).1, true)) :=
    P_partialSealSweep_return (C e) (C j)
      hl hlc (by simpa [j] using hr) (by simpa [j] using hrc)
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simp [localStep, j, hpair]
  · simp [localStep, j, hpair, hje]
  · intro i hie hij
    simp [localStep, j, hpair, hie, hij]

/-! ## All-schedule safety of a unique source -/

def SealSweepAllClosed
    (C : SealSweepConfig n psi kappa tau) : Prop :=
  ∀ i : Fin n, (C i).2 = true

/-- The only nonquiescent shape reachable from a clean singleton launch. -/
def SealSweepActive
    (C : SealSweepConfig n psi kappa tau) : Prop :=
  ∃ anchor probe : Fin n,
    anchor ≠ probe ∧
      sweepLockLeader (C anchor) = true ∧
      (C anchor).2 = false ∧
      sweepLockLeader (C probe) = false ∧
      (C probe).2 = false ∧
      ∀ i : Fin n, i ≠ anchor → i ≠ probe → (C i).2 = true

/-- Operational safety mode.  Unlike the previous kernel, it deliberately
allows one causally generated open anchor/probe pair. -/
def SealSweepLegitMode
    (C : SealSweepConfig n psi kappa tau) : Prop :=
  UniqueLeaderOutput
      (P_partialSealSweepProtocol psi kappa tau) n C isLeaderOutput ∧
    (SealSweepAllClosed C ∨ SealSweepActive C)

private theorem sealSweep_output_leader_true
    (u : SealSweepState psi kappa tau)
    (hu : sweepLockLeader u = true) :
    isLeaderOutput
      ((P_partialSealSweepProtocol psi kappa tau).output u) = true := by
  change isLeaderOutput
    (if sweepLockLeader u then LeaderOutput.leader
      else LeaderOutput.follower) = true
  rw [hu]
  rfl

private theorem sealSweep_unique_of_output_eq
    (C D : SealSweepConfig n psi kappa tau)
    (hC : UniqueLeaderOutput
      (P_partialSealSweepProtocol psi kappa tau) n C isLeaderOutput)
    (hout : ∀ i : Fin n,
      (P_partialSealSweepProtocol psi kappa tau).output (D i) =
        (P_partialSealSweepProtocol psi kappa tau).output (C i)) :
    UniqueLeaderOutput
      (P_partialSealSweepProtocol psi kappa tau) n D isLeaderOutput := by
  obtain ⟨root, hroot, honly⟩ := hC
  refine ⟨root, ?_, ?_⟩
  · rw [hout root]
    exact hroot
  · intro i hi
    apply honly i
    rw [← hout i]
    exact hi

private theorem sealSweep_output_eq_of_leader_eq
    (u v : SealSweepState psi kappa tau)
    (h : sweepLockLeader u = sweepLockLeader v) :
    (P_partialSealSweepProtocol psi kappa tau).output u =
      (P_partialSealSweepProtocol psi kappa tau).output v := by
  change (if sweepLockLeader u then LeaderOutput.leader
      else LeaderOutput.follower) =
    (if sweepLockLeader v then LeaderOutput.leader
      else LeaderOutput.follower)
  rw [h]

private theorem distinct_fin_implies_nontrivial
    {a b : Fin n} (hab : a ≠ b) : 1 < n := by
  have hv : a.val ≠ b.val := by
    intro h
    exact hab (Fin.ext h)
  have ha := a.isLt
  have hb := b.isLt
  omega

/-! The closedness proof follows after the local mode transition theorem. -/

/-- One local interaction preserves the safety mode and the complete output
vector.  This is the all-schedules core of the repair. -/
theorem sealSweepLegitMode_localStep
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hC : SealSweepLegitMode C) (e : Fin n) :
    let D := localStep ring P_partialSealSweep C e
    SealSweepLegitMode D ∧
      ∀ i : Fin n,
        (P_partialSealSweepProtocol psi kappa tau).output (D i) =
          (P_partialSealSweepProtocol psi kappa tau).output (C i) := by
  dsimp only
  let j := ring.rightNeighbor e
  let D := localStep ring P_partialSealSweep C e
  change SealSweepLegitMode D ∧
    ∀ i : Fin n,
      (if sweepLockLeader (D i) then LeaderOutput.leader
        else LeaderOutput.follower) =
      (if sweepLockLeader (C i) then LeaderOutput.leader
        else LeaderOutput.follower)
  rcases hC with ⟨hunique, hclosed | hactive⟩
  · cases he : sweepLockLeader (C e) with
    | false =>
        have hpair : P_partialSealSweep (C e) (C j) = (C e, C j) :=
          P_partialSealSweep_eq_self_of_leftClosedFollower
            (C e) (C j) he (hclosed e)
        have hDC : D = C := by
          exact sealSweep_step_eq_of_pair_eq ring C e
            (by simpa [j] using hpair)
        rw [hDC]
        exact ⟨⟨hunique, Or.inl hclosed⟩, fun _ => rfl⟩
    | true =>
        cases hj : sweepLockLeader (C j) with
        | true =>
            obtain ⟨root, hroot, honly⟩ := hunique
            have heroot : e = root := honly e
              (sealSweep_output_leader_true (C e) he)
            have hjroot : j = root := honly j
              (sealSweep_output_leader_true (C j) hj)
            have hjeq : j = e := hjroot.trans heroot.symm
            have hpair : P_partialSealSweep (C e) (C j) =
                (((C e).1, true),
                  (clearMinimalLockLeader (C j).1, true)) :=
              P_partialSealSweep_twoClosedLeaders
                (C e) (C j) he (hclosed e) hj (hclosed j)
            have hleft : ((C e).1, true) = C e :=
              Prod.ext rfl (hclosed e).symm
            have hDC : D = C := by
              funext i
              change (if i = e then
                  (P_partialSealSweep (C e) (C j)).1
                else if i = j then
                  (P_partialSealSweep (C e) (C j)).2
                else C i) = C i
              rw [hpair]
              by_cases hie : i = e
              · subst i
                simpa using hleft
              · simp [hie, hjeq]
            rw [hDC]
            exact ⟨⟨⟨root, hroot, honly⟩, Or.inl hclosed⟩,
              fun _ => rfl⟩
        | false =>
            have hje : j ≠ e := by
              intro h
              have hb := congrArg (fun x => sweepLockLeader (C x)) h
              rw [hj, he] at hb
              contradiction
            have hn : 1 < n := distinct_fin_implies_nontrivial hje
            have hedge := sealSweep_localStep_launch
              ring hn C e he (hclosed e)
                (by simpa [j] using hj) (hclosed j)
            change D e = ((C e).1, false) ∧
                D j = ((C j).1, false) ∧
                ∀ i : Fin n, i ≠ e → i ≠ j → D i = C i at hedge
            have hout : ∀ i : Fin n,
                (P_partialSealSweepProtocol psi kappa tau).output (D i) =
                  (P_partialSealSweepProtocol psi kappa tau).output (C i) := by
              intro i
              by_cases hie : i = e
              · subst i
                rw [hedge.1]
                exact sealSweep_output_eq_of_leader_eq _ _ rfl
              · by_cases hij : i = j
                · subst i
                  rw [hedge.2.1]
                  exact sealSweep_output_eq_of_leader_eq _ _ rfl
                · rw [hedge.2.2 i hie hij]
            have hDunique := sealSweep_unique_of_output_eq
              C D hunique hout
            have hactiveD : SealSweepActive D := by
              refine ⟨e, j, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · exact hje.symm
              · rw [hedge.1]
                exact he
              · exact congrArg (fun u => u.2) hedge.1
              · rw [hedge.2.1]
                exact hj
              · exact congrArg (fun u => u.2) hedge.2.1
              · intro i hie hij
                rw [hedge.2.2 i hie hij]
                exact hclosed i
            exact ⟨⟨hDunique, Or.inr hactiveD⟩, hout⟩
  · rcases hactive with
      ⟨anchor, probe, hanchorProbe, hanchorLeader, hanchorOpen,
        hprobeFollower, hprobeOpen, hotherClosed⟩
    have hn : 1 < n := distinct_fin_implies_nontrivial hanchorProbe
    have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
    obtain ⟨root, hroot, honly⟩ := hunique
    have hanchorRoot : anchor = root := honly anchor
      (sealSweep_output_leader_true (C anchor) hanchorLeader)
    by_cases hep : e = probe
    · subst e
      by_cases hja : j = anchor
      · have hedge := sealSweep_localStep_return
          ring hn C probe hprobeFollower hprobeOpen
            (by simpa [j, hja] using hanchorLeader)
            (by simpa [j, hja] using hanchorOpen)
        change D probe = ((C probe).1, true) ∧
            D j = ((C j).1, true) ∧
            ∀ i : Fin n, i ≠ probe → i ≠ j → D i = C i at hedge
        have hout : ∀ i : Fin n,
            (P_partialSealSweepProtocol psi kappa tau).output (D i) =
              (P_partialSealSweepProtocol psi kappa tau).output (C i) := by
          intro i
          by_cases hip : i = probe
          · subst i
            rw [hedge.1]
            exact sealSweep_output_eq_of_leader_eq _ _ rfl
          · by_cases hij : i = j
            · subst i
              rw [hedge.2.1]
              exact sealSweep_output_eq_of_leader_eq _ _ rfl
            · rw [hedge.2.2 i hip hij]
        have hDclosed : SealSweepAllClosed D := by
          intro i
          by_cases hip : i = probe
          · subst i
            exact congrArg (fun u => u.2) hedge.1
          · by_cases hij : i = j
            · subst i
              exact congrArg (fun u => u.2) hedge.2.1
            · rw [hedge.2.2 i hip hij]
              apply hotherClosed i
              · intro hia
                apply hij
                exact hia.trans hja.symm
              · exact hip
        exact ⟨⟨sealSweep_unique_of_output_eq C D
          ⟨root, hroot, honly⟩ hout,
          Or.inl hDclosed⟩, hout⟩
      · have hjp : j ≠ probe := hje
        have hjClosed : (C j).2 = true :=
          hotherClosed j hja hjp
        have hjFollower : sweepLockLeader (C j) = false := by
          cases hj : sweepLockLeader (C j) with
          | false => rfl
          | true =>
              have hjroot : j = root := honly j
                (sealSweep_output_leader_true (C j) hj)
              exact (hja (hjroot.trans hanchorRoot.symm)).elim
        have hedge := sealSweep_localStep_probe_closed
          ring hn C probe hprobeFollower hprobeOpen hjClosed
        change D probe = ((C probe).1, true) ∧
            (D j).2 = false ∧
            sweepLockLeader (D j) = false ∧
            ∀ i : Fin n, i ≠ probe → i ≠ j → D i = C i at hedge
        have hout : ∀ i : Fin n,
            (P_partialSealSweepProtocol psi kappa tau).output (D i) =
              (P_partialSealSweepProtocol psi kappa tau).output (C i) := by
          intro i
          by_cases hip : i = probe
          · subst i
            rw [hedge.1]
            exact sealSweep_output_eq_of_leader_eq _ _ rfl
          · by_cases hij : i = j
            · subst i
              exact sealSweep_output_eq_of_leader_eq _ _
                (hedge.2.2.1.trans hjFollower.symm)
            · rw [hedge.2.2.2 i hip hij]
        have hactiveD : SealSweepActive D := by
          refine ⟨anchor, j, Ne.symm hja, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hedge.2.2.2 anchor hanchorProbe (Ne.symm hja)]
            exact hanchorLeader
          · rw [hedge.2.2.2 anchor hanchorProbe (Ne.symm hja)]
            exact hanchorOpen
          · exact hedge.2.2.1
          · exact hedge.2.1
          · intro i hia hij
            by_cases hip : i = probe
            · subst i
              exact congrArg (fun u => u.2) hedge.1
            · rw [hedge.2.2.2 i hip hij]
              exact hotherClosed i hia hip
        exact ⟨⟨sealSweep_unique_of_output_eq C D
          ⟨root, hroot, honly⟩ hout,
          Or.inr hactiveD⟩, hout⟩
    · have hpair : P_partialSealSweep (C e) (C j) = (C e, C j) := by
        by_cases hea : e = anchor
        · subst e
          exact P_partialSealSweep_eq_self_of_leftOpenLeader
            (C anchor) (C j) hanchorLeader hanchorOpen
        · have heClosed : (C e).2 = true := hotherClosed e hea hep
          have heFollower : sweepLockLeader (C e) = false := by
            cases hel : sweepLockLeader (C e) with
            | false => rfl
            | true =>
                have heroot : e = root := honly e
                  (sealSweep_output_leader_true (C e) hel)
                exact (hea (heroot.trans hanchorRoot.symm)).elim
          exact P_partialSealSweep_eq_self_of_leftClosedFollower
            (C e) (C j) heFollower heClosed
      have hDC : D = C :=
        sealSweep_step_eq_of_pair_eq ring C e
          (by simpa [j] using hpair)
      rw [hDC]
      exact ⟨⟨⟨root, hroot, honly⟩,
        Or.inr ⟨anchor, probe, hanchorProbe, hanchorLeader,
          hanchorOpen, hprobeFollower, hprobeOpen, hotherClosed⟩⟩,
        fun _ => rfl⟩

/-- The two-mode predicate is closed under the packaged protocol. -/
theorem sealSweepLegitMode_closed
    (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred
      (P_partialSealSweepProtocol psi kappa tau) ring
      SealSweepLegitMode := by
  intro C hC D hstep
  obtain ⟨e, rfl⟩ := hstep
  exact (sealSweepLegitMode_localStep ring C hC e).1

/-- Every step in the two-mode predicate preserves every site output. -/
theorem sealSweepLegitMode_stepOutput
    (ring : DirectedRing n) :
    StepOutputPreservingOn
      (P_partialSealSweepProtocol psi kappa tau) ring
      SealSweepLegitMode := by
  intro C hC D hstep i
  obtain ⟨e, rfl⟩ := hstep
  exact (sealSweepLegitMode_localStep ring C hC e).2 i

/-- Every clean all-closed singleton belongs to the operational mode. -/
theorem allClosedUnique_mem_sealSweepLegitMode
    (C : SealSweepConfig n psi kappa tau)
    (hclosed : SealSweepAllClosed C)
    (hunique : UniqueLeaderOutput
      (P_partialSealSweepProtocol psi kappa tau) n C isLeaderOutput) :
    SealSweepLegitMode C :=
  ⟨hunique, Or.inl hclosed⟩

/-- Main all-schedules safety statement: commandeering the bit does not move or
delete the unique output at any site. -/
theorem allClosedUnique_isSafe
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hclosed : SealSweepAllClosed C)
    (hunique : UniqueLeaderOutput
      (P_partialSealSweepProtocol psi kappa tau) n C isLeaderOutput) :
    PopulationProtocol.IsSafe
      (P_partialSealSweepProtocol psi kappa tau)
      ring C isLeaderOutput := by
  exact isSafe_of_operational_legitimacy
    (P_partialSealSweepProtocol psi kappa tau) ring isLeaderOutput
    SealSweepLegitMode
    (sealSweepLegitMode_closed ring)
    (fun _ h => h.1)
    (sealSweepLegitMode_stepOutput ring)
    (allClosedUnique_mem_sealSweepLegitMode C hclosed hunique)

/-! ## Serialized clockwise sweep -/

theorem P_partialSealSweep_runLocalSchedule_reachable
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (word : DetSchedule n) :
    PopulationProtocol.Reachable
      (P_partialSealSweepProtocol psi kappa tau) ring C
      (runLocalSchedule ring P_partialSealSweep C word) := by
  induction word generalizing C with
  | nil =>
      exact @PopulationProtocol.Reachable.refl n
        (P_partialSealSweepProtocol psi kappa tau) ring C
  | cons e rest ih =>
      exact (PopulationProtocol.OneStep.to_reachable ⟨e, rfl⟩).trans
        (ih (localStep ring P_partialSealSweep C e))

private theorem cwPos_ne_of_ne_below_sealSweep
    (ring : DirectedRing n) (start : Fin n)
    {a b : Nat} (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    cwPos ring start a ≠ cwPos ring start b := by
  intro hpos
  apply hab
  have ha' := cwPos_bounded_unique ring start
    (cwPos ring start a) a ha rfl
  have hb' := cwPos_bounded_unique ring start
    (cwPos ring start a) b hb hpos.symm
  exact ha'.trans hb'.symm

/-- Exact proper-prefix invariant for the serialized word.  The source is an
open leader, the current positive offset is the unique open follower probe,
all earlier positive offsets are closed followers, and all later offsets are
still their initial closed states. -/
theorem sealSweep_clockwise_prefix
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SealSweepConfig n psi kappa tau) (seed : Fin n)
    (hclosed : SealSweepAllClosed C)
    (hseed : sweepLockLeader (C seed) = true)
    (hsucc : sweepLockLeader (C (ring.rightNeighbor seed)) = false)
    (steps : Nat) (hpos : 0 < steps) (hlt : steps < n) :
    let D := runLocalSchedule ring P_partialSealSweep C
      (clockwiseEdgeSchedule ring seed steps)
    D seed = ((C seed).1, false) ∧
      sweepLockLeader (D (cwPos ring seed steps)) = false ∧
      (D (cwPos ring seed steps)).2 = false ∧
      (∀ k : Nat, 0 < k → k < steps →
        sweepLockLeader (D (cwPos ring seed k)) = false ∧
          (D (cwPos ring seed k)).2 = true) ∧
      (∀ k : Nat, steps < k → k < n →
        D (cwPos ring seed k) = C (cwPos ring seed k)) := by
  induction steps with
  | zero => omega
  | succ s ih =>
      cases s with
      | zero =>
          let e := seed
          let j := ring.rightNeighbor e
          have hedge := sealSweep_localStep_launch
            ring hn C e hseed (hclosed e)
              (by simpa [e, j] using hsucc) (hclosed j)
          have hrun :
              runLocalSchedule ring P_partialSealSweep C
                  (clockwiseEdgeSchedule ring seed 1) =
                localStep ring P_partialSealSweep C e := by
            simp [clockwiseEdgeSchedule, runLocalSchedule, e]
          rw [hrun]
          have hjpos : j = cwPos ring seed 1 := by
            simpa [j, e] using (cwPos_succ ring seed 0).symm
          constructor
          · simpa [e] using hedge.1
          constructor
          · rw [← hjpos]
            have hjstate := hedge.2.1
            rw [hjstate]
            exact hsucc
          constructor
          · rw [← hjpos]
            exact congrArg (fun u => u.2) hedge.2.1
          constructor
          · intro k hk hklt
            omega
          · intro k hk hkn
            have hke : cwPos ring seed k ≠ e := by
              simpa [e] using cwPos_ne_of_ne_below_sealSweep
                ring seed hkn (by omega : 0 < n) (by omega)
            have hkj : cwPos ring seed k ≠ j := by
              rw [hjpos]
              exact cwPos_ne_of_ne_below_sealSweep
                ring seed hkn (by omega) (by omega)
            exact hedge.2.2 (cwPos ring seed k) hke hkj
      | succ s =>
          have hprev := ih (by omega) (by omega)
          let D := runLocalSchedule ring P_partialSealSweep C
            (clockwiseEdgeSchedule ring seed (s + 1))
          change D seed = ((C seed).1, false) ∧
              sweepLockLeader (D (cwPos ring seed (s + 1))) = false ∧
              (D (cwPos ring seed (s + 1))).2 = false ∧
              (∀ k : Nat, 0 < k → k < s + 1 →
                sweepLockLeader (D (cwPos ring seed k)) = false ∧
                  (D (cwPos ring seed k)).2 = true) ∧
              (∀ k : Nat, s + 1 < k → k < n →
                D (cwPos ring seed k) = C (cwPos ring seed k)) at hprev
          let e := cwPos ring seed (s + 1)
          let j := ring.rightNeighbor e
          have hjpos : j = cwPos ring seed (s + 2) := by
            simpa [j, e, Nat.add_assoc] using
              (cwPos_succ ring seed (s + 1)).symm
          have hDj : D j = C j := by
            rw [hjpos]
            exact hprev.2.2.2.2 (s + 2) (by omega) hlt
          have hedge := sealSweep_localStep_probe_closed
            ring hn D e
              (by simpa [e] using hprev.2.1)
              (by simpa [e] using hprev.2.2.1)
              (by rw [hDj]; exact hclosed j)
          let E := localStep ring P_partialSealSweep D e
          have hrun :
              runLocalSchedule ring P_partialSealSweep C
                  (clockwiseEdgeSchedule ring seed (s + 2)) = E := by
            change runLocalSchedule ring P_partialSealSweep C
                (clockwiseEdgeSchedule ring seed (s + 1) ++ [e]) = _
            rw [PPLLSchedulerBlocks.runLocalSchedule_append]
            rfl
          rw [hrun]
          constructor
          · have hse : seed ≠ e := by
              have hzero : 0 < n := by omega
              have heoff : s + 1 < n := by omega
              have hne : (0 : Nat) ≠ s + 1 := by omega
              simpa [e] using cwPos_ne_of_ne_below_sealSweep
                ring seed hzero heoff hne
            have hsj : seed ≠ j := by
              have hzero : 0 < n := by omega
              have hne : (0 : Nat) ≠ s + 2 := by omega
              rw [hjpos]
              simpa using cwPos_ne_of_ne_below_sealSweep
                ring seed hzero hlt hne
            exact (hedge.2.2.2 seed hse hsj).trans hprev.1
          constructor
          · rw [← hjpos]
            exact hedge.2.2.1
          constructor
          · rw [← hjpos]
            exact hedge.2.1
          constructor
          · intro k hk hklt
            by_cases hcurrent : k = s + 1
            · subst k
              have heq := hedge.1
              change sweepLockLeader (E e) = false ∧
                (E e).2 = true
              constructor
              · have hold : sweepLockLeader (D e) = false := by
                  simpa [e] using hprev.2.1
                have hout := congrArg sweepLockLeader heq
                have hout' : sweepLockLeader (E e) =
                    sweepLockLeader (D e) := by
                  simpa [sweepLockLeader] using hout
                exact hout'.trans hold
              · exact congrArg (fun u => u.2) heq
            · have hkprev : k < s + 1 := by omega
              have hke : cwPos ring seed k ≠ e := by
                have hkbound : k < n := by omega
                have hebound : s + 1 < n := by omega
                simpa [e] using cwPos_ne_of_ne_below_sealSweep
                  ring seed hkbound hebound hcurrent
              have hkj : cwPos ring seed k ≠ j := by
                have hkbound : k < n := by omega
                have hne : k ≠ s + 2 := by omega
                rw [hjpos]
                exact cwPos_ne_of_ne_below_sealSweep
                  ring seed hkbound hlt hne
              have hframe := hedge.2.2.2
                (cwPos ring seed k) hke hkj
              have hold := hprev.2.2.2.1 k hk hkprev
              exact ⟨(congrArg sweepLockLeader hframe).trans hold.1,
                (congrArg (fun u => u.2) hframe).trans hold.2⟩
          · intro k hk hkn
            have hke : cwPos ring seed k ≠ e := by
              have hebound : s + 1 < n := by omega
              have hne : k ≠ s + 1 := by omega
              simpa [e] using cwPos_ne_of_ne_below_sealSweep
                ring seed hkn hebound hne
            have hkj : cwPos ring seed k ≠ j := by
              have hne : k ≠ s + 2 := by omega
              rw [hjpos]
              exact cwPos_ne_of_ne_below_sealSweep
                ring seed hkn hlt hne
            exact (hedge.2.2.2 (cwPos ring seed k) hke hkj).trans
              (hprev.2.2.2.2 k (by omega) hkn)

/-- The exact `n`-edge serialized word launches once, visits every other site,
and returns the probe to the source. -/
theorem sealSweep_serialized_reaches_allClosedUnique
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SealSweepConfig n psi kappa tau)
    (hclosed : SealSweepAllClosed C)
    (seed : Fin n)
    (hseed : sweepLockLeader (C seed) = true)
    (hsucc : sweepLockLeader (C (ring.rightNeighbor seed)) = false) :
    let word := clockwiseEdgeSchedule ring seed n
    let D := runLocalSchedule ring P_partialSealSweep C word
    word.length = n ∧
      PopulationProtocol.Reachable
        (P_partialSealSweepProtocol psi kappa tau) ring C D ∧
      SealSweepAllClosed D ∧
      UniqueLeaderOutput
        (P_partialSealSweepProtocol psi kappa tau) n D isLeaderOutput := by
  let prefixWord := clockwiseEdgeSchedule ring seed (n - 1)
  let B := runLocalSchedule ring P_partialSealSweep C prefixWord
  have hprefix := sealSweep_clockwise_prefix
    ring hn C seed hclosed hseed hsucc (n - 1) (by omega) (by omega)
  change B seed = ((C seed).1, false) ∧
      sweepLockLeader (B (cwPos ring seed (n - 1))) = false ∧
      (B (cwPos ring seed (n - 1))).2 = false ∧
      (∀ k : Nat, 0 < k → k < n - 1 →
        sweepLockLeader (B (cwPos ring seed k)) = false ∧
          (B (cwPos ring seed k)).2 = true) ∧
      (∀ k : Nat, n - 1 < k → k < n →
        B (cwPos ring seed k) = C (cwPos ring seed k)) at hprefix
  let e := cwPos ring seed (n - 1)
  have hneighbor : ring.rightNeighbor e = seed := by
    rw [← cwPos_succ]
    have hncalc : n - 1 + 1 = n := by omega
    rw [hncalc, cwPos_period]
  have hBseedLeader : sweepLockLeader (B seed) = true := by
    rw [hprefix.1]
    exact hseed
  have hBseedOpen : (B seed).2 = false :=
    congrArg (fun u => u.2) hprefix.1
  have hedge := sealSweep_localStep_return
    ring hn B e
      (by simpa [e] using hprefix.2.1)
      (by simpa [e] using hprefix.2.2.1)
      (by rw [hneighbor]; exact hBseedLeader)
      (by rw [hneighbor]; exact hBseedOpen)
  let D := localStep ring P_partialSealSweep B e
  rw [hneighbor] at hedge
  change D e = ((B e).1, true) ∧
      D seed = ((B seed).1, true) ∧
      ∀ i : Fin n, i ≠ e → i ≠ seed → D i = B i at hedge
  have heseed : e ≠ seed := by
    simpa [hneighbor] using
      (Ne.symm (rightNeighbor_ne_self_of_one_lt ring hn e))
  have hrun :
      runLocalSchedule ring P_partialSealSweep C
          (clockwiseEdgeSchedule ring seed n) = D := by
    have hsched :
        clockwiseEdgeSchedule ring seed (n - 1 + 1) =
          clockwiseEdgeSchedule ring seed (n - 1) ++
            [cwPos ring seed (n - 1)] := by
      rfl
    have hncalc : n - 1 + 1 = n := by omega
    rw [hncalc] at hsched
    rw [hsched, PPLLSchedulerBlocks.runLocalSchedule_append]
    rfl
  have hDclosed : SealSweepAllClosed D := by
    intro i
    by_cases hie : i = e
    · subst i
      exact congrArg (fun u => u.2) hedge.1
    · by_cases his : i = seed
      · subst i
        exact congrArg (fun u => u.2) hedge.2.1
      · rw [hedge.2.2 i hie his]
        let d := cwDist ring seed i
        have hdlt : d < n := cwDist_lt ring seed i
        have hdpos : 0 < d := by
          have hdne : d ≠ 0 := by
            intro hd0
            have hpos := cwPos_cwDist ring seed i
            rw [show cwDist ring seed i = 0 by simpa [d] using hd0,
              cwPos_zero] at hpos
            exact his hpos.symm
          omega
        have hdle : d ≤ n - 1 := by omega
        have hdneLast : d ≠ n - 1 := by
          intro hdlast
          apply hie
          have hpos := cwPos_cwDist ring seed i
          rw [show cwDist ring seed i = n - 1 by
            simpa [d] using hdlast] at hpos
          exact hpos.symm
        have hdproper : d < n - 1 := by omega
        rw [← cwPos_cwDist ring seed i]
        exact (hprefix.2.2.2.1 d hdpos hdproper).2
  have hDseedLeader : sweepLockLeader (D seed) = true := by
    rw [hedge.2.1]
    exact hBseedLeader
  have hDfollower : ∀ i : Fin n, i ≠ seed →
      sweepLockLeader (D i) = false := by
    intro i his
    by_cases hie : i = e
    · subst i
      have heq := congrArg sweepLockLeader hedge.1
      have hbefore : sweepLockLeader (B e) = false := by
        simpa [e] using hprefix.2.1
      have heq' : sweepLockLeader (D e) =
          sweepLockLeader (B e) := by
        simpa [sweepLockLeader] using heq
      exact heq'.trans hbefore
    · rw [hedge.2.2 i hie his]
      let d := cwDist ring seed i
      have hdlt : d < n := cwDist_lt ring seed i
      have hdpos : 0 < d := by
        have hdne : d ≠ 0 := by
          intro hd0
          have hpos := cwPos_cwDist ring seed i
          rw [show cwDist ring seed i = 0 by simpa [d] using hd0,
            cwPos_zero] at hpos
          exact his hpos.symm
        omega
      have hdle : d ≤ n - 1 := by omega
      by_cases hdlast : d = n - 1
      · have hdlast' : cwDist ring seed i = n - 1 := by
          simpa [d] using hdlast
        rw [← cwPos_cwDist ring seed i, hdlast']
        exact hprefix.2.1
      · have hdproper : d < n - 1 := by omega
        rw [← cwPos_cwDist ring seed i]
        simpa [d] using (hprefix.2.2.2.1 d hdpos hdproper).1
  have hDunique : UniqueLeaderOutput
      (P_partialSealSweepProtocol psi kappa tau) n D isLeaderOutput := by
    refine ⟨seed, ?_, ?_⟩
    · exact sealSweep_output_leader_true (D seed) hDseedLeader
    · intro i hi
      by_cases his : i = seed
      · exact his
      · have hf := hDfollower i his
        change isLeaderOutput
          (if sweepLockLeader (D i) then LeaderOutput.leader
            else LeaderOutput.follower) = true at hi
        simp [hf, isLeaderOutput] at hi
  dsimp only
  refine ⟨clockwiseEdgeSchedule_length ring seed n, ?_, ?_, ?_⟩
  · have hreach := P_partialSealSweep_runLocalSchedule_reachable
      ring C (clockwiseEdgeSchedule ring seed n)
    exact hreach
  · rw [hrun]
    exact hDclosed
  · rw [hrun]
    exact hDunique

/-! ## Separated-start capstone -/

/-- The exact starting class addressed by the serialized theorem. -/
def SealSweepSeparatedStart
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau) : Prop :=
  SealSweepAllClosed C ∧
    SweepResetNoAdjacentLeaders ring C ∧
    HasTwoLeaderOutputs
      (P_partialSealSweepProtocol psi kappa tau) isLeaderOutput C

private theorem sweepLeader_true_of_output_true
    (u : SealSweepState psi kappa tau)
    (hu : isLeaderOutput
      ((P_partialSealSweepProtocol psi kappa tau).output u) = true) :
    sweepLockLeader u = true := by
  change isLeaderOutput
    (if sweepLockLeader u then LeaderOutput.leader
      else LeaderOutput.follower) = true at hu
  cases h : sweepLockLeader u
  · simp [h, isLeaderOutput] at hu
  · rfl

/-- Every all-closed separated multi-leader configuration has an explicit
serialized length-`n` execution to the all-closed unique-leader kernel. -/
theorem separatedStart_serialized_escape
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hC : SealSweepSeparatedStart ring C) :
    ∃ seed : Fin n,
      let word := clockwiseEdgeSchedule ring seed n
      let D := runLocalSchedule ring P_partialSealSweep C word
      word.length = n ∧
        PopulationProtocol.Reachable
          (P_partialSealSweepProtocol psi kappa tau) ring C D ∧
        SealSweepAllClosed D ∧
        UniqueLeaderOutput
          (P_partialSealSweepProtocol psi kappa tau) n D isLeaderOutput := by
  rcases hC.2.2 with ⟨seed, other, hne, hseedOut, hotherOut⟩
  have hn : 1 < n := distinct_fin_implies_nontrivial hne
  have hseed : sweepLockLeader (C seed) = true :=
    sweepLeader_true_of_output_true (C seed) hseedOut
  have hsucc : sweepLockLeader (C (ring.rightNeighbor seed)) = false := by
    cases hs : sweepLockLeader (C (ring.rightNeighbor seed)) with
    | false => rfl
    | true => exact (hC.2.1 seed ⟨hseed, hs⟩).elim
  refine ⟨seed, ?_⟩
  exact sealSweep_serialized_reaches_allClosedUnique
    ring hn C hC.1 seed hseed hsucc

/-! ## Exact unchanged state factor -/

def sealSweepStateCertificate (psi kappa tau : Nat) :
    ExhaustiveList (SealSweepState psi kappa tau) :=
  sweepResetStateCertificate psi kappa tau

theorem sealSweepStateCertificate_values_length
    (psi kappa tau : Nat) :
    (sealSweepStateCertificate psi kappa tau).values.length =
      ((2 * (PPLLFinite.boundedAgentState psi kappa).values.length) *
        (tau + 1)) * 4 := by
  exact sweepResetStateCertificate_values_length psi kappa tau

end PPartialSealSweepOverlaySol
end PPLLCompleteMultiLeaderCleanup
