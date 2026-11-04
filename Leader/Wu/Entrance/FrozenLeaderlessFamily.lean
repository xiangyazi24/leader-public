import Leader.Wu.Entrance.AdmissionCyclicRuler
import Leader.Wu.Splice.NeutralGuardsFalse
import Leader.Wu.Splice.NeutralRow
import Leader.Wu.Entrance.CalibratedLeaf
import Leader.Wu.Birth.RingLabelGeometry

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace ZZFrozenFamily

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open Q11593SpliceControllerDesign
open B9Host B9FullCarrierHost B9FullCarrierRows
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6
  B9SpliceControllerR1TableV7 B9SpliceControllerR1TableV8
  B9SpliceControllerR1TableV9 B9SpliceControllerR1TableV10b
open B9OrphanToFence B9SpliceTableV10e B9SpliceTableV10g
  B9SpliceTableHost
open BirthLeaderlessBirthMassRenewal BirthTwoStageEscape
open ZZNeutralGuardsFalse

variable {n psi kappa tau : Nat}

/-! ## 1. The arbitrary-kappa/tau frozen carrier -/

private def laws (psi kappa tau : Nat) :
    PhysCarrierLaws (P psi kappa tau) psi kappa tau :=
  carrierLaws (ψ := psi) (κ := kappa) (τ := tau)

private def host (kappa tau : Nat)
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) :
    HostRow (P psi kappa tau) :=
  hostR2C (κ := kappa) (τ := tau) hpsi h2

private noncomputable def port (kappa tau : Nat)
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) :
    Port (κ := kappa) (τ := tau) hpsi h2 :=
  B9FullCarrierRows.fullRowPort
    (laws psi kappa tau) (host kappa tau hpsi h2) hpsi

/--
A completely direct follower payload.  This avoids the accidental
`κ=ψ, τ=16ψ` type specialization of `WriterProducerRegression.clean`.
Every finite numeric coordinate is set to zero; `label` is the only spatial
coordinate that varies.
-/
private def literalFollower (lab : Fin psi) : R2.Cell psi kappa tau :=
  let b : BoundedAgentState psi kappa := {
    leader := false
    probe := false
    phase := false
    bit := false
    wait := true
    state := .none
    path := .bot
    reset := false
    carry := false
    count := 0
    label := lab
    h_field := false
    path2 := none
    path3 := none
    path4 := none
    path5 := none
    p := false
    p_carry := false
    reset_cmd := false
    echo := false
    signal_B := 0
    bullet := 0
    shield := false
    write_state := .none
    write := .none
    last := false
    last_set := false
    last_unset := false
    b_carry := false
    gen_ws := false
    ws_echo := false
    signal_ws := false }
  ⟨⟨⟨b, false⟩, 0⟩, 0⟩

private def frozenR2C (lab : Fin psi) : R2Coherence.Cell psi kappa tau :=
  ⟨literalFollower lab, ⟨.closing, .none⟩⟩

private def frozenFinalCell (lab : Fin psi) : Cell psi kappa tau :=
  ⟨frozenR2C lab, .none, false, false⟩

def labAt (hpsi : 0 < psi) (i : Fin n) : Fin psi :=
  ⟨i.val % psi, Nat.mod_lt _ hpsi⟩

/-- The requested general frozen configuration. -/
def frozenN (hpsi : 0 < psi) : Config n psi kappa tau :=
  fun i => frozenFinalCell (labAt hpsi i)

/-- `ψ ∣ n` has a positive quotient in the nontrivial ring regime. -/
theorem divisorFactorPos
    (h2 : 2 ≤ psi) (hn : 1 < n) (hd : psi ∣ n) :
    ∃ k : Nat, 0 < k ∧ n = psi * k := by
  rcases hd with ⟨k, hk⟩
  have hkpos : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hk0
    subst k
    simp at hk
    omega
  exact ⟨k, hkpos, hk⟩

private theorem neutralAt (hpsi : 0 < psi) (i : Fin n) :
    NeutralController
      ((frozenN (n := n) (kappa := kappa) (tau := tau) hpsi) i) :=
  ⟨rfl, rfl, rfl⟩

private theorem outputFalse (hpsi : 0 < psi) (i : Fin n) :
    outputFinal
      ((frozenN (n := n) (kappa := kappa) (tau := tau) hpsi) i) = false := by
  rfl

/-- Every site is a physical follower. -/
theorem leaderless (hpsi : 0 < psi) :
    FinalLeaderless
      (frozenN (n := n) (kappa := kappa) (tau := tau) hpsi) := by
  intro i
  exact outputFalse hpsi i

/-! ## 2. Exact cyclic ruler and generic recovery audit -/

/-- Arbitrary-κ/τ version of `CFinalJ2Edge2.FinalCyclicRuler`. -/
def CyclicRuler
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) : Prop :=
  ∀ a : Fin n,
    ((oldConfig C) (ring.rightNeighbor a)).carrier.splice.base.core.core.label =
      ⟨(((oldConfig C) a).carrier.splice.base.core.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩

/--
The wrap edge is included.  `Nat.mod_mod_of_dvd` is the only global arithmetic
fact needed from `ψ ∣ n`.
-/
theorem cyclicRuler
    (hpsi : 0 < psi) (ring : DirectedRing n) (hd : psi ∣ n) :
    CyclicRuler hpsi ring
      (frozenN (n := n) (kappa := kappa) (tau := tau) hpsi) := by
  intro a
  apply Fin.ext
  change ((a.val + 1) % n) % psi = (a.val % psi + 1) % psi
  rw [Nat.mod_mod_of_dvd _ hd]
  exact (mod_succ_eq a.val psi).symm

/--
Independent `isBarrier` audit of the same ruler.  This is not needed by the
fixed-point proof, but it prevents accidentally proving only the non-wrap
edges.
-/
theorem noBarrier
    (hpsi : 0 < psi) (ring : DirectedRing n) (hd : psi ∣ n) :
    RingLabelGeometry.NoBarrier ring (labAt (n := n) hpsi) := by
  intro e hB
  unfold RingLabelGeometry.Barrier at hB
  apply hB
  change ((e.val + 1) % n) % psi = (e.val % psi + 1) % psi
  rw [Nat.mod_mod_of_dvd _ hd]
  exact (mod_succ_eq e.val psi).symm

/--
Generic copy of `CFinalJ2Edge.no_finalScrubGarbage_of_neutral`.
Its original proof was already independent of κ and τ.
-/
private theorem noFinalScrubGarbage_of_neutral
    (l r : Cell psi kappa tau)
    (hl : NeutralController l) (hr : NeutralController r) :
    ¬ B9ControllerRecovery.ScrubGarbage (oldCell l) (oldCell r) := by
  intro h
  rcases h with hL | hR | hB
  · have ht : l.acquireTicket = true := hL.1
    rw [hl.2.2] at ht
    cases ht
  · have ht : r.acquireTicket = true := hR.1
    rw [hr.2.2] at ht
    cases ht
  · have hp : l.spliceRole = .predecessorArmed := hB.1.1
    rw [hl.1] at hp
    cases hp

/--
Generic copy of `CFinalJ2Edge2.no_finalHole_of_cyclicRuler`.
The decisive theorem `danger_iff_physical` is already polymorphic in κ and τ.
This explicitly audits the erased projection used by recovery.
-/
private theorem noFinalHole_of_cyclicRuler
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau)
    (hR : CyclicRuler hpsi ring C) (a : Fin n) :
    ¬ FinalHole hpsi (C a) (C (ring.rightNeighbor a)) := by
  intro hH
  have hH' : B9ControllerRecovery.Hole hpsi
      ((oldConfig C) a) ((oldConfig C) (ring.rightNeighbor a)) := hH
  have hD : B9SpliceControllerR1Table.PreparedDangerAt hpsi ring
      (B9SpliceControllerR1TableV6.projectV6 (oldConfig C)) a := hH'.1
  have hp :=
    (B9SpliceV10ePhysicalHoldNoBirth.danger_iff_physical
      hpsi ring (oldConfig C) a).1 hD
  exact hp.2.2 (hR a)

private theorem noFinalGarbage_of_neutral_noHole
    (hpsi : 0 < psi) {l r : Cell psi kappa tau}
    (hl : NeutralController l) (hr : NeutralController r)
    (hHole : ¬ FinalHole hpsi l r) :
    ¬ FinalGarbage hpsi l r := by
  intro hG
  change B9ControllerRecovery.Garbage hpsi (oldCell l) (oldCell r) at hG
  rcases hG with hScrub | hH
  · exact noFinalScrubGarbage_of_neutral l r hl hr hScrub
  · exact hHole hH

private theorem noGarbage
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (hd : psi ∣ n) (e : Fin n) :
    ¬ FinalGarbage hpsi
      ((frozenN (kappa := kappa) (tau := tau) hpsi) e)
      ((frozenN (kappa := kappa) (tau := tau) hpsi)
        (ring.rightNeighbor e)) := by
  exact noFinalGarbage_of_neutral_noHole hpsi
    (neutralAt hpsi e)
    (neutralAt hpsi (ring.rightNeighbor e))
    (noFinalHole_of_cyclicRuler hpsi ring
      (frozenN (kappa := kappa) (tau := tau) hpsi)
      (cyclicRuler hpsi ring hd) e)

/-! ## 3. Inner old row and complete B9 row are exact identities -/

private theorem hostFixed
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (a b : Fin psi) :
    (host kappa tau hpsi h2).row
        (frozenR2C (kappa := kappa) (tau := tau) a)
        (frozenR2C (kappa := kappa) (tau := tau) b) =
      (frozenR2C (kappa := kappa) (tau := tau) a,
       frozenR2C (kappa := kappa) (tau := tau) b) := by
  change R2Coherence.row hpsi (by decide : 0 < 2) h2
    (frozenR2C (kappa := kappa) (tau := tau) a)
    (frozenR2C (kappa := kappa) (tau := tau) b) =
      (frozenR2C (kappa := kappa) (tau := tau) a,
       frozenR2C (kappa := kappa) (tau := tau) b)
  simp [R2Coherence.row, R2Coherence.ordinaryStage, frozenR2C]

private theorem allNeutral (a b : Fin psi) :
    AllNeutral
      (frozenFinalCell (kappa := kappa) (tau := tau) a)
      (frozenFinalCell (kappa := kappa) (tau := tau) b) := by
  exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

private theorem portNotRelabel
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (a b : Fin psi) :
    (port kappa tau hpsi h2).action
      (frozenFinalCell (kappa := kappa) (tau := tau) a)
      (frozenFinalCell (kappa := kappa) (tau := tau) b) ≠ .relabel := by
  have ha := ZZNeutralGuardsFalse.fullActionP_host_of_allNeutral
    (laws psi kappa tau) (host kappa tau hpsi h2) hpsi
    (frozenFinalCell (kappa := kappa) (tau := tau) a)
    (frozenFinalCell (kappa := kappa) (tau := tau) b)
    (allNeutral a b)
  change fullActionP (laws psi kappa tau) (host kappa tau hpsi h2) hpsi
      (frozenFinalCell (kappa := kappa) (tau := tau) a)
      (frozenFinalCell (kappa := kappa) (tau := tau) b) ≠ .relabel
  rw [ha]
  decide

private def shadowAt
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (a b : Fin psi) :
    HostRow (OldPhys psi kappa tau) :=
  shadowHostAt (laws psi kappa tau) (host kappa tau hpsi h2)
    (frozenFinalCell (kappa := kappa) (tau := tau) a).phys
    (frozenFinalCell (kappa := kappa) (tau := tau) b).phys

private theorem shadowHostFixed
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (a b : Fin psi) :
    (shadowAt (kappa := kappa) (tau := tau) hpsi h2 a b).row
      (toOld (laws psi kappa tau)
        (frozenFinalCell (kappa := kappa) (tau := tau) a)).carrier.splice.base
      (toOld (laws psi kappa tau)
        (frozenFinalCell (kappa := kappa) (tau := tau) b)).carrier.splice.base =
    ((toOld (laws psi kappa tau)
        (frozenFinalCell (kappa := kappa) (tau := tau) a)).carrier.splice.base,
     (toOld (laws psi kappa tau)
        (frozenFinalCell (kappa := kappa) (tau := tau) b)).carrier.splice.base) := by
  unfold shadowAt B9FullCarrierHost.shadowHostAt
  dsimp only
  rw [show (frozenFinalCell (kappa := kappa) (tau := tau) a).phys =
        frozenR2C (kappa := kappa) (tau := tau) a from rfl,
      show (frozenFinalCell (kappa := kappa) (tau := tau) b).phys =
        frozenR2C (kappa := kappa) (tau := tau) b from rfl]
  rw [hostFixed hpsi h2 a b]
  rfl

private theorem ordinaryOldFixed
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (a b : Fin psi) :
    ordinaryRowH (shadowAt (kappa := kappa) (tau := tau) hpsi h2 a b)
      (toOld (laws psi kappa tau)
        (frozenFinalCell (kappa := kappa) (tau := tau) a)).carrier
      (toOld (laws psi kappa tau)
        (frozenFinalCell (kappa := kappa) (tau := tau) b)).carrier =
    ((toOld (laws psi kappa tau)
        (frozenFinalCell (kappa := kappa) (tau := tau) a)).carrier,
     (toOld (laws psi kappa tau)
        (frozenFinalCell (kappa := kappa) (tau := tau) b)).carrier) := by
  unfold ordinaryRowH
  dsimp only
  rw [shadowHostFixed hpsi h2 a b]
  rfl

private theorem noLdc
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (a b : Fin psi) :
    ¬ ldc (shadowAt (kappa := kappa) (tau := tau) hpsi h2 a b)
      (toOld (laws psi kappa tau)
        (frozenFinalCell (kappa := kappa) (tau := tau) a)).carrier
      (toOld (laws psi kappa tau)
        (frozenFinalCell (kappa := kappa) (tau := tau) b)).carrier := by
  simpa only [shadowAt] using
    (ZZNeutralRow.not_ldc_of_left_follower
      (laws psi kappa tau) (host kappa tau hpsi h2)
      (frozenFinalCell (kappa := kappa) (tau := tau) a)
      (frozenFinalCell (kappa := kappa) (tau := tau) b)
      (by rfl))

private theorem rightFollowerRelabelledFalse
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (a b : Fin psi) :
    rightFollowerRelabelledV7
      (toOld (laws psi kappa tau)
        (frozenFinalCell (kappa := kappa) (tau := tau) b)).carrier
      (ordinaryRowH
        (shadowAt (kappa := kappa) (tau := tau) hpsi h2 a b)
        (toOld (laws psi kappa tau)
          (frozenFinalCell (kappa := kappa) (tau := tau) a)).carrier
        (toOld (laws psi kappa tau)
          (frozenFinalCell (kappa := kappa) (tau := tau) b)).carrier).2 = false := by
  rw [ordinaryOldFixed hpsi h2 a b]
  unfold rightFollowerRelabelledV7
  simp

private theorem rewrapFrozen (lab : Fin psi) :
    ofOldWith
      (toOld (laws psi kappa tau)
        (frozenFinalCell (kappa := kappa) (tau := tau) lab))
      (frozenR2C (kappa := kappa) (tau := tau) lab) =
      frozenFinalCell (kappa := kappa) (tau := tau) lab := by
  rfl

private theorem portRowFixed
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (a b : Fin psi) :
    (port kappa tau hpsi h2).row
      (frozenFinalCell (kappa := kappa) (tau := tau) a)
      (frozenFinalCell (kappa := kappa) (tau := tau) b) =
      (frozenFinalCell (kappa := kappa) (tau := tau) a,
       frozenFinalCell (kappa := kappa) (tau := tau) b) := by
  have hrow := ZZNeutralRow.fullRowP_host_of_allNeutral
    (laws psi kappa tau) (host kappa tau hpsi h2) hpsi
    (frozenFinalCell (kappa := kappa) (tau := tau) a)
    (frozenFinalCell (kappa := kappa) (tau := tau) b)
    (allNeutral a b) (noLdc hpsi h2 a b)
    (rightFollowerRelabelledFalse hpsi h2 a b)
  change fullRowP (laws psi kappa tau) (host kappa tau hpsi h2) hpsi
      (frozenFinalCell (kappa := kappa) (tau := tau) a)
      (frozenFinalCell (kappa := kappa) (tau := tau) b) =
      (frozenFinalCell (kappa := kappa) (tau := tau) a,
       frozenFinalCell (kappa := kappa) (tau := tau) b)
  calc
    fullRowP (laws psi kappa tau) (host kappa tau hpsi h2) hpsi
        (frozenFinalCell (kappa := kappa) (tau := tau) a)
        (frozenFinalCell (kappa := kappa) (tau := tau) b) =
      (ofOldWith
          (toOld (laws psi kappa tau)
            (frozenFinalCell (kappa := kappa) (tau := tau) a))
          ((host kappa tau hpsi h2).row
            (frozenFinalCell (kappa := kappa) (tau := tau) a).phys
            (frozenFinalCell (kappa := kappa) (tau := tau) b).phys).1,
       ofOldWith
          (toOld (laws psi kappa tau)
            (frozenFinalCell (kappa := kappa) (tau := tau) b))
          ((host kappa tau hpsi h2).row
            (frozenFinalCell (kappa := kappa) (tau := tau) a).phys
            (frozenFinalCell (kappa := kappa) (tau := tau) b).phys).2) := hrow
    _ = (frozenFinalCell (kappa := kappa) (tau := tau) a,
         frozenFinalCell (kappa := kappa) (tau := tau) b) := by
      rw [show (frozenFinalCell (kappa := kappa) (tau := tau) a).phys =
            frozenR2C (kappa := kappa) (tau := tau) a from rfl,
          show (frozenFinalCell (kappa := kappa) (tau := tau) b).phys =
            frozenR2C (kappa := kappa) (tau := tau) b from rfl]
      rw [hostFixed hpsi h2 a b]
      simp only [rewrapFrozen]

/-! ## 4. Installed old final row and scheduler step -/

private theorem rowFinalEqPort
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : Cell psi kappa tau)
    (hg : ¬ FinalGarbage hpsi l r)
    (ha : (port kappa tau hpsi h2).action l r ≠ .relabel) :
    rowFinal hpsi h2 (port kappa tau hpsi h2) l r =
      (port kappa tau hpsi h2).row l r := by
  classical
  unfold rowFinal finalAction
  rw [if_neg hg]
  cases h : (port kappa tau hpsi h2).action l r with
  | keep => rfl
  | host => rfl
  | relabel => exact (ha h).elim

private theorem rightNe
    (hn : 1 < n) (ring : DirectedRing n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = e.val at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega

private theorem rowFinalFixed
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (hd : psi ∣ n) (e : Fin n) :
    rowFinal hpsi h2 (port kappa tau hpsi h2)
      ((frozenN (kappa := kappa) (tau := tau) hpsi) e)
      ((frozenN (kappa := kappa) (tau := tau) hpsi)
        (ring.rightNeighbor e)) =
      ((frozenN (kappa := kappa) (tau := tau) hpsi) e,
       (frozenN (kappa := kappa) (tau := tau) hpsi)
        (ring.rightNeighbor e)) := by
  have hr := rowFinalEqPort hpsi h2
    ((frozenN (kappa := kappa) (tau := tau) hpsi) e)
    ((frozenN (kappa := kappa) (tau := tau) hpsi)
      (ring.rightNeighbor e))
    (noGarbage hpsi ring hd e)
    (by
      simpa [frozenN] using
        portNotRelabel (kappa := kappa) (tau := tau) hpsi h2
          (labAt hpsi e) (labAt hpsi (ring.rightNeighbor e)))
  rw [hr]
  simpa [frozenN] using
    portRowFixed (kappa := kappa) (tau := tau) hpsi h2
      (labAt hpsi e) (labAt hpsi (ring.rightNeighbor e))

/-- Main kernel target: every scheduler letter fixes the general frozen state. -/
theorem stepFixed
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (hn : 1 < n) (ring : DirectedRing n) (hd : psi ∣ n)
    (e : Fin n) :
    stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring
      (frozenN (n := n) (kappa := kappa) (tau := tau) hpsi) e =
      frozenN (n := n) (kappa := kappa) (tau := tau) hpsi := by
  change stepFinal hpsi h2 (port kappa tau hpsi h2) ring
      (frozenN (n := n) (kappa := kappa) (tau := tau) hpsi) e =
      frozenN (n := n) (kappa := kappa) (tau := tau) hpsi
  unfold stepFinal
  rw [if_neg (rightNe hn ring e), rowFinalFixed hpsi h2 ring hd e]
  funext i
  by_cases hi : i = e
  · simp [B9FullCarrierHost.writeAtP, hi]
  · by_cases hj : i = ring.rightNeighbor e
    · have hne := rightNe hn ring e
      simp [B9FullCarrierHost.writeAtP, hi, hj, hne]
    · simp [B9FullCarrierHost.writeAtP, hi, hj]

/-- Convenient closed-singleton package. -/
theorem closedLeaderlessFixed
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (hn : 1 < n) (ring : DirectedRing n) (hd : psi ∣ n) :
    FinalLeaderless
        (frozenN (n := n) (kappa := kappa) (tau := tau) hpsi) ∧
      ∀ e : Fin n,
        stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring
          (frozenN (n := n) (kappa := kappa) (tau := tau) hpsi) e =
          frozenN (n := n) (kappa := kappa) (tau := tau) hpsi :=
  ⟨leaderless hpsi, stepFixed hpsi h2 hn ring hd⟩

/-! ## 5. Count and mass consequences -/

private theorem fixedAliveCount {S : Type} {m : Nat}
    (step : S → Fin m → S) (Good : S → Prop) (x : S)
    (hx : Good x) (hfixed : ∀ e, step x e = x) (K : Nat) :
    aliveCount step Good x K = m ^ K := by
  induction K with
  | zero =>
      unfold BirthLeaderlessBirthMassRenewal.aliveCount
        FixedSpanRenewalPayload.wordSum
      classical
      simp [allSchedules, BirthLeaderlessBirthMassRenewal.aliveBit,
        BirthLeaderlessBirthMassRenewal.AliveAlong, hx]
  | succ K ih =>
      rw [aliveCount_succ step Good x hx]
      calc
        (List.ofFn (fun e : Fin m =>
          aliveCount step Good (step x e) K)).sum =
            (List.ofFn (fun _ : Fin m => m ^ K)).sum := by
              apply FiniteUniformStoppingTree.ofFn_sum_eq
              intro e
              rw [hfixed e]
              exact ih
        _ = m * m ^ K :=
          FiniteUniformStoppingTree.ofFn_sum_const m (m ^ K)
        _ = m ^ (K + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

/-- Every length-K scheduler word remains leaderless. -/
theorem aliveCountEq
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (hn : 1 < n) (ring : DirectedRing n) (hd : psi ∣ n)
    (K : Nat) :
    aliveCount
      (stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring)
      FinalLeaderless
      (frozenN (n := n) (kappa := kappa) (tau := tau) hpsi) K =
      n ^ K :=
  fixedAliveCount
    (stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring)
    FinalLeaderless
    (frozenN (n := n) (kappa := kappa) (tau := tau) hpsi)
    (leaderless hpsi)
    (stepFixed hpsi h2 hn ring hd) K

/-- No positive-denominator escape-mass inequality can hold on the witness. -/
theorem leaderlessMassFalse
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (hn : 1 < n) (ring : DirectedRing n) (hd : psi ∣ n)
    (K Q : Nat) (hQ : 1 ≤ Q) :
    ¬ (Q * aliveCount
          (stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring)
          FinalLeaderless
          (frozenN (n := n) (kappa := kappa) (tau := tau) hpsi) K
        ≤ (Q - 1) * n ^ K) := by
  intro h
  rw [aliveCountEq hpsi h2 hn ring hd K] at h
  have hpow : 0 < n ^ K := Nat.pow_pos ring.hn
  have hscaled : n ^ K * Q ≤ n ^ K * (Q - 1) := by
    simpa only [Nat.mul_comm] using h
  have hbad : Q ≤ Q - 1 := Nat.le_of_mul_le_mul_left hscaled hpow
  omega

/--
Current `FinalB7OneOverN` is campaign-shaped (`κ=ψ`, `τ=16ψ`).  The general
fixed-point theorem above specializes to that carrier and refutes the terminal
for every horizon.
-/
theorem finalB7OneOverN_false_all
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (hn : 1 < n) (ring : DirectedRing n) (hd : psi ∣ n) :
    ∀ H, ¬ CFinalAssembly2.FinalB7OneOverN hpsi h2 ring H := by
  intro H hFinal
  have hbad := hFinal
    (frozenN (n := n) (kappa := psi) (tau := 16 * psi) hpsi)
    (leaderless (n := n) (kappa := psi) (tau := 16 * psi) hpsi)
  rw [BirthLeaderlessBirthMassB7Generic.firstLeaderFailureNumerator_eq_aliveCount,
      aliveCountEq (kappa := psi) (tau := 16 * psi)
        hpsi h2 hn ring hd] at hbad
  have hpow : 0 < n ^ (6 * (Nat.log2 n + 1) * H) :=
    Nat.pow_pos ring.hn
  have hscaled :
      n ^ (6 * (Nat.log2 n + 1) * H) * n ≤
        n ^ (6 * (Nat.log2 n + 1) * H) * 1 := by
    simpa [Nat.mul_comm, Nat.mul_one, Nat.one_mul] using hbad
  have hnle : n ≤ 1 := Nat.le_of_mul_le_mul_left hscaled hpow
  omega

/-! ## 6. Small new specialization: n=6, psi=3 -/

private theorem h3 : 0 < 3 := by decide
private theorem h23 : 2 ≤ 3 := by decide
private theorem hn6 : 1 < 6 := by decide
private def ring6 : DirectedRing 6 := ⟨by decide⟩

/-- Same family, now with κ=3 and τ=48, exactly the requested small witness. -/
theorem frozen6_stepFixed (e : Fin 6) :
    stepConcrete (κ := 3) (τ := 48) h3 h23 ring6
      (frozenN (n := 6) (kappa := 3) (tau := 48) h3) e =
      frozenN (n := 6) (kappa := 3) (tau := 48) h3 := by
  simpa using
    (stepFixed (n := 6) (psi := 3) (kappa := 3) (tau := 48)
      h3 h23 hn6 ring6 (by decide : 3 ∣ 6) e)

theorem frozen6_aliveCount (K : Nat) :
    aliveCount
      (stepConcrete (κ := 3) (τ := 48) h3 h23 ring6)
      FinalLeaderless
      (frozenN (n := 6) (kappa := 3) (tau := 48) h3) K = 6 ^ K := by
  simpa using
    (aliveCountEq (n := 6) (psi := 3) (kappa := 3) (tau := 48)
      h3 h23 hn6 ring6 (by decide : 3 ∣ 6) K)

#print axioms ZZFrozenFamily.cyclicRuler
#print axioms ZZFrozenFamily.stepFixed
#print axioms ZZFrozenFamily.leaderless
#print axioms ZZFrozenFamily.aliveCountEq
#print axioms ZZFrozenFamily.leaderlessMassFalse
#print axioms ZZFrozenFamily.finalB7OneOverN_false_all
#print axioms ZZFrozenFamily.frozen6_stepFixed

end ZZFrozenFamily
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
