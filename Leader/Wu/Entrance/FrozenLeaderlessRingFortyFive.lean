import Leader.Wu.Entrance.FirstHitAdmissionMass
import Leader.Wu.Entrance.AdmissionCyclicRuler
import Leader.Wu.Splice.NeutralGuardsFalse
import Leader.Wu.Splice.NeutralRow
import Leader.Wu.Entrance.CalibratedLeaf

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace ZZFrozen45

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
open B9OrphanToFence B9SpliceTableV10e B9SpliceTableHost
open BirthLeaderlessBirthMassRenewal BirthTwoStageEscape
open ZZNeutralGuardsFalse

private theorem h3 : 0 < 3 := by decide
private theorem h23 : 2 ≤ 3 := by decide
private def ring45 : DirectedRing 45 := ⟨by decide⟩

private abbrev FCell := Cell 3 3 48
private abbrev FCfg := Config 45 3 3 48

private def laws := carrierLaws (ψ := 3) (κ := 3) (τ := 48)
private def host := hostR2C (κ := 3) (τ := 48) h3 h23

/-- The exact port frozen by `FinalCandidateConcrete.stepConcrete`, defined
here directly so this file does not pass through `FullRowPortFaithful`. -/
private noncomputable def port : Port (κ := 3) (τ := 48) h3 h23 :=
  B9FullCarrierRows.fullRowPort laws host h3

private def literalFollower (lab : Fin 3) : R2.Cell 3 3 48 :=
  let seed := WriterProducerRegression.clean h3 (fun _ => false) lab
  let b := seed.base.core.core
  let b' : BoundedAgentState 3 3 := {
    b with
      leader := false
      shield := false
      gen_ws := false
      label := lab
      state := .none
      path := .bot
      bit := false
      path2 := none
      path3 := none
      path4 := none
      path5 := none
      p := false
      p_carry := false
      reset_cmd := false
      echo := false
      write_state := .none
      write := .none
      b_carry := false }
  ⟨⟨⟨b', false⟩, 48⟩, 0⟩

private def frozenR2C (lab : Fin 3) : R2Coherence.Cell 3 3 48 :=
  ⟨literalFollower lab, ⟨.closing, .none⟩⟩

private def frozenFinalCell (lab : Fin 3) : FCell :=
  ⟨frozenR2C lab, .none, false, false⟩

private def labAt (i : Fin 45) : Fin 3 :=
  ⟨i.val % 3, Nat.mod_lt _ h3⟩

def frozen45 : FCfg := fun i => frozenFinalCell (labAt i)

private theorem neutralAt (i : Fin 45) : NeutralController (frozen45 i) :=
  ⟨rfl, rfl, rfl⟩

private theorem outputFalse (i : Fin 45) : outputFinal (frozen45 i) = false := by
  rfl

theorem noLeader : ¬ HasLeader frozen45 := by
  rintro ⟨i, hi⟩
  rw [outputFalse i] at hi
  cases hi

private theorem notAllOpen : ¬ FinalAllOpen frozen45 := by
  intro h
  have hm := (h (0 : Fin 45)).1
  change R2Coherence.Mark.closing = R2Coherence.Mark.open at hm
  cases hm

theorem notAdmitted :
    ¬ ConcreteB7AdmittedPassive h3 h23 ring45 frozen45 := by
  intro h
  exact notAllOpen h.2.2.1

private theorem cyclicRuler :
    CFinalJ2Edge2.FinalCyclicRuler h3 ring45 frozen45 := by
  intro a
  apply Fin.ext
  change ((a.val + 1) % 45) % 3 = (a.val % 3 + 1) % 3
  omega

private theorem noGarbage (e : Fin 45) :
    ¬ FinalGarbage h3 (frozen45 e) (frozen45 (ring45.rightNeighbor e)) := by
  exact CFinalJ2Edge.no_finalGarbage_of_neutral_noHole h3
    (neutralAt e) (neutralAt (ring45.rightNeighbor e))
    (CFinalJ2Edge2.no_finalHole_of_cyclicRuler
      h3 ring45 frozen45 cyclicRuler e)

/-! ## Inner row on the frozen cells -/

private theorem hostFixed (a b : Fin 3) :
    host.row (frozenR2C a) (frozenR2C b) =
      (frozenR2C a, frozenR2C b) := by
  change R2Coherence.row h3 (by decide : 0 < 2) h23
    (frozenR2C a) (frozenR2C b) =
      (frozenR2C a, frozenR2C b)
  simp [R2Coherence.row, R2Coherence.ordinaryStage, frozenR2C]

/-! ## Generic-neutral replacement for `FullRowPortFaithful` -/

private theorem allNeutral (a b : Fin 3) :
    AllNeutral (frozenFinalCell a) (frozenFinalCell b) := by
  exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- Direct generic dispatch: the full port action is HOST, hence not RELABEL. -/
private theorem portNotRelabel (a b : Fin 3) :
    port.action (frozenFinalCell a) (frozenFinalCell b) ≠ .relabel := by
  have ha := ZZNeutralGuardsFalse.fullActionP_host_of_allNeutral
    laws host h3
    (frozenFinalCell a) (frozenFinalCell b) (allNeutral a b)
  change fullActionP laws host h3
      (frozenFinalCell a) (frozenFinalCell b) ≠ .relabel
  rw [ha]
  decide

/-- Pair-local erased host used only to state the two payload side conditions
of the generic neutral-row theorem.  Unlike the old file this is constructed
directly from `shadowHostAt`; there is no `FullRowPortFaithful.shadowAt`. -/
private def shadowAt (a b : Fin 3) :
    B9Host.HostRow (B9FullCarrierHost.OldPhys 3 3 48) :=
  shadowHostAt laws host
    (frozenFinalCell a).phys (frozenFinalCell b).phys

private theorem shadowHostFixed (a b : Fin 3) :
    (shadowAt a b).row
      (toOld laws (frozenFinalCell a)).carrier.splice.base
      (toOld laws (frozenFinalCell b)).carrier.splice.base =
    ((toOld laws (frozenFinalCell a)).carrier.splice.base,
      (toOld laws (frozenFinalCell b)).carrier.splice.base) := by
  unfold shadowAt B9FullCarrierHost.shadowHostAt
  dsimp only
  rw [show (frozenFinalCell a).phys = frozenR2C a from rfl,
      show (frozenFinalCell b).phys = frozenR2C b from rfl]
  rw [hostFixed a b]
  rfl

private theorem ordinaryOldFixed (a b : Fin 3) :
    ordinaryRowH (shadowAt a b)
      (toOld laws (frozenFinalCell a)).carrier
      (toOld laws (frozenFinalCell b)).carrier =
    ((toOld laws (frozenFinalCell a)).carrier,
      (toOld laws (frozenFinalCell b)).carrier) := by
  unfold ordinaryRowH
  dsimp only
  rw [shadowHostFixed a b]
  rfl

/-- The left raw state is a follower, so the top-level deletion detector is
false.  `not_ldc_of_left_follower` is the public packaged proof of exactly the
requested `ldc`/`LeftDeletionCandidate` unfolding. -/
private theorem noLdc (a b : Fin 3) :
    ¬ B9SpliceTableHost.ldc (shadowAt a b)
      (toOld laws (frozenFinalCell a)).carrier
      (toOld laws (frozenFinalCell b)).carrier := by
  simpa only [shadowAt] using
    (ZZNeutralRow.not_ldc_of_left_follower
      laws host (frozenFinalCell a) (frozenFinalCell b) (by rfl))

/-- The host is physically fixed, so the responder label is unchanged and the
same-row HOST-fence observable evaluates to false. -/
private theorem rightFollowerRelabelledFalse (a b : Fin 3) :
    rightFollowerRelabelledV7
      (toOld laws (frozenFinalCell b)).carrier
      (ordinaryRowH (shadowAt a b)
        (toOld laws (frozenFinalCell a)).carrier
        (toOld laws (frozenFinalCell b)).carrier).2 = false := by
  rw [ordinaryOldFixed a b]
  unfold rightFollowerRelabelledV7
  simp

/-- `ofOldWith (toOld neutralCell) physical` is definitionally the same
neutral complete-carrier cell. -/
private theorem rewrapFrozen (lab : Fin 3) :
    ofOldWith (toOld laws (frozenFinalCell lab)) (frozenR2C lab) =
      frozenFinalCell lab := by
  rfl

/-- Exact replacement for the old controller-faithfulness proof. -/
private theorem portRowFixed (a b : Fin 3) :
    port.row (frozenFinalCell a) (frozenFinalCell b) =
      (frozenFinalCell a, frozenFinalCell b) := by
  have hrow := ZZNeutralRow.fullRowP_host_of_allNeutral
    laws host h3
    (frozenFinalCell a) (frozenFinalCell b)
    (allNeutral a b) (noLdc a b) (rightFollowerRelabelledFalse a b)
  change fullRowP laws host h3
      (frozenFinalCell a) (frozenFinalCell b) =
    (frozenFinalCell a, frozenFinalCell b)
  calc
    fullRowP laws host h3
        (frozenFinalCell a) (frozenFinalCell b) =
      (ofOldWith (toOld laws (frozenFinalCell a))
          (host.row (frozenFinalCell a).phys (frozenFinalCell b).phys).1,
       ofOldWith (toOld laws (frozenFinalCell b))
          (host.row (frozenFinalCell a).phys (frozenFinalCell b).phys).2) := hrow
    _ = (frozenFinalCell a, frozenFinalCell b) := by
      rw [show (frozenFinalCell a).phys = frozenR2C a from rfl,
          show (frozenFinalCell b).phys = frozenR2C b from rfl]
      rw [hostFixed a b]
      simp only [rewrapFrozen]

/-! ## Final row and installed concrete step -/

private theorem rowFinalEqPort (l r : FCell)
    (hg : ¬ FinalGarbage h3 l r)
    (ha : port.action l r ≠ .relabel) :
    rowFinal h3 h23 port l r = port.row l r := by
  classical
  unfold rowFinal finalAction
  rw [if_neg hg]
  cases h : port.action l r with
  | keep => rfl
  | host => rfl
  | relabel => exact (ha h).elim

private theorem rightNe (e : Fin 45) : ring45.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val + 1) % 45 = e.val at hv
  have he := e.isLt
  by_cases hlt : e.val + 1 < 45
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = 45 := by omega
    rw [heq, Nat.mod_self] at hv
    omega

private theorem rowFinalFixed (e : Fin 45) :
    rowFinal h3 h23 port
      (frozen45 e) (frozen45 (ring45.rightNeighbor e)) =
      (frozen45 e, frozen45 (ring45.rightNeighbor e)) := by
  have hr := rowFinalEqPort
    (frozen45 e) (frozen45 (ring45.rightNeighbor e))
    (noGarbage e)
    (by
      simpa [frozen45] using
        portNotRelabel (labAt e) (labAt (ring45.rightNeighbor e)))
  rw [hr]
  simpa [frozen45] using
    portRowFixed (labAt e) (labAt (ring45.rightNeighbor e))

theorem stepFixed (e : Fin 45) :
    stepConcrete (κ := 3) (τ := 48) h3 h23 ring45 frozen45 e = frozen45 := by
  change stepFinal h3 h23 port ring45 frozen45 e = frozen45
  unfold stepFinal
  rw [if_neg (rightNe e), rowFinalFixed e]
  funext i
  by_cases hi : i = e
  · simp [B9FullCarrierHost.writeAtP, hi]
  · by_cases hj : i = ring45.rightNeighbor e
    · have hne := rightNe e
      simp [B9FullCarrierHost.writeAtP, hi, hj, hne]
    · simp [B9FullCarrierHost.writeAtP, hi, hj]

/-! ## Original entrance-mass refutation -/

private def EntranceTarget (D : FCfg) : Prop :=
  HasLeader D ∨ ConcreteB7AdmittedPassive h3 h23 ring45 D

private theorem notEntrance : ¬ EntranceTarget frozen45 := by
  rintro (h | h)
  · exact noLeader h
  · exact notAdmitted h

private theorem fixedAvoidCount {S : Type} {m : Nat}
    (step : S → Fin m → S) (Good Target : S → Prop) (x : S)
    (hx : Good x ∧ ¬ Target x) (hfixed : ∀ e, step x e = x)
    (H : Nat) :
    avoidCount step Good Target x H = m ^ H := by
  induction H with
  | zero =>
      simpa only [Nat.pow_zero] using
        avoidCount_zero step Good Target x hx
  | succ H ih =>
      rw [avoidCount_succ step Good Target x hx H]
      calc
        (List.ofFn (fun e : Fin m =>
          avoidCount step Good Target (step x e) H)).sum =
            (List.ofFn (fun _ : Fin m => m ^ H)).sum := by
              apply FiniteUniformStoppingTree.ofFn_sum_eq
              intro e
              rw [hfixed e]
              exact ih
        _ = m * m ^ H :=
          FiniteUniformStoppingTree.ofFn_sum_const m (m ^ H)
        _ = m ^ (H + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

theorem avoidCountEq (H : Nat) :
    avoidCount
      (stepConcrete (κ := 3) (τ := 48) h3 h23 ring45)
      (fun _ : FCfg => True) EntranceTarget frozen45 H = 45 ^ H :=
  fixedAvoidCount
    (stepConcrete (κ := 3) (τ := 48) h3 h23 ring45)
    (fun _ : FCfg => True) EntranceTarget frozen45
    ⟨True.intro, notEntrance⟩ stepFixed H

private theorem entranceMassFalse (H Q : Nat) (hQ : 1 ≤ Q) :
    ¬ (Q * avoidCount
        (stepConcrete (κ := 3) (τ := 48) h3 h23 ring45)
        (fun _ : FCfg => True) EntranceTarget frozen45 H
      ≤ (Q - 1) * 45 ^ H) := by
  intro h
  rw [avoidCountEq H] at h
  have hpow : 0 < 45 ^ H := Nat.pow_pos (by decide)
  have hscaled : 45 ^ H * Q ≤ 45 ^ H * (Q - 1) := by
    simpa only [Nat.mul_comm] using h
  have hbad : Q ≤ Q - 1 := Nat.le_of_mul_le_mul_left hscaled hpow
  omega

theorem firstHit_refuted (H Q : Nat) :
    ¬ CFinalAdmissionEntrance.firstHitToAdmittedPassiveOrLeaderMass
      h3 h23 ring45 H Q := by
  intro h
  have hm := h.2 frozen45
  change Q * avoidCount
      (stepConcrete (κ := 3) (τ := 48) h3 h23 ring45)
      (fun _ : FCfg => True) EntranceTarget frozen45 H ≤
      (Q - 1) * 45 ^ H at hm
  exact entranceMassFalse H Q h.1 hm

/-! ## Standalone leaderless mass and terminal CFinalAssembly2 refutation -/

/-- `HasLeader` is false exactly where the final Good predicate is true. -/
theorem frozen45Leaderless : FinalLeaderless frozen45 :=
  (finalLeaderless_iff_not_hasLeader frozen45).2 noLeader

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

/-- Every length-K scheduler word stays final-leaderless at frozen45. -/
theorem aliveCountEq (K : Nat) :
    aliveCount
        (stepConcrete (κ := 3) (τ := 48) h3 h23 ring45)
        FinalLeaderless frozen45 K = 45 ^ K :=
  fixedAliveCount
    (stepConcrete (κ := 3) (τ := 48) h3 h23 ring45)
    FinalLeaderless frozen45 frozen45Leaderless stepFixed K

/-- Any positive-denominator escape-mass inequality is impossible on the
fixed leaderless witness.  In particular Q=8 is impossible. -/
theorem leaderlessMassFalse (K Q : Nat) (hQ : 1 ≤ Q) :
    ¬ (Q * aliveCount
          (stepConcrete (κ := 3) (τ := 48) h3 h23 ring45)
          FinalLeaderless frozen45 K
        ≤ (Q - 1) * 45 ^ K) := by
  intro h
  rw [aliveCountEq K] at h
  have hpow : 0 < 45 ^ K := Nat.pow_pos (by decide)
  have hscaled : 45 ^ K * Q ≤ 45 ^ K * (Q - 1) := by
    simpa only [Nat.mul_comm] using h
  have hbad : Q ≤ Q - 1 := Nat.le_of_mul_le_mul_left hscaled hpow
  omega

/-- Unrestricted CFinalAssembly2 terminal is false at this exact old carrier,
for every horizon H.  This proof no longer imports the broken
`CFinalAssembly2Refutation` file; it uses only the green `CFinalAssembly2`
interface plus the local fixed-point receipt above. -/
theorem finalB7OneOverN_false_all :
    ∀ H, ¬ CFinalAssembly2.FinalB7OneOverN h3 h23 ring45 H := by
  intro H hFinal
  have hbad := hFinal frozen45 frozen45Leaderless
  rw [BirthLeaderlessBirthMassB7Generic.firstLeaderFailureNumerator_eq_aliveCount,
      aliveCountEq] at hbad
  have hpos : 0 < 45 ^ (6 * (Nat.log2 45 + 1) * H) :=
    Nat.pow_pos (by decide)
  omega

#print axioms ZZFrozen45.stepFixed
#print axioms ZZFrozen45.noLeader
#print axioms ZZFrozen45.notAdmitted
#print axioms ZZFrozen45.firstHit_refuted
#print axioms ZZFrozen45.aliveCountEq
#print axioms ZZFrozen45.leaderlessMassFalse
#print axioms ZZFrozen45.finalB7OneOverN_false_all

end ZZFrozen45
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
