import Leader.Wu.Elimination.SinkStallWitness
import Leader.Wu.Elimination.SinkAbsorbKernel


open LDSinkGapCleanup LDSinkKernelC LDSinkStallWitness PPLLRepair


namespace LDSinkKernelCPrime


set_option autoImplicit false


/-- K2': a shielded signal-zero leader treats a parked live responder bullet
as evidence: unshield the leader and preserve the bullet.  Every other MOVE
case is exactly K2's `absorbProtectedMove`. -/
def evidenceUnshieldMove {ψ : Nat} (hψ : ψ > 0) (nl : Fin ψ)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  if l.leader = true ∧ l.shield = true ∧
      l.signal_B = (0 : Fin 2) ∧
      r.leader = false ∧ r.bullet = (2 : Fin 3) then
    ({ l with shield := false }, r)
  else
    absorbProtectedMove hψ nl l r


/-- Same FIRE/MOVE/SIGNAL/dummy-sink staging as K2; only MOVE is K2'. -/
def sinkKernelC' {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let nl : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let q0 := eliminateLeadersNoCollisionFire hψ l r
  let q1 := evidenceUnshieldMove hψ nl q0.1 q0.2
  let q2 := eliminateLeadersNoCollisionSignalLeaderSink nl q1.1 q1.2
  dummyBulletSink q2


/-- Off the post-FIRE evidence guard, K2' is definitionally K2. -/
theorem kernelC'_eq_kernelC_of_not_evidence {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hnot : ¬ (
      (eliminateLeadersNoCollisionFire hψ l r).1.leader = true ∧
      (eliminateLeadersNoCollisionFire hψ l r).1.shield = true ∧
      (eliminateLeadersNoCollisionFire hψ l r).1.signal_B = (0 : Fin 2) ∧
      (eliminateLeadersNoCollisionFire hψ l r).2.leader = false ∧
      (eliminateLeadersNoCollisionFire hψ l r).2.bullet = (2 : Fin 3))) :
    sinkKernelC' hψ l r = sinkKernelC hψ l r := by
  simp only [sinkKernelC', sinkKernelC, evidenceUnshieldMove, if_neg hnot]


private theorem fire_labels {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionFire hψ l r).1.label = l.label ∧
    (eliminateLeadersNoCollisionFire hψ l r).2.label = r.label := by
  constructor <;>
    (simp only [eliminateLeadersNoCollisionFire] <;>
      (repeat split <;> rfl))


private def finish {ψ : Nat} (nl : Fin ψ)
    (q : AgentState ψ × AgentState ψ) : AgentState ψ × AgentState ψ :=
  dummyBulletSink
    (eliminateLeadersNoCollisionSignalLeaderSink nl q.1 q.2)


private theorem signal_frame {ψ : Nat} (nl : Fin ψ)
    (q : AgentState ψ × AgentState ψ) :
    (eliminateLeadersNoCollisionSignalLeaderSink nl q.1 q.2).1.label =
      q.1.label ∧
    (eliminateLeadersNoCollisionSignalLeaderSink nl q.1 q.2).2.label =
      q.2.label ∧
    (eliminateLeadersNoCollisionSignalLeaderSink nl q.1 q.2).1.leader =
      q.1.leader ∧
    (eliminateLeadersNoCollisionSignalLeaderSink nl q.1 q.2).2.leader =
      q.2.leader := by
  unfold eliminateLeadersNoCollisionSignalLeaderSink
  dsimp only
  repeat (first | rfl | exact True.intro | apply And.intro | split)


private theorem dummySink_frame {ψ : Nat}
    (q : AgentState ψ × AgentState ψ) :
    (dummyBulletSink q).1.label = q.1.label ∧
    (dummyBulletSink q).2.label = q.2.label ∧
    (dummyBulletSink q).1.leader = q.1.leader ∧
    (dummyBulletSink q).2.leader = q.2.leader := by
  unfold dummyBulletSink
  dsimp only
  repeat (first | rfl | exact True.intro | apply And.intro | split)


private theorem finish_labels {ψ : Nat} (nl : Fin ψ)
    (q : AgentState ψ × AgentState ψ) :
    (finish nl q).1.label = q.1.label ∧
    (finish nl q).2.label = q.2.label := by
  let s := eliminateLeadersNoCollisionSignalLeaderSink nl q.1 q.2
  have hs := signal_frame nl q
  have hd := dummySink_frame s
  change (dummyBulletSink s).1.label = q.1.label ∧
    (dummyBulletSink s).2.label = q.2.label
  exact ⟨hd.1.trans hs.1, hd.2.1.trans hs.2.1⟩


private theorem finish_leaders {ψ : Nat} (nl : Fin ψ)
    (q : AgentState ψ × AgentState ψ) :
    (finish nl q).1.leader = q.1.leader ∧
    (finish nl q).2.leader = q.2.leader := by
  let s := eliminateLeadersNoCollisionSignalLeaderSink nl q.1 q.2
  have hs := signal_frame nl q
  have hd := dummySink_frame s
  change (dummyBulletSink s).1.leader = q.1.leader ∧
    (dummyBulletSink s).2.leader = q.2.leader
  exact ⟨hd.2.2.1.trans hs.2.2.1,
    hd.2.2.2.trans hs.2.2.2⟩


/-- K2' preserves both endpoint labels. -/
theorem kernelC'_labels {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (sinkKernelC' hψ l r).1.label = l.label ∧
    (sinkKernelC' hψ l r).2.label = r.label := by
  let nl : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let q0 := eliminateLeadersNoCollisionFire hψ l r
  by_cases he : q0.1.leader = true ∧ q0.1.shield = true ∧
      q0.1.signal_B = (0 : Fin 2) ∧
      q0.2.leader = false ∧ q0.2.bullet = (2 : Fin 3)
  · have hm : evidenceUnshieldMove hψ nl q0.1 q0.2 =
        ({ q0.1 with shield := false }, q0.2) := by
      simp [evidenceUnshieldMove, he]
    have h0 := fire_labels hψ l r
    have hf := finish_labels nl ({ q0.1 with shield := false }, q0.2)
    change (finish nl (evidenceUnshieldMove hψ nl q0.1 q0.2)).1.label =
        l.label ∧
      (finish nl (evidenceUnshieldMove hψ nl q0.1 q0.2)).2.label = r.label
    rw [hm]
    exact ⟨hf.1.trans h0.1, hf.2.trans h0.2⟩
  · have hnot : ¬ (
        (eliminateLeadersNoCollisionFire hψ l r).1.leader = true ∧
        (eliminateLeadersNoCollisionFire hψ l r).1.shield = true ∧
        (eliminateLeadersNoCollisionFire hψ l r).1.signal_B = (0 : Fin 2) ∧
        (eliminateLeadersNoCollisionFire hψ l r).2.leader = false ∧
        (eliminateLeadersNoCollisionFire hψ l r).2.bullet = (2 : Fin 3)) := by
      simpa [q0] using he
    rw [kernelC'_eq_kernelC_of_not_evidence hψ l r hnot]
    exact kernelC_labels hψ l r


private theorem evidenceUnshieldMove_leaders {ψ : Nat}
    (hψ : ψ > 0) (nl : Fin ψ) (l r : AgentState ψ) :
    (evidenceUnshieldMove hψ nl l r).1.leader =
        (absorbProtectedMove hψ nl l r).1.leader ∧
      (evidenceUnshieldMove hψ nl l r).2.leader =
        (absorbProtectedMove hψ nl l r).2.leader := by
  by_cases he : l.leader = true ∧ l.shield = true ∧
      l.signal_B = (0 : Fin 2) ∧
      r.leader = false ∧ r.bullet = (2 : Fin 3)
  · have hp : l.leader = true ∧ l.shield = true ∧
        r.leader = false ∧ r.bullet = (2 : Fin 3) :=
      ⟨he.1, he.2.1, he.2.2.2.1, he.2.2.2.2⟩
    simp [evidenceUnshieldMove, he, absorbProtectedMove, hp]
  · simp [evidenceUnshieldMove, he]


/-- On one fixed input pair K2' and K2 delete exactly the same leaders.
The extra deletion is therefore delayed: evidence changes shield/bullet state,
and a later interaction may delete a leader that K2 had kept protected. -/
theorem kernelC'_no_new_deletion_except_evidence {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ) :
    (sinkKernelC' hψ l r).1.leader = (sinkKernelC hψ l r).1.leader ∧
    (sinkKernelC' hψ l r).2.leader = (sinkKernelC hψ l r).2.leader := by
  let nl : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let q0 := eliminateLeadersNoCollisionFire hψ l r
  let qp := evidenceUnshieldMove hψ nl q0.1 q0.2
  let qc := absorbProtectedMove hψ nl q0.1 q0.2
  have hm := evidenceUnshieldMove_leaders hψ nl q0.1 q0.2
  have hp := finish_leaders nl qp
  have hc := finish_leaders nl qc
  change (finish nl qp).1.leader = (finish nl qc).1.leader ∧
    (finish nl qp).2.leader = (finish nl qc).2.leader
  exact ⟨hp.1.trans (hm.1.trans hc.1.symm),
    hp.2.trans (hm.2.trans hc.2.symm)⟩


/-! ## Exact six-agent trap test -/


/-- First service of edge (0,1): leader 0 is unshielded and the live bullet
at 1 is deliberately kept.  SIGNAL clamps the bullet-carrying responder to
signal zero, so no other field changes. -/
theorem stallC'_edge0 :
    sinkKernelC' (by decide : 1 > 0) (stall 0) (stall 1) =
      ({ (stall 0) with shield := false }, stall 1) := by
  rfl


/-- The input pair is exactly the output of `stallC'_edge0`.  Servicing the
same edge again hits the now-unshielded leader: leader 0 is deleted and the
live responder bullet degrades from 2 to the dummy value 1. -/
theorem stallC'_edge0_then_edge0_kills :
    sinkKernelC' (by decide : 1 > 0)
        ({ (stall 0) with shield := false }) (stall 1) =
      ({ (stall 0) with shield := false, leader := false },
       { (stall 1) with bullet := (1 : Fin 3) }) := by
  rfl


/-- The witness runner with its kernel replaced by K2'. -/
def run' : List (Fin 6) → (Fin 6 → AgentState 1) →
    (Fin 6 → AgentState 1)
  | [], C => C
  | e :: es, C =>
      run' es (updatePair C e (rightNeighbor e)
        (sinkKernelC' (by decide : 1 > 0)
          (C e) (C (rightNeighbor e))))


/-- The leaderless trap is real.  The first 0,2,4 pass unshields the three
shielded leaders; the second pass lets the three parked live bullets kill
them on their disjoint edges. -/
theorem stallC'_all_die :
    ∃ es : List (Fin 6), ∀ i, (run' es stall i).leader = false := by
  exact ⟨[0, 2, 4, 0, 2, 4], by decide⟩


end LDSinkKernelCPrime


#print axioms LDSinkKernelCPrime.kernelC'_eq_kernelC_of_not_evidence
#print axioms LDSinkKernelCPrime.kernelC'_labels
#print axioms LDSinkKernelCPrime.kernelC'_no_new_deletion_except_evidence
#print axioms LDSinkKernelCPrime.stallC'_edge0
#print axioms LDSinkKernelCPrime.stallC'_edge0_then_edge0_kills
#print axioms LDSinkKernelCPrime.stallC'_all_die
