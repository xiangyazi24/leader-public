import Leader.Wu.Protocol.SubProtocol
import Leader.Wu.Safety.ConcreteProtocolProperties
import Leader.Wu.Protocol.Repairs
import Leader.Wu.Protocol.GenSigStaged
import Leader.Wu.Protocol.EliminateSigFrames
import Leader.Wu.Safety.NoCheckBirthLeaderFrames


set_option autoImplicit false
set_option Elab.async false


namespace ZZF3Skeleton


open PPLL PPLLRepair PPLLVerify
open PPLLNoCheckBirthLeaderFrames

/-- Inlined verbatim from
`Leader/PPartialFactorSixteenSameEpochResetNoGoSol.lean:42-47`.  That module
sits behind a twelve-deep chain of uncompiled dependencies, one of them
eighteen thousand lines, so importing it costs far more than restating six
lines. -/
def EdgewiseFixed {Q : Type} {m : Nat}
    (ring : DirectedRing m) (T : Q → Q → Q × Q)
    (C : Fin m → Q) : Prop :=
  ∀ e : Fin m,
    T (C e) (C (ring.rightNeighbor e)) =
      (C e, C (ring.rightNeighbor e))


/-!
Source map.


* `isBarrier`: Leader/Wu/Protocol/SubProtocol.lean:11-12.
* `pPsi`: Leader/Wu/Protocol/Algorithm.lean:29-46.
* COMPARE/CMP_UPDATE: Leader/Wu/Protocol/Algorithm.lean:368-463.
* Algorithm-1 prefix boundaries: Leader/Wu/Protocol/Algorithm.lean:1081-1109.
* `ppllNoBulletSignalCollision`: Leader/Wu/Protocol/Repairs.lean:914-919.
* `EdgewiseFixed`: Leader/PPartialFactorSixteenSameEpochResetNoGoSol.lean:42-47.
* Public label frames: Leader/Wu/Safety/ConcreteProtocolProperties.lean:801,815,2311-2318,
  2348-2397; Leader/Wu/Protocol/GenSigStaged.lean:261-267;
  Leader/Wu/Protocol/EliminateSigFrames.lean:19-25.
* Public leader frames used only for the `r.probe = true` correction:
  Leader/Wu/Safety/ConcreteProtocolProperties.lean:2338-2346,2401-2449;
  Leader/Wu/Protocol/GenSigStaged.lean:256-263;
  Leader/Wu/Safety/NoCheckBirthLeaderFrames.lean:257-261.
* The Algorithm-15 no-collision label frame is still private at
  Leader/Wu/Safety/NoCheckBirthLeaderFrames.lean:291-296, so it remains an explicit
  hypothesis here.
-/


universe u


@[simp] theorem ite_same_local
    {α : Sort u} {c : Prop} [Decidable c] (a : α) :
    (if c then a else a) = a := by
  by_cases h : c <;> simp [h]


#print axioms ZZF3Skeleton.ite_same_local


@[simp] theorem agentState_label_ite
    {psi : Nat} {c : Prop} [Decidable c]
    (a b : AgentState psi) :
    (if c then a else b).label =
      (if c then a.label else b.label) := by
  by_cases h : c
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]


#print axioms ZZF3Skeleton.agentState_label_ite


theorem cmpUpdatePropagate_l_label
    {psi : Nat} (hpsi : 0 < psi)
    (l r : AgentState psi) :
    (cmpUpdatePropagate hpsi l r).1.label = l.label := by
  unfold cmpUpdatePropagate
  try dsimp only []
  repeat (first | rfl | split)


#print axioms ZZF3Skeleton.cmpUpdatePropagate_l_label


theorem cmpUpdatePropagate_r_label
    {psi : Nat} (hpsi : 0 < psi)
    (l r : AgentState psi) :
    (cmpUpdatePropagate hpsi l r).2.label = r.label := by
  unfold cmpUpdatePropagate
  try dsimp only []
  repeat (first | rfl | split)


#print axioms ZZF3Skeleton.cmpUpdatePropagate_r_label


theorem cmpUpdateSetPath2_label
    {psi : Nat} (hpsi : 0 < psi)
    (l : AgentState psi) :
    (cmpUpdateSetPath2 hpsi l).label = l.label := by
  unfold cmpUpdateSetPath2
  try dsimp only []
  repeat (first | rfl | split)


#print axioms ZZF3Skeleton.cmpUpdateSetPath2_label


theorem cmpUpdate_l_label
    {psi : Nat} (hpsi : 0 < psi)
    (l r : AgentState psi) :
    (cmpUpdate hpsi l r).1.label = l.label := by
  simp only [cmpUpdate, cmpUpdatePropagate_l_label,
    cmpUpdateSetPath2_label, agentState_label_ite, ite_same_local]


#print axioms ZZF3Skeleton.cmpUpdate_l_label


theorem cmpUpdate_r_label
    {psi : Nat} (hpsi : 0 < psi)
    (l r : AgentState psi) :
    (cmpUpdate hpsi l r).2.label = r.label := by
  simp only [cmpUpdate, cmpUpdatePropagate_r_label]


#print axioms ZZF3Skeleton.cmpUpdate_r_label


theorem compareSigInit_label
    {psi : Nat} (l : AgentState psi) :
    (compareSigInit l).label = l.label := by
  unfold compareSigInit
  try dsimp only []
  repeat (first | rfl | split)


#print axioms ZZF3Skeleton.compareSigInit_label


theorem compareSigDispatch_l_label
    {psi : Nat} (hpsi : 0 < psi)
    (l r : AgentState psi) :
    (compareSigDispatch hpsi l r).1.label = l.label :=
  (PPLLVerify.compareSigDispatch_labels_eq hpsi l r).1


#print axioms ZZF3Skeleton.compareSigDispatch_l_label


theorem compareSigDispatch_r_label
    {psi : Nat} (hpsi : 0 < psi)
    (l r : AgentState psi) :
    (compareSigDispatch hpsi l r).2.label = r.label :=
  (PPLLVerify.compareSigDispatch_labels_eq hpsi l r).2


#print axioms ZZF3Skeleton.compareSigDispatch_r_label


theorem compareSig_l_label
    {psi : Nat} (hpsi : 0 < psi)
    (l r : AgentState psi) :
    (compareSig hpsi l r).1.label = l.label := by
  unfold compareSig
  dsimp only []
  split
  · exact compareSigInit_label l
  · split
    · simp only [compareSigDispatch_l_label,
        cmpUpdate_l_label, compareSigInit_label]
    · exact compareSigInit_label l


#print axioms ZZF3Skeleton.compareSig_l_label


theorem compareSig_r_label
    {psi : Nat} (hpsi : 0 < psi)
    (l r : AgentState psi) :
    (compareSig hpsi l r).2.label = r.label := by
  unfold compareSig
  dsimp only []
  split
  · rfl
  · split
    · simp only [compareSigDispatch_r_label,
        cmpUpdate_r_label]
    · rfl


#print axioms ZZF3Skeleton.compareSig_r_label


theorem compareSig_labels_eq
    {psi : Nat} (hpsi : 0 < psi)
    (l r : AgentState psi) :
    (compareSig hpsi l r).1.label = l.label ∧
      (compareSig hpsi l r).2.label = r.label :=
  ⟨compareSig_l_label hpsi l r,
    compareSig_r_label hpsi l r⟩


#print axioms ZZF3Skeleton.compareSig_labels_eq


/-- Every stage after `pPsi` in `ppllNoBulletSignalCollision` frames both
labels.  The GENSIG frame is now discharged by its public theorem; the
Algorithm-15 no-collision label frame remains an explicit hypothesis. -/
theorem ppllNoBulletSignalCollision_labels_after_pPsi
    {psi : Nat} (hpsi : 0 < psi) (kappa : Nat)
    (hEliminate : ∀ a b : AgentState psi,
      (eliminateLeadersNoCollision hpsi a b).1.label = a.label ∧
        (eliminateLeadersNoCollision hpsi a b).2.label = b.label)
    (l r : AgentState psi) :
    (PPLLRepair.ppllNoBulletSignalCollision
        hpsi kappa l r).1.label =
      (pPsi hpsi l r).1.label ∧
    (PPLLRepair.ppllNoBulletSignalCollision
        hpsi kappa l r).2.label =
      (pPsi hpsi l r).2.label := by
  have hGenL : ∀ a b : AgentState psi,
      (genSig hpsi kappa a b).1.label = a.label :=
    fun a b => (ZZT1GenSig.genSig_label hpsi kappa a b).1
  have hGenR : ∀ a b : AgentState psi,
      (genSig hpsi kappa a b).2.label = b.label :=
    fun a b => (ZZT1GenSig.genSig_label hpsi kappa a b).2
  have hCleanL : ∀ a b : AgentState psi,
      (cleanSig hpsi a b).1.label = a.label :=
    fun a b => (PPLLVerify.cleanSig_labels_eq hpsi a b).1
  have hCleanR : ∀ a b : AgentState psi,
      (cleanSig hpsi a b).2.label = b.label :=
    fun a b => (PPLLVerify.cleanSig_labels_eq hpsi a b).2
  have hEliminateSigL : ∀ a b : AgentState psi,
      (eliminateSig hpsi a b).1.label = a.label :=
    fun a b => (ZZT1EliminateSig.eliminateSig_label hpsi a b).1
  have hEliminateSigR : ∀ a b : AgentState psi,
      (eliminateSig hpsi a b).2.label = b.label :=
    fun a b => (ZZT1EliminateSig.eliminateSig_label hpsi a b).2
  have hMoveL : ∀ a b : AgentState psi,
      (sigMove hpsi a b).1.label = a.label :=
    fun a b => (PPLLVerify.sigMove_labels_eq hpsi a b).1
  have hMoveR : ∀ a b : AgentState psi,
      (sigMove hpsi a b).2.label = b.label :=
    fun a b => (PPLLVerify.sigMove_labels_eq hpsi a b).2
  have hCheckL : ∀ a b : AgentState psi,
      (checkSig hpsi a b).1.label = a.label :=
    fun a b => (PPLLVerify.checkSig_labels_eq hpsi a b).1
  have hCheckR : ∀ a b : AgentState psi,
      (checkSig hpsi a b).2.label = b.label :=
    fun a b => (PPLLVerify.checkSig_labels_eq hpsi a b).2
  have hDisappearL : ∀ a b : AgentState psi,
      (disappear hpsi a b).1.label = a.label :=
    fun a b => (PPLLVerify.disappear_labels_eq hpsi a b).1
  have hDisappearR : ∀ a b : AgentState psi,
      (disappear hpsi a b).2.label = b.label :=
    fun a b => (PPLLVerify.disappear_labels_eq hpsi a b).2
  have hSuppressL : ∀ a b : AgentState psi,
      (suppressSig hpsi a b).1.label = a.label :=
    fun a b => (PPLLVerify.suppressSig_labels_eq hpsi a b).1
  have hSuppressR : ∀ a b : AgentState psi,
      (suppressSig hpsi a b).2.label = b.label :=
    fun a b => (PPLLVerify.suppressSig_labels_eq hpsi a b).2
  have hEliminateL : ∀ a b : AgentState psi,
      (eliminateLeadersNoCollision hpsi a b).1.label = a.label :=
    fun a b => (hEliminate a b).1
  have hEliminateR : ∀ a b : AgentState psi,
      (eliminateLeadersNoCollision hpsi a b).2.label = b.label :=
    fun a b => (hEliminate a b).2
  constructor
  · simp only [PPLLRepair.ppllNoBulletSignalCollision,
      PPLL.ppllBeforeEliminateLeaders, PPLL.ppllAfterCheck,
      PPLL.ppllBeforeCheck, PPLLVerify.writeSeq_l_label,
      hEliminateL, hSuppressL, compareSig_l_label,
      hDisappearL, hCheckL, hMoveL, hEliminateSigL,
      hCleanL, hGenL]
  · simp only [PPLLRepair.ppllNoBulletSignalCollision,
      PPLL.ppllBeforeEliminateLeaders, PPLL.ppllAfterCheck,
      PPLL.ppllBeforeCheck, PPLLVerify.writeSeq_r_label,
      hEliminateR, hSuppressR, compareSig_r_label,
      hDisappearR, hCheckR, hMoveR, hEliminateSigR,
      hCleanR, hGenR]


#print axioms ZZF3Skeleton.ppllNoBulletSignalCollision_labels_after_pPsi


/-- If `pPsi` has already produced a label-zero responder leader, every
post-`pPsi` stage in this chain preserves that fact through the final WRITE. -/
theorem ppllNoBulletSignalCollision_responder_leader_of_pPsi_zero
    {psi : Nat} (hpsi : 0 < psi) (kappa : Nat)
    (hEliminate : ∀ a b : AgentState psi,
      (eliminateLeadersNoCollision hpsi a b).1.label = a.label ∧
        (eliminateLeadersNoCollision hpsi a b).2.label = b.label)
    (l r : AgentState psi)
    (hPLeader : (pPsi hpsi l r).2.leader = true)
    (hPLabel : (pPsi hpsi l r).2.label = ⟨0, hpsi⟩) :
    (PPLLRepair.ppllNoBulletSignalCollision
      hpsi kappa l r).2.leader = true := by
  have hGenLeaderR : ∀ a b : AgentState psi,
      (genSig hpsi kappa a b).2.leader = b.leader :=
    fun a b => (ZZT1GenSig.genSig_leader hpsi kappa a b).2
  have hGenLabelR : ∀ a b : AgentState psi,
      (genSig hpsi kappa a b).2.label = b.label :=
    fun a b => (ZZT1GenSig.genSig_label hpsi kappa a b).2
  have hCleanLeaderR : ∀ a b : AgentState psi,
      (cleanSig hpsi a b).2.leader = b.leader :=
    fun a b => (PPLLVerify.cleanSig_leaders_eq hpsi a b).2
  have hCleanLabelR : ∀ a b : AgentState psi,
      (cleanSig hpsi a b).2.label = b.label :=
    fun a b => (PPLLVerify.cleanSig_labels_eq hpsi a b).2
  have hEliminateSigLeaderR : ∀ a b : AgentState psi,
      (eliminateSig hpsi a b).2.leader = b.leader :=
    fun a b => (PPLLVerify.eliminateSig_leaders_eq hpsi a b).2
  have hEliminateSigLabelR : ∀ a b : AgentState psi,
      (eliminateSig hpsi a b).2.label = b.label :=
    fun a b => (ZZT1EliminateSig.eliminateSig_label hpsi a b).2
  have hMoveLeaderR : ∀ a b : AgentState psi,
      (sigMove hpsi a b).2.leader = b.leader :=
    fun a b => (PPLLVerify.sigMove_leaders_eq hpsi a b).2
  have hMoveLabelR : ∀ a b : AgentState psi,
      (sigMove hpsi a b).2.label = b.label :=
    fun a b => (PPLLVerify.sigMove_labels_eq hpsi a b).2
  have hCheckLeaderR : ∀ a b : AgentState psi,
      b.leader = true → (checkSig hpsi a b).2.leader = true :=
    fun a b hb =>
      PPLLVerify.checkSig_responder_leader_of_true hpsi a b hb
  have hCheckLabelR : ∀ a b : AgentState psi,
      (checkSig hpsi a b).2.label = b.label :=
    fun a b => (PPLLVerify.checkSig_labels_eq hpsi a b).2
  have hDisappearLeaderR : ∀ a b : AgentState psi,
      (disappear hpsi a b).2.leader = b.leader :=
    fun a b => (PPLLVerify.disappear_leaders_eq hpsi a b).2
  have hDisappearLabelR : ∀ a b : AgentState psi,
      (disappear hpsi a b).2.label = b.label :=
    fun a b => (PPLLVerify.disappear_labels_eq hpsi a b).2
  have hCompareLeaderR : ∀ a b : AgentState psi,
      (compareSig hpsi a b).2.leader = b.leader :=
    fun a b => (PPLLVerify.compareSig_leaders_eq hpsi a b).2
  have hCompareLabelR : ∀ a b : AgentState psi,
      (compareSig hpsi a b).2.label = b.label :=
    fun a b => compareSig_r_label hpsi a b
  have hSuppressLeaderR : ∀ a b : AgentState psi,
      (suppressSig hpsi a b).2.leader = b.leader :=
    fun a b => (PPLLVerify.suppressSig_leaders_eq hpsi a b).2
  have hSuppressLabelR : ∀ a b : AgentState psi,
      (suppressSig hpsi a b).2.label = b.label :=
    fun a b => (PPLLVerify.suppressSig_labels_eq hpsi a b).2
  have hNoCollisionLeaderR : ∀ a b : AgentState psi,
      (eliminateLeadersNoCollision hpsi a b).2.leader = b.leader :=
    fun a b =>
      PPLLNoCheckBirthLeaderFrames.eliminateLeadersNoCollision_responder_leader_eq
        hpsi a b
  have hNoCollisionLabelR : ∀ a b : AgentState psi,
      (eliminateLeadersNoCollision hpsi a b).2.label = b.label :=
    fun a b => (hEliminate a b).2
  have hWriteLeaderR : ∀ a b : AgentState psi,
      b.leader = true → b.label = ⟨0, hpsi⟩ →
        (writeSeq hpsi a b).2.leader = true :=
    fun a b hb hl =>
      PPLLVerify.writeSeq_responder_leader_of_label_zero
        hpsi a b hb hl
  simp only [PPLLRepair.ppllNoBulletSignalCollision,
    PPLL.ppllBeforeEliminateLeaders, PPLL.ppllAfterCheck,
    PPLL.ppllBeforeCheck, hPLeader, hPLabel,
    hGenLeaderR, hGenLabelR,
    hCleanLeaderR, hCleanLabelR,
    hEliminateSigLeaderR, hEliminateSigLabelR,
    hMoveLeaderR, hMoveLabelR,
    hCheckLeaderR, hCheckLabelR,
    hDisappearLeaderR, hDisappearLabelR,
    hCompareLeaderR, hCompareLabelR,
    hSuppressLeaderR, hSuppressLabelR,
    hNoCollisionLeaderR, hNoCollisionLabelR,
    hWriteLeaderR]


#print axioms ZZF3Skeleton.ppllNoBulletSignalCollision_responder_leader_of_pPsi_zero


/-- Pair-level F3.  A leaderless responder cannot be a fixed point of the
full chain on a barrier edge. -/
theorem ppllNoBulletSignalCollision_fixed_forces_nonbarrier
    {psi : Nat} (hpsi : 0 < psi) (kappa : Nat)
    (hEliminate : ∀ a b : AgentState psi,
      (eliminateLeadersNoCollision hpsi a b).1.label = a.label ∧
        (eliminateLeadersNoCollision hpsi a b).2.label = b.label)
    (l r : AgentState psi)
    (_hl : l.leader = false) (hr : r.leader = false)
    (hfix : PPLLRepair.ppllNoBulletSignalCollision
      hpsi kappa l r = (l, r)) :
    ¬isBarrier hpsi l r := by
  have hFinalLabel :
      (PPLLRepair.ppllNoBulletSignalCollision
        hpsi kappa l r).2.label = r.label := by
    simpa only using
      (congrArg
        (fun q : AgentState psi × AgentState psi => q.2.label)
        hfix)
  have hAfter :=
    ppllNoBulletSignalCollision_labels_after_pPsi
      hpsi kappa hEliminate l r
  have hPFixedLabel : (pPsi hpsi l r).2.label = r.label :=
    hAfter.2.symm.trans hFinalLabel
  intro hBarrier
  have hb :
      r.label ≠
        (⟨(l.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ : Fin psi) := by
    simpa only [isBarrier] using hBarrier
  by_cases hp : r.probe = true
  · have hPLeader : (pPsi hpsi l r).2.leader = true := by
      simp [PPLL.pPsi, hb, hp]
    have hPZero :
        (pPsi hpsi l r).2.label = (⟨0, hpsi⟩ : Fin psi) := by
      simp [PPLL.pPsi, hb, hp]
    have hPersist :=
      ppllNoBulletSignalCollision_responder_leader_of_pPsi_zero
        hpsi kappa hEliminate l r hPLeader hPZero
    have hFinalLeader :
        (PPLLRepair.ppllNoBulletSignalCollision
          hpsi kappa l r).2.leader = r.leader := by
      simpa only using
        (congrArg
          (fun q : AgentState psi × AgentState psi => q.2.leader)
          hfix)
    have hfalse : true = false :=
      hPersist.symm.trans (hFinalLeader.trans hr)
    cases hfalse
  · have hPNext :
        (pPsi hpsi l r).2.label =
          (⟨(l.label.val + 1) % psi,
            Nat.mod_lt _ hpsi⟩ : Fin psi) := by
      simp [PPLL.pPsi, hb, hp, hr]
    exact hb (hPFixedLabel.symm.trans hPNext)


#print axioms ZZF3Skeleton.ppllNoBulletSignalCollision_fixed_forces_nonbarrier


/-- Edgewise F3: in a leaderless edgewise fixed configuration, every
responder has the successor label of its initiator. -/
theorem leaderless_edgewiseFixed_forces_successor_labels
    {n psi : Nat} (hpsi : 0 < psi) (kappa : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState psi)
    (hEliminate : ∀ a b : AgentState psi,
      (eliminateLeadersNoCollision hpsi a b).1.label = a.label ∧
        (eliminateLeadersNoCollision hpsi a b).2.label = b.label)
    (hfixed : EdgewiseFixed ring
      (PPLLRepair.ppllNoBulletSignalCollision hpsi kappa) C)
    (hlead : ∀ i : Fin n, (C i).leader = false) :
    ∀ e : Fin n,
      (C (ring.rightNeighbor e)).label.val =
        ((C e).label.val + 1) % psi := by
  intro e
  have hNonBarrier :=
    ppllNoBulletSignalCollision_fixed_forces_nonbarrier
      hpsi kappa hEliminate
      (C e) (C (ring.rightNeighbor e))
      (hlead e) (hlead (ring.rightNeighbor e)) (hfixed e)
  by_cases heq :
      (C (ring.rightNeighbor e)).label =
        (⟨((C e).label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ : Fin psi)
  · simpa only using (congrArg Fin.val heq)
  · have hBarrier :
        isBarrier hpsi (C e) (C (ring.rightNeighbor e)) := by
      simpa only [isBarrier] using heq
    exact (hNonBarrier hBarrier).elim


#print axioms ZZF3Skeleton.leaderless_edgewiseFixed_forces_successor_labels


end ZZF3Skeleton
