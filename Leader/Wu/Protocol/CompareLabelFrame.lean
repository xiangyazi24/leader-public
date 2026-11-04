import Leader.Wu.Birth.LeaderlessEscapeCleanBotRepairs

set_option autoImplicit false
set_option Elab.async false

namespace ZZCmpLabel

open PPLL

/-- The COMPARE initializer rewrites only the state field. -/
theorem compareSigInit_label {ψ : Nat} (l : AgentState ψ) :
    (compareSigInit l).label = l.label := by
  unfold compareSigInit
  repeat (first | rfl | dsimp only | split)

/-- The left bit-update helper rewrites only path2. -/
theorem compareBitUpdateL_label {ψ : Nat} (hψ : ψ > 0) (l : AgentState ψ) :
    (compareBitUpdateL hψ l).label = l.label := by
  unfold compareBitUpdateL
  repeat (first | rfl | dsimp only | split)

/-- The right bit-update helper rewrites only path2. -/
theorem compareBitUpdateR_label {ψ : Nat} (hψ : ψ > 0) (r : AgentState ψ) :
    (compareBitUpdateR hψ r).label = r.label := by
  unfold compareBitUpdateR
  repeat (first | rfl | dsimp only | split)

/-- compareBit rewrites only path2 on both sides. -/
theorem compareBit_label {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (compareBit hψ l r).1.label = l.label ∧ (compareBit hψ l r).2.label = r.label := by
  unfold compareBit
  dsimp only
  exact ⟨compareBitUpdateL_label hψ l, compareBitUpdateR_label hψ r⟩

/-- The dispatch falls through to compareBit or to the identity pair. -/
theorem compareSigDispatch_label {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (compareSigDispatch hψ l r).1.label = l.label ∧
      (compareSigDispatch hψ l r).2.label = r.label := by
  unfold compareSigDispatch
  repeat (first | (exact compareBit_label hψ l r) | (exact ⟨rfl, rfl⟩) | dsimp only | split)

/-- Propagation rewrites only states and the leader flag. -/
theorem cmpUpdatePropagate_label {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (cmpUpdatePropagate hψ l r).1.label = l.label ∧
      (cmpUpdatePropagate hψ l r).2.label = r.label := by
  unfold cmpUpdatePropagate
  repeat (first | (exact ⟨rfl, rfl⟩) | dsimp only | split)

/-- The path2 writer rewrites only path2. -/
theorem cmpUpdateSetPath2_label {ψ : Nat} (hψ : ψ > 0) (l : AgentState ψ) :
    (cmpUpdateSetPath2 hψ l).label = l.label := by
  unfold cmpUpdateSetPath2
  repeat (first | rfl | dsimp only | split)

/-- The guarded update keeps both labels. -/
theorem cmpUpdateGuarded_label {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (ZZRepairAll8.cmpUpdateGuarded hψ l r).1.label = l.label ∧
      (ZZRepairAll8.cmpUpdateGuarded hψ l r).2.label = r.label := by
  unfold ZZRepairAll8.cmpUpdateGuarded
  dsimp only
  split
  · exact ⟨(cmpUpdateSetPath2_label hψ _).trans
      (cmpUpdatePropagate_label hψ _ r).1,
      (cmpUpdatePropagate_label hψ _ r).2⟩
  · exact ⟨(cmpUpdateSetPath2_label hψ _).trans
      (cmpUpdatePropagate_label hψ _ r).1,
      (cmpUpdatePropagate_label hψ _ r).2⟩

/-- Main lemma: the COMPARE guarded wrapper never transfers the left label. -/
theorem cmp_preserves_left_label {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (ZZRepairAll8.compareSigGuarded hψ l r).1.label = l.label := by
  unfold ZZRepairAll8.compareSigGuarded
  dsimp only
  split
  · exact compareSigInit_label l
  · split
    · exact ((compareSigDispatch_label hψ _ _).1.trans
        (cmpUpdateGuarded_label hψ _ r).1).trans (compareSigInit_label l)
    · exact compareSigInit_label l

#print axioms cmp_preserves_left_label
#print axioms compareSigDispatch_label
#print axioms cmpUpdatePropagate_label

end ZZCmpLabel
