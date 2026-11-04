import Leader.Wu.ShortGap.SpliceCommit
import Leader.Wu.ShortGap.SpliceAdoptCorrected
open ShortGapSpliceCommit


namespace ShortGapSpliceFusedRow


/--
The six structural conjuncts of the direct fused retirement guard do not by
themselves exclude `RetireLaunch` on an arbitrary `SNode`, because `SEmpty`
does not mention `splice`.  The final conjunct is therefore the minimal extra
disjointness guard needed for a theorem over arbitrary states.
-/
abbrev RetireFused (a b : SNode) : Prop :=
  a.splice = .adopted ∧
    a.witness = .none ∧
    b.splice = .bridged ∧
    b.core.leader = false ∧
    settledCw b.core.raw = true ∧
    b.witness = .none ∧
    ¬ SEmpty a


instance instDecidableRetireFused (a b : SNode) :
    Decidable (RetireFused a b) := by
  unfold RetireFused
  infer_instance


/-- Length-one retirement: convert the adopted source and drain the bridge in
one firing on the direct edge. -/
def retireFused (a b : SNode) : SNode × SNode :=
  (retiredL a, drainR b)


/-- The old splice table extended by the direct length-one retirement row. -/
def spliceRowF (a b : SNode) : SNode × SNode :=
  if h : RetireFused a b then
    retireFused a b
  else
    spliceRow a b




theorem retireFused_disjoint (a b : SNode) :
    RetireFused a b →
      ¬ RetireLaunch a b ∧ ¬ RetireDeposit a b ∧ ¬ RetireBackward a b := by
  intro hf
  have hnotEmpty : ¬ SEmpty a := hf.2.2.2.2.2.2
  have hbwNone : b.witness = RetireWitness.none := hf.2.2.2.2.2.1
  constructor
  · intro hlaunch
    exact hnotEmpty hlaunch.1
  · constructor
    · intro hdeposit
      have hnoneToken : RetireWitness.none = RetireWitness.token :=
        hbwNone.symm.trans hdeposit.2.2
      cases hnoneToken
    · intro hbackward
      exact hnotEmpty hbackward.1




theorem spliceRowF_eq_of_not_fused (a b : SNode)
    (h : ¬ RetireFused a b) :
    spliceRowF a b = spliceRow a b := by
  simp [spliceRowF, h]




theorem spliceRowF_frame (a b : SNode) (h : RetireFused a b) :
    (spliceRowF a b).1.core = a.core ∧
      (spliceRowF a b).2.core = b.core := by
  rw [spliceRowF, dif_pos h]
  exact ⟨rfl, rfl⟩




theorem fused_lands (a b : SNode) (h : RetireFused a b) :
    (spliceRowF a b).1.splice = SpliceCtl.retired ∧
      (spliceRowF a b).2.splice = SpliceCtl.drained ∧
      ¬ RetireFused (retiredL a) (drainR b) := by
  have hleft : (spliceRowF a b).1.splice = SpliceCtl.retired := by
    rw [spliceRowF, dif_pos h]
    rfl
  have hright : (spliceRowF a b).2.splice = SpliceCtl.drained := by
    rw [spliceRowF, dif_pos h]
    rfl
  have hnotAgain : ¬ RetireFused (retiredL a) (drainR b) := by
    intro hf
    have hs : (retiredL a).splice = SpliceCtl.adopted := hf.1
    change SpliceCtl.retired = SpliceCtl.adopted at hs
    cases hs
  constructor
  · exact hleft
  · constructor
    · exact hright
    · exact hnotAgain




theorem fused_debt_one : 1 ≤ spliceDebt 1 := by
  simp [spliceDebt]


end ShortGapSpliceFusedRow


#print axioms ShortGapSpliceFusedRow.retireFused_disjoint
#print axioms ShortGapSpliceFusedRow.spliceRowF_eq_of_not_fused
#print axioms ShortGapSpliceFusedRow.spliceRowF_frame
#print axioms ShortGapSpliceFusedRow.fused_lands
#print axioms ShortGapSpliceFusedRow.fused_debt_one
