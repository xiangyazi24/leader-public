import Leader.PPL.ReachCPB.BulletGlue
import Leader.PPL.Convergence.BulletLineageSweepReach

/-! Lemma 15 closes the Lemma 16 bullet-sweep leaf unconditionally. -/

namespace PPL.Convergence.ReachCPB

theorem lemma16BulletSweepNatBound_closed :
    Lemma16BulletSweepNatBound :=
  lemma16BulletSweepNatBound_of_sublist
    PPL.Convergence.BulletLineage.lemma15SublistSweep_proved

end PPL.Convergence.ReachCPB

#print axioms PPL.Convergence.ReachCPB.lemma16BulletSweepNatBound_closed
