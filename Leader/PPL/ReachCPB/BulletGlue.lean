import Leader.PPL.Convergence.BulletLineage
import Leader.PPL.ReachCPB.WordBound


namespace PPL.Convergence.ReachCPB


set_option autoImplicit false
set_option Elab.async false


open PPL.Probability


private theorem countP_mono_bulletGlue
    {A : Type}
    (xs : List A)
    (p q : A -> Bool)
    (hpq : forall x, p x = true -> q x = true) :
    xs.countP p <= xs.countP q := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.countP_cons, List.countP_cons]
      cases hp : p x with
      | false =>
          cases hq : q x <;>
            simp [hp, hq] <;>
            omega
      | true =>
          have hqx : q x = true :=
            hpq x hp
          simp [hp, hqx]
          omega


/-- Glue Lemma 15's ordered-subsequence endpoint theorem into the exact
Nat interface consumed by the Lemma 16 assembly.

There is no interface mismatch:
* BulletSweep.Config and ReachCPB.Config are both PPL.Config;
* lemma16H15 and BulletSweep.lemma15Horizon are definitionally the same
  horizon after unfolding their identical log2 parameters;
* the endpoint predicates are the same AllLivePeaceful proposition;
* BulletSweep.run and Probability.runPPL are the same physical P_PL run.

Thus an endpoint failure can only occur on a schedule missing the prescribed
two-sweep word as an ordered subsequence.  The existing fixed-word count then
supplies the one-over-n bound. -/
theorem lemma16BulletSweepNatBound_of_sublist
    (h :
      PPL.Convergence.BulletSweep.Lemma15SublistSweep) :
    Lemma16BulletSweepNatBound := by
  intro n psi kappa hn3 hpsi ring C

  have hdom :
      endpointFailureCount
          ring (allLivePeacefulB ring) C
          (lemma16H15 n) <=
        PPL.Probability.fixedWordMissCount
          (PPL.Convergence.BulletSweep.lemma15SweepWord ring)
          (lemma16H15 n) := by
    unfold endpointFailureCount
    change
      (allSchedules n (lemma16H15 n)).countP
          (fun schedule =>
            !allLivePeacefulB ring
              (PPL.Probability.runPPL
                ring C schedule)) <=
        (allSchedules n (lemma16H15 n)).countP
          (fun schedule =>
            decide
              (Not
                ((PPL.Convergence.BulletSweep.lemma15SweepWord
                    ring).Sublist schedule)))
    apply countP_mono_bulletGlue
    intro schedule hbad
    by_cases hsub :
        (PPL.Convergence.BulletSweep.lemma15SweepWord
          ring).Sublist schedule
    · have hgoodSweep :=
        h hn3 hpsi ring C schedule hsub
      have hgood :
          AllLivePeaceful ring
            (PPL.Probability.runPPL
              ring C schedule) := by
        simpa
          [AllLivePeaceful,
            PPL.Convergence.BulletSweep.AllLivePeaceful,
            PPL.Convergence.BulletSweep.run,
            PPL.Probability.runPPL]
          using hgoodSweep
      have hgoodB :
          allLivePeacefulB ring
              (PPL.Probability.runPPL
                ring C schedule) = true := by
        simp [allLivePeacefulB, hgood]
      have hfalse : False := by
        simpa [hgoodB] using hbad
      exact False.elim hfalse
    · simp [hsub]

  have hH :
      lemma16H15 n =
        PPL.Convergence.BulletSweep.lemma15Horizon n := by
    simp
      [lemma16H15, lemma16K,
        PPL.Convergence.BulletSweep.lemma15Horizon,
        PPL.Convergence.BulletSweep.lemma15K]

  have hmiss :=
    PPL.Convergence.BulletSweep.lemma15_fixedWordMiss_one_over_n
      hn3 ring

  calc
    n *
        endpointFailureCount
          ring (allLivePeacefulB ring) C
          (lemma16H15 n) <=
      n *
        PPL.Probability.fixedWordMissCount
          (PPL.Convergence.BulletSweep.lemma15SweepWord ring)
          (lemma16H15 n) :=
      Nat.mul_le_mul_left n hdom
    _ =
      n *
        PPL.Probability.fixedWordMissCount
          (PPL.Convergence.BulletSweep.lemma15SweepWord ring)
          (PPL.Convergence.BulletSweep.lemma15Horizon n) := by
      rw [hH]
    _ <=
      n ^
        PPL.Convergence.BulletSweep.lemma15Horizon n :=
      hmiss
    _ = n ^ lemma16H15 n := by
      rw [hH]


end PPL.Convergence.ReachCPB


#print axioms PPL.Convergence.ReachCPB.lemma16BulletSweepNatBound_of_sublist

