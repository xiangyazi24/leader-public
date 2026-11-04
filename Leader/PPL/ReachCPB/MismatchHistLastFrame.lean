import Leader.PPL.ReachCPB.MismatchCompletionHistSplit
import Leader.PPL.ReachCPB.CdGeometryPairStep
import Leader.PPL.TokenCompletion.GhostStepMirror

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/--
The physical `.last` frame through one proof-only ghost step.

This is intentionally stronger than the historical branch: no non-CPB
hypothesis is required.  LastReadyCapped supplies exactly the three physical
premises of `lemma16CdGeometryStep_closed`:

* DetectReady gives pre-step leaderlessness;
* DistReadyCapped gives the cyclic successor-distance equation;
* LastReadyCapped gives pre-step `last = false` everywhere.

The compiled geometry step first proves the *post-step/pre-step equality* of
the last field.  Only then is the pre-step false value used.
-/
private theorem mismatchHistGhostStep_last_frame
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (step : Nat)
    (G : PPL.GhostConfig n psi kappa)
    (e : Fin n)
    (hready : LastReadyCapped ring G.phys) :
    forall i : Fin n,
      ((PPL.ghostStep hpsi ring step G e).phys i).last = false := by
  unfold LastReadyCapped at hready
  rcases hready with ⟨hdistReady, hlast⟩

  unfold DistReadyCapped at hdistReady
  rcases hdistReady with ⟨hdetectCapped, hdist⟩

  unfold DetectReadyCapped at hdetectCapped
  rcases hdetectCapped with ⟨hdetect, _hcap⟩

  unfold DetectReady at hdetect
  rcases hdetect with
    ⟨_hpeace, hleaderless, _hsignalFree, _hallDetect⟩

  intro i

  have hfields :=
    lemma16CdGeometryStep_closed
      hn3 hpsi ring G.phys e
      hleaderless hdist hlast i
  dsimp only at hfields

  rw [PPL.ghostStep_phys_export
    hpsi ring step G e]

  exact hfields.2.trans (hlast i)


theorem lemma16MismatchHistLastFrameBranch_proved :
    Lemma16MismatchHistLastFrameBranch := by
  unfold Lemma16MismatchHistLastFrameBranch
  intro n psi kappa hpsi hn3 ring C0 pre e
  dsimp only
  intro hready _hnotCPB i

  exact
    mismatchHistGhostStep_last_frame
      hpsi hn3 ring pre.length
      (PPL.ghostRun hpsi ring 0
        (PPL.initialGhost C0) pre)
      e hready i

end PPL.Convergence.ReachCPB

#print axioms PPL.Convergence.ReachCPB.lemma16MismatchHistLastFrameBranch_proved
