import Leader.PPL.Safety.SPLTokenResidualRoute

namespace PPL.Safety.SPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/--
Old-image branch of black post-token correctness.

Truth route: SPLPostTokenOldImage supplies an old physical source occurrence;
initialGhost supplies its ghost owner, remark2_one_step_unique transports the
already-correct SPLAt token, and splAlgorithm23FieldFrameResidual_proved fixes
every id bit, hence sourceIota, so the source-change alternative is impossible.
-/
def SPLAlgorithm23BlackOldImageRow : Prop :=
  PPL.remark2_one_step_unique ->
  forall {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    SPLAt ring root C ->
    forall
      (seg : Fin (segmentCount n psi - 2))
      (i : Fin n)
      (t' : TokenData psi),
      tokenAt .black
          (nextConfig ring C e i) =
        some t' ->
      SPLPostTokenOldImage
          hpsi ring C e i .black t' ->
      (ValidToken .black
          (nextConfig ring C e) i /\
        WorkingFor ring root
          (nextConfig ring C e)
          i .black seg.val) ->
      CorrectToken ring root
        (nextConfig ring C e)
        i .black seg.val

/--
Fresh line-14/15 branch of black post-token correctness.

Truth route: the fresh certificate is exactly the border birth with the
+psi token and x = 0 payload; SPLAt canonical geometry plus WorkingFor pins
the source to the corresponding even interior pair, giving CorrectToken.
-/
def SPLAlgorithm23BlackFreshBirthRow : Prop :=
  forall {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    SPLAt ring root C ->
    forall
      (seg : Fin (segmentCount n psi - 2))
      (i : Fin n)
      (t' : TokenData psi),
      tokenAt .black
          (nextConfig ring C e i) =
        some t' ->
      SPLFreshBorderBirthImage
          hpsi 0 ring C e i .black t' ->
      (ValidToken .black
          (nextConfig ring C e) i /\
        WorkingFor ring root
          (nextConfig ring C e)
          i .black seg.val) ->
      CorrectToken ring root
        (nextConfig ring C e)
        i .black seg.val

/--
Exhaustive provenance adapter to the existing black correctness row.

No projection from SPLPostTokenOldImage or SPLFreshBorderBirthImage is used
here; the two certificates are passed to the corresponding leaf verbatim.
-/
theorem splAlgorithm23BlackCorrectnessRow_of_caseRows
    (hOld : SPLAlgorithm23BlackOldImageRow)
    (hFresh : SPLAlgorithm23BlackFreshBirthRow) :
    SPLAlgorithm23BlackCorrectnessRow := by
  unfold SPLAlgorithm23BlackOldImageRow at hOld
  unfold SPLAlgorithm23BlackFreshBirthRow at hFresh
  unfold SPLAlgorithm23BlackCorrectnessRow

  intro hRemark
  intro n psi kappa
  intro hn3 hpsi ring root C e hSPL
  intro seg i hVW

  rcases hVW with ⟨hValid, hWork⟩

  cases ht :
      tokenAt .black
        (nextConfig ring C e i) with
  | none =>
      unfold ValidToken at hValid
      rw [ht] at hValid
      exact False.elim hValid
  | some t' =>
      have hp :
          SPLPostTokenOldImage
              hpsi ring C e i .black t' \/
            SPLFreshBorderBirthImage
              hpsi 0 ring C e i .black t' :=
        splPostTokenProvenance_proved
          hn3 hpsi 0 ring root C e hSPL
          i .black t' ht

      rcases hp with hOldImage | hFreshImage
      · exact
          hOld hRemark
            hn3 hpsi ring root C e hSPL
            seg i t' ht hOldImage
            ⟨hValid, hWork⟩
      · exact
          hFresh
            hn3 hpsi ring root C e hSPL
            seg i t' ht hFreshImage
            ⟨hValid, hWork⟩

end PPL.Safety.SPL

#print axioms PPL.Safety.SPL.splAlgorithm23BlackCorrectnessRow_of_caseRows
