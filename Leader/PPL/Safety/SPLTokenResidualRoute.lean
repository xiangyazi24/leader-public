import Leader.PPL.Safety.SPLPersistenceClosed
import Leader.PPL.Safety.SPLTokenProvenance


namespace PPL.Safety.SPL


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


/--
No-new-risky is already reduced on main to the two interacted sites.
Off-pair sites are literal frames.


Truth argument: old positive motion preserves its physical target; a fresh
border birth points out of rooted S_0; a c = -1 turn creates a +psi token
whose path leaves S_0; and the only positive wrap into S_0 would cross the
final-segment/root boundary, where canonical last = true closes line 13.
-/
def SPLAlgorithm23NoNewRiskyRow : Prop :=
  SPLNoNewRiskySelectedPair


/--
Black post-token correctness.


Use splPostTokenProvenance_proved with step 0.  In the old-image branch,
initialGhost supplies the physical owner and the supplied repaired Remark 2
transports correctness because the SPL field frame keeps sourceIota fixed.
In the fresh-birth branch, the literal line-14/15 payload is the x = 0
binary-successor payload; SPLAt geometry identifies the interior pair and
its parity.
-/
def SPLAlgorithm23BlackCorrectnessRow : Prop :=
  PPL.remark2_one_step_unique →
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    SPLAt ring root C →
    ∀ (seg : Fin (segmentCount n psi - 2))
      (i : Fin n),
      (ValidToken .black
          (nextConfig ring C e) i ∧
        WorkingFor ring root
          (nextConfig ring C e)
          i .black seg.val) →
      CorrectToken ring root
        (nextConfig ring C e)
        i .black seg.val


/--
White mirror of SPLAlgorithm23BlackCorrectnessRow.


SPLTokenProvenance's selected-input projection already accounts for the
preceding black MoveToken call, so no extra black/white frame premise is
needed in this statement.
-/
def SPLAlgorithm23WhiteCorrectnessRow : Prop :=
  PPL.remark2_one_step_unique →
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    SPLAt ring root C →
    ∀ (seg : Fin (segmentCount n psi - 2))
      (i : Fin n),
      (ValidToken .white
          (nextConfig ring C e) i ∧
        WorkingFor ring root
          (nextConfig ring C e)
          i .white seg.val) →
      CorrectToken ring root
        (nextConfig ring C e)
        i .white seg.val


/--
Exact adapter from the three strictly smaller one-step rows to the only
remaining SPL Algorithm-2/3 token residual.
-/
theorem splAlgorithm23TokenResidual_proved_of_rows
    (hRisk : SPLAlgorithm23NoNewRiskyRow)
    (hBlack : SPLAlgorithm23BlackCorrectnessRow)
    (hWhite : SPLAlgorithm23WhiteCorrectnessRow) :
    SPLAlgorithm23TokenResidual := by
  unfold SPLAlgorithm23NoNewRiskyRow at hRisk
  unfold SPLAlgorithm23BlackCorrectnessRow at hBlack
  unfold SPLAlgorithm23WhiteCorrectnessRow at hWhite
  unfold SPLAlgorithm23TokenResidual
  intro hRemark
  intro n psi kappa hn3 hpsi ring root C e hSPL
  dsimp only
  refine And.intro ?_ ?_
  · exact
      splNoNewRisky_of_selectedPair
        hRisk hn3 hpsi ring root C e hSPL
  · intro seg i
    refine And.intro ?_ ?_
    · intro hb
      exact
        hBlack hRemark
          hn3 hpsi ring root C e hSPL
          seg i hb
    · intro hw
      exact
        hWhite hRemark
          hn3 hpsi ring root C e hSPL
          seg i hw


end PPL.Safety.SPL


#print axioms PPL.Safety.SPL.splAlgorithm23TokenResidual_proved_of_rows
