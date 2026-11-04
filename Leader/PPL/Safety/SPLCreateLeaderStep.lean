import Leader.PPL.Safety.SPL
import Leader.PPL.Safety.PeacefulScan
import Leader.PPL.TokenCorrectness.PersistencePairRow

namespace PPL.Safety.SPL

set_option autoImplicit false
set_option Elab.async false

/-
Truth audit against the literal current Transition.lean:
* in rooted CDL geometry, Algorithm-2 line 4 computes the responder's
  already-canonical distance (zero when the responder is the root, otherwise
  the clockwise successor), so the line-6 inconsistency branch cannot create
  a leader;
* line 8 therefore writes the existing canonical responder distance;
* line 9 writes the existing canonical initiator last bit.
MoveToken and Algorithm 5 frame dist/last.  The remaining nontrivial local
field work is Algorithm-3 line 20 (no new follower leader) and line 22
(idempotent source-id write).  Token preservation is the Remark-2 consumer.

The two residual Props below are intentionally smaller than
SPLAlgorithm23StepProp:
1. SPLAlgorithm23FieldFrameResidual: only the pointwise field frame needed
   to derive the first three global conjuncts;
2. SPLAlgorithm23TokenResidual: only no-risk + post-token correctness, after
   remark2_one_step_unique has been supplied.
-/

/-- The five non-CPB clauses of the Lemma-14 local step. -/
def SPLAlgorithm23StepProp : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    SPLAt ring root C ->
    let C' := nextConfig ring C e
    And
      (∀ i : Fin n, (C' i).leader = true ↔ i = root)
      (And
        (∀ i : Fin n,
          let off := cyclicOffset ring root i
          let zeta := segmentCount n psi
          And
            ((C' i).dist.val = off % (2 * psi))
            ((C' i).last = true ↔ psi * (zeta - 1) ≤ off))
        (And
          (∀ s : Nat,
            rootedSegmentId ring root C' s =
              rootedSegmentId ring root C s)
          (And
            (∀ i : Fin n, Not (Risky ring root C' i))
            (∀ seg : Fin (segmentCount n psi - 2),
              ∀ i : Fin n,
                And
                  ((And
                      (ValidToken .black C' i)
                      (WorkingFor ring root C' i .black seg.val)) ->
                    CorrectToken ring root C' i .black seg.val)
                  ((And
                      (ValidToken .white C' i)
                      (WorkingFor ring root C' i .white seg.val)) ->
                    CorrectToken ring root C' i .white seg.val)))))

/--
Residual 1: the local full-step field frame.

The first clause says an old follower is never turned into a leader.
The other three clauses say the three fields read by the rooted geometry /
segment-ID layer are pointwise framed.  Algorithm 5 already frames
dist/last/id; source audit shows Algorithm 2 frames dist/last in CDLAt.
Thus the real branch content left here is the selected-token Algorithm-3
line-20/22 row plus the small boundary packaging.
-/
def SPLAlgorithm23FieldFrameResidual : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    SPLAt ring root C ->
    let C' := nextConfig ring C e
    And
      (∀ i : Fin n,
        (C i).leader = false -> (C' i).leader = false)
      (And
        (∀ i : Fin n, (C' i).dist = (C i).dist)
        (And
          (∀ i : Fin n, (C' i).last = (C i).last)
          (∀ i : Fin n, (C' i).id = (C i).id)))

/--
Residual 2: after the repaired Remark-2 one-step theorem is available,
the only token layer still required by Lemma 14 is no new risky token plus
correctness of every post-step valid working interior token.
-/
def SPLAlgorithm23TokenResidual : Prop :=
  PPL.remark2_one_step_unique ->
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    SPLAt ring root C ->
    let C' := nextConfig ring C e
    And
      (∀ i : Fin n, Not (Risky ring root C' i))
      (∀ seg : Fin (segmentCount n psi - 2),
        ∀ i : Fin n,
          And
            ((And
                (ValidToken .black C' i)
                (WorkingFor ring root C' i .black seg.val)) ->
              CorrectToken ring root C' i .black seg.val)
            ((And
                (ValidToken .white C' i)
                (WorkingFor ring root C' i .white seg.val)) ->
              CorrectToken ring root C' i .white seg.val))

/-! ## ID-frame transport -/

theorem segmentIdAux_eq_of_id_eq
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C C' : Config n psi kappa)
    (start : Fin n)
    (hid : ∀ i : Fin n, (C' i).id = (C i).id) :
    ∀ len j : Nat,
      segmentIdAux ring C' start len j =
        segmentIdAux ring C start len j := by
  intro len
  induction len with
  | zero =>
      intro j
      rfl
  | succ len ih =>
      intro j
      simp only [segmentIdAux]
      rw [hid (shiftRight ring start j)]
      rw [ih (j + 1)]

theorem rootedSegmentId_eq_of_id_eq
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C C' : Config n psi kappa)
    (hid : ∀ i : Fin n, (C' i).id = (C i).id)
    (s : Nat) :
    rootedSegmentId ring root C' s =
      rootedSegmentId ring root C s := by
  unfold rootedSegmentId segmentIdFrom
  exact
    segmentIdAux_eq_of_id_eq
      ring C C'
      (shiftRight ring root (s * psi))
      hid
      (segmentLength n psi s)
      0

/-! ## First three Algorithm-2/3 conjuncts from the pointwise frame -/

theorem splAlgorithm23_leader_of_field
    (hfield : SPLAlgorithm23FieldFrameResidual)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hC : SPLAt ring root C) :
    let C' := nextConfig ring C e
    ∀ i : Fin n, (C' i).leader = true ↔ i = root := by
  let C' : Config n psi kappa := nextConfig ring C e
  have hf := hfield hn3 hpsi ring root C e hC
  dsimp only at hf
  have hpre :
      ∀ i : Fin n, (C i).leader = true ↔ i = root :=
    hC.1.2.1
  have hcpb :
      CPB ring C' := by
    simpa [C', nextConfig] using
      (PPL.Safety.PeacefulProps.cpb_step_closed_proved
        hn3 hpsi ring C e hC.1.1)
  have hpostToRoot :
      ∀ i : Fin n, (C' i).leader = true -> i = root := by
    intro i hi
    cases hc : (C i).leader with
    | false =>
        have hbad : true = false := by
          calc
            true = (C' i).leader := hi.symm
            _ = false := hf.1 i hc
        cases hbad
    | true =>
        exact (hpre i).1 hc
  have hroot : (C' root).leader = true := by
    rcases hcpb.1 with ⟨j, hj⟩
    have hjr : j = root := hpostToRoot j hj
    subst j
    exact hj
  change ∀ i : Fin n, (C' i).leader = true ↔ i = root
  intro i
  constructor
  · exact hpostToRoot i
  · intro hir
    subst i
    exact hroot

theorem splAlgorithm23_geometry_of_field
    (hfield : SPLAlgorithm23FieldFrameResidual)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hC : SPLAt ring root C) :
    let C' := nextConfig ring C e
    ∀ i : Fin n,
      let off := cyclicOffset ring root i
      let zeta := segmentCount n psi
      And
        ((C' i).dist.val = off % (2 * psi))
        ((C' i).last = true ↔ psi * (zeta - 1) ≤ off) := by
  let C' : Config n psi kappa := nextConfig ring C e
  have hf := hfield hn3 hpsi ring root C e hC
  dsimp only at hf
  have hpre := hC.1.2.2
  change
    ∀ i : Fin n,
      let off := cyclicOffset ring root i
      let zeta := segmentCount n psi
      And
        ((C' i).dist.val = off % (2 * psi))
        ((C' i).last = true ↔ psi * (zeta - 1) ≤ off)
  intro i
  have hi := hpre i
  dsimp only at hi ⊢
  constructor
  · rw [hf.2.1 i]
    exact hi.1
  · rw [hf.2.2.1 i]
    exact hi.2

theorem splAlgorithm23_segmentIds_of_field
    (hfield : SPLAlgorithm23FieldFrameResidual)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hC : SPLAt ring root C) :
    let C' := nextConfig ring C e
    ∀ s : Nat,
      rootedSegmentId ring root C' s =
        rootedSegmentId ring root C s := by
  let C' : Config n psi kappa := nextConfig ring C e
  have hf := hfield hn3 hpsi ring root C e hC
  dsimp only at hf
  change
    ∀ s : Nat,
      rootedSegmentId ring root C' s =
        rootedSegmentId ring root C s
  intro s
  exact
    rootedSegmentId_eq_of_id_eq
      ring root C C' hf.2.2.2 s

/-! ## Remark-2 token seam -/

theorem splAlgorithm23_tokenSafety_of_remark2
    (htoken : SPLAlgorithm23TokenResidual)
    (hRight : PPL.Remark2RightSelectedRow)
    (hLeft : PPL.Remark2LeftSelectedRow) :
    ∀ {n psi kappa : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (ring : DirectedRing n)
      (root : Fin n)
      (C : Config n psi kappa)
      (e : Fin n),
      SPLAt ring root C ->
      let C' := nextConfig ring C e
      And
        (∀ i : Fin n, Not (Risky ring root C' i))
        (∀ seg : Fin (segmentCount n psi - 2),
          ∀ i : Fin n,
            And
              ((And
                  (ValidToken .black C' i)
                  (WorkingFor ring root C' i .black seg.val)) ->
                CorrectToken ring root C' i .black seg.val)
              ((And
                  (ValidToken .white C' i)
                  (WorkingFor ring root C' i .white seg.val)) ->
                CorrectToken ring root C' i .white seg.val)) := by
  exact
    htoken
      (PPL.remark2_one_step_unique_closed hRight hLeft)

/-! ## Five-conjunct assembly -/

theorem splAlgorithm23_of_residuals
    (hfield : SPLAlgorithm23FieldFrameResidual)
    (htoken : SPLAlgorithm23TokenResidual)
    (hRight : PPL.Remark2RightSelectedRow)
    (hLeft : PPL.Remark2LeftSelectedRow) :
    SPLAlgorithm23StepProp := by
  unfold SPLAlgorithm23StepProp
  intro n psi kappa hn3 hpsi ring root C e hC
  have hleader :=
    splAlgorithm23_leader_of_field
      hfield hn3 hpsi ring root C e hC
  have hgeometry :=
    splAlgorithm23_geometry_of_field
      hfield hn3 hpsi ring root C e hC
  have hids :=
    splAlgorithm23_segmentIds_of_field
      hfield hn3 hpsi ring root C e hC
  have hsafety :=
    splAlgorithm23_tokenSafety_of_remark2
      htoken hRight hLeft
      hn3 hpsi ring root C e hC
  dsimp only at hleader hgeometry hids hsafety ⊢
  exact
    And.intro hleader
      (And.intro hgeometry
        (And.intro hids
          (And.intro hsafety.1 hsafety.2)))

/--
The requested split: CPB is no longer part of Algorithm-2/3 work.
It is discharged unconditionally by the proved PeacefulScan/PeacefulKeep
closure theorem on main.
-/
theorem splLocalStep_of_alg23
    (h23 : SPLAlgorithm23StepProp) :
    SPLLocalStepProp := by
  unfold SPLLocalStepProp
  intro n psi kappa hn3 hpsi ring root C e hC
  have hcpb :=
    PPL.Safety.PeacefulProps.cpb_step_closed_proved
      hn3 hpsi ring C e hC.1.1
  have hrest :=
    h23 hn3 hpsi ring root C e hC
  dsimp only at hrest ⊢
  exact
    And.intro
      (by simpa [nextConfig] using hcpb)
      hrest

end PPL.Safety.SPL

#print axioms PPL.Safety.SPL.segmentIdAux_eq_of_id_eq
#print axioms PPL.Safety.SPL.rootedSegmentId_eq_of_id_eq
#print axioms PPL.Safety.SPL.splAlgorithm23_leader_of_field
#print axioms PPL.Safety.SPL.splAlgorithm23_geometry_of_field
#print axioms PPL.Safety.SPL.splAlgorithm23_segmentIds_of_field
#print axioms PPL.Safety.SPL.splAlgorithm23_tokenSafety_of_remark2
#print axioms PPL.Safety.SPL.splAlgorithm23_of_residuals
#print axioms PPL.Safety.SPL.splLocalStep_of_alg23
