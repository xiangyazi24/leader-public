import Leader.Wu.Coherence.Controller


set_option autoImplicit false


namespace R2CoherenceV31


variable {ψ κ τ width : Nat}


/-- Pair-local form of Family (A): token-free and sealed. -/
def FamilyA (u : Cell ψ κ τ) : Prop :=
  u.ctl.tok = .none ∧ u.ctl.mark = .sealed


/--
Family (A) routes the ordinary dispatcher to the sealed stage.
This is the only branch-selection fact supplied by the four
controller equalities alone.
-/
theorem ordinaryStageV3_eq_sealedStage_of_familyA
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ)
    (hl : FamilyA l) (hr : FamilyA r) :
    ordinaryStageV3 hψ hw hle l r =
      sealedStageV3 hψ hw hle l r := by
  unfold ordinaryStageV3
  rw [if_pos ⟨hl.1, hr.1⟩]
  rw [if_pos ⟨hl.2, hr.2⟩]


/--
The full local row also reaches the sealed stage on Family (A):
all six active-token priority tests are false because both tokens
are .none.
-/
theorem rowV3_eq_sealedStage_of_familyA
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ)
    (hl : FamilyA l) (hr : FamilyA r) :
    rowV3 hψ hw hle l r =
      sealedStageV3 hψ hw hle l r := by
  simp [rowV3, ordinaryStageV3, hl.1, hr.1, hl.2, hr.2]


/--
First exact stutter arm. No Family-(A) hypothesis is needed:
when launch fails and the sealed proposal relabels, sealedStageV3
returns (l,r) verbatim.
-/
theorem sealedStageV3_eq_self_of_noLaunch_of_relabels
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ)
    (hLaunch :
      (atRootB l && successorB l r &&
        writerQuiet l && writerQuiet r) = false)
    (hRelabel :
      R2Coherence.pairRelabels
        l.phys r.phys
        (sealedProposalV3 hψ hw hle l r).1
        (sealedProposalV3 hψ hw hle l r).2 = true) :
    sealedStageV3 hψ hw hle l r = (l, r) := by
  simp [sealedStageV3, hLaunch, hRelabel]


/--
Second exact stutter arm. Excluding relabels is still insufficient:
if the physical proposal equals the old physical pair, both installs
are identities.
-/
theorem sealedStageV3_eq_self_of_noLaunch_of_noRelabel_of_proposalEq
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ)
    (hLaunch :
      (atRootB l && successorB l r &&
        writerQuiet l && writerQuiet r) = false)
    (hRelabel :
      R2Coherence.pairRelabels
        l.phys r.phys
        (sealedProposalV3 hψ hw hle l r).1
        (sealedProposalV3 hψ hw hle l r).2 = false)
    (hProposal :
      sealedProposalV3 hψ hw hle l r = (l.phys, r.phys)) :
    sealedStageV3 hψ hw hle l r = (l, r) := by
  have hL :
      (sealedProposalV3 hψ hw hle l r).1 = l.phys :=
    congrArg
      (fun p : R2.Cell ψ κ τ × R2.Cell ψ κ τ => p.1)
      hProposal
  have hR :
      (sealedProposalV3 hψ hw hle l r).2 = r.phys :=
    congrArg
      (fun p : R2.Cell ψ κ τ × R2.Cell ψ κ τ => p.2)
      hProposal
  calc
    sealedStageV3 hψ hw hle l r =
        (install l (sealedProposalV3 hψ hw hle l r).1,
         install r (sealedProposalV3 hψ hw hle l r).2) := by
      simp [sealedStageV3, hLaunch, hRelabel]
    _ = (install l l.phys, install r r.phys) := by
      rw [hL, hR]
    _ = (l, r) := by
      cases l
      cases r
      rfl


/--
Changing a sealed left controller to (.releasing,.release)
cannot be an identity. Only the sealed mark is needed here.
-/
private theorem releasing_release_ne_of_sealed
    (l : Cell ψ κ τ)
    (hsealed : l.ctl.mark = .sealed) :
    setControl l .releasing .release ≠ l := by
  intro h
  have hm :=
    congrArg (fun x : Cell ψ κ τ => x.ctl.mark) h
  change R2Coherence.Mark.releasing = l.ctl.mark at hm
  rw [hsealed] at hm
  cases hm


/--
If the release-launch guard fires, Family (A) makes the first
endpoint provably different: its mark changes from .sealed
to .releasing.
-/
theorem sealedStageV3_ne_of_familyA_of_launch
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ)
    (hl : FamilyA l) (_hr : FamilyA r)
    (hLaunch :
      (atRootB l && successorB l r &&
        writerQuiet l && writerQuiet r) = true) :
    sealedStageV3 hψ hw hle l r ≠ (l, r) := by
  intro hEq
  have hPair :
      (setControl l .releasing .release, r) = (l, r) := by
    simpa [sealedStageV3, hLaunch] using hEq
  have hLeft :
      setControl l .releasing .release = l :=
    congrArg
      (fun p : Cell ψ κ τ × Cell ψ κ τ => p.1)
      hPair
  exact releasing_release_ne_of_sealed l hl.2 hLeft


/--
If the launch guard does not fire, non-identity follows from
the two physical facts missing from Family (A):
  * the pair-relabel stutter arm is not selected; and
  * the sealed physical proposal differs from the input pair.


The proof also handles the case where the launch guard is true,
so no launch-negation premise is required.
-/
theorem sealedStageV3_ne_of_familyA_of_noRelabel_of_proposalMoves
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ)
    (hl : FamilyA l) (_hr : FamilyA r)
    (hRelabel :
      R2Coherence.pairRelabels
        l.phys r.phys
        (sealedProposalV3 hψ hw hle l r).1
        (sealedProposalV3 hψ hw hle l r).2 = false)
    (hMove :
      sealedProposalV3 hψ hw hle l r ≠ (l.phys, r.phys)) :
    sealedStageV3 hψ hw hle l r ≠ (l, r) := by
  intro hEq
  cases hLaunch :
      (atRootB l && successorB l r &&
        writerQuiet l && writerQuiet r) with
  | false =>
      have hPair :
          (install l (sealedProposalV3 hψ hw hle l r).1,
           install r (sealedProposalV3 hψ hw hle l r).2) =
            (l, r) := by
        simpa [sealedStageV3, hLaunch, hRelabel] using hEq
      have hLeft :
          install l (sealedProposalV3 hψ hw hle l r).1 = l :=
        congrArg
          (fun p : Cell ψ κ τ × Cell ψ κ τ => p.1)
          hPair
      have hRight :
          install r (sealedProposalV3 hψ hw hle l r).2 = r :=
        congrArg
          (fun p : Cell ψ κ τ × Cell ψ κ τ => p.2)
          hPair
      have hPhysLeft :
          (sealedProposalV3 hψ hw hle l r).1 = l.phys := by
        have h :=
          congrArg (fun x : Cell ψ κ τ => x.phys) hLeft
        change
          (sealedProposalV3 hψ hw hle l r).1 = l.phys at h
        exact h
      have hPhysRight :
          (sealedProposalV3 hψ hw hle l r).2 = r.phys := by
        have h :=
          congrArg (fun x : Cell ψ κ τ => x.phys) hRight
        change
          (sealedProposalV3 hψ hw hle l r).2 = r.phys at h
        exact h
      apply hMove
      exact Prod.ext hPhysLeft hPhysRight
  | true =>
      have hPair :
          (setControl l .releasing .release, r) = (l, r) := by
        simpa [sealedStageV3, hLaunch] using hEq
      have hLeft :
          setControl l .releasing .release = l :=
        congrArg
          (fun p : Cell ψ κ τ × Cell ψ κ τ => p.1)
          hPair
      exact releasing_release_ne_of_sealed l hl.2 hLeft


/--
Clean final theorem: this progress hypothesis closes both stutter
holes in sealedStageV3.
-/
theorem sealedStageV3_ne_of_familyA_of_progress
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ)
    (hl : FamilyA l) (hr : FamilyA r)
    (hProgress :
      (atRootB l && successorB l r &&
        writerQuiet l && writerQuiet r) = true ∨
      (R2Coherence.pairRelabels
          l.phys r.phys
          (sealedProposalV3 hψ hw hle l r).1
          (sealedProposalV3 hψ hw hle l r).2 = false ∧
       sealedProposalV3 hψ hw hle l r ≠ (l.phys, r.phys))) :
    sealedStageV3 hψ hw hle l r ≠ (l, r) := by
  cases hProgress with
  | inl hLaunch =>
      exact sealedStageV3_ne_of_familyA_of_launch
        hψ hw hle l r hl hr hLaunch
  | inr hRest =>
      exact
        sealedStageV3_ne_of_familyA_of_noRelabel_of_proposalMoves
          hψ hw hle l r hl hr hRest.1 hRest.2


/--
Consequently the complete local V3 row is non-identity on
Family (A) under the same physical-progress condition.
-/
theorem rowV3_ne_of_familyA_of_progress
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ)
    (hl : FamilyA l) (hr : FamilyA r)
    (hProgress :
      (atRootB l && successorB l r &&
        writerQuiet l && writerQuiet r) = true ∨
      (R2Coherence.pairRelabels
          l.phys r.phys
          (sealedProposalV3 hψ hw hle l r).1
          (sealedProposalV3 hψ hw hle l r).2 = false ∧
       sealedProposalV3 hψ hw hle l r ≠ (l.phys, r.phys))) :
    rowV3 hψ hw hle l r ≠ (l, r) := by
  rw [rowV3_eq_sealedStage_of_familyA hψ hw hle l r hl hr]
  exact sealedStageV3_ne_of_familyA_of_progress
    hψ hw hle l r hl hr hProgress


end R2CoherenceV31
