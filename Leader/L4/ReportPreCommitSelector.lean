import Leader.L4.ReportGenerationAncestry

namespace L4.ReportPreCommitSelector
open AllSizeProtocol PhysicalCustody
open ReportResetRawHooks ReportResetBarrier ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportLeaseOwner ReportGenerationAncestry ReportByteRows
open ShortResetCycle

variable {s n : Nat} {h : Fin n→Bool}

/-- A healthy positive opcode cannot belong to a different command in
the serial rail. Inherited tokens are excluded by the rail hypothesis,
not by a decoder byte pattern. -/
theorem healthy_positive_opcode (sheet : Sheet) (C : Chart h)
    (x : Raw s n) (g : GenerationTag) (G : railState sheet C x g)
    (k : Nat) (K : k<C.L) (H : (tok sheet C x k).fault=false)
    (O : (tok sheet C x k).opcode ≠ 0) :
    (tok sheet C x k).opcode=g.op := by
  cases R : g.rail with
  | issue =>
    unfold railState at G
    rw [R] at G
    rw [G.2 k K] at O
    exact False.elim (O rfl)
  | forward j t | reverse j t =>
    unfold railState at G
    rw [R] at G
    have E := G.2.2.2.2 k K
    by_cases L : k<j
    · rw [E,if_pos L] at O
      exact False.elim (O rfl)
    · rw [E,if_neg L] at H O ⊢
      by_cases J : k=j
      · rw [if_pos J] at H ⊢
        exact G.2.2.2.1 H
      · rw [if_neg J] at O
        exact False.elim (O rfl)

/-- A mark cannot change this centre's selector during a non-COMMIT
command on its own serial rail. This excludes even an arbitrary rival
owner's rows, since the physical lane-0 ingress belongs to this chart. -/
theorem selector_frame_noncommit
    (sheet : Sheet) (G : GapInput h) (r : Owner h)
    (x : Raw s n) (g : GenerationTag)
    (R : railState sheet (charter G r) x g)
    (O : g.op≠commitOp (params sheet s))
    (e : Fin n) (N : 1<n)
    (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i) :
    rawSelector sheet (rawNext s x e) (centre (charter G r))=
      rawSelector sheet x (centre (charter G r)) := by
  apply Classical.byContradiction
  intro C
  obtain ⟨K,_,F,W⟩ := changed_centre_owns_ingress sheet G r x e N mask C
  have M : (tok sheet (charter G r) x ((charter G r).a-1)).opcode≠0 := by
    rw [W]
    unfold commitOp
    omega
  exact O ((healthy_positive_opcode sheet _ x g R _ K F M).symm.trans W)

theorem selector_frame_during_write
    (sheet : Sheet) (G : GapInput h) (r : Owner h)
    (x : Raw s n) (g : GenerationTag)
    (R : railState sheet (charter G r) x g)
    (k : Nat) (K : k<(charter G r).L)
    (W : WriteCommand (params sheet s) (tok sheet (charter G r) x k))
    (e : Fin n) (N : 1<n)
    (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i) :
    rawSelector sheet (rawNext s x e) (centre (charter G r))=
      rawSelector sheet x (centre (charter G r)) := by
  have M : (tok sheet (charter G r) x k).opcode≠0 := by
    have A := W.2.2.1
    unfold writeOp at A
    omega
  have H := healthy_positive_opcode sheet _ x g R k K W.2.1 M
  apply selector_frame_noncommit sheet G r x g R _ e N mask
  rw [← H]
  have A := W.2.2.2
  unfold sealOp commitOp at *
  omega

end L4.ReportPreCommitSelector
