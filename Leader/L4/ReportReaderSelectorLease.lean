import Leader.L4.ReportGenerationAncestry

namespace L4.ReportReaderSelectorLease
open AllSizeProtocol PhysicalCustody ReportResetRawHooks ReportRawProjection
open ReportByteRows ReportLeaseGrants ReportGenerationAncestry

variable {s n : Nat}

/-- Exact old-bank read authority. Incoming report COMMIT needs the
old writer grant, so a compatible side reader excludes the only
selector-changing branch. This does not assume the winner's provenance. -/
theorem reader_grant_protects_selector (sheet : Sheet)
    (x : Raw s n) (e i : Fin n) (N : 1<n) (j : Fin 3)
    (Side : j=0 ∨ j=2) (C : Compatible (rawGrant sheet x i))
    (Held : rawGrant sheet x i j=true) :
    rawSelector sheet (rawNext s x e) i=rawSelector sheet x i := by
  apply raw_selector_frame sheet x e i N
  rintro ⟨R,P⟩
  subst i
  unfold oldCommitAt ancestryCommitOpportunity at P
  have NoWriter : rawGrant sheet x (rightNeighbor e) 1=false := by
    apply Bool.eq_false_iff.mpr
    intro W
    exact Bool.noConfusion (Held.symm.trans (Side.elim (fun J=>J ▸ (C W).1) (fun J=>J ▸ (C W).2)))
  have NW :
      reportOldGrant (params sheet s) (selectBytes sheet (x (rightNeighbor e))) 1=false :=
    NoWriter
  let p := params sheet s
  let v := selectBytes sheet (x (rightNeighbor e))
  let t := publicationToken p (lower sheet (oldHeaders (rows s) (x e)))
    (selectBytes sheet (x e)) 0
  have A := P.2.2.2.2
  change (!t.applied && reportOldGrant p v 1 &&
    (publicationSelector p v==t.payload/8) &&
    (reportOldSeal p v==some t.payload))=true at A
  change reportOldGrant p v 1=false at NW
  simp [NW] at A

/-- The single old row preserves a side lease up to its real outgoing
RESET release. Responder canonicalization does not drop a compatible
grant; no fresh draw or resampling is used. -/
theorem reader_grant_step (sheet : Sheet) (x : Raw s n) (e i : Fin n)
    (N : 1<n) (j : Fin 3) (Side : j=0 ∨ j=2)
    (Hdr : lower sheet (oldHeaders (rows s) (x i))=true)
    (C : Compatible (rawGrant sheet x i)) (Held : rawGrant sheet x i j=true)
    (NoRelease : e=i → (oldIncidence sheet x i).release j=false) :
    Compatible (rawGrant sheet (rawNext s x e) i) ∧
    rawGrant sheet (rawNext s x e) i j=true ∧
    rawSelector sheet (rawNext s x e) i=rawSelector sheet x i := by
  refine ⟨raw_compatible_step sheet x e i (ShortResetCycle.edge_sep N e) C,?_,
    reader_grant_protects_selector sheet x e i N j Side C Held⟩
  have H : (oldIncidence sheet x i).canonical j=true :=
    (canonical_eq _ C j).trans Held
  apply (held_grant_survives_iff sheet x e i j N Hdr Held).mpr
  unfold grantSurvives
  by_cases E : i=e
  · rw [if_pos E]
    exact ⟨H,NoRelease E.symm⟩
  · rw [if_neg E]
    by_cases R : i=rightNeighbor e
    · rw [if_pos R]
      exact H
    · rw [if_neg R]
      trivial

/-- Inspect the actual old states of the observed segment, not a
separately generated or commuted word. A later RESET after the
segment is allowed. -/
def NoSideRelease (sheet : Sheet) (i : Fin n) (j : Fin 3) :
    Raw s n → List (Fin n) → Prop
  | _,[] => True
  | x,e::es => lower sheet (oldHeaders (rows s) (x i))=true ∧
      (e=i → (oldIncidence sheet x i).release j=false) ∧
      NoSideRelease sheet i j (rawNext s x e) es

theorem reader_grant_run (sheet : Sheet) (x : Raw s n) (i : Fin n)
    (N : 1<n) (j : Fin 3) (Side : j=0 ∨ j=2)
    (C : Compatible (rawGrant sheet x i)) (Held : rawGrant sheet x i j=true)
    (w : List (Fin n)) (NR : NoSideRelease sheet i j x w) :
    Compatible (rawGrant sheet (rawRun x w) i) ∧
    rawGrant sheet (rawRun x w) i j=true ∧
    rawSelector sheet (rawRun x w) i=rawSelector sheet x i := by
  induction w generalizing x with
  | nil => exact ⟨C,Held,rfl⟩
  | cons e w IH =>
    have R : lower sheet (oldHeaders (rows s) (x i))=true ∧
        (e=i → (oldIncidence sheet x i).release j=false) ∧
          NoSideRelease sheet i j (rawNext s x e) w := NR
    obtain ⟨C',H',S⟩ := reader_grant_step sheet x e i N j Side R.1 C Held R.2.1
    obtain ⟨C'',H'',S'⟩ := IH _ C' H' R.2.2
    exact ⟨C'',H'',S'.trans S⟩

#print axioms reader_grant_protects_selector
#print axioms reader_grant_step
#print axioms reader_grant_run
end L4.ReportReaderSelectorLease
