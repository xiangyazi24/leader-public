import Leader.Wu.Coherence.TokenFreeMixedStageMoves


set_option autoImplicit false
set_option Elab.async false


namespace ZZV31RowEscapesTokenFreeMixed


variable {n ψ κ τ width : Nat}


/-- The V3.1 row itself cannot stutter on a token-free mixed pair. -/
theorem rowV3_tokenFreeMixed_ne
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : R2CoherenceV31.Cell ψ κ τ)
    (hlTok : l.ctl.tok = R2CoherenceV31.TokenV3.none)
    (hrTok : r.ctl.tok = R2CoherenceV31.TokenV3.none)
    (hNotSealed :
      ¬ (l.ctl.mark = R2Coherence.Mark.sealed ∧
         r.ctl.mark = R2Coherence.Mark.sealed))
    (hNotOpen :
      ¬ (l.ctl.mark = R2Coherence.Mark.open ∧
         r.ctl.mark = R2Coherence.Mark.open)) :
    R2CoherenceV31.rowV3 hψ hw hle l r ≠ (l, r) := by
  simpa [R2CoherenceV31.rowV3, hlTok, hrTok] using
    (ZZV31EscapesTokenFreeMixed.ordinaryStageV3_tokenFreeMixed_ne
      hψ hw hle l r hlTok hrTok hNotSealed hNotOpen)


/-- The exact token-free mixed condition at one directed ring edge. -/
def TokenFreeMixedAt
    (ring : DirectedRing n)
    (C : R2CoherenceV31.FC n ψ κ τ)
    (e : Fin n) : Prop :=
  (C e).ctl.tok = R2CoherenceV31.TokenV3.none ∧
  (C (ring.rightNeighbor e)).ctl.tok = R2CoherenceV31.TokenV3.none ∧
  ¬ ((C e).ctl.mark = R2Coherence.Mark.sealed ∧
     (C (ring.rightNeighbor e)).ctl.mark = R2Coherence.Mark.sealed) ∧
  ¬ ((C e).ctl.mark = R2Coherence.Mark.open ∧
     (C (ring.rightNeighbor e)).ctl.mark = R2Coherence.Mark.open)


/-- Every directed edge is in the token-free mixed family. -/
def AllEdgesTokenFreeMixed
    (ring : DirectedRing n)
    (C : R2CoherenceV31.FC n ψ κ τ) : Prop :=
  ∀ e : Fin n, TokenFreeMixedAt ring C e


private theorem rightNeighbor_ne_of_two
    (ring : DirectedRing n) (hn : 2 ≤ n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega


/-- On a non-self service edge, a token-free mixed pair forces a global move. -/
theorem stepV3_tokenFreeMixedAt_ne
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n)
    (C : R2CoherenceV31.FC n ψ κ τ)
    (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hMixed : TokenFreeMixedAt ring C e) :
    R2CoherenceV31.stepV3 hψ h2 ring C e ≠ C := by
  unfold TokenFreeMixedAt at hMixed
  rcases hMixed with ⟨hlTok, hrTok, hNotSealed, hNotOpen⟩
  have hRow :
      R2CoherenceV31.rowV3 hψ (by decide : 0 < 2) h2
          (C e) (C (ring.rightNeighbor e)) ≠
        (C e, C (ring.rightNeighbor e)) :=
    rowV3_tokenFreeMixed_ne
      hψ (by decide : 0 < 2) h2
      (C e) (C (ring.rightNeighbor e))
      hlTok hrTok hNotSealed hNotOpen
  intro hStep
  apply hRow
  apply Prod.ext
  · have hLeft := congrFun hStep e
    simpa [R2CoherenceV31.stepV3,
      R2CoherenceV31.protocolV3,
      PopulationProtocol.step] using hLeft
  · have hRight := congrFun hStep (ring.rightNeighbor e)
    simpa [R2CoherenceV31.stepV3,
      R2CoherenceV31.protocolV3,
      PopulationProtocol.step, hne] using hRight


/-- If every edge is token-free mixed, every V3.1 service moves the state. -/
theorem stepV3_allEdgesTokenFreeMixed_ne
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : R2CoherenceV31.FC n ψ κ τ)
    (hAll : AllEdgesTokenFreeMixed ring C)
    (e : Fin n) :
    R2CoherenceV31.stepV3 hψ h2 ring C e ≠ C := by
  exact stepV3_tokenFreeMixedAt_ne
    hψ h2 ring C e
    (rightNeighbor_ne_of_two ring hn e)
    (hAll e)


/-- Requested protocol-level edge-0 corollary. -/
theorem stepV3_edge0_allEdgesTokenFreeMixed_ne
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : R2CoherenceV31.FC n ψ κ τ)
    (hAll : AllEdgesTokenFreeMixed ring C) :
    R2CoherenceV31.stepV3 hψ h2 ring C
      (⟨0, by omega⟩ : Fin n) ≠ C := by
  exact stepV3_allEdgesTokenFreeMixed_ne
    hψ h2 ring hn C hAll (⟨0, by omega⟩ : Fin n)


#print axioms ZZV31RowEscapesTokenFreeMixed.rowV3_tokenFreeMixed_ne
#print axioms ZZV31RowEscapesTokenFreeMixed.stepV3_edge0_allEdgesTokenFreeMixed_ne


end ZZV31RowEscapesTokenFreeMixed
