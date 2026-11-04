import Leader.L3.Top.SettledPotentialNominate

/-!
# Q7 (P.8--P.10): the port edges of a front-free window

The clean edge changes nothing in a window whose live carries have empty hosts.  The accept
edge turns an empty carry-free border register into a pending one: the measure does not rise,
and it falls by `r + 2` when no live carry consumes.

Consumer: `Leader/L3/Top/SettledPotentialStep.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The clean edge changes nothing when live carries have empty hosts.

Consumer: `Leader/L3/Top/SettledPotentialStep.lean`. -/
theorem clean_id (r : Nat) (cells : Nat → Cell) (h : FEnv r cells) (hr : 0 < r) :
    setOne cells 0 (portClean (cells 0)) = cells := by
  funext k
  unfold setOne
  by_cases hk : k = 0
  · subst hk
    simp only [if_true]
    unfold portClean
    by_cases hc : (cells 0).c = .off
    · rw [if_pos hc]
    · rw [if_neg hc]
      rcases h.host hr with h1 | ⟨h1, _⟩
      · exact absurd h1 hc
      · rcases hx : cells 0 with ⟨a, b⟩
        rw [hx] at h1
        simp only at h1 ⊢
        rw [h1]
  · simp [hk]

/-- The accept edge on a window that does not offer an empty carry-free border register changes
nothing.

Consumer: `Leader/L3/Top/SettledPotentialStep.lean`. -/
theorem accept_id (cells : Nat → Cell) (t : Bool) (h : cells 0 ≠ { i := .e, c := .off }) :
    setOne cells 0 (portAccept t (cells 0)) = cells := by
  funext k
  unfold setOne
  by_cases hk : k = 0
  · subst hk
    simp only [if_true]
    unfold portAccept
    rw [if_neg h]
  · simp [hk]

/-- **The accept edge.**  A pending packet appears at the empty border register.

Consumer: `Leader/L3/Top/SettledPotentialStep.lean`. -/
theorem gv_accept (r : Nat) (cells : Nat → Cell) (h : FEnv r cells) (hr : 1 < r)
    (i : Inp) (hi : i.isP = true) (hx : cells 0 = { i := .e, c := .off }) :
    (ConsAt r (setOne cells 0 { i := i, c := .off }) ↔ ConsAt r cells) ∧
    (ConsAt r cells → Gv r (setOne cells 0 { i := i, c := .off }) = Gv r cells) ∧
    (¬ ConsAt r cells → Gv r (setOne cells 0 { i := i, c := .off }) + (r + 2) = Gv r cells) := by
  generalize hc' : setOne cells 0 { i := i, c := .off } = cells'
  have hout : ∀ k, k ≠ 0 → cells' k = cells k := by
    intro k h1; rw [← hc']; simp [setOne, h1]
  have h0 : cells' 0 = { i := i, c := .off } := by rw [← hc']; simp [setOne]
  have hnS := isP_not_isS hi
  have hS : fsOf r cells' = fsOf r cells := by
    unfold fsOf
    apply firstS_congr
    intro k hk
    by_cases k1 : k = 0
    · subst k1; rw [h0, hx]; exact hnS
    · rw [hout k k1]
  have hH : hpOf r cells' = hpOf r cells := by
    unfold hpOf
    apply firstS_congr
    intro k hk
    by_cases k1 : k = 0
    · subst k1; rw [h0, hx]
    · rw [hout k k1]
  have hcons : ConsAt r cells' ↔ ConsAt r cells := by
    unfold ConsAt
    rw [hH]
    by_cases hlt : hpOf r cells < r
    · by_cases hq : hpOf r cells + 1 < r
      · rw [hout (hpOf r cells + 1) (by omega)]
      · simp [hq]
    · simp [hlt]
  have hfs0 : 1 ≤ fsOf r cells := by
    have h1 := h.fs_settled
    have h2 : fsOf r cells ≠ 0 := fun hh => by rw [hh, hx] at h1; exact absurd h1 (by simp [Inp.isS])
    omega
  have hFT : FT r cells' + (r + 2) = FT r cells := by
    unfold FT
    rw [hS, if_pos h.fs_lt, if_pos h.fs_lt]
    have := wsum_edit_one (fillW r cells) (fillW r cells') 0 (by
      intro k h1; unfold fillW; rw [hout k h1]) (fsOf r cells) hfs0
    have e1 : fillW r cells 0 = 0 + r + 3 := by
      unfold fillW; rw [hx]; simp [Inp.isP]
    have e2 : fillW r cells' 0 = 1 := by unfold fillW; rw [h0]; simp [hi]
    omega
  refine ⟨hcons, ?_, ?_⟩
  · intro hcc
    have hcc' := hcons.2 hcc
    rw [Gv_cons r cells' hcc', Gv_cons r cells hcc, hH]
  · intro hcc
    have hcc' : ¬ ConsAt r cells' := fun hh => hcc (hcons.1 hh)
    by_cases hlt : hpOf r cells < r
    · rw [Gv_host r cells' (by rw [hH]; exact hlt) hcc', Gv_host r cells hlt hcc]
      omega
    · rw [Gv_free r cells' (by rw [hH]; exact hlt), Gv_free r cells hlt]
      omega

end MarkedCells
end L3

#print axioms L3.MarkedCells.gv_accept
#print axioms L3.MarkedCells.clean_id
#print axioms L3.MarkedCells.accept_id
