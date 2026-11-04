import Leader.Wu.Coherence.TokenFreeMixedRowMoves

set_option autoImplicit false
set_option Elab.async false

/-!
# The `rowV3` identity branch cannot cycle on a ring

`rowV3`'s six token guards are asymmetric: `sweep`, `release` and `openR` are tested on
the LEFT cell of the pair, while `seek`, `commit` and `scrubL` are tested on the RIGHT.
On a directed ring every cell is both the left endpoint of one edge and the right
endpoint of another, so if every edge dodges its own guards then every cell must dodge
all six, which leaves only `TokenV3.none`.

See ERRATA R261.
-/

namespace ZZV31RingTokenCollapse

open R2CoherenceV31

variable {n ψ κ τ : Nat}

/-- Every cell on a directed ring has a predecessor. -/
theorem rightNeighbor_surjective
    (ring : DirectedRing n) (hn : 2 ≤ n) (i : Fin n) :
    ∃ e : Fin n, ring.rightNeighbor e = i := by
  refine ⟨⟨(i.val + n - 1) % n, Nat.mod_lt _ (by omega)⟩, ?_⟩
  apply Fin.ext
  unfold DirectedRing.rightNeighbor
  dsimp only
  have hi := i.isLt
  by_cases h0 : i.val = 0
  · have hpre : (i.val + n - 1) % n = n - 1 := by
      rw [h0, Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hpre]
    have : n - 1 + 1 = n := by omega
    rw [this, Nat.mod_self, h0]
  · have hpre : (i.val + n - 1) % n = i.val - 1 := by
      have hlt : i.val - 1 < n := by omega
      have heq : i.val + n - 1 = (i.val - 1) + n := by omega
      rw [heq, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt hlt
    rw [hpre]
    have hsucc : i.val - 1 + 1 = i.val := by omega
    rw [hsucc]
    exact Nat.mod_eq_of_lt hi

/-- If every edge dodges all six `rowV3` token guards, every cell is token-free. -/
theorem ring_all_none_of_guards_fail
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : R2CoherenceV31.FC n ψ κ τ)
    (hL : ∀ e : Fin n,
      (C e).ctl.tok ≠ TokenV3.sweep ∧
      (C e).ctl.tok ≠ TokenV3.release ∧
      (C e).ctl.tok ≠ TokenV3.openR)
    (hR : ∀ e : Fin n,
      (C (ring.rightNeighbor e)).ctl.tok ≠ TokenV3.seek ∧
      (C (ring.rightNeighbor e)).ctl.tok ≠ TokenV3.commit ∧
      (C (ring.rightNeighbor e)).ctl.tok ≠ TokenV3.scrubL) :
    ∀ i : Fin n, (C i).ctl.tok = TokenV3.none := by
  intro i
  obtain ⟨e, he⟩ := rightNeighbor_surjective ring hn i
  have hRi := hR e
  rw [he] at hRi
  have hLi := hL i
  cases htok : (C i).ctl.tok with
  | none => rfl
  | seek => exact absurd htok hRi.1
  | sweep => exact absurd htok hLi.1
  | commit => exact absurd htok hRi.2.1
  | release => exact absurd htok hLi.2.1
  | scrubL => exact absurd htok hRi.2.2
  | openR => exact absurd htok hLi.2.2

end ZZV31RingTokenCollapse

#print axioms ZZV31RingTokenCollapse.rightNeighbor_surjective
#print axioms ZZV31RingTokenCollapse.ring_all_none_of_guards_fail
