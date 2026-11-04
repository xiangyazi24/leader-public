import Leader.L3.Top.PinnedGv

/-!
# Q7 (P.8--P.10): the invariants of a front-free window and the facts they give

Consumer: `Leader/L3/Top/PinnedStep.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The invariants of a front-free window with a settled input: fresh-carry invariants, no
inherited carry, the pending barrier, a settled register, and no erasure front.

Consumer: `Leader/L3/Top/PinnedStep.lean`. -/
structure FEnv (r : Nat) (cells : Nat → Cell) : Prop where
  inv : Inv r cells
  ni : NoInh r cells
  bar : Barrier r cells
  ex : ∃ j, j < r ∧ (cells j).i.isS = true
  nx : ∀ k, k < r → (cells k).i ≠ .x

/-- A live carry is a fresh carry on an empty host.

Consumer: `Leader/L3/Top/PinnedStep.lean`. -/
theorem FEnv.host {r : Nat} {cells : Nat → Cell} (h : FEnv r cells) {k : Nat} (hk : k < r) :
    (cells k).c = .off ∨ ((cells k).i = .e ∧ (cells k).c = .fresh) := by
  by_cases hc : (cells k).c = .off
  · exact Or.inl hc
  · right
    have hf : (cells k).c = .fresh := by
      have := h.ni k hk
      cases hh : (cells k).c <;> simp_all
    exact ⟨(h.inv.1 k hk hf).1, hf⟩

/-- At most one live carry.

Consumer: `Leader/L3/Top/PinnedStep.lean`. -/
theorem FEnv.uniq {r : Nat} {cells : Nat → Cell} (h : FEnv r cells) {j k : Nat} (hj : j < r)
    (hk : k < r) (hcj : (cells j).c ≠ .off) (hck : (cells k).c ≠ .off) : j = k := by
  have h1 : (cells j).c = .fresh := by
    have := h.ni j hj
    cases hh : (cells j).c <;> simp_all
  have h2 : (cells k).c = .fresh := by
    have := h.ni k hk
    cases hh : (cells k).c <;> simp_all
  exact h.inv.2 j k hj hk h1 h2

/-- Only empty or pending inputs stand left of a live carry.

Consumer: `Leader/L3/Top/PinnedStep.lean`. -/
theorem FEnv.left {r : Nat} {cells : Nat → Cell} (h : FEnv r cells) {j : Nat} (hj : j < r)
    (hcj : (cells j).c ≠ .off) {i : Nat} (hi : i < j) : EP (cells i) := by
  have h1 : (cells j).c = .fresh := by
    have := h.ni j hj
    cases hh : (cells j).c <;> simp_all
  exact (h.inv.1 j hj h1).2 i hi

/-- A pending input stands strictly left of every settled input and live carry.

Consumer: `Leader/L3/Top/PinnedStep.lean`. -/
theorem FEnv.pend_lt {r : Nat} {cells : Nat → Cell} (h : FEnv r cells) {p j : Nat}
    (hp : p < r) (hj : j < r) (hP : (cells p).i.isP = true)
    (hob : (cells j).i.isS = true ∨ (cells j).c ≠ .off) : p < j := by
  apply h.bar p j hp hj hP
  unfold obC
  rcases hob with hh | hh
  · simp [hh]
  · simp [hh]

/-- The first settled site is below `r` and settled.

Consumer: `Leader/L3/Top/PinnedStep.lean`. -/
theorem FEnv.fs_lt {r : Nat} {cells : Nat → Cell} (h : FEnv r cells) : fsOf r cells < r := by
  unfold fsOf
  rw [firstS_lt_iff]
  obtain ⟨j, hj, hs⟩ := h.ex
  exact ⟨j, hj, hs⟩

/-- The first settled site is settled.

Consumer: `Leader/L3/Top/PinnedStep.lean`. -/
theorem FEnv.fs_settled {r : Nat} {cells : Nat → Cell} (h : FEnv r cells) :
    (cells (fsOf r cells)).i.isS = true :=
  firstS_hit (fun k => (cells k).i.isS) r h.fs_lt

/-- Nothing before the first settled site is settled.

Consumer: `Leader/L3/Top/PinnedStep.lean`. -/
theorem fs_before {r : Nat} {cells : Nat → Cell} {k : Nat} (hk : k < fsOf r cells) :
    (cells k).i.isS = false :=
  firstS_before (fun k => (cells k).i.isS) r k hk

/-- Nothing before the live carry has a live carry.

Consumer: `Leader/L3/Top/PinnedStep.lean`. -/
theorem hp_before {r : Nat} {cells : Nat → Cell} {k : Nat} (hk : k < hpOf r cells) :
    (cells k).c = .off := by
  have := firstS_before (fun k => decide ((cells k).c ≠ .off)) r k hk
  simpa using this

/-- The live carry site, when below `r`, carries.

Consumer: `Leader/L3/Top/PinnedStep.lean`. -/
theorem hp_hit {r : Nat} {cells : Nat → Cell} (hk : hpOf r cells < r) :
    (cells (hpOf r cells)).c ≠ .off := by
  exact of_decide_eq_true (firstS_hit (fun k => decide ((cells k).c ≠ .off)) r hk)

/-- With a live carry at `j` the carry site is `j`.

Consumer: `Leader/L3/Top/PinnedStep.lean`. -/
theorem hp_eq {r : Nat} {cells : Nat → Cell} (h : FEnv r cells) {j : Nat} (hj : j < r)
    (hc : (cells j).c ≠ .off) : hpOf r cells = j := by
  unfold hpOf
  apply firstS_eq _ r j hj (by simpa using hc)
  intro k hk
  have : ¬ (cells k).c ≠ .off := fun hh => by
    have := h.uniq (by omega) hj hh hc
    omega
  simpa using this

/-- Without a live carry the carry site is `r`.

Consumer: `Leader/L3/Top/PinnedStep.lean`. -/
theorem hp_none {r : Nat} {cells : Nat → Cell} (hn : ∀ k, k < r → (cells k).c = .off) :
    hpOf r cells = r := by
  unfold hpOf
  apply firstS_end
  intro k hk
  simp [hn k hk]

end MarkedCells
end L3

#print axioms L3.MarkedCells.hp_eq
#print axioms L3.MarkedCells.FEnv.host
#print axioms L3.MarkedCells.FEnv.uniq
#print axioms L3.MarkedCells.FEnv.left
#print axioms L3.MarkedCells.FEnv.pend_lt
#print axioms L3.MarkedCells.FEnv.fs_lt
#print axioms L3.MarkedCells.FEnv.fs_settled
#print axioms L3.MarkedCells.fs_before
#print axioms L3.MarkedCells.hp_before
#print axioms L3.MarkedCells.hp_hit
#print axioms L3.MarkedCells.hp_none
