import Leader.L3.Top.PinnedPhaseFillPot

/-!
# Q7 (P.12 preparation, lemma 3, abstract layer): the weight from the pending tail on

After the tail is accepted the potential is the weight of the pending registers from the first
pending tail on.  This module shows how that weight changes under a move, a settlement, a terminal
settlement and an acceptance, and how the reading of tail bits changes.

Consumer: `Leader/L3/Top/PinnedPhaseFillStep.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The cut weight of a register: the weight of a pending register at or after `ρ`.

Consumer: `fwPt`. -/
def wcut (ρ r : Nat) (c : Nat → Cell) (j : Nat) : Nat := if ρ ≤ j then fwt r c j else 0

/-- The weight from the first pending tail on is a cut weight.

Consumer: `fwPt_move`. -/
theorem fwPt_eq (r : Nat) (c : Nat → Cell) : fwPt r c = wsum (wcut (fpos r c) r c) r := rfl

/-- The first pending tail is at or before any pending tail.

Consumer: `fwPt_move`. -/
theorem fpos_le_of (r : Nat) (c : Nat → Cell) (j : Nat) (hj : j < r) (h : (c j).i = .pt) :
    fpos r c ≤ j := by
  apply Classical.byContradiction
  intro hlt
  have := firstS_before (fun j => decide ((c j).i = .pt)) r j (by unfold fpos at hlt; omega)
  simp [h] at this

/-- The first pending tail, when there is one, is a pending tail.

Consumer: `fwPt_move`. -/
theorem fpos_hit (r : Nat) (c : Nat → Cell) (h : fpos r c < r) : (c (fpos r c)).i = .pt := by
  unfold fpos at h ⊢
  have := firstS_hit (fun j => decide ((c j).i = .pt)) r h
  simpa using this

/-- No pending tail before the first one.

Consumer: `fwPt_move`. -/
theorem fpos_before (r : Nat) (c : Nat → Cell) (j : Nat) (h : j < fpos r c) :
    (c j).i ≠ .pt := by
  have := firstS_before (fun j => decide ((c j).i = .pt)) r j h
  simpa using this

/-- The first pending tail depends on the pending tails only.

Consumer: `fwPt_move`. -/
theorem fpos_congr (r : Nat) (c c' : Nat → Cell)
    (h : ∀ j, j < r → ((c' j).i = .pt ↔ (c j).i = .pt)) : fpos r c' = fpos r c := by
  unfold fpos
  apply firstS_congr
  intro k hk
  have := h k hk
  by_cases hc : (c k).i = .pt
  · simp [hc, this.2 hc]
  · have : ¬ (c' k).i = .pt := fun h' => hc (this.1 h')
    simp [hc, this]

/-- The first pending tail is the least index of a pending tail.

Consumer: `fwPt_move`, `fwPt_accept_pt`. -/
theorem fpos_eq (r : Nat) (c : Nat → Cell) (a : Nat) (ha : a < r) (h : (c a).i = .pt)
    (hnot : ∀ k, k < a → (c k).i ≠ .pt) : fpos r c = a := by
  unfold fpos
  apply firstS_eq (fun j => decide ((c j).i = .pt)) r a ha (by simpa using h)
  intro k hk
  have := hnot k hk
  simpa using this

/-- **The weight from the pending tail on, under a move.**

Consumer: `fill_step_window`. -/
theorem fwPt_move (r p : Nat) (hp : p + 1 < r) (c : Nat → Cell) (hP : (c p).i.isP = true)
    (hy : c (p + 1) = { i := .e, c := .off }) :
    (fpos r c ≤ p → fwPt r (mvC c p) + 1 = fwPt r c) ∧
    (p < fpos r c → fwPt r (mvC c p) = fwPt r c) := by
  have hyi : (c (p + 1)).i = .e := by rw [hy]
  have hpP : (c p).i = .pt ∨ (c p).i = .pn := by
    rcases hx : (c p).i with _ | _ | _ | _ | _ | _ <;> rw [hx] at hP <;>
      simp [Inp.isP] at hP ⊢
  constructor
  · intro hρ
    -- the pending tail and its successor
    have hρ' : fpos r (mvC c p) = fpos r c ∨ (fpos r c = p ∧ fpos r (mvC c p) = p + 1) := by
      by_cases hlt : fpos r c < p
      · left
        have hρr : fpos r c < r := by omega
        apply fpos_eq r (mvC c p) _ hρr
        · have := fpos_hit r c hρr
          simp [mvC, setTwo, show fpos r c ≠ p by omega, show fpos r c ≠ p + 1 by omega, this]
        · intro k hk
          have := fpos_before r c k hk
          simp [mvC, setTwo, show k ≠ p by omega, show k ≠ p + 1 by omega, this]
      · right
        have hρp : fpos r c = p := by omega
        refine ⟨hρp, ?_⟩
        have hptp : (c p).i = .pt := by
          have := fpos_hit r c (by omega)
          rw [hρp] at this
          exact this
        apply fpos_eq r (mvC c p) (p + 1) hp
        · simp [mvC, setTwo, hptp]
        · intro k hk
          by_cases hkp : k = p
          · simp [mvC, setTwo, hkp]
          · have hk' : k < p := by omega
            have := fpos_before r c k (by omega)
            simp [mvC, setTwo, hkp, show k ≠ p + 1 by omega, this]
    rcases hρ' with hρ1 | ⟨hρ2, hρ3⟩
    · rw [fwPt_eq, fwPt_eq, hρ1]
      have key := wsum_edit (wcut (fpos r c) r c) (wcut (fpos r c) r (mvC c p)) p
        (by
          intro k hk1 hk2
          simp [wcut, fwt, mvC, setTwo, hk1, hk2]) r (by omega)
      have e1 : wcut (fpos r c) r c p = r - p := by simp [wcut, fwt, hP, hρ]
      have e2 : wcut (fpos r c) r c (p + 1) = 0 := by
        simp [wcut, fwt, hyi, Inp.isP]
      have e3 : wcut (fpos r c) r (mvC c p) p = 0 := by simp [wcut, fwt, mvC, setTwo, Inp.isP]
      have e4 : wcut (fpos r c) r (mvC c p) (p + 1) = r - (p + 1) := by
        simp [wcut, fwt, mvC, setTwo, hP]; omega
      omega
    · rw [fwPt_eq, fwPt_eq, hρ2, hρ3]
      have key := wsum_edit (wcut p r c) (wcut (p + 1) r (mvC c p)) p
        (by
          intro k hk1 hk2
          by_cases hkp : k < p
          · simp [wcut, hk1, hk2, show ¬ p ≤ k by omega, show ¬ p + 1 ≤ k by omega]
          · simp [wcut, fwt, mvC, setTwo, hk1, hk2, show p ≤ k by omega, show p + 1 ≤ k by omega]) r
        (by omega)
      have e1 : wcut p r c p = r - p := by simp [wcut, fwt, hP]
      have e2 : wcut p r c (p + 1) = 0 := by simp [wcut, fwt, hyi, Inp.isP]
      have e3 : wcut (p + 1) r (mvC c p) p = 0 := by simp [wcut, show ¬ p + 1 ≤ p by omega]
      have e4 : wcut (p + 1) r (mvC c p) (p + 1) = r - (p + 1) := by
        simp [wcut, fwt, mvC, setTwo, hP]
      omega
  · intro hlt
    have hpn : (c p).i = .pn := by
      rcases hpP with h | h
      · exact absurd (fpos_le_of r c p (by omega) h) (by omega)
      · exact h
    have hρ : fpos r (mvC c p) = fpos r c := by
      apply fpos_congr
      intro j hj
      by_cases h1 : j = p
      · subst h1; simp [mvC, setTwo, hpn]
      · by_cases h2 : j = p + 1
        · subst h2; simp [mvC, setTwo, hpn, hyi]
        · simp [mvC, setTwo, h1, h2]
    have hρ2 : p + 2 ≤ fpos r c := by
      have : fpos r c ≠ p + 1 := by
        intro h
        have := fpos_hit r c (by omega)
        rw [h, hyi] at this
        exact absurd this (by decide)
      omega
    rw [fwPt_eq, fwPt_eq, hρ]
    apply wsum_congr
    intro k hk
    by_cases hkp : k ≤ p + 1
    · simp [wcut, show ¬ fpos r c ≤ k by omega]
    · have h1 : k ≠ p := by omega
      have h2 : k ≠ p + 1 := by omega
      simp [wcut, fwt, mvC, setTwo, h1, h2]

/-- **The weight from the pending tail on, under a settlement of a pending non-tail packet.**

Consumer: `fill_step_window`. -/
theorem fwPt_settle (r p : Nat) (hp : p < r) (c : Nat → Cell) (hpn : (c p).i = .pn) :
    (fpos r c ≤ p → fwPt r (stC c p { i := .sn, c := .off }) + (r - p) = fwPt r c) ∧
    (p < fpos r c → fwPt r (stC c p { i := .sn, c := .off }) = fwPt r c) := by
  have hρ : fpos r (stC c p { i := .sn, c := .off }) = fpos r c := by
    apply fpos_congr
    intro j hj
    by_cases h1 : j = p
    · subst h1; simp [stC, setOne, hpn]
    · simp [stC, setOne, h1]
  constructor
  · intro hρp
    rw [fwPt_eq, fwPt_eq, hρ]
    have key := wsum_edit_one (wcut (fpos r c) r c)
      (wcut (fpos r c) r (stC c p { i := .sn, c := .off })) p
      (by
        intro k hk
        simp [wcut, fwt, stC, setOne, hk]) r (by omega)
    have e1 : wcut (fpos r c) r c p = r - p := by
      simp [wcut, fwt, hpn, hρp, Inp.isP]
    have e2 : wcut (fpos r c) r (stC c p { i := .sn, c := .off }) p = 0 := by
      simp [wcut, fwt, stC, setOne, Inp.isP]
    omega
  · intro hlt
    rw [fwPt_eq, fwPt_eq, hρ]
    apply wsum_congr
    intro k hk
    by_cases h1 : k = p
    · subst h1; simp [wcut, show ¬ fpos r c ≤ k by omega]
    · simp [wcut, fwt, stC, setOne, h1]

/-- **The weight from the pending tail on, under the acceptance of a non-tail packet.**

Consumer: `fill_step_window`. -/
theorem fwPt_accept_pn (r : Nat) (hr : 0 < r) (c : Nat → Cell) (h0 : c 0 = { i := .e, c := .off }) :
    fwPt r (stC c 0 { i := .pn, c := .off }) = fwPt r c := by
  have h0i : (c 0).i = .e := by rw [h0]
  have hρ : fpos r (stC c 0 { i := .pn, c := .off }) = fpos r c := by
    apply fpos_congr
    intro j hj
    by_cases h1 : j = 0
    · subst h1; simp [stC, setOne, h0i]
    · simp [stC, setOne, h1]
  have hρ0 : ¬ fpos r c ≤ 0 := by
    intro h
    have hr0 : fpos r c < r := by omega
    have := fpos_hit r c hr0
    have h00 : fpos r c = 0 := by omega
    rw [h00, h0i] at this
    exact absurd this (by decide)
  rw [fwPt_eq, fwPt_eq, hρ]
  apply wsum_congr
  intro k hk
  by_cases h1 : k = 0
  · subst h1; simp [wcut, hρ0]
  · simp [wcut, fwt, stC, setOne, h1]

/-- **The weight from the pending tail on, under the acceptance of a tail.**

Consumer: `fill_step_window`. -/
theorem fwPt_accept_pt (r : Nat) (hr : 0 < r) (c : Nat → Cell) :
    fwPt r (stC c 0 { i := .pt, c := .off }) = fwAll r (stC c 0 { i := .pt, c := .off }) := by
  have hρ : fpos r (stC c 0 { i := .pt, c := .off }) = 0 := by
    apply fpos_eq r _ 0 hr
    · simp [stC, setOne]
    · intro k hk; omega
  rw [fwPt_eq, hρ]
  unfold fwAll
  apply wsum_congr
  intro k hk
  simp [wcut]

/-- The reading of tail bits does not change when the flags and tail bits agree.

Consumer: `tl_move`, `fill_step_window`. -/
theorem tl_congr (r : Nat) (c c' : Nat → Cell)
    (h1 : ∀ j, j < r → puNonE (c j).i = puNonE (c' j).i)
    (h2 : ∀ j, j < r → puNonE (c j).i = true → tailBit (c j) = tailBit (c' j)) :
    tl r c = tl r c' :=
  ordLab_congr _ _ _ _ r h1 h2

/-- The reading of tail bits under a move.

Consumer: `fill_step_window`. -/
theorem tl_move (r p : Nat) (hp : p + 1 < r) (c : Nat → Cell) (hP : (c p).i.isP = true)
    (hy : c (p + 1) = { i := .e, c := .off }) : tl r (mvC c p) = tl r c := by
  have hyi : (c (p + 1)).i = .e := by rw [hy]
  have hnon : puNonE (c p).i = true := by simp [puNonE, hP]
  unfold tl
  have hbase : ordLab (fun j => puNonE (mvC c p j).i) (fun j => tailBit (mvC c p j)) p =
      ordLab (fun j => puNonE (c j).i) (fun j => tailBit (c j)) p := by
    apply ordLab_congr
    · intro j hj; simp [mvC, setTwo, show j ≠ p by omega, show j ≠ p + 1 by omega]
    · intro j hj _; simp [mvC, setTwo, show j ≠ p by omega, show j ≠ p + 1 by omega]
  have h2 : ordLab (fun j => puNonE (mvC c p j).i) (fun j => tailBit (mvC c p j)) (p + 2) =
      ordLab (fun j => puNonE (c j).i) (fun j => tailBit (c j)) (p + 2) := by
    show (if puNonE (mvC c p (p + 1)).i = true then [tailBit (mvC c p (p + 1))] else []) ++
      ((if puNonE (mvC c p p).i = true then [tailBit (mvC c p p)] else []) ++
        ordLab (fun j => puNonE (mvC c p j).i) (fun j => tailBit (mvC c p j)) p) =
      (if puNonE (c (p + 1)).i = true then [tailBit (c (p + 1))] else []) ++
      ((if puNonE (c p).i = true then [tailBit (c p)] else []) ++
        ordLab (fun j => puNonE (c j).i) (fun j => tailBit (c j)) p)
    rw [hbase]
    have e1 : puNonE (mvC c p (p + 1)).i = true := by simp [mvC, setTwo, hnon]
    have e2 : puNonE (mvC c p p).i = false := by simp [mvC, setTwo, puNonE, Inp.isP, Inp.isS]
    have e3 : puNonE (c (p + 1)).i = false := by simp [hyi, puNonE, Inp.isP, Inp.isS]
    have e4 : tailBit (mvC c p (p + 1)) = tailBit (c p) := by simp [mvC, setTwo, tailBit]
    simp [e1, e2, e3, hnon, e4]
  apply ordLab_ext _ _ _ _ (p + 2) h2 r (by omega)
  · intro j hj1 hj2; simp [mvC, setTwo, show j ≠ p by omega, show j ≠ p + 1 by omega]
  · intro j hj1 hj2 _; simp [mvC, setTwo, show j ≠ p by omega, show j ≠ p + 1 by omega]

/-- The reading of tail bits after the deletion of the pending tail at the terminal.

Consumer: `fill_step_window`. -/
theorem tl_delete (r : Nat) (hr : 0 < r) (c : Nat → Cell) (hpt : (c (r - 1)).i = .pt) :
    tl r c = true :: tl r (stC c (r - 1) { i := .e, c := .off }) := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hpt
  unfold tl
  have hf : puNonE (c m).i = true := by simp [puNonE, hpt, Inp.isP]
  rw [ordLab_succ_flag _ _ m hf]
  have hf' : puNonE (stC c m { i := .e, c := .off } m).i = false := by
    simp [stC, setOne, puNonE, Inp.isP, Inp.isS]
  rw [ordLab_succ_noflag _ _ m hf']
  have hb : tailBit (c m) = true := by simp [tailBit, hpt]
  rw [hb]
  congr 1
  apply ordLab_congr
  · intro j hj; simp [stC, setOne, show j ≠ m by omega]
  · intro j hj _; simp [stC, setOne, show j ≠ m by omega]

/-- The reading of tail bits after an acceptance.

Consumer: `fill_step_window`. -/
theorem tl_accept (r : Nat) (hr : 0 < r) (c : Nat → Cell) (t : Bool)
    (h0 : c 0 = { i := .e, c := .off }) :
    tl r (stC c 0 { i := (if t then .pt else .pn), c := .off }) = tl r c ++ [t] := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  have h0i : (c 0).i = .e := by rw [h0]
  have ho0 : puNonE (c 0).i = false := by simp [h0i, puNonE, Inp.isP, Inp.isS]
  unfold tl
  have hb := ordLab_bottom (fun j => puNonE (c j).i) (fun j => tailBit (c j)) t ho0 m
  rw [← hb]
  apply ordLab_congr
  · intro j hj
    by_cases h1 : j = 0
    · subst h1; cases t <;> simp [stC, setOne, puNonE, Inp.isP]
    · simp [stC, setOne, h1]
  · intro j hj _
    by_cases h1 : j = 0
    · subst h1; cases t <;> simp [stC, setOne, tailBit]
    · simp [stC, setOne, h1]

end MarkedCells
end L3

#print axioms L3.MarkedCells.fwPt_move
#print axioms L3.MarkedCells.fwPt_settle
#print axioms L3.MarkedCells.tl_move
#print axioms L3.MarkedCells.tl_accept
