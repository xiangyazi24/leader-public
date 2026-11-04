import Leader.L3.Top.PinnedPhaseFillStep
import Leader.L3.Top.SettledPotentialSrc

/-!
# Q7 (P.12 preparation, lemma 3, abstract layer): one step of the fill regime

The potential `fillPhi` never rises along a step of the window and the source block, the fill
invariant is kept, and the window leaves the invariant only by a settled tail (`st`), which is a
misplaced cut away from the border and an aligned window at the border.  The nominated letters
lower the potential by one.

Consumer: `Leader/L3/Top/PinnedPhaseFillNominate.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The potential while the tail is still to be accepted.

Consumer: `phi_drop`. -/
theorem fillPhi_I {r : Nat} {c : Nat → Cell} {src : Nat → Tok} {a : Nat}
    (h : fcnt r c ≤ ftail r a) :
    fillPhi r c src a = fwAll r c + dist r src + (r + 1) + (ftail r a - fcnt r c) * (2 * r + 2) := by
  unfold fillPhi
  rw [if_pos h]

/-- The potential once the tail is accepted.

Consumer: `phi_drop`. -/
theorem fillPhi_II {r : Nat} {c : Nat → Cell} {src : Nat → Tok} {a : Nat}
    (h : ¬ fcnt r c ≤ ftail r a) : fillPhi r c src a = fwPt r c := by
  unfold fillPhi
  rw [if_neg h]

/-- **A step that takes weight `w` off a counted pending packet lowers the potential.**

Consumer: `fill_move_step`, `fill_settle_step`, `fill_term_pn_step`. -/
theorem phi_drop (r : Nat) (c c' : Nat → Cell) (src : Nat → Tok) (a p w : Nat) (hw : 1 ≤ w)
    (hcnt : fcnt r c' = fcnt r c) (h1 : fwAll r c' + w = fwAll r c)
    (h2 : fpos r c ≤ p → fwPt r c' + w = fwPt r c) (h3 : p < fpos r c → fwPt r c' = fwPt r c) :
    fillPhi r c' src a ≤ fillPhi r c src a ∧
    ((fcnt r c ≤ ftail r a ∨ fpos r c ≤ p) → fillPhi r c' src a + 1 ≤ fillPhi r c src a) := by
  by_cases h : fcnt r c ≤ ftail r a
  · have h' : fcnt r c' ≤ ftail r a := by rw [hcnt]; exact h
    rw [fillPhi_I h', fillPhi_I h, hcnt]
    generalize (ftail r a - fcnt r c) * (2 * r + 2) = K
    refine ⟨by omega, fun _ => by omega⟩
  · have h' : ¬ fcnt r c' ≤ ftail r a := by rw [hcnt]; exact h
    rw [fillPhi_II h', fillPhi_II h]
    by_cases hp : fpos r c ≤ p
    · have := h2 hp
      exact ⟨by omega, fun _ => by omega⟩
    · have := h3 (by omega)
      refine ⟨by omega, ?_⟩
      intro hh
      rcases hh with hh | hh
      · exact absurd hh h
      · exact absurd hh hp

/-- One edge of the source block, other than the port, does not raise the distance.

Consumer: `fill_step`. -/
theorem dist_edge_le (r : Nat) (hr : 3 ≤ r) (src : Nat → Tok) (acc : Bool) (j : Nat)
    (hj : j + 1 < r) : dist r (srcStepAt r acc src j) ≤ dist r src := by
  by_cases hd : dist r src = 0
  · rcases dist_zero_step r hr src acc j (by omega) hd with h | ⟨h, _⟩
    · omega
    · omega
  · exact dist_step_le r hr src _ (SrcStep.edge j (by omega) acc) hd

/-- The port edge that does not accept does not raise the distance.

Consumer: `fill_step`. -/
theorem dist_clean_le (r : Nat) (hr : 3 ≤ r) (src : Nat → Tok) (acc : Bool)
    (h : (src (r - 1)).isD = true → acc = false) :
    dist r (srcStepAt r acc src (r - 1)) ≤ dist r src := by
  by_cases hd : dist r src = 0
  · have hD := (dist_zero_iff r (by omega) src).1 hd
    have hacc := h hD
    rcases dist_zero_step r hr src acc (r - 1) (by omega) hd with h1 | ⟨_, h2⟩
    · omega
    · rw [hacc] at h2; exact absurd h2 (by decide)
  · exact dist_step_le r hr src _ (SrcStep.edge (r - 1) (by omega) acc) hd

/-- **A move keeps the invariant and does not raise the potential.**

Consumer: `fill_step`. -/
theorem fill_move_step (r : Nat) (c : Nat → Cell) (src : Nat → Tok) (a : Nat)
    (hI : FillInv r c a) (p : Nat) (hp : p + 1 < r) (hP : (c p).i.isP = true)
    (hy : c (p + 1) = { i := .e, c := .off }) :
    FillInv r (mvC c p) a ∧ fillPhi r (mvC c p) src a ≤ fillPhi r c src a ∧
    ((fcnt r c ≤ ftail r a ∨ fpos r c ≤ p) →
      fillPhi r (mvC c p) src a + 1 ≤ fillPhi r c src a) := by
  obtain ⟨hc1, hc2⟩ := move_counts r p hp c hP hy
  obtain ⟨hw1, hw2⟩ := fwPt_move r p hp c hP hy
  refine ⟨⟨fillShape_move hI.1 hp hP hy, ?_⟩, ?_⟩
  · rw [tl_move r p hp c hP hy, hI.2, hc1]
  · exact phi_drop r c (mvC c p) src a p 1 (by omega) hc1 hc2
      (fun h => hw1 h) (fun h => hw2 h)

/-- **A settlement of a pending non-tail packet next to the block.**

Consumer: `fill_step`. -/
theorem fill_settle_step (r : Nat) (hr : 3 ≤ r) (c : Nat → Cell) (src : Nat → Tok) (a : Nat)
    (ha : a < r) (hI : FillInv r c a) (p : Nat) (hp : p + 1 < r) (hpn : (c p).i = .pn)
    (hy : c (p + 1) = { i := .sn, c := .off }) :
    FillInv r (stC c p { i := .sn, c := .off }) a ∧
    fillPhi r (stC c p { i := .sn, c := .off }) src a ≤ fillPhi r c src a ∧
    ((fcnt r c ≤ ftail r a ∨ fpos r c ≤ p) →
      fillPhi r (stC c p { i := .sn, c := .off }) src a + 1 ≤ fillPhi r c src a) := by
  have hP : (c p).i.isP = true := by simp [hpn, Inp.isP]
  have h0 : 0 < p := by
    apply Nat.pos_of_ne_zero
    intro hp0
    subst hp0
    exact fill_border_full (by omega) ha hI hpn hy (by omega)
  obtain ⟨hc1, hc2⟩ := settle_counts r p (by omega) c hP { i := .sn, c := .off } rfl rfl
  obtain ⟨hw1, hw2⟩ := fwPt_settle r p (by omega) c hpn
  refine ⟨⟨fillShape_settle hI.1 hp hpn h0 hy, ?_⟩, ?_⟩
  · rw [hc1, ← hI.2]
    apply tl_congr
    · intro j hj
      by_cases h1 : j = p
      · subst h1; simp [stC, setOne, hpn, puNonE, Inp.isP, Inp.isS]
      · simp [stC, setOne, h1]
    · intro j hj _
      by_cases h1 : j = p
      · subst h1; simp [stC, setOne, hpn, tailBit]
      · simp [stC, setOne, h1]
  · exact phi_drop r c _ src a p (r - p) (by omega) hc1 hc2 hw1 hw2

/-- **A terminal settlement of a pending non-tail packet.**

Consumer: `fill_step`. -/
theorem fill_term_pn_step (r : Nat) (hr : 3 ≤ r) (c : Nat → Cell) (src : Nat → Tok) (a : Nat)
    (hI : FillInv r c a) (hpn : (c (r - 1)).i = .pn) :
    FillInv r (stC c (r - 1) { i := .sn, c := .off }) a ∧
    fillPhi r (stC c (r - 1) { i := .sn, c := .off }) src a ≤ fillPhi r c src a ∧
    ((fcnt r c ≤ ftail r a ∨ fpos r c ≤ r - 1) →
      fillPhi r (stC c (r - 1) { i := .sn, c := .off }) src a + 1 ≤ fillPhi r c src a) := by
  have hP : (c (r - 1)).i.isP = true := by simp [hpn, Inp.isP]
  obtain ⟨hc1, hc2⟩ := settle_counts r (r - 1) (by omega) c hP { i := .sn, c := .off } rfl rfl
  obtain ⟨hw1, hw2⟩ := fwPt_settle r (r - 1) (by omega) c hpn
  refine ⟨⟨fillShape_term_pn hI.1 (by omega) hpn, ?_⟩, ?_⟩
  · rw [hc1, ← hI.2]
    apply tl_congr
    · intro j hj
      by_cases h1 : j = r - 1
      · subst h1; simp [stC, setOne, hpn, puNonE, Inp.isP, Inp.isS]
      · simp [stC, setOne, h1]
    · intro j hj _
      by_cases h1 : j = r - 1
      · subst h1; simp [stC, setOne, hpn, tailBit]
      · simp [stC, setOne, h1]
  · exact phi_drop r c _ src a (r - 1) (r - (r - 1)) (by omega) hc1 hc2 hw1 hw2

/-- **The terminal deletion of the oldest outstanding tail**: the residue wraps to zero and the
potential falls by one.

Consumer: `fill_step`. -/
theorem fill_term_pt_step (r : Nat) (hr : 3 ≤ r) (c : Nat → Cell) (src : Nat → Tok) (a : Nat)
    (ha : a < r) (hI : FillInv r c a) (hpt : (c (r - 1)).i = .pt) :
    a = r - 1 ∧ FillInv r (stC c (r - 1) { i := .e, c := .off }) 0 ∧
    fillPhi r (stC c (r - 1) { i := .e, c := .off }) src 0 + 1 ≤ fillPhi r c src a := by
  have har : a = r - 1 := fill_pt_term (by omega) ha hI hpt
  have hP : (c (r - 1)).i.isP = true := by simp [hpt, Inp.isP]
  obtain ⟨hc1, hc2⟩ := delete_counts r (by omega) c hP
  have hle := fcnt_le r c
  have hft1 : ftail r a = r := by
    unfold ftail; rw [if_neg (by omega)]
  have hft0 : ftail r 0 = r - 1 := by
    unfold ftail; rw [if_pos (by omega)]; omega
  refine ⟨har, ⟨fillShape_term_pt hI.1 (by omega) hpt, ?_⟩, ?_⟩
  · have hd := tl_delete r (by omega) c hpt
    have h2 := hI.2
    obtain ⟨p0, hp0⟩ : ∃ p0, fcnt r (stC c (r - 1) { i := .e, c := .off }) = p0 := ⟨_, rfl⟩
    have hp1 : fcnt r c = p0 + 1 := by omega
    rw [hp1, pat_cons, hd] at h2
    have h3 := (List.cons.inj h2).2
    rw [hp0, h3, har]
    have : r - 1 + 1 = r := by omega
    rw [this, ← pat_mod r r p0, Nat.mod_self]
  · have hc : fcnt r c ≤ ftail r a := by omega
    have hc' : fcnt r (stC c (r - 1) { i := .e, c := .off }) ≤ ftail r 0 := by omega
    rw [fillPhi_I hc', fillPhi_I hc]
    have : ftail r 0 - fcnt r (stC c (r - 1) { i := .e, c := .off }) = ftail r a - fcnt r c := by
      omega
    rw [this]
    generalize (ftail r a - fcnt r c) * (2 * r + 2) = K
    omega

/-- **An acceptance.**

Consumer: `fill_step`. -/
theorem fill_accept_step (r : Nat) (hr : 3 ≤ r) (c : Nat → Cell) (src : Nat → Tok) (a : Nat)
    (ha : a < r) (hI : FillInv r c a) (t : Bool) (h0 : c 0 = { i := .e, c := .off })
    (hD : (src (r - 1)).isD = true) (ht : t = decide ((a + fcnt r c) % r = r - 1)) :
    FillInv r (stC c 0 { i := (if t then .pt else .pn), c := .off }) a ∧
    fillPhi r (stC c 0 { i := (if t then .pt else .pn), c := .off }) (srcStepAt r true src (r - 1)) a ≤
      fillPhi r c src a ∧
    (fcnt r c ≤ ftail r a →
      fillPhi r (stC c 0 { i := (if t then .pt else .pn), c := .off })
        (srcStepAt r true src (r - 1)) a + 1 ≤ fillPhi r c src a) := by
  obtain ⟨hc1, hc2⟩ := accept_counts r (by omega) c t h0
  have hle' := fcnt_le r (stC c 0 { i := (if t then .pt else .pn), c := .off })
  have hd0 : dist r src = 0 := (dist_zero_iff r (by omega) src).2 hD
  have hd' := dist_le r (srcStepAt r true src (r - 1))
  have hFI : FillInv r (stC c 0 { i := (if t then .pt else .pn), c := .off }) a := by
    refine ⟨fillShape_accept hI.1 (by omega) t h0, ?_⟩
    rw [tl_accept r (by omega) c t h0, hc1, pat_succ, ← ht, hI.2]
  refine ⟨hFI, ?_⟩
  by_cases hA : fcnt r c ≤ ftail r a
  · by_cases hA1 : fcnt r c + 1 ≤ ftail r a
    · have hc' : fcnt r (stC c 0 { i := (if t then .pt else .pn), c := .off }) ≤ ftail r a := by
        omega
      rw [fillPhi_I hc', fillPhi_I hA, hc1, hc2, hd0]
      obtain ⟨K, hK⟩ : ∃ K, ftail r a - fcnt r c = K + 1 := ⟨ftail r a - fcnt r c - 1, by omega⟩
      have hK' : ftail r a - (fcnt r c + 1) = K := by omega
      rw [hK, hK', Nat.add_mul]
      generalize K * (2 * r + 2) = K'
      refine ⟨by omega, fun _ => by omega⟩
    · have hEq : fcnt r c = ftail r a := by omega
      have hr1 : a + 1 < r := by
        apply Classical.byContradiction
        intro hh
        unfold ftail at hEq
        rw [if_neg hh] at hEq
        omega
      have htt : t = true := by
        rw [ht, hEq]; exact accept_bit_tail (by omega) hr1 rfl
      subst htt
      have hc' : ¬ fcnt r (stC c 0 { i := (if true then .pt else .pn), c := .off }) ≤ ftail r a := by
        omega
      rw [fillPhi_II hc', fillPhi_I hA]
      have := fwPt_accept_pt r (by omega) c
      simp only [if_true] at hc2 this ⊢
      rw [this, hc2, hEq]
      simp
      omega
  · have hr1 : a + 1 < r := by
      apply Classical.byContradiction
      intro hh
      unfold ftail at hA
      rw [if_neg hh] at hA
      omega
    have hlt : fcnt r c < r := by omega
    have htf : t = false := by
      rw [ht]
      exact accept_bit_after (by omega) hr1 (by omega) hlt
    subst htf
    have hc' : ¬ fcnt r (stC c 0 { i := (if false then .pt else .pn), c := .off }) ≤ ftail r a := by
      omega
    rw [fillPhi_II hc', fillPhi_II hA]
    have := fwPt_accept_pn r (by omega) c h0
    simp only [Bool.false_eq_true, if_false] at this ⊢
    rw [this]
    exact ⟨Nat.le_refl _, fun h => absurd h hA⟩

/-- **The abstract step of the fill regime**: a window step together with the source block, with
the residue `a` of the oldest outstanding serial.

Consumer: `fill_step`. -/
inductive FillStep (r : Nat) (c : Nat → Cell) (src : Nat → Tok) (a : Nat) :
    (Nat → Cell) → (Nat → Tok) → Nat → Prop
  | frame : FillStep r c src a c src a
  | edge (p : Nat) (hp : p + 1 < r) :
      FillStep r c src a
        (setTwo c p (pair (decide (p = 0)) false (c p) (c (p + 1))).1
          (pair (decide (p = 0)) false (c p) (c (p + 1))).2) src a
  | term :
      FillStep r c src a
        (setOne c (r - 1) (pair false true (c (r - 1)) { i := .e, c := .off }).1) src
        (if (c (r - 1)).i = .pt then (a + 1) % r else a)
  | srcEdge (j : Nat) (hj : j + 1 < r) (acc : Bool) :
      FillStep r c src a c (srcStepAt r acc src j) a
  | clean (acc : Bool) (h : (src (r - 1)).isD = true → acc = false) :
      FillStep r c src a (setOne c 0 (portClean (c 0))) (srcStepAt r acc src (r - 1)) a
  | accept (t : Bool) (h0 : c 0 = { i := .e, c := .off }) (hD : (src (r - 1)).isD = true)
      (ht : t = decide ((a + fcnt r c) % r = r - 1)) :
      FillStep r c src a (setOne c 0 (portAccept t (c 0))) (srcStepAt r true src (r - 1)) a

/-- A source step that does not raise the distance keeps the potential from rising.

Consumer: `fill_step`. -/
theorem phi_src_le (r : Nat) (c : Nat → Cell) (src src' : Nat → Tok) (a : Nat)
    (h : dist r src' ≤ dist r src) : fillPhi r c src' a ≤ fillPhi r c src a := by
  by_cases hc : fcnt r c ≤ ftail r a
  · rw [fillPhi_I hc, fillPhi_I hc]
    omega
  · rw [fillPhi_II hc, fillPhi_II hc]
    exact Nat.le_refl _

/-- **One step of the fill regime**: the window leaves the invariant only by a settled tail, and
otherwise the invariant is kept and the potential does not rise.

Consumer: `Leader/L3/Top/PinnedPhaseFillNominate.lean`. -/
theorem fill_step (r : Nat) (hr : 3 ≤ r) (c : Nat → Cell) (src : Nat → Tok) (a : Nat)
    (ha : a < r) (hI : FillInv r c a) {c' : Nat → Cell} {src' : Nat → Tok} {a' : Nat}
    (hs : FillStep r c src a c' src' a') :
    (∃ j, j < r ∧ ExitShape r c' j ∧ j = a ∧ a' = a) ∨
    (a' < r ∧ FillInv r c' a' ∧ fillPhi r c' src' a' ≤ fillPhi r c src a ∧
      (a ≠ r - 1 → a' = a)) := by
  cases hs with
  | frame => exact Or.inr ⟨ha, hI, Nat.le_refl _, fun _ => rfl⟩
  | edge p hp =>
    rcases fill_edge_cases r p hp c hI.1 with h | ⟨hP, hy, he⟩ | ⟨hP, hy, he⟩
    · rw [h]; exact Or.inr ⟨ha, hI, Nat.le_refl _, fun _ => rfl⟩
    · rw [he]
      obtain ⟨h1, h2, _⟩ := fill_move_step r c src a hI p hp hP hy
      exact Or.inr ⟨ha, h1, h2, fun _ => rfl⟩
    · rcases (show (c p).i = .pt ∨ (c p).i = .pn by
        rcases hx : (c p).i with _ | _ | _ | _ | _ | _ <;> rw [hx] at hP <;>
          simp [Inp.isP] at hP ⊢) with hpt | hpn
      · left
        have hy' : c (p + 1) = { i := .sn, c := .off } := hy
        refine ⟨p, by omega, ?_, exit_pos_a ha hI hp hpt hy', rfl⟩
        rw [he]
        have hif : (if (c p).i = Inp.pt then Inp.st else Inp.sn) = Inp.st := if_pos hpt
        rw [hif]
        exact exit_of_settle hI.1 hp hpt hy
      · have hif : (if (c p).i = Inp.pt then Inp.st else Inp.sn) = Inp.sn := by
          rw [hpn]; decide
        rw [he, hif]
        have hy' : c (p + 1) = { i := .sn, c := .off } := hy
        obtain ⟨h1, h2, _⟩ := fill_settle_step r hr c src a ha hI p hp hpn hy'
        exact Or.inr ⟨ha, h1, h2, fun _ => rfl⟩
  | term =>
    rcases fill_term_cases r (by omega) c hI.1 with ⟨hk, he⟩ | ⟨hpn, he⟩ | ⟨hpt, he⟩
    · rw [he]
      have hnp : (c (r - 1)).i ≠ .pt := by
        rcases hk with h | h <;> rw [h] <;> decide
      rw [if_neg hnp]
      exact Or.inr ⟨ha, hI, Nat.le_refl _, fun _ => rfl⟩
    · rw [he, if_neg (by rw [hpn]; decide)]
      obtain ⟨h1, h2, _⟩ := fill_term_pn_step r hr c src a hI hpn
      exact Or.inr ⟨ha, h1, h2, fun _ => rfl⟩
    · rw [he, if_pos hpt]
      obtain ⟨har, h1, h2⟩ := fill_term_pt_step r hr c src a ha hI hpt
      have : (a + 1) % r = 0 := by
        rw [har, show r - 1 + 1 = r by omega, Nat.mod_self]
      rw [this]
      unfold stC at h1 h2
      exact Or.inr ⟨by omega, h1, by omega, fun hne => absurd har hne⟩
  | srcEdge j hj acc =>
    exact Or.inr ⟨ha, hI, phi_src_le r c src _ a (dist_edge_le r hr src acc j hj), fun _ => rfl⟩
  | clean acc h =>
    have hk := fill_kind hI.1 0 (by omega)
    have hcl : setOne c 0 (portClean (c 0)) = c := by
      funext j
      by_cases hj : j = 0
      · subst hj; simp [setOne, pu_port_clean _ hk.1]
      · simp [setOne, hj]
    rw [hcl]
    exact Or.inr ⟨ha, hI, phi_src_le r c src _ a (dist_clean_le r hr src acc h), fun _ => rfl⟩
  | accept t h0 hD ht =>
    have hpa : setOne c 0 (portAccept t (c 0)) =
        stC c 0 { i := (if t then .pt else .pn), c := .off } := by
      unfold portAccept stC
      rw [if_pos h0]
    rw [hpa]
    obtain ⟨h1, h2, _⟩ := fill_accept_step r hr c src a ha hI t h0 hD ht
    exact Or.inr ⟨ha, h1, h2, fun _ => rfl⟩

end MarkedCells
end L3

#print axioms L3.MarkedCells.fill_step
#print axioms L3.MarkedCells.phi_drop
