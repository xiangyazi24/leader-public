import Leader.L3.Top.PinnedPhaseFillRun

/-!
# Q7 (P.12 preparation, lemma 3, abstract layer): the nominated letters lower the potential

The potential is positive off the exits, and the nominated letter lowers it by one (or the window
leaves the invariant by a settled tail):

* while a pending packet stands in the window, the edge of the rightmost pending register (the
  terminal edge for the last register);
* otherwise, while the source distance is positive, the edge of the last busy source site (the port
  edge for the terminal site);
* otherwise (a sampled token at the terminal, no pending packet, so an empty border register) the
  port edge, which accepts.

Consumer: `Leader/L3/Top/PinnedPhaseFillCost.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The rightmost pending register below `k`.

Consumer: `fill_win_edge`, `fill_win_term`. -/
def lastP (c : Nat → Cell) : Nat → Option Nat
  | 0 => none
  | k + 1 => if (c k).i.isP = true then some k else lastP c k

/-- The rightmost pending register is pending and nothing right of it is.

Consumer: `fill_win_edge`. -/
theorem lastP_some (c : Nat → Cell) : ∀ k q, lastP c k = some q →
    q < k ∧ (c q).i.isP = true ∧ ∀ j, q < j → j < k → (c j).i.isP = false
  | 0, q, h => by simp [lastP] at h
  | k + 1, q, h => by
      simp only [lastP] at h
      by_cases hk : (c k).i.isP = true
      · rw [if_pos hk] at h
        have hq : k = q := Option.some.inj h
        subst hq
        refine ⟨by omega, hk, ?_⟩
        intro j h1 h2; omega
      · rw [if_neg hk] at h
        obtain ⟨h1, h2, h3⟩ := lastP_some c k q h
        refine ⟨by omega, h2, ?_⟩
        intro j hj1 hj2
        by_cases hjk : j = k
        · subst hjk; simpa using hk
        · exact h3 j hj1 (by omega)

/-- With no rightmost pending register, no register is pending.

Consumer: `fill_nominate_port`, `fill_pos`. -/
theorem lastP_none (c : Nat → Cell) : ∀ k, lastP c k = none → ∀ j, j < k → (c j).i.isP = false
  | 0, _, j, hj => by omega
  | k + 1, h, j, hj => by
      simp only [lastP] at h
      by_cases hk : (c k).i.isP = true
      · rw [if_pos hk] at h; exact absurd h (by simp)
      · rw [if_neg hk] at h
        by_cases hjk : j = k
        · subst hjk; simpa using hk
        · exact lastP_none c k h j (by omega)

/-- A term of a sum is at most the sum.

Consumer: `fill_pos`. -/
theorem wsum_ge_term (f : Nat → Nat) : ∀ a k, k < a → f k ≤ wsum f a
  | 0, k, h => by omega
  | a + 1, k, h => by
      simp only [wsum]
      by_cases hk : k = a
      · subst hk; omega
      · have := wsum_ge_term f a k (by omega)
        omega

/-- **The potential is positive in the invariant.**

Consumer: `fill_cost_row`. -/
theorem fill_pos (r : Nat) (hr : 3 ≤ r) (c : Nat → Cell) (src : Nat → Tok) (a : Nat)
    (ha : a < r) (hI : FillInv r c a) : 0 < fillPhi r c src a := by
  by_cases h : fcnt r c ≤ ftail r a
  · rw [fillPhi_I h]; omega
  · have hr1 : a + 1 < r := by
      apply Classical.byContradiction
      intro hh
      unfold ftail at h
      rw [if_neg hh] at h
      have := fcnt_le r c
      omega
    have hp : r - 1 - a < fcnt r c := by
      unfold ftail at h; rw [if_pos hr1] at h; omega
    obtain ⟨j, hj, hpt⟩ := fill_pt_exists (by omega) hr1 hI hp
    rw [fillPhi_II h]
    have hρ : fpos r c ≤ j := fpos_le_of r c j hj hpt
    have hρr : fpos r c < r := by omega
    have hhit := fpos_hit r c hρr
    unfold fwPt
    have := wsum_ge_term (fun k => if fpos r c ≤ k then fwt r c k else 0) r (fpos r c) hρr
    have h2 : fwt r c (fpos r c) = r - fpos r c := by simp [fwt, hhit, Inp.isP]
    simp only [Nat.le_refl, if_true, h2] at this
    omega

/-- **The nominated window edge** (a pending packet in a non-terminal register, none to its
right): the window leaves the invariant by a settled tail, or the potential falls by one.

Consumer: `fill_cost_row`. -/
theorem fill_win_edge (r : Nat) (hr : 3 ≤ r) (c : Nat → Cell) (src : Nat → Tok) (a : Nat)
    (ha : a < r) (hI : FillInv r c a) (q : Nat) (hq : q + 1 < r) (hP : (c q).i.isP = true)
    (hright : ∀ j, q < j → j < r → (c j).i.isP = false) :
    (∃ j, j < r ∧ ExitShape r (setTwo c q (pair (decide (q = 0)) false (c q) (c (q + 1))).1
        (pair (decide (q = 0)) false (c q) (c (q + 1))).2) j ∧ j = a) ∨
    (FillInv r (setTwo c q (pair (decide (q = 0)) false (c q) (c (q + 1))).1
        (pair (decide (q = 0)) false (c q) (c (q + 1))).2) a ∧
      fillPhi r (setTwo c q (pair (decide (q = 0)) false (c q) (c (q + 1))).1
        (pair (decide (q = 0)) false (c q) (c (q + 1))).2) src a + 1 ≤ fillPhi r c src a) := by
  have hcond : fcnt r c ≤ ftail r a ∨ fpos r c ≤ q := by
    by_cases h : fcnt r c ≤ ftail r a
    · exact Or.inl h
    · right
      have hr1 : a + 1 < r := by
        apply Classical.byContradiction
        intro hh
        unfold ftail at h
        rw [if_neg hh] at h
        have := fcnt_le r c
        omega
      have hp : r - 1 - a < fcnt r c := by
        unfold ftail at h; rw [if_pos hr1] at h; omega
      obtain ⟨j, hj, hpt⟩ := fill_pt_exists (by omega) hr1 hI hp
      have h1 := fpos_le_of r c j hj hpt
      have hjq : j ≤ q := by
        apply Classical.byContradiction
        intro hh
        have := hright j (by omega) hj
        rw [hpt] at this
        simp [Inp.isP] at this
      omega
  have hy := fill_kind hI.1 (q + 1) hq
  have hnp : (c (q + 1)).i.isP = false := hright (q + 1) (by omega) hq
  rcases fill_edge_cases r q hq c hI.1 with h | ⟨_, hy', he⟩ | ⟨_, hy', he⟩
  · exfalso
    -- the pending packet would stay: impossible next to an empty or settled register
    have hyk : (c (q + 1)).i = .e ∨ (c (q + 1)).i = .sn := by
      rcases hy.2 with h' | h' | h' | h'
      · exact Or.inl h'
      · rw [h'] at hnp; simp [Inp.isP] at hnp
      · rw [h'] at hnp; simp [Inp.isP] at hnp
      · exact Or.inr h'
    rcases hyk with hyk | hyk
    · have hyc : c (q + 1) = { i := .e, c := .off } := by
        rcases hc : c (q + 1) with ⟨yi, yk⟩
        rw [hc] at hyk hy
        simp only at hyk hy
        rw [hyk, hy.1]
      have := fill_pair_move (decide (q = 0)) (c q) (fill_kind hI.1 q (by omega)).1 hP
      rw [hyc, this] at h
      have h2 := congrFun h (q + 1)
      simp [setTwo] at h2
      rw [hyc] at h2
      have h3 : (c q).i = .e := by
        have := congrArg Cell.i h2
        simpa using this
      rw [h3] at hP; simp [Inp.isP] at hP
    · have hyc : c (q + 1) = { i := .sn, c := .off } := by
        rcases hc : c (q + 1) with ⟨yi, yk⟩
        rw [hc] at hyk hy
        simp only at hyk hy
        rw [hyk, hy.1]
      have := fill_pair_settle (decide (q = 0)) (c q) (fill_kind hI.1 q (by omega)).1 hP
      rw [hyc, this] at h
      have h2 := congrFun h q
      have h2' : ({ i := (if (c q).i = Inp.pt then Inp.st else Inp.sn), c := Car.off } : Cell) = c q := by
        have e1 : setTwo c q { i := (if (c q).i = Inp.pt then Inp.st else Inp.sn), c := Car.off }
            { i := .sn, c := .off } q =
            { i := (if (c q).i = Inp.pt then Inp.st else Inp.sn), c := Car.off } := by
          simp [setTwo]
        rw [e1] at h2
        exact h2
      have h3 := congrArg Cell.i h2'
      simp only at h3
      rcases hx : (c q).i with _ | _ | _ | _ | _ | _ <;> rw [hx] at h3 hP <;>
        simp [Inp.isP] at h3 hP
  · right
    rw [he]
    obtain ⟨h1, _, h3⟩ := fill_move_step r c src a hI q hq hP hy'
    exact ⟨h1, h3 hcond⟩
  · rcases (show (c q).i = .pt ∨ (c q).i = .pn by
      rcases hx : (c q).i with _ | _ | _ | _ | _ | _ <;> rw [hx] at hP <;>
        simp [Inp.isP] at hP ⊢) with hpt | hpn
    · left
      refine ⟨q, by omega, ?_, exit_pos_a ha hI hq hpt hy'⟩
      rw [he]
      have hif : (if (c q).i = Inp.pt then Inp.st else Inp.sn) = Inp.st := if_pos hpt
      rw [hif]
      exact exit_of_settle hI.1 hq hpt hy'

    · right
      have hif : (if (c q).i = Inp.pt then Inp.st else Inp.sn) = Inp.sn := by
        rw [hpn]; decide
      rw [he, hif]
      obtain ⟨h1, _, h3⟩ := fill_settle_step r hr c src a ha hI q hq hpn hy'
      exact ⟨h1, h3 hcond⟩

/-- **The nominated terminal edge** (a pending packet in the last register).

Consumer: `fill_cost_row`. -/
theorem fill_win_term (r : Nat) (hr : 3 ≤ r) (c : Nat → Cell) (src : Nat → Tok) (a : Nat)
    (ha : a < r) (hI : FillInv r c a) (hP : (c (r - 1)).i.isP = true) :
    ((if (c (r - 1)).i = .pt then (a + 1) % r else a) < r ∧
      FillInv r (setOne c (r - 1) (pair false true (c (r - 1)) { i := .e, c := .off }).1)
        (if (c (r - 1)).i = .pt then (a + 1) % r else a) ∧
      fillPhi r (setOne c (r - 1) (pair false true (c (r - 1)) { i := .e, c := .off }).1) src
        (if (c (r - 1)).i = .pt then (a + 1) % r else a) + 1 ≤ fillPhi r c src a) := by
  rcases fill_term_cases r (by omega) c hI.1 with ⟨hk, _⟩ | ⟨hpn, he⟩ | ⟨hpt, he⟩
  · exfalso
    rcases hk with h | h <;> rw [h] at hP <;> simp [Inp.isP] at hP
  · rw [he, if_neg (by rw [hpn]; decide)]
    have hcond : fcnt r c ≤ ftail r a ∨ fpos r c ≤ r - 1 := by
      by_cases h : fcnt r c ≤ ftail r a
      · exact Or.inl h
      · right
        have hr1 : a + 1 < r := by
          apply Classical.byContradiction
          intro hh
          unfold ftail at h
          rw [if_neg hh] at h
          have := fcnt_le r c
          omega
        have hp : r - 1 - a < fcnt r c := by
          unfold ftail at h; rw [if_pos hr1] at h; omega
        obtain ⟨j, hj, hpt⟩ := fill_pt_exists (by omega) hr1 hI hp
        have h1 := fpos_le_of r c j hj hpt
        omega
    obtain ⟨h1, _, h3⟩ := fill_term_pn_step r hr c src a hI hpn
    exact ⟨ha, h1, h3 hcond⟩
  · rw [he, if_pos hpt]
    obtain ⟨har, h1, h2⟩ := fill_term_pt_step r hr c src a ha hI hpt
    have : (a + 1) % r = 0 := by
      rw [har, show r - 1 + 1 = r by omega, Nat.mod_self]
    rw [this]
    unfold stC at h1 h2
    exact ⟨by omega, h1, h2⟩

/-- With no pending packet the tail is still to be accepted.

Consumer: `fill_src_drop`, `fill_port_accept`. -/
theorem nopending_phase (r : Nat) (hr : 3 ≤ r) (c : Nat → Cell) (a : Nat) (hI : FillInv r c a)
    (hnp : ∀ j, j < r → (c j).i.isP = false) : fcnt r c ≤ ftail r a := by
  by_cases h : fcnt r c ≤ ftail r a
  · exact h
  · exfalso
    have hr1 : a + 1 < r := by
      apply Classical.byContradiction
      intro hh
      unfold ftail at h
      rw [if_neg hh] at h
      have := fcnt_le r c
      omega
    have hp : r - 1 - a < fcnt r c := by
      unfold ftail at h; rw [if_pos hr1] at h; omega
    obtain ⟨j, hj, hpt⟩ := fill_pt_exists (by omega) hr1 hI hp
    have := hnp j hj
    rw [hpt] at this
    simp [Inp.isP] at this

/-- **The nominated source edge** (no pending packet, positive distance): the edge of the last busy
site lowers the distance and hence the potential.

Consumer: `fill_cost_row`. -/
theorem fill_src_drop (r : Nat) (hr : 3 ≤ r) (c : Nat → Cell) (src : Nat → Tok) (a : Nat)
    (hI : FillInv r c a) (hnp : ∀ j, j < r → (c j).i.isP = false) (hd : dist r src ≠ 0)
    (acc : Bool) :
    srcIdx r src < r ∧
    fillPhi r c (srcStepAt r acc src (srcIdx r src)) a + 1 ≤ fillPhi r c src a := by
  obtain ⟨h1, h2⟩ := dist_step_drop r hr src acc hd
  refine ⟨h1, ?_⟩
  have hph := nopending_phase r hr c a hI hnp
  rw [fillPhi_I hph, fillPhi_I hph]
  omega

/-- **The nominated port edge** (no pending packet, a sampled token at the terminal): the packet is
accepted and the potential falls by one.

Consumer: `fill_cost_row`. -/
theorem fill_port_accept (r : Nat) (hr : 3 ≤ r) (c : Nat → Cell) (src : Nat → Tok) (a : Nat)
    (ha : a < r) (hI : FillInv r c a) (hnp : ∀ j, j < r → (c j).i.isP = false)
    (hd : dist r src = 0) :
    c 0 = { i := .e, c := .off } ∧
    FillInv r (stC c 0 { i := (if decide ((a + fcnt r c) % r = r - 1) then .pt else .pn), c := .off }) a ∧
    fillPhi r (stC c 0 { i := (if decide ((a + fcnt r c) % r = r - 1) then .pt else .pn), c := .off }) (srcStepAt r true src (r - 1)) a + 1 ≤ fillPhi r c src a := by
  have h0 : c 0 = { i := .e, c := .off } := by
    have hk := fill_kind hI.1 0 (by omega)
    have hb := fill_border hI.1 (by omega)
    have hn := hnp 0 (by omega)
    rcases hb with h | h | h
    · rcases hc : c 0 with ⟨yi, yk⟩
      rw [hc] at h hk
      simp only at h hk
      rw [h, hk.1]
    · rw [h] at hn; simp [Inp.isP] at hn
    · rw [h] at hn; simp [Inp.isP] at hn
  have hD : (src (r - 1)).isD = true := (dist_zero_iff r (by omega) src).1 hd
  obtain ⟨h1, _, h3⟩ := fill_accept_step r hr c src a ha hI _ h0 hD rfl
  exact ⟨h0, h1, h3 (nopending_phase r hr c a hI hnp)⟩

end MarkedCells
end L3

#print axioms L3.MarkedCells.fill_win_edge
#print axioms L3.MarkedCells.fill_win_term
#print axioms L3.MarkedCells.fill_pos
#print axioms L3.MarkedCells.fill_src_drop
#print axioms L3.MarkedCells.fill_port_accept
