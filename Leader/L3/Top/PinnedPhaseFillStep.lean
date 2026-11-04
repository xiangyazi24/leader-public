import Leader.L3.Top.PinnedPrepareAlign
import Leader.L3.Top.PinnedPhaseFillTail

/-!
# Q7 (P.12 preparation, lemma 3, abstract layer): the facts the fill invariant gives

The fill invariant `FillInv` ties the tail bits of the packets in the window to the pattern of
consecutive serials.  This module extracts the five facts the potential argument needs: the number
of flagged registers is at most `r`; a pending tail at the terminal forces the oldest outstanding
serial to be a tail (`a = r - 1`); once the tail is accepted a pending tail stands in the window;
a full window cannot end in a non-tail packet; and the tail bit of the next accepted packet.

Consumer: `Leader/L3/TopPinnedPhaseFillStepProof.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The flag count is at most `r`.

Consumer: `fill_step`. -/
theorem fcnt_le (r : Nat) (c : Nat → Cell) : fcnt r c ≤ r := by
  have := wsum_le (fl c) 1 (fun k => by unfold fl; split <;> omega) r
  unfold fcnt
  simpa using this

/-- With every register flagged the flag count is `r`.

Consumer: `fill_border_full`. -/
theorem fcnt_full (r : Nat) (c : Nat → Cell) (h : ∀ j, j < r → puNonE (c j).i = true) :
    fcnt r c = r := by
  unfold fcnt
  have : wsum (fl c) r = wsum (fun _ => 1) r := by
    apply wsum_congr
    intro k hk
    simp [fl, h k hk]
  rw [this]
  clear this h
  induction r with
  | zero => rfl
  | succ r ih => simp [wsum, ih]

/-- The length of the reading is the flag count.

Consumer: `fill_pt_term`. -/
theorem tl_length (r : Nat) (c : Nat → Cell) : (tl r c).length = fcnt r c :=
  ordLab_length (fun j => puNonE (c j).i) (fun j => tailBit (c j)) r

/-- A tail bit in the reading comes from a pending tail of the window.

Consumer: `fill_pt_exists`, `fill_border_full`. -/
theorem tl_true_pt {r : Nat} {c : Nat → Cell} (hs : FillShape r c) (h : true ∈ tl r c) :
    ∃ j, j < r ∧ (c j).i = .pt := by
  obtain ⟨j, hj, _, hb⟩ := ordLab_true_mem r h
  refine ⟨j, hj, ?_⟩
  have hk := fill_kind hs j hj
  have hb' : (c j).i = .pt ∨ (c j).i = .st := by simpa [tailBit] using hb
  rcases hb' with h | h
  · exact h
  · rcases hk.2 with h' | h' | h' | h' <;> rw [h'] at h <;> exact absurd h (by decide)

/-- A pending tail at the terminal means that the oldest outstanding serial is a tail.

Consumer: `fill_step`. -/
theorem fill_pt_term {r a : Nat} {c : Nat → Cell} (hr : 0 < r) (ha : a < r) (hI : FillInv r c a)
    (hpt : (c (r - 1)).i = .pt) : a = r - 1 := by
  have hd := tl_delete r hr c hpt
  have hlen := tl_length r c
  rw [hd] at hlen
  simp only [List.length_cons] at hlen
  obtain ⟨p0, hp0⟩ : ∃ p0, fcnt r c = p0 + 1 := ⟨(tl r (stC c (r - 1) { i := .e, c := .off })).length,
    by omega⟩
  have h2 := hI.2
  rw [hp0, pat_cons, hd] at h2
  have h3 := (List.cons.inj h2).1
  have h4 : a % r = r - 1 := by simpa using h3.symm
  rw [Nat.mod_eq_of_lt ha] at h4
  exact h4

/-- Once the tail is accepted a pending tail stands in the window.

Consumer: `fill_step`. -/
theorem fill_pt_exists {r a : Nat} {c : Nat → Cell} (hr : 0 < r) (ha : a + 1 < r)
    (hI : FillInv r c a) (hp : r - 1 - a < fcnt r c) : ∃ j, j < r ∧ (c j).i = .pt := by
  apply tl_true_pt hI.1
  rw [hI.2]
  unfold pat
  rw [List.mem_map]
  refine ⟨r - 1 - a, List.mem_range.2 hp, ?_⟩
  have : a + (r - 1 - a) = r - 1 := by omega
  rw [this, Nat.mod_eq_of_lt (by omega)]
  simp

/-- A tail bit is in a pattern that covers the tail.

Consumer: `fill_border_full`. -/
theorem true_mem_pat {r a p : Nat} (hr : 0 < r) (ha : a < r) (hp : r - 1 - a < p) :
    true ∈ pat r a p := by
  unfold pat
  rw [List.mem_map]
  refine ⟨r - 1 - a, List.mem_range.2 hp, ?_⟩
  have : a + (r - 1 - a) = r - 1 := by omega
  rw [this, Nat.mod_eq_of_lt (by omega)]
  simp

/-- **A border pending non-tail packet next to a block of `r - 1` settled packets is
impossible**: a window of `r` consecutive serials holds a tail.

Consumer: `fill_step`. -/
theorem fill_border_full {r a : Nat} {c : Nat → Cell} (hr : 0 < r) (ha : a < r)
    (hI : FillInv r c a) (hpn : (c 0).i = .pn) (hy : c 1 = { i := .sn, c := .off })
    (h2 : 2 ≤ r) : False := by
  obtain ⟨m, hm, hreg, hblk⟩ := hI.1
  have hm1 : r - m ≤ 1 := by
    apply Classical.byContradiction
    intro h
    have := (hreg 1 (by omega)).2
    rw [hy] at this
    simp at this
  have hall : ∀ j, j < r → puNonE (c j).i = true := by
    intro j hj
    by_cases h0 : j = 0
    · subst h0; simp [hpn, puNonE, Inp.isP]
    · have := hblk j (by omega) hj
      rw [this]; simp [puNonE, Inp.isS]
  have hcnt := fcnt_full r c hall
  have htrue : true ∈ tl r c := by
    rw [hI.2, hcnt]
    exact true_mem_pat hr ha (by omega)
  obtain ⟨j, hj, hjpt⟩ := tl_true_pt hI.1 htrue
  by_cases h0 : j = 0
  · subst h0; rw [hpn] at hjpt; exact absurd hjpt (by decide)
  · have := hblk j (by omega) hj
    rw [this] at hjpt
    exact absurd hjpt (by simp)

/-- The tail bit of the packet accepted into a window that does not yet hold the tail.

Consumer: `fill_step`. -/
theorem accept_bit_before {r a p : Nat} (hr : 0 < r) (ha : a < r) (hp : p < ftail r a)
    (hp' : p < r) :
    decide ((a + p) % r = r - 1) = decide (a = r - 1 ∧ p = 0) := by
  unfold ftail at hp
  by_cases h1 : a + 1 < r
  · rw [if_pos h1] at hp
    have : (a + p) % r = a + p := Nat.mod_eq_of_lt (by omega)
    rw [this]
    have h3 : ¬ (a = r - 1 ∧ p = 0) := by omega
    simp [h3]
    omega
  · rw [if_neg h1] at hp
    have har : a = r - 1 := by omega
    subst har
    by_cases hp0 : p = 0
    · subst hp0; simp [Nat.mod_eq_of_lt ha]
    · have hlt : (r - 1 + p) % r = p - 1 := by
        have : r - 1 + p = (p - 1) + r := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hlt]
      simp [hp0]
      omega

/-- The packet accepted when the tail is next is the tail.

Consumer: `fill_step`. -/
theorem accept_bit_tail {r a p : Nat} (hr : 0 < r) (ha : a + 1 < r) (hp : p = ftail r a) :
    decide ((a + p) % r = r - 1) = true := by
  unfold ftail at hp
  rw [if_pos ha] at hp
  have : a + p = r - 1 := by omega
  rw [this, Nat.mod_eq_of_lt (by omega)]
  simp

/-- The packet accepted after the tail is a non-tail.

Consumer: `fill_step`. -/
theorem accept_bit_after {r a p : Nat} (hr : 0 < r) (ha : a + 1 < r) (hp : ftail r a < p)
    (hp' : p < r) : decide ((a + p) % r = r - 1) = false := by
  unfold ftail at hp
  rw [if_pos ha] at hp
  have h1 : (a + p) % r = a + p - r := by
    have : a + p = (a + p - r) + r := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [h1]
  have : ¬ (a + p - r = r - 1) := by omega
  simp [this]

/-- **A settled tail forms at the position of the residue**: the pending tail next to a block of
`m` settled non-tails has rank `m`, so `(a + m) mod r = r - 1`, i.e. its register is `a`.

Consumer: `fill_step`, `fill_win_edge`. -/
theorem exit_pos_a {r a : Nat} {c : Nat → Cell} (ha : a < r) (hI : FillInv r c a) {p : Nat}
    (hp : p + 1 < r) (hpt : (c p).i = .pt) (hy : c (p + 1) = { i := .sn, c := .off }) :
    p = a := by
  obtain ⟨m, hm, hreg, hblk⟩ := hI.1
  have hpr : p < r - m := by
    apply Classical.byContradiction
    intro h
    have := hblk p (by omega) (by omega)
    rw [this] at hpt
    simp at hpt
  have hpr1 : r - m ≤ p + 1 := by
    apply Classical.byContradiction
    intro h
    have := (hreg (p + 1) (by omega)).2
    rw [hy] at this
    simp at this
  have hall : ∀ j, p ≤ j → j < r → puNonE (c j).i = true := by
    intro j h1 h2
    by_cases hjp : j = p
    · subst hjp; rw [hpt]; rfl
    · rw [hblk j (by omega) h2]; rfl
  have hget := ordLab_get_all (fun j => puNonE (c j).i) (fun j => tailBit (c j)) p r hall p
    (Nat.le_refl _) (by omega)
  have hgetT : (tl r c)[r - 1 - p]? = some true := by
    unfold tl
    rw [hget]
    simp [tailBit, hpt]
  rw [hI.2] at hgetT
  unfold pat at hgetT
  rw [List.getElem?_map] at hgetT
  rcases hq : (List.range (fcnt r c))[r - 1 - p]? with _ | i
  · rw [hq] at hgetT; simp at hgetT
  · rw [hq] at hgetT
    simp only [Option.map_some] at hgetT
    have hi := Option.some.inj hgetT
    have hiv : i = r - 1 - p := by
      have := List.getElem?_eq_some_iff.1 hq
      obtain ⟨_, hh⟩ := this
      simpa using hh.symm
    subst hiv
    have hmod : (a + (r - 1 - p)) % r = r - 1 := by simpa using hi
    by_cases hlt : a + (r - 1 - p) < r
    · rw [Nat.mod_eq_of_lt hlt] at hmod
      omega
    · have h1 : (a + (r - 1 - p)) % r = a + (r - 1 - p) - r := by
        have : a + (r - 1 - p) = (a + (r - 1 - p) - r) + r := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
      omega

end MarkedCells
end L3

#print axioms L3.MarkedCells.exit_pos_a
#print axioms L3.MarkedCells.fill_border_full
#print axioms L3.MarkedCells.fill_pt_term
