import Leader.L3.Width.DigitQuietStepGlue

/-!
# The quiet class after one letter: the three region clauses

The leading segment, the first segment and the final fragment of `WidthDigitQuiet` are closed under
a letter.  The view of a site after the letter is the left or right result of `laneRow` of the old
views, or the old view (`regionB_view_after`).  A region cell never holds a packet, a carry (but
the inert one at the last site) or a tail, so the new in-slot, carry and out-slot of a region cell
do not depend on a neighbour that may be arbitrary (the next delimiter or the last cell of the
previous block).

Consumer: `QuietStepLaw` (WidthDigitQuiet), the `leading`, `firstSegment` and `fragment` fields.
-/

namespace L3.DigitQuiet

open L3
open L3.AcceptedReceipts

set_option autoImplicit false

variable {c : Compiled} {n : Nat}

/-- The right neighbour map is injective.  Consumer: `regionB_view_after`. -/
theorem regionB_rightNeighbor_inj (ring : DirectedRing n) (a b : Fin n)
    (h : ring.rightNeighbor a = ring.rightNeighbor b) : a = b := by
  apply Fin.ext
  have h1 := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at h1
  have ha := a.isLt
  have hb := b.isLt
  rcases Nat.lt_or_ge (a.val + 1) n with h2 | h2 <;>
  rcases Nat.lt_or_ge (b.val + 1) n with h3 | h3
  · rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3] at h1; omega
  · have h4 : b.val + 1 = n := by omega
    rw [Nat.mod_eq_of_lt h2, h4, Nat.mod_self] at h1; omega
  · have h4 : a.val + 1 = n := by omega
    rw [h4, Nat.mod_self, Nat.mod_eq_of_lt h3] at h1; omega
  · have h4 : a.val + 1 = n := by omega
    have h5 : b.val + 1 = n := by omega
    omega

/-- The site at position `k` with `0 < k < n` is not the root.  Consumer: `regionB_leader_pos`. -/
theorem regionB_site_ne_root (ring : DirectedRing n) (root : Fin n) (k : Nat) (h0 : 0 < k)
    (hk : k < n) : digitSite ring root k ≠ root := by
  intro h
  have hv := congrArg Fin.val h
  rw [L3.RenewalReferenceClock.bankRepairDigitSiteVal] at hv
  have hr := root.isLt
  by_cases hlt : root.val + k < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hv
    omega

/-- The site at position `n` is the root.  Consumer: `regionB_leader_n`. -/
theorem regionB_site_n (ring : DirectedRing n) (root : Fin n) : digitSite ring root n = root := by
  apply Fin.ext
  rw [L3.RenewalReferenceClock.bankRepairDigitSiteVal, Nat.add_comm, Nat.add_mod_left,
    Nat.mod_eq_of_lt root.isLt]

/-- The leader flag of a lane view is the leader flag of the record.  Consumer: the region
lemmas. -/
theorem regionB_view_leader (ring : DirectedRing n) (root : Fin n) (S : Fin n → ProjD c)
    (lane : DigitLane) (k : Nat) :
    (view ring root S lane k).leader = (S (digitSite ring root k)).word.native.l := by
  cases lane <;> rfl

/-- The marker of a lane view is the beta of the record.  Consumer: the region lemmas. -/
theorem regionB_view_marker (ring : DirectedRing n) (root : Fin n) (S : Fin n → ProjD c)
    (lane : DigitLane) (k : Nat) :
    (view ring root S lane k).marker = (S (digitSite ring root k)).word.beta := by
  cases lane <;> rfl

/-- The sites strictly between the root and its return are not leaders.  Consumer: the region
lemmas. -/
theorem regionB_leader_pos {first : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjD c) (hQ : WidthDigitQuiet ring root first S) (lane : DigitLane) (k : Nat)
    (h0 : 0 < k) (hk : k < n) : (view ring root S lane k).leader = false := by
  rw [regionB_view_leader]
  cases hl : (S (digitSite ring root k)).word.native.l
  · rfl
  · exact absurd ((hQ.rootFixed _).mp hl) (regionB_site_ne_root ring root k h0 hk)

/-- Position `0` is the leader.  Consumer: the region lemmas. -/
theorem regionB_leader_zero {first : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjD c) (hQ : WidthDigitQuiet ring root first S) (lane : DigitLane) :
    (view ring root S lane 0).leader = true := by
  rw [regionB_view_leader]
  exact (hQ.rootFixed _).mpr rfl

/-- Position `n` is the leader.  Consumer: the region lemmas. -/
theorem regionB_leader_n {first : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjD c) (hQ : WidthDigitQuiet ring root first S) (lane : DigitLane) :
    (view ring root S lane n).leader = true := by
  rw [regionB_view_leader, regionB_site_n]
  exact (hQ.rootFixed _).mpr rfl

/-- The marker of the view at `0 < k < n`.  Consumer: the region lemmas. -/
theorem regionB_marker {first : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjD c) (hQ : WidthDigitQuiet ring root first S) (lane : DigitLane) (k : Nat)
    (h0 : 0 < k) (hk : k < n) :
    (view ring root S lane k).marker = true ↔ first ≤ k ∧ (k - first) % digitSpan c = 0 := by
  rw [regionB_view_marker]
  exact (hQ.layout.2.2 k h0 hk)

/-- **The view after a letter at position `j ≥ 1`**: it is the left or right result of `laneRow`
of the old views, or the old view.  Consumer: the three region closures. -/
theorem regionB_view_after (ring : DirectedRing n) (root : Fin n) (S : Fin n → ProjD c)
    (hW : QWord ring (wordProjection S)) (e : Fin n) (hne : ring.rightNeighbor e ≠ e)
    (lane : DigitLane) (j : Nat) (hj : 1 ≤ j) :
    (digitSite ring root j = e ∧
      LaneFieldsEq (view ring root (phiD ring S e) lane j)
        (laneRow lane (view ring root S lane j) (view ring root S lane (j + 1))).1) ∨
    (digitSite ring root (j - 1) = e ∧
      LaneFieldsEq (view ring root (phiD ring S e) lane j)
        (laneRow lane (view ring root S lane (j - 1)) (view ring root S lane j)).2) ∨
    view ring root (phiD ring S e) lane j = view ring root S lane j := by
  by_cases h1 : digitSite ring root j = e
  · left
    refine ⟨h1, ?_⟩
    subst h1
    exact (glue_left ring S hW _ hne lane).1
  · by_cases h2 : digitSite ring root j = ring.rightNeighbor e
    · right
      left
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have h3 : digitSite ring root i = e :=
        regionB_rightNeighbor_inj ring _ _ h2
      refine ⟨by simpa using h3, ?_⟩
      subst h3
      exact (glue_right ring S hW _ hne lane).1
    · right
      right
      exact glue_other ring S e _ h1 h2 lane


/-- Row lemma.  Consumer: `regionB_leading`, `regionB_firstSegment`, `regionB_fragment`. -/
theorem regionB_row_leader (lane : DigitLane) (vx vy : DigitLaneView c)
    (h : (vx.leader || vy.leader) = true) :
    (laneRow lane vx vy).1.out = .E ∧ (laneRow lane vx vy).1.input = .E ∧
      (laneRow lane vx vy).1.carryLive = false ∧
    (laneRow lane vx vy).2.out = .E ∧ (laneRow lane vx vy).2.input = .E ∧
      (laneRow lane vx vy).2.carryLive = false := by
  simp [laneRow, rowIn, rowOut, rowCarry, h]

/-- Row lemma left.  Consumer: `regionB_leading`, `regionB_firstSegment`, `regionB_fragment`. -/
theorem regionB_left (lane : DigitLane) (vx vy : DigitLaneView c) (hl : vx.leader = false)
    (hc : vx.carryLive = false)
    (hi : vx.input = .E ∨ (vx.marker = false ∧ ∃ v, vx.input = .S v false)) :
    (laneRow lane vx vy).1.carryLive = false ∧
    ((laneRow lane vx vy).1.input = .E ∨ ∃ v, (laneRow lane vx vy).1.input = .S v false) ∧
    (vx.input = .E → (laneRow lane vx vy).1.input = .E) ∧
    (vx.out = .E → vx.marker = false → (laneRow lane vx vy).1.out = .E) := by
  rcases vx with ⟨xl, xm, xd, xo, xi, xc, xb, xe⟩
  rcases vy with ⟨yl, ym, yd, yo, yi, yc, yb, ye⟩
  dsimp only at hl hc hi
  subst hl hc
  rcases hi with h | ⟨hm, v, h⟩
  · subst h
    cases yl <;> cases ym <;> cases yc <;> cases yi <;> cases xm <;> cases xo <;>
      simp [laneRow, rowIn, rowOut, rowCarry, rowSucc, rowLaunch, InTok.isS, InTok.isE,
        InTok.isX, InTok.isP, OutTok.isD, OutTok.isU, OutTok.isE]
  · subst h hm
    cases yl <;> cases ym <;> cases yc <;> cases yi <;> cases xo <;>
      simp [laneRow, rowIn, rowOut, rowCarry, rowSucc, rowLaunch, InTok.isS, InTok.isE,
        InTok.isX, InTok.isP, OutTok.isD, OutTok.isU, OutTok.isE, inT]


/-- Row lemma right.  Consumer: `regionB_leading`, `regionB_firstSegment`, `regionB_fragment`. -/
theorem regionB_right (lane : DigitLane) (vx vy : DigitLaneView c) (hl : vx.leader = false)
    (hl' : vy.leader = false) (hc : vx.carryLive = false)
    (hi : vx.input = .E ∨ ∃ v, vx.input = .S v false)
    (hm : vy.marker = false ∨ vx.out.isD = false) :
    (laneRow lane vx vy).2.carryLive = vy.carryLive ∧
    (vy.carryLive = false → (laneRow lane vx vy).2.input = vy.input) ∧
    (vx.out = .E → (laneRow lane vx vy).2.out = vy.out) := by
  rcases vx with ⟨xl, xm, xd, xo, xi, xc, xb, xe⟩
  rcases vy with ⟨yl, ym, yd, yo, yi, yc, yb, ye⟩
  dsimp only at hl hl' hc hi hm
  subst hl hl' hc
  rcases hi with h | ⟨v, h⟩
  · subst h
    cases ym <;> cases yc <;> cases yi <;> cases xm <;> cases xo <;>
      simp_all [laneRow, rowIn, rowOut, rowCarry, rowSucc, rowLaunch, InTok.isS, InTok.isE,
        InTok.isX, InTok.isP, OutTok.isD, OutTok.isU, OutTok.isE]
  · subst h
    cases ym <;> cases yc <;> cases yi <;> cases xm <;> cases xo <;>
      simp_all [laneRow, rowIn, rowOut, rowCarry, rowSucc, rowLaunch, InTok.isS, InTok.isE,
        InTok.isX, InTok.isP, OutTok.isD, OutTok.isU, OutTok.isE, inT]

/-- Row lemma: a new left settled input comes from an old settled input without live carry or
from an old settled input of the right neighbour.  Consumer: `regionB_leading`, `regionB_firstSegment`, `regionB_fragment`. -/
theorem regionB_frag_x (lane : DigitLane) (vx vy : DigitLaneView c)
    (hlead : (vx.leader || vy.leader) = false) (hm : vy.marker = false) (v : Fin c.topA)
    (t : Bool) (h : (laneRow lane vx vy).1.input = .S v t) :
    (vx.input = .S v t ∧ vx.carryLive = false) ∨
      ∃ w u, vy.input = .S w u ∧ vy.carryLive = false := by
  rcases vx with ⟨xl, xm, xd, xo, xi, xc, xb, xe⟩
  rcases vy with ⟨yl, ym, yd, yo, yi, yc, yb, ye⟩
  dsimp only at hlead hm
  simp only [Bool.or_eq_false_iff] at hlead
  obtain ⟨hl, hl'⟩ := hlead
  subst hl hl' hm
  cases xm <;> cases yc <;> cases xc <;> cases xo <;> cases xi <;> cases yi <;>
    simp_all [laneRow, rowIn, rowSucc, rowLaunch, InTok.isS, InTok.isE, InTok.isX, InTok.isP,
      OutTok.isD, inT, inV] <;> (try split at h) <;> simp_all

/-- Row lemma: a new right settled input is an old settled input without live carry.
Consumer: `regionB_leading`, `regionB_firstSegment`, `regionB_fragment`. -/
theorem regionB_frag_y (lane : DigitLane) (vx vy : DigitLaneView c)
    (hlead : (vx.leader || vy.leader) = false) (v : Fin c.topA)
    (t : Bool) (h : (laneRow lane vx vy).2.input = .S v t) :
    vy.input = .S v t ∧ vy.carryLive = false := by
  rcases vx with ⟨xl, xm, xd, xo, xi, xc, xb, xe⟩
  rcases vy with ⟨yl, ym, yd, yo, yi, yc, yb, ye⟩
  dsimp only at hlead
  simp only [Bool.or_eq_false_iff] at hlead
  obtain ⟨hl, hl'⟩ := hlead
  subst hl hl'
  cases xm <;> cases ym <;> cases yc <;> cases xc <;> cases xo <;> cases xi <;> cases yi <;>
    simp_all [laneRow, rowIn, rowSucc, rowLaunch, InTok.isS, InTok.isE, InTok.isX, InTok.isP,
      OutTok.isD, inT, inV] <;> (try split at h) <;> simp_all

/-- Inside the leading segment the marker is off.  Consumer: `regionB_leading`. -/
theorem regionB_marker_lt {first : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjD c) (hQ : WidthDigitQuiet ring root first S) (lane : DigitLane) (k : Nat)
    (h0 : 0 < k) (hk : k < n) (hkf : k < first) : (view ring root S lane k).marker = false := by
  cases hm : (view ring root S lane k).marker
  · rfl
  · have := ((regionB_marker ring root S hQ lane k h0 hk).mp hm).1
    omega

/-- Inside the first segment, off the first delimiter, the marker is off.  Consumer:
`regionB_firstSegment`. -/
theorem regionB_marker_first {first : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjD c) (hQ : WidthDigitQuiet ring root first S) (lane : DigitLane) (k : Nat)
    (hk : k < n) (hfk : first < k) (hkR : k < first + digitSpan c) :
    (view ring root S lane k).marker = false := by
  cases hm : (view ring root S lane k).marker
  · rfl
  · have := ((regionB_marker ring root S hQ lane k (by omega) hk).mp hm).2
    rw [Nat.mod_eq_of_lt (by omega)] at this
    omega

/-- In the fragment after the last delimiter the marker is off.  Consumer: `regionB_fragment`. -/
theorem regionB_marker_frag {first : Nat} (hR : 0 < digitSpan c) (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → ProjD c) (hQ : WidthDigitQuiet ring root first S)
    (lane : DigitLane) (k : Nat) (hk : k < n) (hLk : lastDelimiter first (digitSpan c) n < k) :
    (view ring root S lane k).marker = false := by
  cases hm : (view ring root S lane k).marker
  · rfl
  · obtain ⟨hfk, hmod⟩ := (regionB_marker ring root S hQ lane k (by unfold lastDelimiter at hLk; omega) hk).mp hm
    unfold lastDelimiter at hLk
    obtain ⟨m, hm'⟩ : digitSpan c ∣ k - first := Nat.dvd_of_mod_eq_zero hmod
    have hdm := Nat.div_add_mod (n - 1 - first) (digitSpan c)
    have hlt := Nat.mod_lt (n - 1 - first) hR
    have h1 : digitSpan c * ((n - 1 - first) / digitSpan c) < digitSpan c * m := by omega
    have h2 : (n - 1 - first) / digitSpan c < m := Nat.lt_of_mul_lt_mul_left h1
    have h3 : digitSpan c * ((n - 1 - first) / digitSpan c + 1) ≤ digitSpan c * m :=
      Nat.mul_le_mul_left _ h2
    rw [Nat.mul_add, Nat.mul_one] at h3
    omega

/-- **The leading segment after a letter.**  Consumer: `quiet_leading_step`. -/
theorem regionB_leading (hn : 2 ≤ n) {first : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjD c) (hQ : WidthDigitQuiet ring root first S)
    (hW : QWord ring (wordProjection S)) (e : Fin n) :
    ∀ (lane : DigitLane) (k : Nat), 0 < k → k < first →
      (view ring root (phiD ring S e) lane k).out = .E ∧
      DigitLeadingInput (view ring root (phiD ring S e) lane k).input ∧
      (view ring root (phiD ring S e) lane k).carryLive = false := by
  intro lane k hk0 hkf
  have hne := rightNeighbor_ne ring hn e
  have hfn : first < n := hQ.layout.2.1
  have hkn : k < n := by omega
  rcases regionB_view_after ring root S hW e hne lane k hk0 with ⟨-, hf⟩ | ⟨-, hf⟩ | hv
  · obtain ⟨hout, hin, hlive⟩ := hQ.leading lane k hk0 hkf
    have hlead := regionB_leader_pos ring root S hQ lane k hk0 hkn
    have hmark := regionB_marker_lt ring root S hQ lane k hk0 hkn hkf
    have hi : (view ring root S lane k).input = .E ∨
        ((view ring root S lane k).marker = false ∧
          ∃ v, (view ring root S lane k).input = .S v false) := by
      rcases hin with h | ⟨v, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨hmark, v, h⟩
    obtain ⟨r1, r2, r3, r4⟩ := regionB_left lane (view ring root S lane k)
      (view ring root S lane (k + 1)) hlead hlive hi
    obtain ⟨f1, f2, f3, -, -⟩ := hf
    exact ⟨f1.trans (r4 hout hmark), by rw [f2]; exact r2, f3.trans r1⟩
  · by_cases hk1 : k - 1 = 0
    · have hx : (view ring root S lane (k - 1)).leader = true := by
        rw [hk1]; exact regionB_leader_zero ring root S hQ lane
      have hxy : ((view ring root S lane (k - 1)).leader || (view ring root S lane k).leader) =
          true := by simp [hx]
      obtain ⟨-, -, -, r1, r2, r3⟩ := regionB_row_leader lane _ _ hxy
      obtain ⟨f1, f2, f3, -, -⟩ := hf
      exact ⟨f1.trans r1, by rw [f2, r2]; exact Or.inl rfl, f3.trans r3⟩
    · obtain ⟨hxo, hxi, hxc⟩ := hQ.leading lane (k - 1) (by omega) (by omega)
      obtain ⟨hyo, hyi, hyc⟩ := hQ.leading lane k hk0 hkf
      have hxl := regionB_leader_pos ring root S hQ lane (k - 1) (by omega) (by omega)
      have hyl := regionB_leader_pos ring root S hQ lane k hk0 hkn
      obtain ⟨r1, r2, r3⟩ := regionB_right lane (view ring root S lane (k - 1))
        (view ring root S lane k) hxl hyl hxc hxi (Or.inr (by rw [hxo]; rfl))
      obtain ⟨f1, f2, f3, -, -⟩ := hf
      exact ⟨f1.trans ((r3 hxo).trans hyo), by rw [f2, r2 hyc]; exact hyi,
        f3.trans (r1.trans hyc)⟩
  · rw [hv]
    exact hQ.leading lane k hk0 hkf

/-- **The first segment after a letter.**  Consumer: `quiet_firstSegment_step`. -/
theorem regionB_firstSegment (hn : 2 ≤ n) {first : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjD c) (hQ : WidthDigitQuiet ring root first S)
    (hW : QWord ring (wordProjection S)) (e : Fin n) :
    ∀ (lane : DigitLane) (k : Nat), first ≤ k → k < first + digitSpan c → k < n →
      (k + 1 = n ∧ (view ring root (phiD ring S e) lane k).carryLive = true) ∨
        ((view ring root (phiD ring S e) lane k).carryLive = false ∧
          (if k = first then (view ring root (phiD ring S e) lane k).input = .E
            else DigitLeadingInput (view ring root (phiD ring S e) lane k).input)) := by
  intro lane k hfk hkR hkn
  have hne := rightNeighbor_ne ring hn e
  have hf2 : 2 ≤ first := hQ.layout.1
  have hk0 : 0 < k := by omega
  rcases regionB_view_after ring root S hW e hne lane k hk0 with ⟨-, hf⟩ | ⟨-, hf⟩ | hv
  · rcases hQ.firstSegment lane k hfk hkR hkn with ⟨hk1, hlive⟩ | ⟨hlive, hin⟩
    · have hy : (view ring root S lane (k + 1)).leader = true := by
        rw [hk1]; exact regionB_leader_n ring root S hQ lane
      have hxy : ((view ring root S lane k).leader || (view ring root S lane (k + 1)).leader) =
          true := by simp [hy]
      obtain ⟨-, r2, r3, -, -, -⟩ := regionB_row_leader lane _ _ hxy
      obtain ⟨-, f2, f3, -, -⟩ := hf
      refine Or.inr ⟨f3.trans r3, ?_⟩
      have h : (view ring root (phiD ring S e) lane k).input = .E := f2.trans r2
      by_cases hkf : k = first
      · rw [if_pos hkf]; exact h
      · rw [if_neg hkf, h]; exact Or.inl rfl
    · have hlead := regionB_leader_pos ring root S hQ lane k hk0 hkn
      have hi : (view ring root S lane k).input = .E ∨
          ((view ring root S lane k).marker = false ∧
            ∃ v, (view ring root S lane k).input = .S v false) := by
        by_cases hkf : k = first
        · rw [if_pos hkf] at hin
          exact Or.inl hin
        · rw [if_neg hkf] at hin
          have hmk := regionB_marker_first ring root S hQ lane k hkn (by omega) hkR
          rcases hin with h | ⟨v, h⟩
          · exact Or.inl h
          · exact Or.inr ⟨hmk, v, h⟩
      obtain ⟨r1, r2, r3, -⟩ := regionB_left lane (view ring root S lane k)
        (view ring root S lane (k + 1)) hlead hlive hi
      obtain ⟨-, f2, f3, -, -⟩ := hf
      refine Or.inr ⟨f3.trans r1, ?_⟩
      by_cases hkf : k = first
      · rw [if_pos hkf] at hin ⊢
        rw [f2]
        exact r3 hin
      · rw [if_neg hkf]
        rw [f2]
        exact r2
  · have hxl := regionB_leader_pos ring root S hQ lane (k - 1) (by omega) (by omega)
    have hyl := regionB_leader_pos ring root S hQ lane k hk0 hkn
    have hx : (view ring root S lane (k - 1)).carryLive = false ∧
        ((view ring root S lane (k - 1)).input = .E ∨
          ∃ v, (view ring root S lane (k - 1)).input = .S v false) ∧
        ((view ring root S lane k).marker = false ∨
          (view ring root S lane (k - 1)).out.isD = false) := by
      by_cases hkf : k = first
      · obtain ⟨hxo, hxi, hxc⟩ := hQ.leading lane (k - 1) (by omega) (by omega)
        exact ⟨hxc, hxi, Or.inr (by rw [hxo]; rfl)⟩
      · have hmk := regionB_marker_first ring root S hQ lane k hkn (by omega) hkR
        rcases hQ.firstSegment lane (k - 1) (by omega) (by omega) (by omega) with
          ⟨h1, -⟩ | ⟨hxc, hxi⟩
        · omega
        · by_cases hk2 : k - 1 = first
          · rw [if_pos hk2] at hxi
            exact ⟨hxc, Or.inl hxi, Or.inl hmk⟩
          · rw [if_neg hk2] at hxi
            exact ⟨hxc, hxi, Or.inl hmk⟩
    obtain ⟨hxc, hxi, hxm⟩ := hx
    obtain ⟨r1, r2, -⟩ := regionB_right lane (view ring root S lane (k - 1))
      (view ring root S lane k) hxl hyl hxc hxi hxm
    obtain ⟨-, f2, f3, -, -⟩ := hf
    rcases hQ.firstSegment lane k hfk hkR hkn with ⟨hk1, hlive⟩ | ⟨hlive, hin⟩
    · exact Or.inl ⟨hk1, f3.trans (r1.trans hlive)⟩
    · refine Or.inr ⟨f3.trans (r1.trans hlive), ?_⟩
      rw [f2, r2 hlive]
      exact hin
  · rw [hv]
    exact hQ.firstSegment lane k hfk hkR hkn

/-- **The final fragment after a letter.**  Consumer: `quiet_fragment_step`. -/
theorem regionB_fragment (hn : 2 ≤ n) (hR : 0 < digitSpan c) {first : Nat} (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → ProjD c) (hQ : WidthDigitQuiet ring root first S)
    (hW : QWord ring (wordProjection S)) (e : Fin n) :
    first + digitSpan c < n →
      ∀ (lane : DigitLane) (k : Nat), lastDelimiter first (digitSpan c) n ≤ k → k < n →
        ∀ (val : Fin c.topA) (tail : Bool),
          (view ring root (phiD ring S e) lane k).input ≠ .S val tail ∨
            (k + 1 = n ∧ (view ring root (phiD ring S e) lane k).carryLive = true) := by
  intro hfr lane k hLk hkn val tail
  have hne := rightNeighbor_ne ring hn e
  have hf2 : 2 ≤ first := hQ.layout.1
  have hk0 : 0 < k := by unfold lastDelimiter at hLk; omega
  rcases regionB_view_after ring root S hW e hne lane k hk0 with ⟨-, hf⟩ | ⟨-, hf⟩ | hv
  · left
    intro hS
    obtain ⟨-, f2, -, -, -⟩ := hf
    rw [f2] at hS
    by_cases hlead : ((view ring root S lane k).leader ||
        (view ring root S lane (k + 1)).leader) = true
    · obtain ⟨-, r2, -, -, -, -⟩ := regionB_row_leader lane _ _ hlead
      rw [r2] at hS
      cases hS
    · have hlead' : ((view ring root S lane k).leader ||
          (view ring root S lane (k + 1)).leader) = false := by simpa using hlead
      have hk1 : k + 1 < n := by
        rcases Nat.lt_or_ge (k + 1) n with h | h
        · exact h
        · exfalso
          have hkk : k + 1 = n := by omega
          have hy : (view ring root S lane (k + 1)).leader = true := by
            rw [hkk]; exact regionB_leader_n ring root S hQ lane
          rw [hy] at hlead'
          simp at hlead'
      have hm := regionB_marker_frag hR ring root S hQ lane (k + 1) hk1 (by omega)
      rcases regionB_frag_x lane _ _ hlead' hm val tail hS with ⟨h1, h2⟩ | ⟨w, u, h1, h2⟩
      · rcases hQ.fragment hfr lane k hLk hkn val tail with h | ⟨-, h⟩
        · exact h h1
        · rw [h2] at h
          exact absurd h (by decide)
      · rcases hQ.fragment hfr lane (k + 1) (by omega) hk1 w u with h | ⟨-, h⟩
        · exact h h1
        · rw [h2] at h
          exact absurd h (by decide)
  · left
    intro hS
    obtain ⟨-, f2, -, -, -⟩ := hf
    rw [f2] at hS
    by_cases hlead : ((view ring root S lane (k - 1)).leader ||
        (view ring root S lane k).leader) = true
    · obtain ⟨-, -, -, -, r2, -⟩ := regionB_row_leader lane _ _ hlead
      rw [r2] at hS
      cases hS
    · have hlead' : ((view ring root S lane (k - 1)).leader ||
          (view ring root S lane k).leader) = false := by simpa using hlead
      obtain ⟨h1, h2⟩ := regionB_frag_y lane _ _ hlead' val tail hS
      rcases hQ.fragment hfr lane k hLk hkn val tail with h | ⟨-, h⟩
      · exact h h1
      · rw [h2] at h
        exact absurd h (by decide)
  · rw [hv]
    exact hQ.fragment hfr lane k hLk hkn val tail

/-- The block span of the compiled width is at least two.  Consumer: `quiet_fragment_step`. -/
theorem regionB_span_ge_two (hn : 5 ≤ n) : 2 ≤ digitSpan (compileAdvice (ceilLogTwo n)) := by
  have ht := compileAdvice_t_ge_two (ceilLogTwo n) (ringQ_facts n hn).1
  unfold digitSpan
  have h4 : 2 ^ 2 ≤ 2 ^ (compileAdvice (ceilLogTwo n)).t := Nat.pow_le_pow_right (by omega) ht
  omega

/-- **The leading clause of the quiet class is closed under a letter.**  Consumer:
`QuietStepLaw` (WidthDigitQuiet), field `leading`. -/
theorem quiet_leading_step {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n) (root : Fin n)
    (first : Nat) (S : Fin n → ProjD (compileAdvice (ceilLogTwo n)))
    (hQ : WidthDigitQuiet ring root first S) (hF : WFixedRoot ring root (wordProjection S))
    (hW : QWord ring (wordProjection S)) (e : Fin n) :
    ∀ (lane : DigitLane) (k : Nat), 0 < k → k < first →
      (view ring root (phiD ring S e) lane k).out = .E ∧
      DigitLeadingInput (view ring root (phiD ring S e) lane k).input ∧
      (view ring root (phiD ring S e) lane k).carryLive = false :=
  regionB_leading (by omega) ring root S hQ hW e

/-- **The first-segment clause of the quiet class is closed under a letter.**  Consumer:
`QuietStepLaw` (WidthDigitQuiet), field `firstSegment`. -/
theorem quiet_firstSegment_step {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n) (root : Fin n)
    (first : Nat) (S : Fin n → ProjD (compileAdvice (ceilLogTwo n)))
    (hQ : WidthDigitQuiet ring root first S) (hF : WFixedRoot ring root (wordProjection S))
    (hW : QWord ring (wordProjection S)) (e : Fin n) :
    ∀ (lane : DigitLane) (k : Nat), first ≤ k → k < first + digitSpan (compileAdvice (ceilLogTwo n)) →
      k < n →
      (k + 1 = n ∧ (view ring root (phiD ring S e) lane k).carryLive = true) ∨
        ((view ring root (phiD ring S e) lane k).carryLive = false ∧
          (if k = first then (view ring root (phiD ring S e) lane k).input = .E
            else DigitLeadingInput (view ring root (phiD ring S e) lane k).input)) :=
  regionB_firstSegment (by omega) ring root S hQ hW e

/-- **The fragment clause of the quiet class is closed under a letter.**  Consumer:
`QuietStepLaw` (WidthDigitQuiet), field `fragment`. -/
theorem quiet_fragment_step {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n) (root : Fin n)
    (first : Nat) (S : Fin n → ProjD (compileAdvice (ceilLogTwo n)))
    (hQ : WidthDigitQuiet ring root first S) (hF : WFixedRoot ring root (wordProjection S))
    (hW : QWord ring (wordProjection S)) (e : Fin n) :
    first + digitSpan (compileAdvice (ceilLogTwo n)) < n →
      ∀ (lane : DigitLane) (k : Nat),
        lastDelimiter first (digitSpan (compileAdvice (ceilLogTwo n))) n ≤ k → k < n →
        ∀ (val : Fin (compileAdvice (ceilLogTwo n)).topA) (tail : Bool),
          (view ring root (phiD ring S e) lane k).input ≠ .S val tail ∨
            (k + 1 = n ∧ (view ring root (phiD ring S e) lane k).carryLive = true) :=
  regionB_fragment (by omega) (by have := regionB_span_ge_two hn; omega) ring root S hQ hW e

end L3.DigitQuiet

#print axioms L3.DigitQuiet.quiet_leading_step
#print axioms L3.DigitQuiet.quiet_firstSegment_step
#print axioms L3.DigitQuiet.quiet_fragment_step
