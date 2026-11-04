import Leader.L3.Top.PinnedEnv

/-!
# Q7 (P.8--P.10): the measure along the shapes of one window edge

Consumer: `Leader/L3/TopPinnedEdge.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The live carry consumes: its right neighbour is settled.

Consumer: `Gv_cons`. -/
def ConsAt (r : Nat) (cells : Nat → Cell) : Prop :=
  hpOf r cells < r ∧ hpOf r cells + 1 < r ∧ (cells (hpOf r cells + 1)).i.isS = true

/-- The measure while the carry consumes.

Consumer: `Leader/L3/TopPinnedEdge.lean`. -/
theorem Gv_cons (r : Nat) (cells : Nat → Cell) (h : ConsAt r cells) :
    Gv r cells = r - hpOf r cells := by
  unfold Gv
  rw [if_pos h.1, if_pos ⟨h.2.1, h.2.2⟩]

/-- The measure with a live carry that does not consume.

Consumer: `Leader/L3/TopPinnedEdge.lean`. -/
theorem Gv_host (r : Nat) (cells : Nat → Cell) (h1 : hpOf r cells < r) (h2 : ¬ ConsAt r cells) :
    Gv r cells = 1 + FT r cells := by
  unfold Gv
  rw [if_pos h1]
  have : ¬ (hpOf r cells + 1 < r ∧ (cells (hpOf r cells + 1)).i.isS = true) :=
    fun hh => h2 ⟨h1, hh.1, hh.2⟩
  rw [if_neg this]

/-- The measure without a live carry.

Consumer: `Leader/L3/TopPinnedEdge.lean`. -/
theorem Gv_free (r : Nat) (cells : Nat → Cell) (h1 : ¬ hpOf r cells < r) :
    Gv r cells = FT r cells := by
  unfold Gv
  rw [if_neg h1]

/-- Settled and pending inputs are disjoint.

Consumer: `Leader/L3/TopPinnedEdge.lean`. -/
theorem isP_not_isS {i : Inp} (h : i.isP = true) : i.isS = false := by
  cases i <;> simp_all [Inp.isP, Inp.isS]

/-- The fill work after a pending packet moves into the next empty site.

Consumer: `gv_move`. -/
theorem FT_move (r p : Nat) (cells cells' : Nat → Cell)
    (hout : ∀ k, k ≠ p → k ≠ p + 1 → cells' k = cells k)
    (hP0 : (cells p).i.isP = true) (hP1 : (cells (p + 1)).i.isP = false)
    (hP0' : (cells' p).i.isP = false) (hP1' : (cells' (p + 1)).i.isP = true)
    (hfs : p + 2 ≤ fsOf r cells) (hS : fsOf r cells' = fsOf r cells)
    (hfr : fsOf r cells < r) : FT r cells' + 1 = FT r cells := by
  unfold FT
  rw [hS, if_pos hfr, if_pos hfr]
  have := wsum_edit (fillW r cells) (fillW r cells') p (by
    intro k h1 h2
    unfold fillW
    rw [hout k h1 h2]) (fsOf r cells) hfs
  have e1 : fillW r cells p = 1 := by unfold fillW; rw [if_pos hP0]
  have e2 : fillW r cells (p + 1) = p + 1 + r + 3 := by
    unfold fillW; rw [if_neg (by simp [hP1])]
  have e3 : fillW r cells' p = p + r + 3 := by
    unfold fillW; rw [if_neg (by simp [hP0'])]
  have e4 : fillW r cells' (p + 1) = 1 := by unfold fillW; rw [if_pos hP1']
  omega

/-- **A pending packet moves into the next empty site.**  The measure does not rise, and it
falls when no live carry consumes.

Consumer: `Leader/L3/TopPinnedEdge.lean`. -/
theorem gv_move (r p : Nat) (cells : Nat → Cell) (h : FEnv r cells) (hp : p + 1 < r)
    (hx : (cells p).i.isP = true) (hxc : (cells p).c = .off)
    (hy : cells (p + 1) = { i := .e, c := .off }) :
    (ConsAt r cells → Gv r (setTwo cells p { i := .e, c := .off } { i := (cells p).i, c := .off })
        = Gv r cells) ∧
    (¬ ConsAt r cells →
      Gv r (setTwo cells p { i := .e, c := .off } { i := (cells p).i, c := .off }) + 1 =
        Gv r cells) := by
  generalize hc' : setTwo cells p { i := .e, c := .off } { i := (cells p).i, c := .off } = cells'
  have hout : ∀ k, k ≠ p → k ≠ p + 1 → cells' k = cells k := by
    intro k h1 h2; rw [← hc']; simp [setTwo, h1, h2]
  have h0 : cells' p = { i := .e, c := .off } := by rw [← hc']; simp [setTwo]
  have h1 : cells' (p + 1) = { i := (cells p).i, c := .off } := by
    rw [← hc']; simp [setTwo]
  have hnS := isP_not_isS hx
  have hob : ∀ j, j < r → ((cells j).i.isS = true ∨ (cells j).c ≠ .off) → p < j :=
    fun j hj hh => h.pend_lt (by omega) hj hx hh
  have hyS : (cells (p + 1)).i.isS = false := by rw [hy]; rfl
  have hfsl := h.fs_lt
  have hfss := h.fs_settled
  have hfs : p + 2 ≤ fsOf r cells := by
    have h1 := hob _ hfsl (Or.inl hfss)
    have h2 : fsOf r cells ≠ p + 1 := fun hh => by rw [hh] at hfss; rw [hyS] at hfss; exact absurd hfss (by simp)
    omega
  have hS : fsOf r cells' = fsOf r cells := by
    unfold fsOf
    apply firstS_congr
    intro k hk
    by_cases k1 : k = p
    · subst k1; rw [h0, hnS]; rfl
    · by_cases k2 : k = p + 1
      · subst k2; rw [h1, hyS]; exact isP_not_isS hx
      · rw [hout k k1 k2]
  have hH : hpOf r cells' = hpOf r cells := by
    unfold hpOf
    apply firstS_congr
    intro k hk
    by_cases k1 : k = p
    · subst k1; rw [h0, hxc]
    · by_cases k2 : k = p + 1
      · subst k2; rw [h1, hy]
      · rw [hout k k1 k2]
  have hFT := FT_move r p cells cells' hout hx (by rw [hy]; rfl) (by rw [h0]; rfl)
    (by rw [h1]; exact hx) hfs hS hfsl
  have hhp : hpOf r cells < r → p + 2 ≤ hpOf r cells := by
    intro hlt
    have h1' := hp_hit hlt
    have h2' := hob _ hlt (Or.inr h1')
    have h3' : hpOf r cells ≠ p + 1 := fun hh => by
      rw [hh, hy] at h1'; exact h1' rfl
    omega
  have hcons : ConsAt r cells' ↔ ConsAt r cells := by
    unfold ConsAt
    rw [hH]
    by_cases hlt : hpOf r cells < r
    · have := hhp hlt
      rw [hout (hpOf r cells + 1) (by omega) (by omega)]
    · simp [hlt]
  constructor
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

/-- Settled inputs are neither empty nor pending.

Consumer: `gv_settle`. -/
theorem isS_not_isP {i : Inp} (h : i.isS = true) : i.isP = false := by
  cases i <;> simp_all [Inp.isP, Inp.isS]

/-- **A pending packet settles before a settled site.**  The measure falls by one.

Consumer: `Leader/L3/TopPinnedEdge.lean`. -/
theorem gv_settle (r p : Nat) (cells : Nat → Cell) (h : FEnv r cells) (hp : p + 1 < r)
    (x' : Cell) (hx : (cells p).i.isP = true) (hxc : (cells p).c = .off)
    (hy : (cells (p + 1)).i.isS = true) (hyc : (cells (p + 1)).c = .off)
    (hx'S : x'.i.isS = true) (hx'c : x'.c = .off) :
    Gv r (setTwo cells p x' (cells (p + 1))) + 1 = Gv r cells := by
  generalize hc' : setTwo cells p x' (cells (p + 1)) = cells'
  have hout : ∀ k, k ≠ p → k ≠ p + 1 → cells' k = cells k := by
    intro k h1 h2; rw [← hc']; simp [setTwo, h1, h2]
  have h0 : cells' p = x' := by rw [← hc']; simp [setTwo]
  have h1 : cells' (p + 1) = cells (p + 1) := by rw [← hc']; simp [setTwo]
  have hob : ∀ j, j < r → ((cells j).i.isS = true ∨ (cells j).c ≠ .off) → p < j :=
    fun j hj hh => h.pend_lt (by omega) hj hx hh
  -- no live carry
  have hnc : ∀ k, k < r → (cells k).c = .off := by
    intro k hk
    apply Classical.byContradiction
    intro hne
    have h1' := hob k hk (Or.inr hne)
    have h2' : k ≠ p + 1 := fun hh => by rw [hh] at hne; exact hne hyc
    have h3 := h.left hk hne (i := p + 1) (by omega)
    rcases h3 with h3 | h3
    · rw [h3] at hy; exact absurd hy (by simp [Inp.isS])
    · rw [isS_not_isP hy] at h3; exact absurd h3 (by simp)
  have hnc' : ∀ k, k < r → (cells' k).c = .off := by
    intro k hk
    by_cases k1 : k = p
    · subst k1; rw [h0]; exact hx'c
    · by_cases k2 : k = p + 1
      · subst k2; rw [h1]; exact hyc
      · rw [hout k k1 k2]; exact hnc k hk
  have hHp : ¬ hpOf r cells < r := by rw [hp_none hnc]; omega
  have hHp' : ¬ hpOf r cells' < r := by rw [hp_none hnc']; omega
  -- the first settled site
  have hfs : fsOf r cells = p + 1 := by
    unfold fsOf
    apply firstS_eq _ r (p + 1) hp hy
    intro k hk
    by_cases k1 : k = p
    · subst k1; exact isP_not_isS hx
    · apply Classical.byContradiction
      intro hne
      have := hob k (by omega) (Or.inl (by simpa using hne))
      omega
  have hfs' : fsOf r cells' = p := by
    unfold fsOf
    apply firstS_eq _ r p (by omega) (by rw [h0]; exact hx'S)
    intro k hk
    rw [hout k (by omega) (by omega)]
    apply Classical.byContradiction
    intro hne
    have := hob k (by omega) (Or.inl (by simpa using hne))
    omega
  rw [Gv_free r cells' hHp', Gv_free r cells hHp]
  unfold FT
  rw [hfs, hfs', if_pos (by omega), if_pos (by omega)]
  have e1 : wsum (fillW r cells) (p + 1) = wsum (fillW r cells) p + 1 := by
    simp only [wsum]
    unfold fillW
    rw [if_pos hx]
  have e2 : wsum (fillW r cells') p = wsum (fillW r cells) p := by
    apply wsum_congr
    intro k hk
    unfold fillW
    rw [hout k (by omega) (by omega)]
  omega

/-- The fill work only reads the settled and pending inputs.

Consumer: `gv_death`. -/
theorem FT_congr_in (r : Nat) (c1 c2 : Nat → Cell)
    (h : ∀ k, k < r → (c1 k).i.isS = (c2 k).i.isS ∧ (c1 k).i.isP = (c2 k).i.isP) :
    FT r c1 = FT r c2 := by
  have hs : fsOf r c1 = fsOf r c2 := firstS_congr _ _ r (fun k hk => (h k hk).1)
  unfold FT
  rw [hs]
  by_cases hf : fsOf r c2 < r
  · rw [if_pos hf, if_pos hf]
    have := fsOf_le r c2
    rw [wsum_congr (fillW r c1) (fillW r c2) _ (fun k hk => by
      unfold fillW
      rw [(h k (by omega)).2])]
  · rw [if_neg hf, if_neg hf]

/-- **A live carry retires.**  Its host stays empty, nothing else changes, and its right
neighbour is not settled: the measure falls by one.

Consumer: `Leader/L3/TopPinnedEdge.lean`. -/
theorem gv_death (r p : Nat) (cells cells' : Nat → Cell) (h : FEnv r cells) (hp : p < r)
    (hx : cells p = { i := .e, c := .fresh }) (hx' : cells' p = { i := .e, c := .off })
    (hout : ∀ k, k ≠ p → cells' k = cells k)
    (hy : p + 1 < r → (cells (p + 1)).i.isS = false) :
    Gv r cells' + 1 = Gv r cells := by
  have hc : (cells p).c ≠ .off := by rw [hx]; simp
  have hH : hpOf r cells = p := hp_eq h hp hc
  have hnc' : ∀ k, k < r → (cells' k).c = .off := by
    intro k hk
    by_cases k1 : k = p
    · subst k1; rw [hx']
    · rw [hout k k1]
      apply Classical.byContradiction
      intro hne
      exact k1 (h.uniq hk hp hne hc)
  have hHp' : ¬ hpOf r cells' < r := by rw [hp_none hnc']; omega
  have hcons : ¬ ConsAt r cells := by
    intro hh
    obtain ⟨_, hh1, hh2⟩ := hh
    rw [hH] at hh1 hh2
    have := hy hh1
    rw [this] at hh2
    exact absurd hh2 (by simp)
  rw [Gv_free r cells' hHp', Gv_host r cells (by rw [hH]; exact hp) hcons]
  have : FT r cells' = FT r cells := by
    apply FT_congr_in
    intro k hk
    by_cases k1 : k = p
    · subst k1; rw [hx', hx]; exact ⟨rfl, rfl⟩
    · rw [hout k k1]; exact ⟨rfl, rfl⟩
  omega

/-- Membership in the settled set of a window.

Consumer: `at_lt_single`. -/
theorem actF_iff (r : Nat) (cells : Nat → Cell) (k : Nat) :
    act r cells (fun _ => False) k = true ↔ k < r ∧ (cells k).i.isS = true := by
  rw [act_iff]
  simp

/-- Removing a settled site with no settled right neighbour lowers the charge.

Consumer: `Leader/L3/TopPinnedEdge.lean`. -/
theorem at_lt_single (r q : Nat) (cells cells' : Nat → Cell) (hq : q < r)
    (hS : (cells q).i.isS = true) (hS' : (cells' q).i.isS = false)
    (hout : ∀ m, m ≠ q → m < r → (cells' m).i.isS = (cells m).i.isS)
    (hend : q + 1 < r → (cells (q + 1)).i.isS = false) :
    At r cells' < At r cells := by
  unfold At
  refine charge_cut_lt (act r cells (fun _ => False)) (act r cells' (fun _ => False)) q q
    (Nat.le_refl _) ?_ ?_ ?_ r (by omega)
  · intro m hm1 hm2
    have : m = q := by omega
    subst this
    refine ⟨(actF_iff r cells m).2 ⟨hq, hS⟩, ?_⟩
    cases h : act r cells' (fun _ => False) m
    · rfl
    · have := ((actF_iff r cells' m).1 h).2
      rw [hS'] at this; exact absurd this (by simp)
  · intro m hm
    have hmq : m ≠ q := by omega
    by_cases hmr : m < r
    · cases h1 : act r cells (fun _ => False) m
      · cases h2 : act r cells' (fun _ => False) m
        · rfl
        · have := ((actF_iff r cells' m).1 h2).2
          rw [hout m hmq hmr] at this
          have := (actF_iff r cells m).2 ⟨hmr, this⟩
          rw [h1] at this; exact absurd this (by simp)
      · have := ((actF_iff r cells m).1 h1).2
        rw [← hout m hmq hmr] at this
        exact (actF_iff r cells' m).2 ⟨hmr, this⟩
    · rw [act_bd r cells (fun _ => False) m (by omega), act_bd r cells' (fun _ => False) m (by omega)]
  · by_cases h1 : q + 1 < r
    · cases h2 : act r cells (fun _ => False) (q + 1)
      · rfl
      · have := ((actF_iff r cells (q + 1)).1 h2).2
        rw [hend h1] at this; exact absurd this (by simp)
    · exact act_bd r cells (fun _ => False) (q + 1) (by omega)

end MarkedCells
end L3
#print axioms L3.MarkedCells.Gv_cons
#print axioms L3.MarkedCells.Gv_host
#print axioms L3.MarkedCells.Gv_free
#print axioms L3.MarkedCells.isP_not_isS
#print axioms L3.MarkedCells.FT_move
#print axioms L3.MarkedCells.gv_move
#print axioms L3.MarkedCells.isS_not_isP
#print axioms L3.MarkedCells.gv_settle
#print axioms L3.MarkedCells.FT_congr_in
#print axioms L3.MarkedCells.gv_death
#print axioms L3.MarkedCells.actF_iff
#print axioms L3.MarkedCells.at_lt_single
