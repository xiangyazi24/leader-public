import Leader.L3.Top.PinnedPrepareAll

/-!
# Q7 (preparation, lemma 1): a settled tail in the window is a misplaced cut, and the pending
suffix after it is aligned

If the pending-or-settled invariant `PuLinv` and `PuAll` hold at a state whose window is
`E/P` left of a position `h`, a settled tail at `h` and settled non-tails right of `h`, then

* the registers right of `h` hold the sampled operands of consecutive exports, with the tail at
  `h` the newest: by `PureStream` the register `j > h` is the sample of site `certSite s (j - h)`
  and the tail is the sample of site `certSite s 0`: this is `topClockConcreteMisplacedAt`;
* the pending registers read right to left are the exports after the tail, and the serial that
  follows the tail is `0 mod r`: the cohort of the pending inputs is aligned.

Consumer: `Leader/L3/TopPinnedPrepareCert.lean`.
-/

namespace L3
namespace MarkedCells

open Classical

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- When all registers of `[a, m)` are flagged, the reading lists them from the right.

Consumer: `labelled_sample`. -/
theorem ordLab_get_all {α : Type} (o : Nat → Bool) (ℓ : Nat → α) (a : Nat) :
    ∀ m, (∀ j, a ≤ j → j < m → o j = true) → ∀ j, a ≤ j → j < m →
      (ordLab o ℓ m)[m - 1 - j]? = some (ℓ j) := by
  intro m
  induction m with
  | zero => intro _ j h1 h2; omega
  | succ m ih =>
    intro hall j h1 h2
    have hom : o m = true := hall m (by omega) (by omega)
    by_cases hjm : j = m
    · subst hjm
      simp [ordLab, hom]
    · have hj : j < m := by omega
      have := ih (fun i hi1 hi2 => hall i hi1 (by omega)) j h1 hj
      have hidx : m + 1 - 1 - j = (m - 1 - j) + 1 := by omega
      rw [hidx]
      simp only [ordLab, hom, if_true]
      simpa using this

/-- When all registers of `[a, m)` are flagged, the reading splits into their labels and the
reading below `a`.

Consumer: `misplaced_of_labelled`. -/
theorem ordLab_split_all {α : Type} (o : Nat → Bool) (ℓ : Nat → α) (a : Nat) :
    ∀ m, a ≤ m → (∀ j, a ≤ j → j < m → o j = true) →
      ∃ L : List α, L.length = m - a ∧ ordLab o ℓ m = L ++ ordLab o ℓ a := by
  intro m
  induction m with
  | zero => intro ha _; have : a = 0 := by omega
            subst this; exact ⟨[], rfl, rfl⟩
  | succ m ih =>
    intro ha hall
    by_cases ham : a = m + 1
    · subst ham; exact ⟨[], by simp, by simp⟩
    · have hom : o m = true := hall m (by omega) (by omega)
      obtain ⟨L, hL, hord⟩ := ih (by omega) (fun i hi1 hi2 => hall i hi1 (by omega))
      refine ⟨ℓ m :: L, by simp [hL]; omega, ?_⟩
      simp only [ordLab, hom, if_true, hord]
      simp

/-- A residue shifted by `d < r` from `r - 1`.

Consumer: `misplaced_of_labelled`. -/
theorem mod_shift (i d r : Nat) (hr : 0 < r) (hd : d < r) (h : (i + d) % r = r - 1) :
    i % r = r - 1 - d := by
  have hi := Nat.mod_add_div i r
  have ha : i % r < r := Nat.mod_lt _ hr
  have hsum : i + d = (i % r + d) + r * (i / r) := by omega
  have hmod : (i + d) % r = (i % r + d) % r := by
    rw [hsum, Nat.add_mul_mod_self_left]
  rw [hmod] at h
  by_cases hlt : i % r + d < r
  · rw [Nat.mod_eq_of_lt hlt] at h
    omega
  · have hge : r ≤ i % r + d := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at h
    omega

/-- A serial whose residue is `r - 1` is followed by a serial of residue zero.

Consumer: `misplaced_of_labelled`. -/
theorem mod_succ_zero (i r : Nat) (hr : 0 < r) (h : i % r = r - 1) : (i + 1) % r = 0 := by
  have hi := Nat.mod_add_div i r
  have : i + 1 = r * (i / r + 1) := by
    rw [Nat.mul_add, Nat.mul_one]; omega
  rw [this, Nat.mul_mod_right]

/-- The tokens of a window register of a given cell class.

Consumer: `misplaced_of_labelled`. -/
theorem qIn_of_cell {n : Nat} (s : Fin n) (Y : TopFixedTraceState n) (j : Nat) :
    ((cellOf s Y j).i = .st → ∃ v, (Y.1.1 (winSite s j)).qIn = .S v true) ∧
    ((cellOf s Y j).i = .sn → ∃ v, (Y.1.1 (winSite s j)).qIn = .S v false) ∧
    ((cellOf s Y j).i = .e → (Y.1.1 (winSite s j)).qIn = .E) ∧
    ((cellOf s Y j).i = .pt → ∃ v, (Y.1.1 (winSite s j)).qIn = .P v true) ∧
    ((cellOf s Y j).i = .pn → ∃ v, (Y.1.1 (winSite s j)).qIn = .P v false) := by
  unfold cellOf siteCell
  simp only
  rcases (Y.1.1 (winSite s j)).qIn with _ | _ | ⟨v, t⟩ | ⟨v, t⟩ <;> (try cases t) <;>
    simp [absIn]

/-- **The sample of a flagged window register.**  The reading of a window whose registers
`[h, r)` are all flagged lists the exports after the anchor from the index `k0`: the register `j`
holds the sampled operand of the export of index `k0 + (r - 1 - j)`.

Consumer: `misplaced_of_labelled`. -/
theorem labelled_sample {n : Nat} (s : Fin n) (Y : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hpure : topClockConcretePureStream s Y anchor) (k0 : Nat)
    (hlist : ordLab (paFlagSettled s Y anchor.time) (paLabSettled s Y) (topClockSpan n) =
      (paQ s Y anchor.time).drop k0)
    (h : Nat) (hflag : ∀ j, h ≤ j → j < topClockSpan n →
      paFlagSettled s Y anchor.time j = true)
    (j : Nat) (hj1 : h ≤ j) (hj2 : j < topClockSpan n) :
    ∃ sample : DigitSample (compileAdvice (ceilLogTwo n)) n,
      DigitRecordedSample Y.1.2 sample ∧ sample.id.lane = .comparison ∧
      sample.id.site = certSite s (topClockSpan n - 1 - ((k0 + (topClockSpan n - 1 - j)) %
        topClockSpan n)) ∧
      sample.tail = (if (k0 + (topClockSpan n - 1 - j)) % topClockSpan n = topClockSpan n - 1
        then true else false) ∧
      (Y.1.2.current (winSite s j)).comparison.input = some (.sampled sample.id) ∧
      puTok (Y.1.1 (winSite s j)).qIn = .P sample.value sample.tail := by
  have hget := ordLab_get_all (paFlagSettled s Y anchor.time) (paLabSettled s Y) h
    (topClockSpan n) hflag j hj1 hj2
  rw [hlist, List.getElem?_drop] at hget
  unfold paQ at hget
  rw [List.getElem?_map] at hget
  rcases hE : (topClockConcreteExportsAfter s Y anchor.time)[k0 + (topClockSpan n - 1 - j)]? with
    _ | ex
  · rw [hE] at hget; simp at hget
  · rw [hE] at hget
    simp only [Option.map_some] at hget
    have hlab := Option.some.inj hget
    obtain ⟨hi, hex⟩ := List.getElem?_eq_some_iff.1 hE
    obtain ⟨sample, hrec, hlane, hsite, htail, hop, hval, htl⟩ :=
      hpure ⟨k0 + (topClockSpan n - 1 - j), hi⟩
    have hex' : topClockConcreteExportAt s Y anchor.time ⟨k0 + (topClockSpan n - 1 - j), hi⟩ =
        ex := hex
    rw [hex'] at hop hval htl
    refine ⟨sample, hrec, hlane, hsite, htail, ?_, ?_⟩
    · have := congrArg Prod.fst hlab
      simp only [paLabSettled] at this
      rw [← this, hop]
    · have := congrArg Prod.snd hlab
      simp only [paLabSettled] at this
      rw [← this, hval, htl]

/-- **A settled tail with settled non-tails to its right is a misplaced-tail cut**, and the
pending registers read as the exports after the tail, whose first serial is `0 mod r`.

Consumer: `Leader/L3/TopPinnedPrepareCert.lean`. -/
theorem misplaced_of_labelled {n : Nat} (s : Fin n) (Y : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hpure : topClockConcretePureStream s Y anchor)
    (hinv : PuLinv s Y anchor.time) (hall : PuAllAt s Y anchor.time)
    (h : Fin (topClockSpan n)) (hh1 : 1 ≤ h.val) (hh2 : h.val + 1 < topClockSpan n)
    (hleft : ∀ j : Nat, j < h.val → (cellOf s Y j).i = .e ∨ (cellOf s Y j).i = .pt ∨
      (cellOf s Y j).i = .pn)
    (htail : (cellOf s Y h.val).i = .st)
    (hright : ∀ j : Nat, h.val < j → j < topClockSpan n → (cellOf s Y j).i = .sn) :
    topClockConcreteMisplacedAt s Y h ∧
      ∃ k0 : Nat, ordLab (paFlagSettled s Y anchor.time) (paLabSettled s Y) h.val =
          (paQ s Y anchor.time).drop (k0 + (topClockSpan n - h.val)) ∧
        (k0 + (topClockSpan n - h.val)) % topClockSpan n = 0 := by
  obtain ⟨hfree, _, k0, hk0, hlist⟩ := hinv
  have hr : 3 ≤ topClockSpan n := by omega
  have hnonE : ∀ j, h.val ≤ j → j < topClockSpan n → puNonE (cellOf s Y j).i = true := by
    intro j h1 h2
    by_cases hjh : j = h.val
    · subst hjh; rw [htail]; rfl
    · rw [hright j (by omega) h2]; rfl
  have hflag : ∀ j, h.val ≤ j → j < topClockSpan n →
      paFlagSettled s Y anchor.time j = true :=
    fun j h1 h2 => hall j h2 (hnonE j h1 h2)
  have hsamp := fun j hj1 hj2 => labelled_sample s Y anchor hpure k0 hlist h.val hflag j hj1 hj2
  -- the tail
  obtain ⟨sT, hrecT, hlaneT, hsiteT, htailT, hatomT, htokT⟩ := hsamp h.val (Nat.le_refl _) h.isLt
  obtain ⟨vT, hqT⟩ := (qIn_of_cell s Y h.val).1 htail
  have hsT : sT.tail = true := by
    rw [hqT] at htokT
    simp only [puTok] at htokT
    exact (InTok.P.inj htokT).2.symm
  have hmodT : (k0 + (topClockSpan n - 1 - h.val)) % topClockSpan n = topClockSpan n - 1 := by
    rw [hsT] at htailT
    by_cases hc : (k0 + (topClockSpan n - 1 - h.val)) % topClockSpan n = topClockSpan n - 1
    · exact hc
    · rw [if_neg hc] at htailT; exact absurd htailT (by decide)
  refine ⟨⟨hh1, hh2, ⟨sT, hrecT, hlaneT, ?_, hsT, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [hsiteT, hmodT]
    congr 1
    omega
  · have htokT' : InTok.P vT true = InTok.P sT.value sT.tail := by
      rw [hqT] at htokT; exact htokT
    have := (InTok.P.inj htokT').1
    unfold topClockConcreteInputAt
    show (Y.1.1 (winSite s h.val)).qIn = _
    rw [hqT, this]
  · exact hatomT
  · intro j hj
    obtain ⟨sj, hrecj, hlanej, hsitej, htailj, hatomj, htokj⟩ :=
      hsamp j.val (by omega) j.isLt
    obtain ⟨vj, hqj⟩ := (qIn_of_cell s Y j.val).2.1 (hright j.val hj j.isLt)
    have hd : j.val - h.val < topClockSpan n := by omega
    have hidx : k0 + (topClockSpan n - 1 - h.val) =
        (k0 + (topClockSpan n - 1 - j.val)) + (j.val - h.val) := by omega
    have hmodj : (k0 + (topClockSpan n - 1 - j.val)) % topClockSpan n =
        topClockSpan n - 1 - (j.val - h.val) := by
      apply mod_shift _ _ _ (by omega) hd
      rw [← hidx]; exact hmodT
    have hsj : sj.tail = false := by
      rw [hmodj] at htailj
      rw [if_neg (by omega)] at htailj
      exact htailj
    refine ⟨sj, hrecj, hlanej, ?_, hsj, ?_, ?_⟩
    · rw [hsitej, hmodj]
      congr 1
      omega
    · have htokj' : InTok.P vj false = InTok.P sj.value sj.tail := by
        rw [hqj] at htokj; exact htokj
      have := (InTok.P.inj htokj').1
      unfold topClockConcreteInputAt
      show (Y.1.1 (winSite s j.val)).qIn = _
      rw [hqj, this]
    · exact hatomj
  · intro j hj
    rcases hleft j.val hj with h1 | h1 | h1
    · left
      have := (qIn_of_cell s Y j.val).2.2.1 h1
      unfold topClockConcreteInputAt
      show (Y.1.1 (winSite s j.val)).qIn.isE = true
      rw [this]; rfl
    · right
      obtain ⟨v, hv⟩ := (qIn_of_cell s Y j.val).2.2.2.1 h1
      unfold topClockConcreteInputAt
      show (Y.1.1 (winSite s j.val)).qIn.isP = true
      rw [hv]; rfl
    · right
      obtain ⟨v, hv⟩ := (qIn_of_cell s Y j.val).2.2.2.2 h1
      unfold topClockConcreteInputAt
      show (Y.1.1 (winSite s j.val)).qIn.isP = true
      rw [hv]; rfl
  · intro j
    have hc := (hfree j.val j.isLt).1
    have hoff := siteCell_offMatch Y (winSite s j.val)
    unfold OffMatch at hoff
    have : (Y.1.1 (winSite s j.val)).qCarry = .OFF := hoff.1 hc
    exact this
  · -- alignment
    obtain ⟨L, hL, hsplit⟩ := ordLab_split_all (paFlagSettled s Y anchor.time) (paLabSettled s Y)
      h.val (topClockSpan n) (by omega) hflag
    refine ⟨k0, ?_, ?_⟩
    · have h2 : ordLab (paFlagSettled s Y anchor.time) (paLabSettled s Y) (topClockSpan n) =
          L ++ ordLab (paFlagSettled s Y anchor.time) (paLabSettled s Y) h.val := hsplit
      rw [hlist] at h2
      have h3 := congrArg (List.drop (topClockSpan n - h.val)) h2
      rw [List.drop_left' (by omega), List.drop_drop] at h3
      rw [← h3]
    · have := mod_succ_zero _ _ (by omega) hmodT
      have e : k0 + (topClockSpan n - 1 - h.val) + 1 = k0 + (topClockSpan n - h.val) := by omega
      rw [e] at this
      exact this

end MarkedCells
end L3

#print axioms L3.MarkedCells.labelled_sample
#print axioms L3.MarkedCells.misplaced_of_labelled
