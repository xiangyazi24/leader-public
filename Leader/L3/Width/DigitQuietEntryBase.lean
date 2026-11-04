import Leader.L3.Width.DigitQuietEntryBoundary
import Leader.L3.Width.DigitClosePersist
import Leader.L3.Width.DigitFirstZero

/-!
# The entrance into the quiet class: base labels

The clause `base` of `WidthDigitQuiet` (`SEEK` only before `first`, `ZERO` only in
`[first, first + R)`) at a writer comparison cut:

* `goneOfExtinct`: the extinction of the base cut (`DigitBaseExtinct` at `retired`, every label
  root-launched) leaves no inherited label at any later state of the run;
* the position of a root-launched label is the run invariant `WidthFirstZeroInv`
  (`BankRepairDigitZeroLaunchLayout`, rows `bankRepairDigitZeroLaunchStep`), which holds from the
  clean start with no extinction hypothesis, and `bankRepairDigitZeroToksOf` combines the two;
* `quietBaseOfCut`: the field;
* `quietPartsOfCut`: the clauses proved so far, at one `first`.
-/

namespace L3.DigitQuiet

open L3
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.WriterValueCuts
open L3.AcceptedReceipts
open L3.WriterCertificate
open L3.GhostBridge

set_option autoImplicit false

variable {n : Nat} {ring : DirectedRing n}

/-- Induction on a word from its last letter.  Consumer: `goneOfExtinct`. -/
theorem snocInduct {α : Type} {P : List α → Prop} (nil : P [])
    (snoc : ∀ w e, P w → P (w ++ [e])) (l : List α) : P l := by
  have h : ∀ l : List α, P l.reverse := by
    intro l
    induction l with
    | nil => exact nil
    | cons a t ih =>
        rw [List.reverse_cons]
        exact snoc _ a ih
  have := h l.reverse
  rwa [List.reverse_reverse] at this

/-- The frame order along a word from the initial audit.  Consumer: `goneOfExtinct`. -/
theorem frameOrderWord (ref : WidthBoundaryReference ring) (start : ref.State) (word : List (Fin n)) :
    AuditFrameOrder (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start)))).2 := by
  have h0 : AuditFrameOrder (start, digitAuditInitial (piD (ref.phys start))).2 :=
    auditFrameOrderInitial _
  generalize (start, digitAuditInitial (piD (ref.phys start))) = y at h0
  induction word generalizing y with
  | nil => exact h0
  | cons e rest ih => exact ih _ (auditFrameOrderStep ring _ y.2 e h0)

/-- **Extinction at `retired` retires every inherited label at every later state of the run.**
At `retired` every label of the ghost at that time is absent or root-launched; the ghost at the
retired time of the audit is the current ghost of the prefix of the run with that clock, and the
retirement of an inherited label is absorbing.  Consumer: `quietBaseOfCut`. -/
theorem goneOfExtinct (ref : WidthBoundaryReference ring) (hn : 5 ≤ n) (root : Fin n)
    (start : ref.State) (boundary retired : Nat) (word : List (Fin n)) :
    DigitBaseExtinct ring root
      (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).2 boundary retired →
    retired ≤ (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).2.clock →
    widthDigitAllBaseLabelsGone ref.toWidthDigitReference
      (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))) := by
  induction word using snocInduct with
  | nil =>
      rintro ⟨-, T, G, hat, hall⟩ -
      rcases hat with ⟨-, -, rfl⟩ | ⟨f, hf, -⟩
      · rintro ⟨site, i, h⟩
        rcases hall i with ⟨-, hg⟩ | ⟨born, -, -, hg⟩
        · have h' : (digitGhostInitial (piD (ref.phys start)) i).base = _ := h
          rw [show (digitGhostInitial (piD (ref.phys start)) i).base = none from hg] at h'
          cases h'
        · have h' : (digitGhostInitial (piD (ref.phys start)) i).base = _ := h
          rw [show (digitGhostInitial (piD (ref.phys start)) i).base = _ from hg] at h'
          cases h'
      · exact absurd hf (List.not_mem_nil)
  | snoc w e ih =>
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      intro hext hle
      have hfo := frameOrderWord ref start w
      have ih' := ih
      generalize w.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start))) = y at hfo ih' hext hle ⊢
      have hstep : (widthDigitAuditNext ref.toWidthDigitReference y e).2 =
          digitAuditStep ring (piD (ref.phys y.1)) y.2 e := rfl
      rw [hstep] at hext
      by_cases hr : retired ≤ y.2.clock
      · exact widthBoundaryDigitAllBaseLabelsGoneClosed (by omega) ref y e
          (ih' (L3.ClosePersist.extinctBack ring _ _ e root boundary retired hext hr) hr)
      · have hclk : (widthDigitAuditNext ref.toWidthDigitReference y e).2.clock = y.2.clock + 1 :=
          rfl
        rw [hclk] at hle
        have hret : retired = y.2.clock + 1 := by omega
        obtain ⟨-, T, G, hat, hall⟩ := hext
        rcases hat with ⟨h0, -⟩ | ⟨f, hf, hft, -, hG⟩
        · omega
        · rcases List.mem_cons.mp hf with hh | hold
          · subst hh
            rintro ⟨site, i, h⟩
            rcases hall i with ⟨-, hg⟩ | ⟨born, -, -, hg⟩
            · rw [hG] at hg
              have h' : (digitGhostStep ring (piD (ref.phys y.1)) y.2.current (y.2.clock + 1) e
                  i).base = _ := h
              rw [show (digitGhostStep ring (piD (ref.phys y.1)) y.2.current (y.2.clock + 1) e
                  i).base = none from hg] at h'
              cases h'
            · rw [hG] at hg
              have h' : (digitGhostStep ring (piD (ref.phys y.1)) y.2.current (y.2.clock + 1) e
                  i).base = _ := h
              rw [show (digitGhostStep ring (piD (ref.phys y.1)) y.2.current (y.2.clock + 1) e
                  i).base = _ from hg] at h'
              cases h'
          · have := (hfo.2.1 f hold).2
            omega

/-- **The field `base` at a writer comparison cut**, at the first delimiter of the layout at the
cut.  Consumer: `quietPartsOfCut` and the entrance `WidthWriterQuietAtCut`. -/
theorem quietBaseOfCut (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (z : ref.State) (hcut : WidthWriterComparisonCut ref.toWidthDigitReference z)
    (root : Fin n) (hfixed : WFixedRoot ring root (piW (ref.phys z))) (first : Nat)
    (h0 : 0 < first) (hfn : first < n)
    (hb : QuietLayout ring root (piD (ref.phys z)) first) (k : Nat) (hk : k < n) :
    ((piD (ref.phys z) (digitSite ring root k)).top.wBase = .SEEK → k < first) ∧
    ((piD (ref.phys z) (digitSite ring root k)).top.wBase = .ZERO →
      first ≤ k ∧ k < first + digitSpan (compileAdvice (ceilLogTwo n))) := by
  obtain ⟨start, word, root₀, audit, retired, restart, cmp, hstart, hrun, hfixed₀, -, hrec, -, -⟩ :=
    hcut
  have hr₀ : root₀ = root := hfixed.2.1 root₀ hfixed₀.1
  subst hr₀
  obtain ⟨first', stop, baseCut, -, -, -, -, hbase, -, -, -⟩ := hrec
  obtain ⟨⟨hext, hrc, hcc, -⟩, -⟩ := hbase
  have hz : z = word.foldl ref.next start := by
    have := widthAuditFoldFst ref.toWidthDigitReference word start
      (digitAuditInitial (piD (ref.phys start)))
    rw [hrun] at this
    exact this
  obtain ⟨root', hs, hV⟩ := widthCleanBoundaryRoot ref start hstart
  have hW := widthBoundaryDigitBoundaryWFixedRootOfSingleton ref root' start hs word
  rw [← hz] at hW
  have hr : root' = root₀ := hfixed.2.1 root' hW.1
  subst hr
  obtain ⟨f₀, ht, hft, hb₀⟩ := widthCleanBoundaryDelimiters ref hn root' start hV
  have ht2 := compileAdvice_t_ge_two (ceilLogTwo n) (ringQ_facts n hn).1
  have hlead := L3.WriterOrderedClose.leadWidthBand (n := n) hn
  have hd : WidthBoundaryDigitLeadData ref root' f₀ start := ⟨hV.1, by omega, by omega, hb₀⟩
  have hinv := widthFirstZeroInvWord ref hn root' f₀ (by omega) _ word _
    (widthFirstZeroInvInitial ref root' f₀ start hd)
  have hgone := goneOfExtinct ref hn root' start 0 retired word (by rw [hrun]; exact hext)
    (by rw [hrun]; exact Nat.le_trans hrc hcc)
  rw [hrun] at hinv hgone
  obtain ⟨⟨-, -, hsound⟩, ⟨-, -, -, hbz⟩, hL, -⟩ := hinv
  have htoks := bankRepairDigitZeroToksOf ring root' f₀ _ (piD (ref.phys z)) audit.current hsound
    (fun i s h => hgone ⟨s, i, h⟩) hL
  -- the first delimiter of the run is the first delimiter of the cut
  have hff : f₀ = first := by
    refine layoutFirstEq hb h0 hfn f₀ ⟨⟨by omega, by omega, (hbz f₀ (by omega) (by omega)).2
      ⟨Nat.le_refl _, by rw [Nat.sub_self, Nat.zero_mod]⟩⟩, fun j hj hjf => ?_⟩
    cases hbj : (piD (ref.phys z) (digitSite ring root' j)).word.beta with
    | false => rfl
    | true =>
        have := ((hbz j hj (by omega)).1 hbj).1
        omega
  subst hff
  have hstop : widthFirstZeroStop n f₀ ≤ f₀ + digitSpan (compileAdvice (ceilLogTwo n)) :=
    Nat.min_le_left _ _
  constructor
  · intro hw
    have hne : (piD (ref.phys z) (digitSite ring root' k)).top.wBase ≠ .NONE := by
      rw [hw]
      exact fun h => WBase.noConfusion h
    obtain ⟨-, -, -, h2⟩ := htoks.place k hk hne
    rcases Nat.lt_or_ge k f₀ with h | h
    · exact h
    · have := h2 h
      rw [hw] at this
      exact WBase.noConfusion this
  · intro hw
    have hne : (piD (ref.phys z) (digitSite ring root' k)).top.wBase ≠ .NONE := by
      rw [hw]
      exact fun h => WBase.noConfusion h
    obtain ⟨-, hks, h1, -⟩ := htoks.place k hk hne
    refine ⟨?_, by omega⟩
    rcases Nat.lt_or_ge k f₀ with h | h
    · have := h1 h
      rw [hw] at this
      exact WBase.noConfusion this
    · exact h

/-- The first delimiter at the cut is below `t + R`.  Consumer: `quietPartsOfCut`. -/
theorem quietFirstBoundOfCut (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (z : ref.State) (hcut : WidthWriterComparisonCut ref.toWidthDigitReference z)
    (root : Fin n) (hfixed : WFixedRoot ring root (piW (ref.phys z))) (first : Nat)
    (h0 : 0 < first) (hfn : first < n)
    (hb : QuietLayout ring root (piD (ref.phys z)) first) :
    first < (compileAdvice (ceilLogTwo n)).t + digitSpan (compileAdvice (ceilLogTwo n)) := by
  obtain ⟨start, word, -, audit, -, -, -, hstart, hrun, -⟩ := hcut
  have hz : z = word.foldl ref.next start := by
    have := widthAuditFoldFst ref.toWidthDigitReference word start
      (digitAuditInitial (piD (ref.phys start)))
    rw [hrun] at this
    exact this
  obtain ⟨root', hroot'⟩ := ref.startClean start hstart
  have hW := widthCutWordRun ref.toWidthDigitReference hn root' word start
    (ref.startDrained start hstart) hroot'
  rw [← hz] at hW
  have hr : root' = root := hfixed.2.1 root' hW.1.1
  subst hr
  have hsing : ref.singleton root' z := by
    rw [hz]
    exact singletonFold ref.toWidthDigitReference root' word start
      (ref.singletonOfStart root' start hstart hroot'.1)
  obtain ⟨f, ht, hf, hbf⟩ := widthCleanBoundaryDelimiters ref hn root' z ⟨⟨hsing, hW.2.2⟩, hW.2.1⟩
  have ht2 := compileAdvice_t_ge_two (ceilLogTwo n) (ringQ_facts n hn).1
  have hlead := L3.WriterOrderedClose.leadWidthBand (n := n) hn
  have hff : f = first := by
    refine layoutFirstEq hb h0 hfn f ⟨⟨by omega, by omega, (hbf f (by omega) (by omega)).2
      ⟨Nat.le_refl _, by rw [Nat.sub_self, Nat.zero_mod]⟩⟩, fun j hj hjf => ?_⟩
    cases hbj : (piD (ref.phys z) (digitSite ring root' j)).word.beta with
    | false => rfl
    | true =>
        have := ((hbf j hj (by omega)).1 hbj).1
        omega
  rw [← hff]
  exact hf

/-- **The clauses of the quiet class proved at the cut, at one `first`**: unique root, layout,
base labels, leading segment, the first segment in the form of `firstSegmentOfReceipt`, the field
`firstSegment` for `n ≥ 8`, and the final fragment.  Consumer: the entrance `WidthWriterQuietAtCut`, together with the `values` and
`pairs` clauses. -/
theorem quietPartsOfCut (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (z : ref.State) (hcut : WidthWriterComparisonCut ref.toWidthDigitReference z)
    (root : Fin n) (hfixed : WFixedRoot ring root (piW (ref.phys z))) :
    ∃ first : Nat,
      (∀ i : Fin n, (piD (ref.phys z) i).word.native.l = true ↔ i = root) ∧
      (2 ≤ first ∧ first < n ∧ QuietLayout ring root (piD (ref.phys z)) first) ∧
      (∀ k : Nat, 0 < k → k < n →
        ((piD (ref.phys z) (digitSite ring root k)).top.wBase = .SEEK → k < first) ∧
        ((piD (ref.phys z) (digitSite ring root k)).top.wBase = .ZERO →
          first ≤ k ∧ k < first + digitSpan (compileAdvice (ceilLogTwo n)))) ∧
      (∀ (lane : DigitLane) (k : Nat), 0 < k → k < first →
        (view ring root (piD (ref.phys z)) lane k).out = .E ∧
        DigitLeadingInput (view ring root (piD (ref.phys z)) lane k).input ∧
        (view ring root (piD (ref.phys z)) lane k).carryLive = false) ∧
      (∀ (lane : DigitLane) (k : Nat), first ≤ k →
        k < first + digitSpan (compileAdvice (ceilLogTwo n)) → k < n →
        (k + 1 = n ∧ (view ring root (piD (ref.phys z)) lane k).carryLive = true) ∨
        ((view ring root (piD (ref.phys z)) lane k).carryLive = false ∧
          (if k = first then (view ring root (piD (ref.phys z)) lane k).input = .E
           else DigitLeadingInput (view ring root (piD (ref.phys z)) lane k).input))) ∧
      (8 ≤ n → ∀ (lane : DigitLane) (k : Nat), first ≤ k →
        k < first + digitSpan (compileAdvice (ceilLogTwo n)) → k < n →
        (if k = first then (view ring root (piD (ref.phys z)) lane k).input = .E
          else DigitLeadingInput (view ring root (piD (ref.phys z)) lane k).input) ∧
        (k + 1 < n → (view ring root (piD (ref.phys z)) lane k).carryLive = false)) ∧
      (first + digitSpan (compileAdvice (ceilLogTwo n)) < n →
        ∀ (lane : DigitLane) (k : Nat),
          lastDelimiter first (digitSpan (compileAdvice (ceilLogTwo n))) n ≤ k → k < n →
          ∀ (val : Fin (compileAdvice (ceilLogTwo n)).topA) (tail : Bool),
            (view ring root (piD (ref.phys z)) lane k).input ≠ .S val tail ∨
              (k + 1 = n ∧ (view ring root (piD (ref.phys z)) lane k).carryLive = true)) := by
  obtain ⟨first, hroot, ⟨hf2, hfn, hb⟩, hleading⟩ :=
    quietBoundaryOfCut ref hn z hcut root hfixed
  have hrec := quietReceiptOfCut ref.toWidthDigitReference z hcut root hfixed
  have hR := widthBoundaryDigitSpanTwo hn
  exact ⟨first, hroot, ⟨hf2, hfn, hb⟩,
    fun k _ hk => quietBaseOfCut ref hn z hcut root hfixed first (by omega) hfn hb k hk,
    hleading,
    fun lane k h1 h2 h3 => firstSegmentOfReceipt hrec.1 hb (by omega) hfn lane k h1 h2 h3,
    fun h8 lane k h1 h2 h3 => firstSegmentFieldOfBig h8 hrec.1 hb (by omega) hfn
      (quietFirstBoundOfCut ref hn z hcut root hfixed first (by omega) hfn hb) lane k h1 h2 h3,
    fun hlong lane k h1 h3 val tail =>
      fragmentOfReceipt hrec.2 hb (by omega) (by omega) hlong lane k h1 h3 val tail⟩

end L3.DigitQuiet

#print axioms L3.DigitQuiet.goneOfExtinct
#print axioms L3.DigitQuiet.quietBaseOfCut
#print axioms L3.DigitQuiet.quietFirstBoundOfCut
#print axioms L3.DigitQuiet.quietPartsOfCut
