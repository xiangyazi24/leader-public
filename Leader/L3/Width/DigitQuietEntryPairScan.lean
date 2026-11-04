import Leader.L3.Width.DigitQuiet
import Leader.L3.Bank.RepairDigitRearm

/-!
# The pipeline scan of `PairQuiet` from the cycle class

The shape half of `L3.DigitQuiet.PairQuiet`: a masked lane in the cycle class `CohortCycIn` (old
cohort in phase `o`, chosen cohort below it, younger cohort behind the chosen tail), with the values
of its tokens read as source digits, passes the pipeline scan.  This module is purely combinatorial:
its lane views are arbitrary, tied to the masked lane by `ScanTie`, and the token values and carries
are the fields of `ScanVals`.

Scan correspondence.  Reading the target cells from the far end meets the old cohort (its settled
operands above its live carry, or the arrived cohort), then the chosen packets with `nxt = R - 1 - i`
at packet `i` (`scanTargetChosen`, `scanSourceChosen`), then the younger slots of the source at their
own cells with `nxt` equal to the cell (`scanSourceYounger`).  The straggling-tail disjunct of the
scan is never used in the cycle class.

Consumer: `L3.QuietEntryPair.pairQuietOfBundle` (WidthDigitQuietEntryPairBundle).

Paper: research/lean-l3/ledgers/R10c-qdigit-notes.md section 7.3 item 1.
-/

namespace L3.QuietEntryPair

open L3
open L3.DigitQuiet
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.CohortEntry
open L3.PacketClass
open L3.Rearm

set_option autoImplicit false

variable {c : Compiled}

/-! ### One-step equations of the scan -/

section Eqs

variable {R : Nat} {v : Nat → DigitLaneView c} {Dp : Nat → Fin c.topA} {src : Nat → Prop}

/-- Consumer: `scanSourceChosen`. -/
theorem scanSrcE {k nxt : Nat} (ho : (v k).out = .E)
    (h1 : if k = 0 then nxt = 0 else nxt < k) (h2 : ScanSource v Dp k nxt) :
    ScanSource v Dp (k + 1) nxt := by
  simp only [ScanSource, ho]
  exact ⟨h1, h2⟩

/-- Consumer: `scanSourceChosen`, `scanSourceYounger`. -/
theorem scanSrcU {k nxt : Nat} (ho : (v k).out = .U) (h1 : nxt = k)
    (h2 : ScanSource v Dp k (k - 1)) : ScanSource v Dp (k + 1) nxt := by
  simp only [ScanSource, ho]
  exact ⟨h1, h2⟩

/-- Consumer: `scanSourceChosen`, `scanSourceYounger`. -/
theorem scanSrcD {k nxt : Nat} {val : Fin c.topA} {tail : Bool} (ho : (v k).out = .D val tail)
    (h1 : nxt ≤ k) (h2 : val = Dp nxt) (h3 : tail = decide (nxt = 0))
    (h4 : ScanSource v Dp k (if nxt = 0 then k - 1 else nxt - 1)) :
    ScanSource v Dp (k + 1) nxt := by
  simp only [ScanSource, ho]
  exact ⟨h1, h2, h3, h4⟩

/-- Consumer: `scanTargetCarry`. -/
theorem scanTgtLive {k nxt : Nat} {sawP seen : Bool} (hl : (v k).carryLive = true)
    (h1 : nxt = k) (h2 : sawP = false) (h3 : (v k).input = .E)
    (h4 : (v k).carryBit = carryInto Dp (k + 1)) (h5 : (v k).carryError = false)
    (h6 : ScanTarget R v Dp src k (R - 1) sawP true) :
    ScanTarget R v Dp src (k + 1) nxt sawP seen := by
  rw [ScanTarget, if_pos hl]
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- Consumer: `scanTargetChosen`. -/
theorem scanTgtE {k nxt : Nat} {sawP seen : Bool} (hl : (v k).carryLive = false)
    (hi : (v k).input = .E) (h : ScanTarget R v Dp src k nxt sawP seen) :
    ScanTarget R v Dp src (k + 1) nxt sawP seen := by
  rw [ScanTarget, if_neg (by simp [hl]), hi]
  exact h

/-- Consumer: `scanTargetChosen`, `scanTargetArrived`, `scanTargetCarry`. -/
theorem scanTgtS {k nxt : Nat} {sawP seen : Bool} {val : Fin c.topA} {tail : Bool}
    (hl : (v k).carryLive = false) (hi : (v k).input = .S val tail) (h0 : sawP = false) (h1 : nxt = k)
    (h2 : val = Dp k) (h3 : tail = decide (k = 0))
    (h4 : ScanTarget R v Dp src k (if k = 0 then R - 1 else k - 1) sawP true) :
    ScanTarget R v Dp src (k + 1) nxt sawP seen := by
  rw [ScanTarget, if_neg (by simp [hl]), hi]
  exact ⟨h0, h1, h2, h3, h4⟩

/-- Consumer: `scanTargetChosen`, `scanTargetArrived`. -/
theorem scanTgtP {k nxt : Nat} {sawP seen : Bool} {val : Fin c.topA} {tail : Bool}
    (hl : (v k).carryLive = false) (hi : (v k).input = .P val tail) (h1 : k ≤ nxt)
    (h2 : val = Dp nxt) (h3 : tail = decide (nxt = 0))
    (h4 : ScanTarget R v Dp src k (if nxt = 0 then R - 1 else nxt - 1) true true) :
    ScanTarget R v Dp src (k + 1) nxt sawP seen := by
  rw [ScanTarget, if_neg (by simp [hl]), hi]
  exact Or.inr ⟨h1, h2, h3, h4⟩

end Eqs

/-! ### The tie of the views to the masked lane -/

/-- The lane views `tv` (target) and `sv` (source) project to the masked lane `s`.  Consumer:
`scanOfCycle`; producer: `L3.QuietEntryPair.scanTieOfProj`. -/
structure ScanTie (R : Nat) (s : CohortLane) (tv sv : Nat → DigitLaneView c) : Prop where
  out : ∀ k, k < R → s.out k = bankRepairDigitOutShOf (sv k).out
  inp : ∀ k, k < R → s.inp (R + k) = bankRepairDigitInShOf (tv k).input
  live : ∀ k, k < R → s.live (R + k) = (tv k).carryLive

/-- The values and carries of the tokens of the masked lane, against the digits `Dp` of the source:
a chosen packet `i` carries the source digit at offset `R - 1 - i`, an off-slot target cell the
digit of its own offset, a younger source cell the digit of its own offset, and a live target
carry has an empty input, the carry-in bit of the next offset and no error.  Consumer:
`scanOfCycle`; producer: `L3.QuietEntryPair.scanValsOfBundle`. -/
structure ScanVals (R : Nat) (lam : Nat → Nat) (tv sv : Nat → DigitLaneView c)
    (Dp : Nat → Fin c.topA) : Prop where
  targetChosen : ∀ i, i < R → ∀ k, k < R → cohortPos R lam i = R + k →
    ∀ val tail, ((tv k).input = .P val tail ∨ (tv k).input = .S val tail) → val = Dp (R - 1 - i)
  targetOff : ∀ k, k < R → (∀ i, i < R → cohortPos R lam i ≠ R + k) →
    ∀ val tail, ((tv k).input = .P val tail ∨ (tv k).input = .S val tail) → val = Dp k
  sourceChosen : ∀ i, i < R → cohortPos R lam i < R →
    ∀ val tail, (sv (cohortPos R lam i)).out = .D val tail → val = Dp (R - 1 - i)
  sourceYounger : ∀ q, q < R → q < lam (R - 1) →
    ∀ val tail, (sv q).out = .D val tail → val = Dp q
  carry : ∀ k, k < R → (tv k).carryLive = true →
    (tv k).input = .E ∧ (tv k).carryBit = carryInto Dp (k + 1) ∧ (tv k).carryError = false

section Scan

variable {R : Nat} {s : CohortLane} {tv sv : Nat → DigitLaneView c} {Dp : Nat → Fin c.topA}
  {lam : Nat → Nat} {cc : Nat}

/-- The token of a target cell, from its view.  Consumer: `scanTargetChosen`, `scanTargetArrived`,
`scanTargetCarry`. -/
theorem tokTarget (hT : ScanTie R s tv sv) {k : Nat} (hk : k < R) :
    cohortTok R s (R + k) =
      cohortTokIn (bankRepairDigitInShOf (tv k).input) (tv k).carryLive := by
  rw [cohortTokTgt s (by omega : R ≤ R + k), hT.inp k hk, hT.live k hk]

/-- The token of a source cell, from its view.  Consumer: `scanSourceChosen`,
`scanSourceYounger`. -/
theorem tokSource (hT : ScanTie R s tv sv) {k : Nat} (hk : k < R) :
    cohortTok R s k = cohortTokOut (bankRepairDigitOutShOf (sv k).out) := by
  rw [cohortTokSrc s hk, hT.out k hk]

/-- **The younger slots**: below the chosen tail every source cell is an unread marker or an unmoved
packet of its own offset, so the scan continues with `nxt` equal to the cell.  Consumer:
`scanSourceChosen`, `scanTargetChosen`. -/
theorem scanSourceYounger (hT : ScanTie R s tv sv) (hV : ScanVals R lam tv sv Dp)
    (hY : CohortYounger R s (lam (R - 1))) :
    ∀ m, m ≤ R → m ≤ lam (R - 1) → ScanSource sv Dp m (m - 1) := by
  intro m
  induction m with
  | zero => intro _ _; exact trivial
  | succ m ih =>
    intro h1 h2
    have htok := tokSource hT (show m < R by omega)
    have hrec := ih (by omega) (by omega)
    rcases hY m (by omega) (by omega) with h | h <;> rw [htok] at h
    · cases ho : (sv m).out with
      | E => rw [ho] at h; cases h
      | U => exact scanSrcU ho (by omega) hrec
      | D val tail => rw [ho] at h; cases h
    · cases ho : (sv m).out with
      | E => rw [ho] at h; cases h
      | U => rw [ho] at h; cases h
      | D val tail =>
        rw [ho] at h
        have ht : tail = decide (m = 0) := by
          simpa [cohortTokOut, bankRepairDigitOutShOf] using h
        refine scanSrcD ho (by omega) ?_ (by simpa using ht) ?_
        · simpa using hV.sourceYounger m (by omega) (by omega) val tail ho
        · simp only [Nat.add_sub_cancel]
          by_cases h0 : m = 0
          · rw [if_pos h0]
            exact hrec
          · rw [if_neg h0]
            exact hrec

/-- **The chosen packets on the source**: `nxt = R - 1 - i` at the next chosen packet `i`.
Consumer: `scanTargetChosen`. -/
theorem scanSourceChosen (hT : ScanTie R s tv sv) (hV : ScanVals R lam tv sv Dp)
    (hch : CohortChosen R s lam cc) (hc : R ≤ cc) (hY : CohortYounger R s (lam (R - 1))) :
    ∀ m, m ≤ R → ∀ i, i < R → (∀ i', i' < i → m ≤ cohortPos R lam i') →
      cohortPos R lam i < m → ScanSource sv Dp m (R - 1 - i) := by
  have hR := hch.two
  intro m
  induction m with
  | zero => intro _ i _ _ h; omega
  | succ m ih =>
    intro hm i hi hab hlt
    have htok := tokSource hT (show m < R by omega)
    have hposi : cohortPos R lam i = R - 1 - i + lam i := rfl
    by_cases hp : cohortPos R lam i = m
    · -- the cell is the next packet's
      have hlast : lam (R - 1) = cohortPos R lam (R - 1) := by
        unfold cohortPos
        omega
      have hnext : i + 1 < R → ScanSource sv Dp m (R - 1 - (i + 1)) := fun hi1 =>
        ih (by omega) (i + 1) hi1
          (fun i' h' => by
            rcases Nat.lt_or_ge i' i with h'' | h''
            · have := hab i' h''
              omega
            · have : i' = i := by omega
              rw [this]
              exact Nat.le_of_eq hp.symm)
          (by have := chosenPosLt hch (show i < i + 1 by omega) hi1; omega)
      rcases hch.pkt i hi with h | ⟨h, -⟩ | ⟨h, hl0⟩ <;> rw [hp, htok] at h
      · cases ho : (sv m).out with
        | E => rw [ho] at h; cases h
        | U => rw [ho] at h; cases h
        | D val tail =>
          rw [ho] at h
          have ht : tail = cohortTail R i := by
            simpa [cohortTokOut, bankRepairDigitOutShOf] using h
          have hv := hV.sourceChosen i hi (by omega) val tail (by rw [hp]; exact ho)
          refine scanSrcD ho (by omega) hv ?_ ?_
          · rw [ht]
            unfold cohortTail
            by_cases hi1 : i + 1 = R
            · simp [hi1]
            · have : R - 1 - i ≠ 0 := by omega
              simp [hi1, this]
          · by_cases hi1 : i + 1 = R
            · rw [if_pos (by omega)]
              have hlm : lam (R - 1) = m := by
                have : i = R - 1 := by omega
                rw [this] at hp
                rw [hlast]
                exact hp
              exact scanSourceYounger hT hV hY m (by omega) (by omega)
            · rw [if_neg (by omega), show R - 1 - i - 1 = R - 1 - (i + 1) by omega]
              exact hnext (by omega)
      · exact absurd h (cohortTokOutNe _ _)
      · cases ho : (sv m).out with
        | E => rw [ho] at h; cases h
        | D val tail => rw [ho] at h; cases h
        | U =>
          refine scanSrcU ho (by omega) ?_
          by_cases hi1 : i + 1 = R
          · have hm0 : m = 0 := by omega
            rw [hm0]
            exact trivial
          · have := hnext (by omega)
            rw [show R - 1 - (i + 1) = m - 1 by omega] at this
            exact this
    · -- the cell lies in the gap
      have hpos : cohortPos R lam i < m := by omega
      have htailLe := chosenPosTail hch hi
      have hne : ∀ i', i' < R → cohortPos R lam i' ≠ m := by
        intro i' hi' he
        rcases Nat.lt_trichotomy i' i with h' | h' | h'
        · have := hab i' h'
          omega
        · rw [h'] at he
          exact hp he
        · have := chosenPosLt hch h' hi'
          omega
      have hgap := hch.gap m (by omega) (by omega) hne
      rw [htok] at hgap
      cases ho : (sv m).out with
      | U => rw [ho] at hgap; cases hgap
      | D val tail => rw [ho] at hgap; cases hgap
      | E =>
        refine scanSrcE ho ?_ (ih (by omega) i hi (fun i' h' => ?_) hpos)
        · rw [if_neg (by omega)]
          omega
        · have := hab i' h'
          omega

/-- The next offset at the chosen packet `i` (`i = R`: the chosen cohort has been passed).
Consumer: `scanTargetChosen`. -/
def nxtOf (R i : Nat) : Nat := if i < R then R - 1 - i else R - 1

/-- A cell of the target off the chosen slots is empty.  Consumer: `scanTargetChosen`. -/
theorem targetGap (hch : CohortChosen R s lam cc) {q : Nat} (hR : R ≤ q) (hq : q < cc)
    (hne : ∀ i, i < R → cohortPos R lam i ≠ q) : cohortTok R s q = .empty := by
  refine hch.gap q hq ?_ hne
  have htwo := hch.two
  have hle := hch.le (R - 1) (by omega)
  have hpos : cohortPos R lam (R - 1) = lam (R - 1) := by
    unfold cohortPos
    omega
  have := hne (R - 1) (by omega)
  rw [hpos] at this
  omega

/-- A settled chosen packet has every older chosen packet settled.  Consumer: `scanTargetChosen`. -/
theorem chosenSettledUp (hch : CohortChosen R s lam cc) :
    ∀ d i, i + d < R → cohortTok R s (cohortPos R lam (i + d)) = .settled (cohortTail R (i + d)) →
      cohortTok R s (cohortPos R lam i) = .settled (cohortTail R i) := by
  intro d
  induction d with
  | zero => intro i _ h; exact h
  | succ d ih =>
    intro i hi h
    have h1 := hch.top (i + (d + 1)) (by omega) hi h
    rw [show i + (d + 1) - 1 = i + d by omega] at h1
    exact ih i (by omega) h1

/-- **The chosen packets on the target**; no settled chosen packet lies below an in-flight one.
Consumer: `scanOfCycle`. -/
theorem scanTargetChosen (hT : ScanTie R s tv sv) (hV : ScanVals R lam tv sv Dp)
    (hch : CohortChosen R s lam cc) (hc : R ≤ cc) (hY : CohortYounger R s (lam (R - 1)))
    (src : Nat → Prop) (hsrc : ∀ nxt, ScanSource sv Dp R nxt → src nxt) :
    ∀ k, k ≤ R → R + k ≤ cc → ∀ i, i ≤ R →
      (∀ i', i' < i → R + k ≤ cohortPos R lam i') →
      (∀ i', i ≤ i' → i' < R → cohortPos R lam i' < R + k) →
      ∀ sawP seen, (sawP = true → ∀ i', i ≤ i' → i' < R →
        cohortTok R s (cohortPos R lam i') ≠ .settled (cohortTail R i')) →
        ScanTarget R tv Dp src k (nxtOf R i) sawP seen := by
  have hR := hch.two
  have hlast : cohortPos R lam (R - 1) = lam (R - 1) := by
    unfold cohortPos
    omega
  intro k
  induction k with
  | zero =>
    intro _ _ i hi hab hbe _ _ _
    apply hsrc
    by_cases hiR : i < R
    · have := scanSourceChosen hT hV hch hc hY R (Nat.le_refl _) i hiR
        (fun i' h' => by simpa using hab i' h') (by simpa using hbe i (Nat.le_refl _) hiR)
      unfold nxtOf
      rw [if_pos hiR]
      exact this
    · have hiE : i = R := by omega
      have hl := hab (R - 1) (by omega)
      rw [hlast] at hl
      have hle := hch.le (R - 1) (by omega)
      have := scanSourceYounger hT hV hY R (Nat.le_refl _) (by omega)
      unfold nxtOf
      rw [if_neg hiR]
      exact this
  | succ k ih =>
    intro hk hkc i hi hab hbe sawP seen hsaw
    have htok := tokTarget hT (show k < R by omega)
    by_cases hch' : ∃ i', i' < R ∧ cohortPos R lam i' = R + k
    · obtain ⟨i', hi', hpq⟩ := hch'
      have hii : i' = i := by
        rcases Nat.lt_trichotomy i' i with h | h | h
        · have := hab i' h
          omega
        · exact h
        · have h1 := chosenPosLt hch h hi'
          have hiR : i < R := by omega
          have h2 := hbe i (Nat.le_refl _) hiR
          omega
      subst hii
      have hnx : nxtOf R i' = R - 1 - i' := by
        unfold nxtOf
        rw [if_pos hi']
      have hle := hch.le i' hi'
      have hposv : cohortPos R lam i' = R - 1 - i' + lam i' := rfl
      have hrec : ∀ a b, (a = true → ∀ x, i' + 1 ≤ x → x < R →
          cohortTok R s (cohortPos R lam x) ≠ .settled (cohortTail R x)) →
          ScanTarget R tv Dp src k (nxtOf R (i' + 1)) a b :=
        ih (by omega) (by omega) (i' + 1) (by omega)
          (fun x hx => by
            rcases Nat.lt_or_ge x i' with h | h
            · have := hab x h
              omega
            · have : x = i' := by omega
              rw [this, hpq]
              omega)
          (fun x hx hxR => by
            have := chosenPosLt hch (show i' < x by omega) hxR
            omega)
      have hnx1 : nxtOf R (i' + 1) = if R - 1 - i' = 0 then R - 1 else R - 1 - i' - 1 := by
        unfold nxtOf
        by_cases h : i' + 1 < R
        · rw [if_pos h, if_neg (by omega)]
          omega
        · rw [if_neg h, if_pos (by omega)]
      have hTail : cohortTail R i' = decide (R - 1 - i' = 0) := by
        unfold cohortTail
        by_cases hi1 : i' + 1 = R
        · simp [hi1]
        · have : R - 1 - i' ≠ 0 := by omega
          simp [hi1, this]
      rw [hnx]
      rcases hch.pkt i' hi' with h | ⟨h, hlR⟩ | ⟨-, hl0⟩
      · have hnotS : ∀ a, a = true → ∀ x, i' + 1 ≤ x → x < R →
            cohortTok R s (cohortPos R lam x) ≠ .settled (cohortTail R x) := by
          intro _ _ x hx hxR hS
          have hup := chosenSettledUp hch (x - i') i' (by omega) (by
            rw [show i' + (x - i') = x by omega]
            exact hS)
          rw [hup] at h
          cases h
        rw [hpq, htok] at h
        cases hl : (tv k).carryLive with
        | true => rw [hl] at h; simp [cohortTokIn] at h
        | false =>
          rw [hl] at h
          cases hin : (tv k).input with
          | E => rw [hin] at h; simp [cohortTokIn, bankRepairDigitInShOf] at h
          | X => rw [hin] at h; simp [cohortTokIn, bankRepairDigitInShOf] at h
          | S val tail => rw [hin] at h; simp [cohortTokIn, bankRepairDigitInShOf] at h
          | P val tail =>
            rw [hin] at h
            have ht : tail = cohortTail R i' := by
              simpa [cohortTokIn, bankRepairDigitInShOf] using h
            refine scanTgtP hl hin (by omega)
              (hV.targetChosen i' hi' k (by omega) hpq val tail (Or.inl hin)) (by rw [ht, hTail]) ?_
            rw [← hnx1]
            exact hrec _ _ (hnotS _)
      · have hsawF : sawP = false := by
          cases hsp : sawP with
          | false => rfl
          | true => exact absurd h.symm (fun he => hsaw hsp i' (Nat.le_refl _) hi' he.symm)
        rw [hpq, htok] at h
        cases hl : (tv k).carryLive with
        | true => rw [hl] at h; simp [cohortTokIn] at h
        | false =>
          rw [hl] at h
          cases hin : (tv k).input with
          | E => rw [hin] at h; simp [cohortTokIn, bankRepairDigitInShOf] at h
          | X => rw [hin] at h; simp [cohortTokIn, bankRepairDigitInShOf] at h
          | P val tail => rw [hin] at h; simp [cohortTokIn, bankRepairDigitInShOf] at h
          | S val tail =>
            rw [hin] at h
            have ht : tail = cohortTail R i' := by
              simpa [cohortTokIn, bankRepairDigitInShOf] using h
            have hkv : R - 1 - i' = k := by omega
            have hval := hV.targetChosen i' hi' k (by omega) hpq val tail (Or.inr hin)
            rw [hkv] at hval hTail
            refine scanTgtS hl hin hsawF hkv hval (by rw [ht, hTail]) ?_
            have := hrec sawP true (fun ha x hx hxR => hsaw ha x (by omega) hxR)
            rw [hnx1, hkv] at this
            exact this
      · omega
    · have hne : ∀ x, x < R → cohortPos R lam x ≠ R + k := fun x hx he => hch' ⟨x, hx, he⟩
      have hgap := targetGap hch (show R ≤ R + k by omega) (by omega) hne
      rw [htok] at hgap
      cases hl : (tv k).carryLive with
      | true => rw [hl] at hgap; simp [cohortTokIn] at hgap
      | false =>
        rw [hl] at hgap
        cases hin : (tv k).input with
        | X => rw [hin] at hgap; simp [cohortTokIn, bankRepairDigitInShOf] at hgap
        | P val tail => rw [hin] at hgap; simp [cohortTokIn, bankRepairDigitInShOf] at hgap
        | S val tail => rw [hin] at hgap; simp [cohortTokIn, bankRepairDigitInShOf] at hgap
        | E =>
          refine scanTgtE hl hin (ih (by omega) (by omega) i hi (fun x hx => ?_) (fun x hx hxR => ?_) _ _ hsaw)
          · have := hab x hx
            omega
          · have h1 := hbe x hx hxR
            have h2 := hne x hxR
            omega

/-- **The arrived old cohort**: every target cell holds its packet or settled operand.  Consumer:
`scanOfCycle`. -/
theorem scanTargetArrived (hT : ScanTie R s tv sv) (hV : ScanVals R lam tv sv Dp)
    (hR : 2 ≤ R) (src : Nat → Prop) (hsrc : src (R - 1)) (hA : CohortArrived R s)
    (hTop : CohortSettledTop R s)
    (hoff : ∀ i, i < R → cohortPos R lam i < R) :
    ∀ k, k ≤ R → ∀ sawP seen, (sawP = true → ∀ q T, R ≤ q → q < R + k →
        cohortTok R s q ≠ .settled T) →
      ScanTarget R tv Dp src k (if k = 0 then R - 1 else k - 1) sawP seen := by
  intro k
  induction k with
  | zero => intro _ _ _ _; rw [if_pos rfl, ScanTarget]; exact hsrc
  | succ k ih =>
    intro hk sawP seen hsaw
    have htok := tokTarget hT (show k < R by omega)
    have hne : ∀ i, i < R → cohortPos R lam i ≠ R + k := fun i hi => by
      have := hoff i hi
      omega
    have hTail : cohortTail R (R - 1 - k) = decide (k = 0) := by
      unfold cohortTail
      by_cases h0 : k = 0
      · simp [h0]
        omega
      · have : R - 1 - k + 1 ≠ R := by omega
        simp [h0, this]
    rw [show k + 1 - 1 = k by omega, if_neg (by omega)]
    have ha := hA (R - 1 - k) (by omega)
    rw [show 2 * R - 1 - (R - 1 - k) = R + k by omega] at ha
    have hnotS : ∀ a, a = true → cohortTok R s (R + k) = .pkt (cohortTail R (R - 1 - k)) →
        ∀ q T, R ≤ q → q < R + k → cohortTok R s q ≠ .settled T := by
      intro _ _ hp q T hq1 hq2 hS
      obtain ⟨T', hT'⟩ := cohortTopChain hTop (R + k - q) q hq1 (by omega) ⟨T, hS⟩
      rw [show q + (R + k - q) = R + k by omega, hp] at hT'
      cases hT'
    have hsawF : cohortTok R s (R + k) = .settled (cohortTail R (R - 1 - k)) → sawP = false := by
      intro hS
      cases hsp : sawP with
      | false => rfl
      | true => exact absurd hS (hsaw hsp _ _ (by omega) (by omega))
    have ha0 := ha
    rw [htok] at ha
    cases hl : (tv k).carryLive with
    | true => rw [hl] at ha; simp [cohortTokIn] at ha
    | false =>
      rw [hl] at ha
      cases hin : (tv k).input with
      | E => rw [hin] at ha; simp [cohortTokIn, bankRepairDigitInShOf] at ha
      | X => rw [hin] at ha; simp [cohortTokIn, bankRepairDigitInShOf] at ha
      | P val tail =>
        rw [hin] at ha
        have ht : tail = decide (k = 0) := by
          rw [← hTail]
          simpa [cohortTokIn, bankRepairDigitInShOf] using ha
        exact scanTgtP hl hin (Nat.le_refl _)
          (hV.targetOff k (by omega) hne val tail (Or.inl hin)) ht (ih (by omega) _ _ (fun h q T h1 h2 => by
            refine hnotS true rfl ?_ q T h1 h2
            rw [htok, hl, hin]
            simp [cohortTokIn, bankRepairDigitInShOf, ht, hTail]))
      | S val tail =>
        rw [hin] at ha
        have ht : tail = decide (k = 0) := by
          rw [← hTail]
          simpa [cohortTokIn, bankRepairDigitInShOf] using ha
        refine scanTgtS hl hin (hsawF ?_) rfl (hV.targetOff k (by omega) hne val tail (Or.inr hin)) ht
          (ih (by omega) _ _ (fun h q T h1 h2 => hsaw h q T h1 (by omega)))
        rw [htok, hl, hin]
        simp [cohortTokIn, bankRepairDigitInShOf, ht, hTail]

/-- **The old carry**: the settled operands above the live carry at offset `j - 1`.  Consumer:
`scanOfCycle`. -/
theorem scanTargetCarry (hT : ScanTie R s tv sv) (hV : ScanVals R lam tv sv Dp)
    (hR : 2 ≤ R) (src : Nat → Prop) (j : Nat) (hj0 : 1 ≤ j) (hjR : j ≤ R)
    (hlive : s.live (R + j - 1) = true)
    (habove : ∀ q, R + j - 1 < q → q < 2 * R → cohortTok R s q = .settled false)
    (hoff : ∀ i, i < R → cohortPos R lam i < R + j - 1)
    (hbelow : ∀ b, ScanTarget R tv Dp src (j - 1) (R - 1) false b) :
    ∀ k, j ≤ k → k ≤ R → ∀ seen, ScanTarget R tv Dp src k (k - 1) false seen := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro hjk hk seen
    rw [show k + 1 - 1 = k by omega]
    by_cases hjE : k + 1 = j
    · have hl : (tv k).carryLive = true := by
        have := hT.live k (by omega)
        rw [show R + k = R + j - 1 by omega, hlive] at this
        exact this.symm
      obtain ⟨h1, h2, h3⟩ := hV.carry k (by omega) hl
      refine scanTgtLive hl rfl rfl h1 h2 h3 ?_
      have := hbelow true
      rw [show j - 1 = k by omega] at this
      exact this
    · have htok := tokTarget hT (show k < R by omega)
      have ha := habove (R + k) (by omega) (by omega)
      rw [htok] at ha
      have hne : ∀ i, i < R → cohortPos R lam i ≠ R + k := fun i hi => by
        have := hoff i hi
        omega
      cases hl : (tv k).carryLive with
      | true => rw [hl] at ha; simp [cohortTokIn] at ha
      | false =>
        rw [hl] at ha
        cases hin : (tv k).input with
        | E => rw [hin] at ha; simp [cohortTokIn, bankRepairDigitInShOf] at ha
        | X => rw [hin] at ha; simp [cohortTokIn, bankRepairDigitInShOf] at ha
        | P val tail => rw [hin] at ha; simp [cohortTokIn, bankRepairDigitInShOf] at ha
        | S val tail =>
          rw [hin] at ha
          have ht : tail = false := by simpa [cohortTokIn, bankRepairDigitInShOf] using ha
          have hk0 : k ≠ 0 := by omega
          refine scanTgtS hl hin rfl rfl (hV.targetOff k (by omega) hne val tail (Or.inr hin))
            (by simp [ht, hk0]) ?_
          rw [if_neg hk0]
          exact ih (by omega) (by omega) true

/-- **The scan of a lane in the cycle class.**  Consumer: `pairQuietOfBundle`. -/
theorem scanOfCycle (hT : ScanTie R s tv sv) {j o : Nat} {g : (Nat → Nat) × Nat}
    (hcyc : CohortCycIn R j s g o) (hV : ScanVals R g.1 tv sv Dp) :
    ScanTarget R tv Dp (ScanSource sv Dp R) R (R - 1) false false := by
  obtain ⟨-, ⟨hold, hch⟩, hY, -⟩ := hcyc
  have hR := hch.two
  have hle := cohortOldLe hold
  have hsrcId : ∀ nxt, ScanSource sv Dp R nxt → ScanSource sv Dp R nxt := fun _ h => h
  by_cases h1 : o ≤ R
  · rw [cohortBottomSettle h1] at hch
    rw [cohortOldSettle h1] at hold
    have hpos := fun i hi => hch.low i hi
    have hs := scanSourceChosen hT hV hch (Nat.le_refl _) hY R (Nat.le_refl _) 0 (by omega)
      (fun i' h' => absurd h' (Nat.not_lt_zero _)) (hpos 0 (by omega))
    have := scanTargetArrived hT hV hR (ScanSource sv Dp R) hs hold.1 hold.2.1 hpos R (Nat.le_refl _)
      false false (fun h => by cases h)
    rw [if_neg (by omega)] at this
    exact this
  · by_cases h2 : o ≤ 2 * R
    · rw [cohortBottomCarry (by omega)] at hch
      rw [cohortOldCarry (by omega) h2] at hold
      have hj0 : o - R ≠ 0 := by omega
      unfold CohortCarry at hold
      rw [if_neg hj0, if_pos (by omega)] at hold
      obtain ⟨hl, hab⟩ := hold
      have hpos := fun i hi => hch.low i hi
      refine scanTargetCarry hT hV hR _ (o - R) (by omega) (by omega)
        hl hab (fun i hi => by have := hpos i hi; omega) (fun b => ?_) R (by omega)
        (Nat.le_refl _) false
      have hbot : R ≤ o - 1 := by omega
      have := scanTargetChosen hT hV hch hbot hY _ hsrcId (o - R - 1) (by omega) (by omega) 0
        (by omega) (fun i' h' => absurd h' (Nat.not_lt_zero _))
        (fun i' _ hi' => by have := hpos i' hi'; omega) false b (fun h => by cases h)
      rw [show nxtOf R 0 = R - 1 by unfold nxtOf; rw [if_pos (by omega)]; omega] at this
      exact this
    · rw [cohortBottomCarry (by omega), show o - 1 = 2 * R by omega] at hch
      have hpos := fun i hi => hch.low i hi
      have := scanTargetChosen hT hV hch (by omega) hY _ hsrcId R (Nat.le_refl _) (by omega) 0
        (by omega) (fun i' h' => absurd h' (Nat.not_lt_zero _))
        (fun i' _ hi' => by have := hpos i' hi'; omega) false false (fun h => by cases h)
      rw [show nxtOf R 0 = R - 1 by unfold nxtOf; rw [if_pos (by omega)]; omega] at this
      exact this

end Scan

end L3.QuietEntryPair

#print axioms L3.QuietEntryPair.scanSourceYounger
#print axioms L3.QuietEntryPair.scanSourceChosen
#print axioms L3.QuietEntryPair.scanTargetChosen
#print axioms L3.QuietEntryPair.scanTargetArrived
#print axioms L3.QuietEntryPair.scanTargetCarry
#print axioms L3.QuietEntryPair.scanOfCycle
