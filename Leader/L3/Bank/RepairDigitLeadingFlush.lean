import Leader.L3.Bank.RepairDigitFlushEdges

/-!
# T17: the leading-region flush certificate

This assembles the per-edge weight inequalities into one global rank. The interior edges come
from `BankRepairDigit.lean` (`bankRepairDigit{Writer,Comparison}{SegSeg,PreOut}*`), and the
edges at the first delimiter from `BankRepairDigitFlushEdges.lean`.

The rank sums both lanes over the leading offsets `0 < k < min (first + R) n` along
`digitSite ring root`, where `first` is the first delimiter and `R = digitSpan`:

* a prefix offset `k < first` carries `PreOutW + SegInW + LiveW` at distance `first - k`;
* the delimiter carries `DelimInW + LiveW R`;
* a segment offset carries `SegInW + LiveW` at distance `first + R - k`.

The result is `bankRepairDigitLeadingFlushTasksHold`, which is
`BankRepairDigitLeadingFlushTasks` at the paper's budget `2 J`. Here `J` is
`bankRepairDigitBoundaryServices`.
-/

namespace L3.RenewalReferenceClock

set_option autoImplicit false

/-! ### Finite sums over an offset range -/

/-- `bankRepairDigitSumCnt f lo cnt = f lo + ... + f (lo + cnt - 1)`. -/
def bankRepairDigitSumCnt (f : Nat → Nat) (lo : Nat) : Nat → Nat
  | 0 => 0
  | cnt + 1 => bankRepairDigitSumCnt f lo cnt + f (lo + cnt)

theorem bankRepairDigitSumCntAdd (f : Nat → Nat) (lo a : Nat) :
    ∀ b, bankRepairDigitSumCnt f lo (a + b) =
      bankRepairDigitSumCnt f lo a + bankRepairDigitSumCnt f (lo + a) b
  | 0 => rfl
  | b + 1 => by
      show bankRepairDigitSumCnt f lo (a + b) + f (lo + (a + b)) =
        bankRepairDigitSumCnt f lo a + (bankRepairDigitSumCnt f (lo + a) b + f (lo + a + b))
      rw [bankRepairDigitSumCntAdd f lo a b, Nat.add_assoc lo a b]
      omega

theorem bankRepairDigitSumCntMono (f g : Nat → Nat) (lo : Nat) :
    ∀ cnt, (∀ i, lo ≤ i → i < lo + cnt → f i ≤ g i) →
      bankRepairDigitSumCnt f lo cnt ≤ bankRepairDigitSumCnt g lo cnt
  | 0, _ => Nat.le_refl 0
  | cnt + 1, h => by
      have ih := bankRepairDigitSumCntMono f g lo cnt (fun i h1 h2 => h i h1 (by omega))
      have hl := h (lo + cnt) (by omega) (by omega)
      show bankRepairDigitSumCnt f lo cnt + f (lo + cnt) ≤
        bankRepairDigitSumCnt g lo cnt + g (lo + cnt)
      omega

/-- One changed point carrying a drop of `δ`. -/
theorem bankRepairDigitSumCntPoint (f g : Nat → Nat) (lo k δ : Nat) :
    ∀ cnt, (∀ i, lo ≤ i → i < lo + cnt → i ≠ k → f i ≤ g i) → lo ≤ k → k < lo + cnt →
      f k + δ ≤ g k → bankRepairDigitSumCnt f lo cnt + δ ≤ bankRepairDigitSumCnt g lo cnt
  | 0, _, _, h2, _ => absurd h2 (by omega)
  | cnt + 1, h, h1, h2, hk => by
      show bankRepairDigitSumCnt f lo cnt + f (lo + cnt) + δ ≤
        bankRepairDigitSumCnt g lo cnt + g (lo + cnt)
      by_cases hc : k = lo + cnt
      · subst hc
        have := bankRepairDigitSumCntMono f g lo cnt
          (fun i h1 h2 => h i h1 (by omega) (by omega))
        omega
      · have ih := bankRepairDigitSumCntPoint f g lo k δ cnt
          (fun i h1 h2 h3 => h i h1 (by omega) h3) h1 (by omega) hk
        have hl := h (lo + cnt) (by omega) (by omega) (fun h' => hc h'.symm)
        omega

/-- Two adjacent changed points carrying a joint drop of `δ`. -/
theorem bankRepairDigitSumCntPair (f g : Nat → Nat) (lo k δ : Nat) :
    ∀ cnt, (∀ i, lo ≤ i → i < lo + cnt → i ≠ k → i ≠ k + 1 → f i ≤ g i) → lo ≤ k →
      k + 1 < lo + cnt → f k + f (k + 1) + δ ≤ g k + g (k + 1) →
      bankRepairDigitSumCnt f lo cnt + δ ≤ bankRepairDigitSumCnt g lo cnt
  | 0, _, _, h2, _ => absurd h2 (by omega)
  | cnt + 1, h, h1, h2, hk => by
      by_cases hc : k + 1 = lo + cnt
      · obtain ⟨c', rfl⟩ : ∃ c', cnt = c' + 1 := ⟨cnt - 1, by omega⟩
        have hk' : k = lo + c' := by omega
        subst hk'
        show bankRepairDigitSumCnt f lo c' + f (lo + c') + f (lo + c' + 1) + δ ≤
          bankRepairDigitSumCnt g lo c' + g (lo + c') + g (lo + c' + 1)
        have := bankRepairDigitSumCntMono f g lo c'
          (fun i h1 h2 => h i h1 (by omega) (by omega) (by omega))
        omega
      · show bankRepairDigitSumCnt f lo cnt + f (lo + cnt) + δ ≤
          bankRepairDigitSumCnt g lo cnt + g (lo + cnt)
        have ih := bankRepairDigitSumCntPair f g lo k δ cnt
          (fun i h1 h2 h3 h4 => h i h1 (by omega) h3 h4) h1 (by omega) hk
        have hl := h (lo + cnt) (by omega) (by omega) (by omega) (by omega)
        omega

theorem bankRepairDigitSumCntBound (f : Nat → Nat) (lo B : Nat) :
    ∀ cnt, (∀ i, lo ≤ i → i < lo + cnt → f i ≤ B) → bankRepairDigitSumCnt f lo cnt ≤ cnt * B
  | 0, _ => by simp [bankRepairDigitSumCnt]
  | cnt + 1, h => by
      have ih := bankRepairDigitSumCntBound f lo B cnt (fun i h1 h2 => h i h1 (by omega))
      have hl := h (lo + cnt) (by omega) (by omega)
      show bankRepairDigitSumCnt f lo cnt + f (lo + cnt) ≤ (cnt + 1) * B
      rw [Nat.succ_mul]
      omega

theorem bankRepairDigitSumCntExtend (f g : Nat → Nat) (lo cnt cnt' : Nat) (hc : cnt ≤ cnt')
    (h : ∀ i, lo ≤ i → i < lo + cnt → f i ≤ g i) :
    bankRepairDigitSumCnt f lo cnt ≤ bankRepairDigitSumCnt g lo cnt' := by
  have e := bankRepairDigitSumCntAdd g lo cnt (cnt' - cnt)
  rw [show cnt + (cnt' - cnt) = cnt' by omega] at e
  have := bankRepairDigitSumCntMono f g lo cnt h
  omega

/-- A positive point has a right-most positive point. -/
theorem bankRepairDigitRightmost (f : Nat → Nat) (lo : Nat) :
    ∀ cnt, (∃ i, lo ≤ i ∧ i < lo + cnt ∧ 0 < f i) →
      ∃ k, lo ≤ k ∧ k < lo + cnt ∧ 0 < f k ∧ ∀ i, k < i → i < lo + cnt → f i = 0
  | 0, ⟨_, h1, h2, _⟩ => absurd h2 (by omega)
  | cnt + 1, ⟨i, h1, h2, h3⟩ => by
      by_cases hl : 0 < f (lo + cnt)
      · exact ⟨lo + cnt, by omega, by omega, hl, fun j hj1 hj2 => absurd hj2 (by omega)⟩
      · have hi : i < lo + cnt := by
          rcases Nat.lt_or_ge i (lo + cnt) with h | h
          · exact h
          · exfalso
            have : i = lo + cnt := by omega
            subst this
            exact hl h3
        obtain ⟨k, k1, k2, k3, k4⟩ := bankRepairDigitRightmost f lo cnt ⟨i, h1, hi, h3⟩
        refine ⟨k, k1, by omega, k3, fun j hj1 hj2 => ?_⟩
        by_cases hj : j = lo + cnt
        · subst hj
          omega
        · exact k4 j hj1 (by omega)

/-! ### Leading weights -/

/-- The leading weight of one lane at offset `k`. -/
def bankRepairDigitLeadW {A : Nat} (R first k : Nat) (o : OutTok A) (i : InTok A)
    (b : Bool) : Nat :=
  if k < first then
    bankRepairDigitPreOutW R (first - k) o + bankRepairDigitSegInW R (first - k) i +
      bankRepairDigitLiveW (first - k) b
  else if k = first then bankRepairDigitDelimInW R i + bankRepairDigitLiveW R b
  else bankRepairDigitSegInW R (first + R - k) i + bankRepairDigitLiveW (first + R - k) b

theorem bankRepairDigitLeadWPre {A : Nat} {o : OutTok A} {i : InTok A} {b : Bool}
    (R first k : Nat) (h : k < first) :
    bankRepairDigitLeadW R first k o i b =
      bankRepairDigitPreOutW R (first - k) o + bankRepairDigitSegInW R (first - k) i +
        bankRepairDigitLiveW (first - k) b := by
  unfold bankRepairDigitLeadW
  rw [if_pos h]

theorem bankRepairDigitLeadWDelim {A : Nat} {o : OutTok A} {i : InTok A} {b : Bool}
    (R first k : Nat) (h : k = first) :
    bankRepairDigitLeadW R first k o i b =
      bankRepairDigitDelimInW R i + bankRepairDigitLiveW R b := by
  unfold bankRepairDigitLeadW
  rw [if_neg (show ¬ k < first by omega), if_pos h]

theorem bankRepairDigitLeadWSeg {A : Nat} {o : OutTok A} {i : InTok A} {b : Bool}
    (R first k : Nat) (h : first < k) :
    bankRepairDigitLeadW R first k o i b =
      bankRepairDigitSegInW R (first + R - k) i + bankRepairDigitLiveW (first + R - k) b := by
  unfold bankRepairDigitLeadW
  rw [if_neg (show ¬ k < first by omega), if_neg (show ¬ k = first by omega)]

/-- Both lanes of a top record at offset `k`. -/
def bankRepairDigitLeadSiteW {c : Compiled} (R first k : Nat) (f : TopFields c) : Nat :=
  bankRepairDigitLeadW R first k f.wOut f.wIn f.wCarry.isW +
    bankRepairDigitLeadW R first k f.qOut f.qIn f.qCarry.isL

/-- Both lanes of an agent at offset `k` (definitionally the weight of `x.top` at `x.lift`). -/
def bankRepairDigitLeadAgentW {c : Compiled} (R first k : Nat) (a : Agent c) : Nat :=
  bankRepairDigitLeadW R first k a.wOut a.wIn a.wCarry.isW +
    bankRepairDigitLeadW R first k a.qOut a.qIn a.qCarry.isL

/-! ### Two-site inequalities on the literal row -/

theorem bankRepairDigitLeadPairPre (c : Compiled) (ox oy : Agent c) (R first k : Nat)
    (hk : k + 1 < first) (hl : ox.l = false) (hly : oy.l = false)
    (hb : ox.beta = false) (hby : oy.beta = false) :
    bankRepairDigitLeadSiteW R first k (liveTopPair c ox oy).x +
      bankRepairDigitLeadSiteW R first (k + 1) (liveTopPair c ox oy).y ≤
    bankRepairDigitLeadAgentW R first k ox + bankRepairDigitLeadAgentW R first (k + 1) oy := by
  have e1 : first - k = first - (k + 1) + 1 := by omega
  simp only [bankRepairDigitLeadSiteW, bankRepairDigitLeadAgentW,
    bankRepairDigitLeadWPre R first k (show k < first by omega),
    bankRepairDigitLeadWPre R first (k + 1) hk, e1]
  have h1 := bankRepairDigitWriterSegSeg c ox oy R (first - (k + 1)) hl hly hb hby
  have h2 := bankRepairDigitWriterPreOut c ox oy R (first - (k + 1)) hl hly hb hby
  have h3 := bankRepairDigitComparisonSegSeg c ox oy R (first - (k + 1)) hl hly hb hby
  have h4 := bankRepairDigitComparisonPreOut c ox oy R (first - (k + 1)) hl hly hb hby
  omega

theorem bankRepairDigitLeadPairPreStrict (c : Compiled) (ox oy : Agent c) (R first k : Nat)
    (hk : k + 1 < first) (hl : ox.l = false) (hly : oy.l = false)
    (hb : ox.beta = false) (hby : oy.beta = false)
    (hx : 1 ≤ bankRepairDigitLeadAgentW R first k ox)
    (hy : bankRepairDigitLeadAgentW R first (k + 1) oy = 0) :
    bankRepairDigitLeadSiteW R first k (liveTopPair c ox oy).x +
      bankRepairDigitLeadSiteW R first (k + 1) (liveTopPair c ox oy).y + 1 ≤
    bankRepairDigitLeadAgentW R first k ox + bankRepairDigitLeadAgentW R first (k + 1) oy := by
  have e1 : first - k = first - (k + 1) + 1 := by omega
  have hd : 1 ≤ first - (k + 1) := by omega
  simp only [bankRepairDigitLeadSiteW, bankRepairDigitLeadAgentW,
    bankRepairDigitLeadWPre R first k (show k < first by omega),
    bankRepairDigitLeadWPre R first (k + 1) hk, e1] at hx hy ⊢
  have h1 := bankRepairDigitWriterSegSeg c ox oy R (first - (k + 1)) hl hly hb hby
  have h2 := bankRepairDigitWriterPreOut c ox oy R (first - (k + 1)) hl hly hb hby
  have h3 := bankRepairDigitComparisonSegSeg c ox oy R (first - (k + 1)) hl hly hb hby
  have h4 := bankRepairDigitComparisonPreOut c ox oy R (first - (k + 1)) hl hly hb hby
  by_cases c1 : 1 ≤ bankRepairDigitSegInW R (first - (k + 1) + 1) ox.wIn +
      bankRepairDigitLiveW (first - (k + 1) + 1) ox.wCarry.isW
  · have := bankRepairDigitWriterSegSegStrict c ox oy R (first - (k + 1)) hd hl hly hb hby c1
      (by omega)
    omega
  by_cases c2 : 1 ≤ bankRepairDigitPreOutW R (first - (k + 1) + 1) ox.wOut
  · have := bankRepairDigitWriterPreOutStrict c ox oy R (first - (k + 1)) hl hly hb hby c2
      (by omega)
    omega
  by_cases c3 : 1 ≤ bankRepairDigitSegInW R (first - (k + 1) + 1) ox.qIn +
      bankRepairDigitLiveW (first - (k + 1) + 1) ox.qCarry.isL
  · have := bankRepairDigitComparisonSegSegStrict c ox oy R (first - (k + 1)) hd hl hly hb hby
      c3 (by omega)
    omega
  · have c4 : 1 ≤ bankRepairDigitPreOutW R (first - (k + 1) + 1) ox.qOut := by omega
    have := bankRepairDigitComparisonPreOutStrict c ox oy R (first - (k + 1)) hl hly hb hby c4
      (by omega)
    omega

theorem bankRepairDigitLeadPairInto (c : Compiled) (ox oy : Agent c) (R first k : Nat)
    (hk : k + 1 = first) (hl : ox.l = false) (hly : oy.l = false)
    (hb : ox.beta = false) (hby : oy.beta = true) :
    bankRepairDigitLeadSiteW R first k (liveTopPair c ox oy).x +
      bankRepairDigitLeadSiteW R first (k + 1) (liveTopPair c ox oy).y ≤
    bankRepairDigitLeadAgentW R first k ox + bankRepairDigitLeadAgentW R first (k + 1) oy := by
  simp only [bankRepairDigitLeadSiteW, bankRepairDigitLeadAgentW,
    bankRepairDigitLeadWPre R first k (show k < first by omega),
    bankRepairDigitLeadWDelim R first (k + 1) hk, show first - k = 1 by omega]
  have h1 := bankRepairDigitWriterIntoDelim c ox oy R hl hly hb hby
  have h2 := bankRepairDigitComparisonIntoDelim c ox oy R hl hly hb hby
  omega

theorem bankRepairDigitLeadPairIntoStrict (c : Compiled) (ox oy : Agent c) (R first k : Nat)
    (hR : 1 ≤ R) (hk : k + 1 = first) (hl : ox.l = false) (hly : oy.l = false)
    (hb : ox.beta = false) (hby : oy.beta = true)
    (hx : 1 ≤ bankRepairDigitLeadAgentW R first k ox)
    (hy : bankRepairDigitLeadAgentW R first (k + 1) oy = 0) :
    bankRepairDigitLeadSiteW R first k (liveTopPair c ox oy).x +
      bankRepairDigitLeadSiteW R first (k + 1) (liveTopPair c ox oy).y + 1 ≤
    bankRepairDigitLeadAgentW R first k ox + bankRepairDigitLeadAgentW R first (k + 1) oy := by
  simp only [bankRepairDigitLeadSiteW, bankRepairDigitLeadAgentW,
    bankRepairDigitLeadWPre R first k (show k < first by omega),
    bankRepairDigitLeadWDelim R first (k + 1) hk, show first - k = 1 by omega] at hx hy ⊢
  have h1 := bankRepairDigitWriterIntoDelim c ox oy R hl hly hb hby
  have h2 := bankRepairDigitComparisonIntoDelim c ox oy R hl hly hb hby
  by_cases c1 : 1 ≤ bankRepairDigitSegInW R 1 ox.wIn + bankRepairDigitLiveW 1 ox.wCarry.isW
  · have := bankRepairDigitWriterIntoDelimStrictIn c ox oy R hR hl hly hb hby c1 (by omega)
    omega
  by_cases c2 : 1 ≤ bankRepairDigitPreOutW R 1 ox.wOut
  · have := bankRepairDigitWriterIntoDelimStrictOut c ox oy R hR hl hly hb hby c2 (by omega)
      (by omega)
    omega
  by_cases c3 : 1 ≤ bankRepairDigitSegInW R 1 ox.qIn + bankRepairDigitLiveW 1 ox.qCarry.isL
  · have := bankRepairDigitComparisonIntoDelimStrictIn c ox oy R hR hl hly hb hby c3 (by omega)
    omega
  · have c4 : 1 ≤ bankRepairDigitPreOutW R 1 ox.qOut := by omega
    have := bankRepairDigitComparisonIntoDelimStrictOut c ox oy R hR hl hly hb hby c4 (by omega)
      (by omega)
    omega

theorem bankRepairDigitLeadPairFrom (c : Compiled) (ox oy : Agent c) (R first k : Nat)
    (hR : 2 ≤ R) (hk : k = first) (hl : ox.l = false) (hly : oy.l = false)
    (hb : ox.beta = true) (hby : oy.beta = false) :
    bankRepairDigitLeadSiteW R first k (liveTopPair c ox oy).x +
      bankRepairDigitLeadSiteW R first (k + 1) (liveTopPair c ox oy).y ≤
    bankRepairDigitLeadAgentW R first k ox + bankRepairDigitLeadAgentW R first (k + 1) oy := by
  simp only [bankRepairDigitLeadSiteW, bankRepairDigitLeadAgentW,
    bankRepairDigitLeadWDelim R first k hk,
    bankRepairDigitLeadWSeg R first (k + 1) (show first < k + 1 by omega),
    show first + R - (k + 1) = R - 1 by omega]
  have h1 := bankRepairDigitWriterFromDelim c ox oy R hR hl hly hb hby
  have h2 := bankRepairDigitComparisonFromDelim c ox oy R hR hl hly hb hby
  omega

theorem bankRepairDigitLeadPairFromStrict (c : Compiled) (ox oy : Agent c) (R first k : Nat)
    (hR : 2 ≤ R) (hk : k = first) (hl : ox.l = false) (hly : oy.l = false)
    (hb : ox.beta = true) (hby : oy.beta = false)
    (hx : 1 ≤ bankRepairDigitLeadAgentW R first k ox)
    (hy : bankRepairDigitLeadAgentW R first (k + 1) oy = 0) :
    bankRepairDigitLeadSiteW R first k (liveTopPair c ox oy).x +
      bankRepairDigitLeadSiteW R first (k + 1) (liveTopPair c ox oy).y + 1 ≤
    bankRepairDigitLeadAgentW R first k ox + bankRepairDigitLeadAgentW R first (k + 1) oy := by
  simp only [bankRepairDigitLeadSiteW, bankRepairDigitLeadAgentW,
    bankRepairDigitLeadWDelim R first k hk,
    bankRepairDigitLeadWSeg R first (k + 1) (show first < k + 1 by omega),
    show first + R - (k + 1) = R - 1 by omega] at hx hy ⊢
  have h1 := bankRepairDigitWriterFromDelim c ox oy R hR hl hly hb hby
  have h2 := bankRepairDigitComparisonFromDelim c ox oy R hR hl hly hb hby
  by_cases c1 : 1 ≤ bankRepairDigitDelimInW R ox.wIn + bankRepairDigitLiveW R ox.wCarry.isW
  · have := bankRepairDigitWriterFromDelimStrict c ox oy R hR hl hly hb hby c1 (by omega)
    omega
  · have c2 : 1 ≤ bankRepairDigitDelimInW R ox.qIn + bankRepairDigitLiveW R ox.qCarry.isL := by
      omega
    have := bankRepairDigitComparisonFromDelimStrict c ox oy R hR hl hly hb hby c2 (by omega)
    omega

theorem bankRepairDigitLeadPairSeg (c : Compiled) (ox oy : Agent c) (R first k : Nat)
    (hk1 : first < k) (hk2 : k + 1 < first + R) (hl : ox.l = false) (hly : oy.l = false)
    (hb : ox.beta = false) (hby : oy.beta = false) :
    bankRepairDigitLeadSiteW R first k (liveTopPair c ox oy).x +
      bankRepairDigitLeadSiteW R first (k + 1) (liveTopPair c ox oy).y ≤
    bankRepairDigitLeadAgentW R first k ox + bankRepairDigitLeadAgentW R first (k + 1) oy := by
  have e1 : first + R - k = first + R - (k + 1) + 1 := by omega
  simp only [bankRepairDigitLeadSiteW, bankRepairDigitLeadAgentW,
    bankRepairDigitLeadWSeg R first k hk1,
    bankRepairDigitLeadWSeg R first (k + 1) (show first < k + 1 by omega), e1]
  have h1 := bankRepairDigitWriterSegSeg c ox oy R (first + R - (k + 1)) hl hly hb hby
  have h2 := bankRepairDigitComparisonSegSeg c ox oy R (first + R - (k + 1)) hl hly hb hby
  omega

theorem bankRepairDigitLeadPairSegStrict (c : Compiled) (ox oy : Agent c) (R first k : Nat)
    (hk1 : first < k) (hk2 : k + 1 < first + R) (hl : ox.l = false) (hly : oy.l = false)
    (hb : ox.beta = false) (hby : oy.beta = false)
    (hx : 1 ≤ bankRepairDigitLeadAgentW R first k ox)
    (hy : bankRepairDigitLeadAgentW R first (k + 1) oy = 0) :
    bankRepairDigitLeadSiteW R first k (liveTopPair c ox oy).x +
      bankRepairDigitLeadSiteW R first (k + 1) (liveTopPair c ox oy).y + 1 ≤
    bankRepairDigitLeadAgentW R first k ox + bankRepairDigitLeadAgentW R first (k + 1) oy := by
  have e1 : first + R - k = first + R - (k + 1) + 1 := by omega
  have hd : 1 ≤ first + R - (k + 1) := by omega
  simp only [bankRepairDigitLeadSiteW, bankRepairDigitLeadAgentW,
    bankRepairDigitLeadWSeg R first k hk1,
    bankRepairDigitLeadWSeg R first (k + 1) (show first < k + 1 by omega), e1] at hx hy ⊢
  have h1 := bankRepairDigitWriterSegSeg c ox oy R (first + R - (k + 1)) hl hly hb hby
  have h2 := bankRepairDigitComparisonSegSeg c ox oy R (first + R - (k + 1)) hl hly hb hby
  by_cases c1 : 1 ≤ bankRepairDigitSegInW R (first + R - (k + 1) + 1) ox.wIn +
      bankRepairDigitLiveW (first + R - (k + 1) + 1) ox.wCarry.isW
  · have := bankRepairDigitWriterSegSegStrict c ox oy R (first + R - (k + 1)) hd hl hly hb hby
      c1 (by omega)
    omega
  · have c2 : 1 ≤ bankRepairDigitSegInW R (first + R - (k + 1) + 1) ox.qIn +
        bankRepairDigitLiveW (first + R - (k + 1) + 1) ox.qCarry.isL := by omega
    have := bankRepairDigitComparisonSegSegStrict c ox oy R (first + R - (k + 1)) hd hl hly hb
      hby c2 (by omega)
    omega

theorem bankRepairDigitLeadOutOfSeg (c : Compiled) (ox oy : Agent c) (R first k : Nat)
    (hk1 : first < k) (hk2 : k + 1 = first + R) (hl : ox.l = false) (hly : oy.l = false)
    (hb : ox.beta = false) (hby : oy.beta = true) :
    bankRepairDigitLeadSiteW R first k (liveTopPair c ox oy).x ≤
      bankRepairDigitLeadAgentW R first k ox := by
  simp only [bankRepairDigitLeadSiteW, bankRepairDigitLeadAgentW,
    bankRepairDigitLeadWSeg R first k hk1, show first + R - k = 1 by omega]
  have h1 := bankRepairDigitWriterOutOfSeg c ox oy R hl hly hb hby
  have h2 := bankRepairDigitComparisonOutOfSeg c ox oy R hl hly hb hby
  omega

theorem bankRepairDigitLeadOutOfSegStrict (c : Compiled) (ox oy : Agent c) (R first k : Nat)
    (hk1 : first < k) (hk2 : k + 1 = first + R) (hl : ox.l = false) (hly : oy.l = false)
    (hb : ox.beta = false) (hby : oy.beta = true)
    (hx : 1 ≤ bankRepairDigitLeadAgentW R first k ox) :
    bankRepairDigitLeadSiteW R first k (liveTopPair c ox oy).x + 1 ≤
      bankRepairDigitLeadAgentW R first k ox := by
  simp only [bankRepairDigitLeadSiteW, bankRepairDigitLeadAgentW,
    bankRepairDigitLeadWSeg R first k hk1, show first + R - k = 1 by omega] at hx ⊢
  have h1 := bankRepairDigitWriterOutOfSeg c ox oy R hl hly hb hby
  have h2 := bankRepairDigitComparisonOutOfSeg c ox oy R hl hly hb hby
  by_cases c1 : 1 ≤ bankRepairDigitSegInW R 1 ox.wIn + bankRepairDigitLiveW 1 ox.wCarry.isW
  · have := bankRepairDigitWriterOutOfSegStrict c ox oy R hl hly hb hby c1
    omega
  · have c2 : 1 ≤ bankRepairDigitSegInW R 1 ox.qIn + bankRepairDigitLiveW 1 ox.qCarry.isL := by
      omega
    have := bankRepairDigitComparisonOutOfSegStrict c ox oy R hl hly hb hby c2
    omega

/-- A leader edge empties both endpoints of every leading weight. -/
theorem bankRepairDigitLeadReset (c : Compiled) (ox oy : Agent c) (bx bY : Bool)
    (R first k k' : Nat) (hr : (ox.l || oy.l) = true) :
    bankRepairDigitLeadSiteW R first k (liveTopPair c ox oy bx bY).x = 0 ∧
      bankRepairDigitLeadSiteW R first k' (liveTopPair c ox oy bx bY).y = 0 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ :=
    bankRepairDigitRootEdgeResets c ox oy bx bY hr
  simp only [bankRepairDigitLeadSiteW, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12]
  constructor <;>
    simp [bankRepairDigitLeadW, bankRepairDigitPreOutW, bankRepairDigitSegInW,
      bankRepairDigitLiveW, bankRepairDigitDelimInW, WCarry.isW, QCarry.isL]

/-! #### The same inequalities on projected records (definitional transfer) -/

theorem bankRepairDigitLeadResetD (c : Compiled) (x y : ProjD c) (R first k k' : Nat)
    (hr : (x.word.native.l || y.word.native.l) = true) :
    bankRepairDigitLeadSiteW R first k (bankRepairDigitTopPairOf c x y).x = 0 ∧
      bankRepairDigitLeadSiteW R first k' (bankRepairDigitTopPairOf c x y).y = 0 :=
  bankRepairDigitLeadReset c x.lift y.lift x.word.beta y.word.beta R first k k' hr

theorem bankRepairDigitLeadPairPreD (c : Compiled) (x y : ProjD c) (R first k : Nat)
    (hk : k + 1 < first) (hl : x.word.native.l = false) (hly : y.word.native.l = false)
    (hb : x.word.beta = false) (hby : y.word.beta = false) :
    bankRepairDigitLeadSiteW R first k (bankRepairDigitTopPairOf c x y).x +
      bankRepairDigitLeadSiteW R first (k + 1) (bankRepairDigitTopPairOf c x y).y ≤
    bankRepairDigitLeadSiteW R first k x.top + bankRepairDigitLeadSiteW R first (k + 1) y.top :=
  bankRepairDigitLeadPairPre c x.lift y.lift R first k hk hl hly hb hby

theorem bankRepairDigitLeadPairPreStrictD (c : Compiled) (x y : ProjD c) (R first k : Nat)
    (hk : k + 1 < first) (hl : x.word.native.l = false) (hly : y.word.native.l = false)
    (hb : x.word.beta = false) (hby : y.word.beta = false)
    (hx : 1 ≤ bankRepairDigitLeadSiteW R first k x.top)
    (hy : bankRepairDigitLeadSiteW R first (k + 1) y.top = 0) :
    bankRepairDigitLeadSiteW R first k (bankRepairDigitTopPairOf c x y).x +
      bankRepairDigitLeadSiteW R first (k + 1) (bankRepairDigitTopPairOf c x y).y + 1 ≤
    bankRepairDigitLeadSiteW R first k x.top + bankRepairDigitLeadSiteW R first (k + 1) y.top :=
  bankRepairDigitLeadPairPreStrict c x.lift y.lift R first k hk hl hly hb hby hx hy

theorem bankRepairDigitLeadPairIntoD (c : Compiled) (x y : ProjD c) (R first k : Nat)
    (hk : k + 1 = first) (hl : x.word.native.l = false) (hly : y.word.native.l = false)
    (hb : x.word.beta = false) (hby : y.word.beta = true) :
    bankRepairDigitLeadSiteW R first k (bankRepairDigitTopPairOf c x y).x +
      bankRepairDigitLeadSiteW R first (k + 1) (bankRepairDigitTopPairOf c x y).y ≤
    bankRepairDigitLeadSiteW R first k x.top + bankRepairDigitLeadSiteW R first (k + 1) y.top :=
  bankRepairDigitLeadPairInto c x.lift y.lift R first k hk hl hly hb hby

theorem bankRepairDigitLeadPairIntoStrictD (c : Compiled) (x y : ProjD c) (R first k : Nat)
    (hR : 1 ≤ R) (hk : k + 1 = first) (hl : x.word.native.l = false)
    (hly : y.word.native.l = false) (hb : x.word.beta = false) (hby : y.word.beta = true)
    (hx : 1 ≤ bankRepairDigitLeadSiteW R first k x.top)
    (hy : bankRepairDigitLeadSiteW R first (k + 1) y.top = 0) :
    bankRepairDigitLeadSiteW R first k (bankRepairDigitTopPairOf c x y).x +
      bankRepairDigitLeadSiteW R first (k + 1) (bankRepairDigitTopPairOf c x y).y + 1 ≤
    bankRepairDigitLeadSiteW R first k x.top + bankRepairDigitLeadSiteW R first (k + 1) y.top :=
  bankRepairDigitLeadPairIntoStrict c x.lift y.lift R first k hR hk hl hly hb hby hx hy

theorem bankRepairDigitLeadPairFromD (c : Compiled) (x y : ProjD c) (R first k : Nat)
    (hR : 2 ≤ R) (hk : k = first) (hl : x.word.native.l = false)
    (hly : y.word.native.l = false) (hb : x.word.beta = true) (hby : y.word.beta = false) :
    bankRepairDigitLeadSiteW R first k (bankRepairDigitTopPairOf c x y).x +
      bankRepairDigitLeadSiteW R first (k + 1) (bankRepairDigitTopPairOf c x y).y ≤
    bankRepairDigitLeadSiteW R first k x.top + bankRepairDigitLeadSiteW R first (k + 1) y.top :=
  bankRepairDigitLeadPairFrom c x.lift y.lift R first k hR hk hl hly hb hby

theorem bankRepairDigitLeadPairFromStrictD (c : Compiled) (x y : ProjD c) (R first k : Nat)
    (hR : 2 ≤ R) (hk : k = first) (hl : x.word.native.l = false)
    (hly : y.word.native.l = false) (hb : x.word.beta = true) (hby : y.word.beta = false)
    (hx : 1 ≤ bankRepairDigitLeadSiteW R first k x.top)
    (hy : bankRepairDigitLeadSiteW R first (k + 1) y.top = 0) :
    bankRepairDigitLeadSiteW R first k (bankRepairDigitTopPairOf c x y).x +
      bankRepairDigitLeadSiteW R first (k + 1) (bankRepairDigitTopPairOf c x y).y + 1 ≤
    bankRepairDigitLeadSiteW R first k x.top + bankRepairDigitLeadSiteW R first (k + 1) y.top :=
  bankRepairDigitLeadPairFromStrict c x.lift y.lift R first k hR hk hl hly hb hby hx hy

theorem bankRepairDigitLeadPairSegD (c : Compiled) (x y : ProjD c) (R first k : Nat)
    (hk1 : first < k) (hk2 : k + 1 < first + R) (hl : x.word.native.l = false)
    (hly : y.word.native.l = false) (hb : x.word.beta = false) (hby : y.word.beta = false) :
    bankRepairDigitLeadSiteW R first k (bankRepairDigitTopPairOf c x y).x +
      bankRepairDigitLeadSiteW R first (k + 1) (bankRepairDigitTopPairOf c x y).y ≤
    bankRepairDigitLeadSiteW R first k x.top + bankRepairDigitLeadSiteW R first (k + 1) y.top :=
  bankRepairDigitLeadPairSeg c x.lift y.lift R first k hk1 hk2 hl hly hb hby

theorem bankRepairDigitLeadPairSegStrictD (c : Compiled) (x y : ProjD c) (R first k : Nat)
    (hk1 : first < k) (hk2 : k + 1 < first + R) (hl : x.word.native.l = false)
    (hly : y.word.native.l = false) (hb : x.word.beta = false) (hby : y.word.beta = false)
    (hx : 1 ≤ bankRepairDigitLeadSiteW R first k x.top)
    (hy : bankRepairDigitLeadSiteW R first (k + 1) y.top = 0) :
    bankRepairDigitLeadSiteW R first k (bankRepairDigitTopPairOf c x y).x +
      bankRepairDigitLeadSiteW R first (k + 1) (bankRepairDigitTopPairOf c x y).y + 1 ≤
    bankRepairDigitLeadSiteW R first k x.top + bankRepairDigitLeadSiteW R first (k + 1) y.top :=
  bankRepairDigitLeadPairSegStrict c x.lift y.lift R first k hk1 hk2 hl hly hb hby hx hy

theorem bankRepairDigitLeadOutOfSegD (c : Compiled) (x y : ProjD c) (R first k : Nat)
    (hk1 : first < k) (hk2 : k + 1 = first + R) (hl : x.word.native.l = false)
    (hly : y.word.native.l = false) (hb : x.word.beta = false) (hby : y.word.beta = true) :
    bankRepairDigitLeadSiteW R first k (bankRepairDigitTopPairOf c x y).x ≤
      bankRepairDigitLeadSiteW R first k x.top :=
  bankRepairDigitLeadOutOfSeg c x.lift y.lift R first k hk1 hk2 hl hly hb hby

theorem bankRepairDigitLeadOutOfSegStrictD (c : Compiled) (x y : ProjD c) (R first k : Nat)
    (hk1 : first < k) (hk2 : k + 1 = first + R) (hl : x.word.native.l = false)
    (hly : y.word.native.l = false) (hb : x.word.beta = false) (hby : y.word.beta = true)
    (hx : 1 ≤ bankRepairDigitLeadSiteW R first k x.top) :
    bankRepairDigitLeadSiteW R first k (bankRepairDigitTopPairOf c x y).x + 1 ≤
      bankRepairDigitLeadSiteW R first k x.top :=
  bankRepairDigitLeadOutOfSegStrict c x.lift y.lift R first k hk1 hk2 hl hly hb hby hx

/-! ### Zero weights are the leading receipt; weight bounds -/

theorem bankRepairDigitPreOutWZero {A : Nat} (R a : Nat) (o : OutTok A)
    (h : bankRepairDigitPreOutW R a o = 0) : o = .E := by
  have hp := bankRepairDigitTailWPos R a
  cases o with
  | E => rfl
  | U => simp only [bankRepairDigitPreOutW] at h <;> omega
  | D v T => cases T <;> simp [bankRepairDigitPreOutW] at h <;> omega

theorem bankRepairDigitSegInWZero {A : Nat} (R a : Nat) (i : InTok A) (ha : 1 ≤ a)
    (h : bankRepairDigitSegInW R a i = 0) : DigitLeadingInput i := by
  cases i with
  | E => exact Or.inl rfl
  | X => simp only [bankRepairDigitSegInW] at h <;> omega
  | P v T => simp only [bankRepairDigitSegInW] at h <;> omega
  | S v T =>
      cases T with
      | false => exact Or.inr ⟨v, rfl⟩
      | true => simp [bankRepairDigitSegInW] at h

theorem bankRepairDigitLiveWZero (a : Nat) (b : Bool) (ha : 1 ≤ a)
    (h : bankRepairDigitLiveW a b = 0) : b = false := by
  cases b with
  | false => rfl
  | true => simp [bankRepairDigitLiveW] at h <;> omega

theorem bankRepairDigitDelimInWZero {A : Nat} (R : Nat) (i : InTok A) (hR : 1 ≤ R)
    (h : bankRepairDigitDelimInW R i = 0) : i = .E := by
  cases i with
  | E => rfl
  | X => simp only [bankRepairDigitDelimInW] at h <;> omega
  | P v T => simp only [bankRepairDigitDelimInW] at h <;> omega
  | S v T => simp only [bankRepairDigitDelimInW] at h <;> omega

theorem bankRepairDigitLeadWZeroPre {A : Nat} {o : OutTok A} {i : InTok A} {b : Bool}
    {R first k : Nat} (hk : k < first) (h : bankRepairDigitLeadW R first k o i b = 0) :
    o = .E ∧ b = false ∧ DigitLeadingInput i := by
  rw [bankRepairDigitLeadWPre R first k hk] at h
  exact ⟨bankRepairDigitPreOutWZero R (first - k) o (by omega),
    bankRepairDigitLiveWZero (first - k) b (by omega) (by omega),
    bankRepairDigitSegInWZero R (first - k) i (by omega) (by omega)⟩

theorem bankRepairDigitLeadWZeroDelim {A : Nat} {o : OutTok A} {i : InTok A} {b : Bool}
    {R first k : Nat} (hR : 1 ≤ R) (hk : k = first)
    (h : bankRepairDigitLeadW R first k o i b = 0) : b = false ∧ i = .E := by
  rw [bankRepairDigitLeadWDelim R first k hk] at h
  exact ⟨bankRepairDigitLiveWZero _ b hR (by omega),
    bankRepairDigitDelimInWZero R i hR (by omega)⟩

theorem bankRepairDigitLeadWZeroSeg {A : Nat} {o : OutTok A} {i : InTok A} {b : Bool}
    {R first k : Nat} (hk1 : first < k) (hk2 : k < first + R)
    (h : bankRepairDigitLeadW R first k o i b = 0) : b = false ∧ DigitLeadingInput i := by
  rw [bankRepairDigitLeadWSeg R first k hk1] at h
  exact ⟨bankRepairDigitLiveWZero (first + R - k) b (by omega) (by omega),
    bankRepairDigitSegInWZero R (first + R - k) i (by omega) (by omega)⟩

theorem bankRepairDigitTailWMono (R a : Nat) :
    ∀ j, bankRepairDigitTailW R a ≤ bankRepairDigitTailW R (a + j)
  | 0 => Nat.le_refl _
  | j + 1 => by
      have := bankRepairDigitTailWMono R a j
      show _ ≤ bankRepairDigitTailW R (a + j) + (a + j) + 2 * R + 5
      omega

theorem bankRepairDigitTailWUpper (R : Nat) :
    ∀ a, bankRepairDigitTailW R a ≤ (a + 1) * (a + 2 * R + 5)
  | 0 => by
      show bankRepairDigitTailW R 0 ≤ (0 + 1) * (0 + 2 * R + 5)
      simp only [bankRepairDigitTailW]
      omega
  | a + 1 => by
      have ih := bankRepairDigitTailWUpper R a
      show bankRepairDigitTailW R a + a + 2 * R + 5 ≤ (a + 1 + 1) * (a + 1 + 2 * R + 5)
      rw [show a + 1 + 2 * R + 5 = (a + 2 * R + 5) + 1 by omega, Nat.add_mul (a + 1) 1,
        Nat.mul_add (a + 1) (a + 2 * R + 5) 1, Nat.one_mul, Nat.mul_one]
      omega

theorem bankRepairDigitPreOutWLe {A : Nat} (R a : Nat) (o : OutTok A) (ha : 1 ≤ a) :
    bankRepairDigitPreOutW R a o ≤ bankRepairDigitTailW R a := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have hp := bankRepairDigitTailWPos R b
  have e : bankRepairDigitTailW R (b + 1) = bankRepairDigitTailW R b + b + 2 * R + 5 := rfl
  cases o with
  | E => exact Nat.zero_le _
  | U => simp only [bankRepairDigitPreOutW]; omega
  | D v T => cases T <;> simp [bankRepairDigitPreOutW] <;> omega

theorem bankRepairDigitSegInWLe {A : Nat} (R a : Nat) (i : InTok A) :
    bankRepairDigitSegInW R a i ≤ a + R + 2 := by
  cases i with
  | E => exact Nat.zero_le _
  | X => simp only [bankRepairDigitSegInW]; omega
  | P v T => simp only [bankRepairDigitSegInW]; omega
  | S v T => cases T <;> simp [bankRepairDigitSegInW] <;> omega

theorem bankRepairDigitLiveWLe (a : Nat) (b : Bool) : bankRepairDigitLiveW a b ≤ a := by
  cases b <;> simp [bankRepairDigitLiveW]

theorem bankRepairDigitDelimInWLe {A : Nat} (R : Nat) (i : InTok A) :
    bankRepairDigitDelimInW R i ≤ 2 * R + 2 := by
  cases i <;> simp only [bankRepairDigitDelimInW] <;> omega

theorem bankRepairDigitLeadWLePre {A : Nat} (R first k : Nat) (o : OutTok A) (i : InTok A)
    (b : Bool) (hk1 : 1 ≤ k) (hk : k < first) :
    bankRepairDigitLeadW R first k o i b ≤
      bankRepairDigitTailW R (first - 1) + 2 * (first - 1) + R + 2 := by
  rw [bankRepairDigitLeadWPre R first k hk]
  have h1 := bankRepairDigitPreOutWLe R (first - k) o (by omega)
  have h2 := bankRepairDigitTailWMono R (first - k) (k - 1)
  rw [show first - k + (k - 1) = first - 1 by omega] at h2
  have h3 := bankRepairDigitSegInWLe R (first - k) i
  have h4 := bankRepairDigitLiveWLe (first - k) b
  omega

theorem bankRepairDigitLeadWLeSeg {A : Nat} (R first k : Nat) (o : OutTok A) (i : InTok A)
    (b : Bool) (_hR : 1 ≤ R) (hk1 : first ≤ k) (hk2 : k < first + R) :
    bankRepairDigitLeadW R first k o i b ≤ 3 * R + 2 := by
  by_cases hkf : k = first
  · rw [bankRepairDigitLeadWDelim R first k hkf]
    have h1 := bankRepairDigitDelimInWLe R i
    have h2 := bankRepairDigitLiveWLe R b
    omega
  · rw [bankRepairDigitLeadWSeg R first k (by omega)]
    have h1 := bankRepairDigitSegInWLe R (first + R - k) i
    have h2 := bankRepairDigitLiveWLe (first + R - k) b
    omega

/-- The per-offset cap used for the initial bound. -/
def bankRepairDigitLeadCapW (R first k : Nat) : Nat :=
  if k < first then 2 * (bankRepairDigitTailW R (first - 1) + 2 * (first - 1) + R + 2)
  else 2 * (3 * R + 2)

/-- The polynomial comparison with `J`. -/
theorem bankRepairDigitLeadBudgetArith (m R Q A : Nat) (hQ : Q = m * (m + 1)) (hA : A ≤ m) :
    2 * (A * (bankRepairDigitTailW R A + 2 * A + R + 2) + R * (3 * R + 2)) ≤
      2 * (Q * (m + 1) + (Q + R) * (R + 2) + 2 * (Q + R + R) * (R + 2) + 2 * R + m ^ 2 + 1) := by
  have hTm : bankRepairDigitTailW R A ≤ bankRepairDigitTailW R m := by
    have := bankRepairDigitTailWMono R A (m - A)
    rwa [show A + (m - A) = m by omega] at this
  have hU := bankRepairDigitTailWUpper R m
  have c1 : A * (bankRepairDigitTailW R A + 2 * A + R + 2) ≤
      m * ((m + 1) * (m + 2 * R + 5) + (2 * m + R + 2)) :=
    Nat.mul_le_mul hA (by omega)
  have c2 : m * ((m + 1) * (m + 2 * R + 5) + (2 * m + R + 2)) =
      Q * (m + 1) + Q * (R + 2) + Q * (R + 2) + m * (2 * m + R + 2) := by
    rw [Nat.mul_add m ((m + 1) * (m + 2 * R + 5)) (2 * m + R + 2),
      ← Nat.mul_assoc m (m + 1) (m + 2 * R + 5), ← hQ,
      show m + 2 * R + 5 = (m + 1) + (R + 2) + (R + 2) by omega,
      Nat.mul_add Q ((m + 1) + (R + 2)) (R + 2), Nat.mul_add Q (m + 1) (R + 2)]
  have c3 : m * (2 * m + R + 2) ≤ Q * (R + 2) := by
    have h : 2 * m + R + 2 ≤ (m + 1) * (R + 2) := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_add]
      omega
    rw [hQ, Nat.mul_assoc]
    exact Nat.mul_le_mul_left m h
  have c4 : (Q + R) * (R + 2) = Q * (R + 2) + R * (R + 2) := Nat.add_mul Q R (R + 2)
  have c5 : 2 * (Q + R + R) * (R + 2) =
      2 * (Q * (R + 2)) + 2 * (R * (R + 2)) + 2 * (R * (R + 2)) := by
    rw [Nat.mul_assoc 2 (Q + R + R) (R + 2), Nat.add_mul (Q + R) R (R + 2),
      Nat.add_mul Q R (R + 2)]
    omega
  have c6 : R * (3 * R + 2) ≤ 3 * (R * (R + 2)) := by
    rw [Nat.mul_left_comm 3 R (R + 2)]
    exact Nat.mul_le_mul_left R (by omega)
  omega

/-- The leading budget fits `2 J_s` whenever the prefix has at most `m_s` offsets. -/
theorem bankRepairDigitLeadBudgetFits (s A : Nat) (hA : A ≤ bankRepairDigitLeadingRecords s) :
    2 * (A * (bankRepairDigitTailW (bankRepairDigitRadius s) A + 2 * A +
        bankRepairDigitRadius s + 2) +
      bankRepairDigitRadius s * (3 * bankRepairDigitRadius s + 2)) ≤
    2 * bankRepairDigitBoundaryServices s :=
  bankRepairDigitLeadBudgetArith (bankRepairDigitLeadingRecords s) (bankRepairDigitRadius s)
    (bankRepairDigitLeadingSquare s) A rfl hA

/-! ### The leading rank on the projected ring -/

def bankRepairDigitLeadRankOf {c : Compiled} {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (R first : Nat) (S : Fin n → ProjD c) : Nat :=
  bankRepairDigitSumCnt
    (fun k => bankRepairDigitLeadSiteW R first k (S (digitSite ring root k)).top) 1
    (min (first + R) n - 1)

theorem bankRepairDigitSiteSurj {n : Nat} (ring : DirectedRing n) (root : Fin n) (e : Fin n) :
    ∃ k, k < n ∧ digitSite ring root k = e := by
  have he := e.isLt
  have hr := root.isLt
  refine ⟨(e.val + n - root.val) % n, Nat.mod_lt _ (by omega), ?_⟩
  apply Fin.ext
  rw [bankRepairDigitSiteVal, Nat.add_mod_mod,
    show root.val + (e.val + n - root.val) = e.val + n by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt he]

theorem bankRepairDigitLeadEdgeSites {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (hn : 2 ≤ n) (root : Fin n) (S : Fin n → ProjD c) (k : Nat) (hk : k < n)
    (hbX : (pairW (S (digitSite ring root k)).word (S (digitSite ring root (k + 1))).word).1.beta =
      (S (digitSite ring root k)).word.beta)
    (hbY : (pairW (S (digitSite ring root k)).word (S (digitSite ring root (k + 1))).word).2.beta =
      (S (digitSite ring root (k + 1))).word.beta) :
    (phiD ring S (digitSite ring root k) (digitSite ring root k)).top =
        (bankRepairDigitTopPairOf c (S (digitSite ring root k))
          (S (digitSite ring root (k + 1)))).x ∧
    (phiD ring S (digitSite ring root k) (digitSite ring root (k + 1))).top =
        (bankRepairDigitTopPairOf c (S (digitSite ring root k))
          (S (digitSite ring root (k + 1)))).y ∧
    ∀ i, 0 < i → i < n → i ≠ k → i ≠ k + 1 →
      phiD ring S (digitSite ring root k) (digitSite ring root i) = S (digitSite ring root i) := by
  obtain ⟨h1, h2, h3, _⟩ := bankRepairDigitPhiDAt ring hn S (digitSite ring root k) hbX hbY
  refine ⟨h1, h2, fun i hi0 hin hik hik1 => h3 _ ?_ ?_⟩
  · intro h
    exact hik (bankRepairDigitSiteInj ring root hin hk h)
  · intro h
    by_cases hk1 : k + 1 < n
    · exact hik1 (bankRepairDigitSiteInj ring root hin hk1 h)
    · have hkn : k + 1 = n := by omega
      rw [show ring.rightNeighbor (digitSite ring root k) = digitSite ring root (k + 1) from rfl,
        hkn, bankRepairDigitSiteN] at h
      have := bankRepairDigitSiteInj ring root hin (by omega : 0 < n)
        (h.trans (rfl : root = digitSite ring root 0))
      omega

theorem bankRepairDigitLeadBetaFalse {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → ProjD c) (R first : Nat)
    (hbeta : ∀ k, 0 < k → k < n →
      ((S (digitSite ring root k)).word.beta = true ↔ first ≤ k ∧ (k - first) % R = 0))
    (k : Nat) (hk0 : 0 < k) (hkn : k < n) (h : first ≤ k → (k - first) % R ≠ 0) :
    (S (digitSite ring root k)).word.beta = false := by
  cases hb : (S (digitSite ring root k)).word.beta with
  | false => rfl
  | true =>
      have := (hbeta k hk0 hkn).1 hb
      exact absurd this.2 (h this.1)

theorem bankRepairDigitLeadBetaTrue {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → ProjD c) (R first : Nat)
    (hbeta : ∀ k, 0 < k → k < n →
      ((S (digitSite ring root k)).word.beta = true ↔ first ≤ k ∧ (k - first) % R = 0))
    (k : Nat) (hk0 : 0 < k) (hkn : k < n) (h1 : first ≤ k) (h2 : (k - first) % R = 0) :
    (S (digitSite ring root k)).word.beta = true :=
  (hbeta k hk0 hkn).2 ⟨h1, h2⟩

/-- All leading weights zero is exactly the leading half of the receipt. -/
theorem bankRepairDigitLeadBoundaryOfZero {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → ProjD c) (R first : Nat) (hR : 2 ≤ R) (hf0 : 0 < first)
    (hfn : first < n)
    (hbeta : ∀ k, 0 < k → k < n →
      ((S (digitSite ring root k)).word.beta = true ↔ first ≤ k ∧ (k - first) % R = 0))
    (hz : ∀ i, 1 ≤ i → i < min (first + R) n →
      bankRepairDigitLeadSiteW R first i (S (digitSite ring root i)).top = 0) :
    DigitLeadingBoundary ring root S := by
  have hfirst : DigitNonrootDelimiter ring root S first :=
    ⟨hf0, hfn, bankRepairDigitLeadBetaTrue ring root S R first hbeta first hf0 hfn
      (Nat.le_refl _) (by rw [Nat.sub_self, Nat.zero_mod])⟩
  refine ⟨first, min (first + R) n,
    ⟨⟨hfirst, fun k hk0 hk1 => bankRepairDigitLeadBetaFalse ring root S R first hbeta k hk0
        (by omega) (fun h => absurd h (by omega))⟩,
      hfirst, by omega, by omega,
      fun hlt => bankRepairDigitLeadBetaTrue ring root S R first hbeta _ (by omega) hlt
        (by omega) (by rw [show min (first + R) n - first = R by omega, Nat.mod_self]),
      fun k hk0 hk1 => bankRepairDigitLeadBetaFalse ring root S R first hbeta k (by omega)
        (by omega) (fun _ => by
          rw [Nat.mod_eq_of_lt (show k - first < R by omega)]
          omega)⟩, ?_, ?_⟩
  · intro lane k hk0 hk1
    have h0 := hz k hk0 (by omega)
    unfold bankRepairDigitLeadSiteW at h0
    have hw := bankRepairDigitLeadWZeroPre hk1
      (show bankRepairDigitLeadW R first k (S (digitSite ring root k)).top.wOut
        (S (digitSite ring root k)).top.wIn (S (digitSite ring root k)).top.wCarry.isW = 0
        by omega)
    have hq := bankRepairDigitLeadWZeroPre hk1
      (show bankRepairDigitLeadW R first k (S (digitSite ring root k)).top.qOut
        (S (digitSite ring root k)).top.qIn (S (digitSite ring root k)).top.qCarry.isL = 0
        by omega)
    obtain ⟨e1, e2, e3⟩ := bankRepairDigitEndpointViewLane lane S (digitSite ring root k)
    dsimp only
    rw [e1, e2, e3]
    cases lane
    · exact hw
    · exact hq
  · intro lane k hk0 hk1
    have h0 := hz k (by omega) hk1
    unfold bankRepairDigitLeadSiteW at h0
    have hw0 : bankRepairDigitLeadW R first k (S (digitSite ring root k)).top.wOut
        (S (digitSite ring root k)).top.wIn (S (digitSite ring root k)).top.wCarry.isW = 0 := by
      omega
    have hq0 : bankRepairDigitLeadW R first k (S (digitSite ring root k)).top.qOut
        (S (digitSite ring root k)).top.qIn (S (digitSite ring root k)).top.qCarry.isL = 0 := by
      omega
    have hseg : BankRepairDigitSegOK n first k
        (bankRepairDigitLaneLive lane (S (digitSite ring root k)).top)
        (bankRepairDigitLaneIn lane (S (digitSite ring root k)).top) := by
      unfold BankRepairDigitSegOK
      refine Or.inr ?_
      by_cases hkf : k = first
      · have hw := bankRepairDigitLeadWZeroDelim (by omega) hkf hw0
        have hq := bankRepairDigitLeadWZeroDelim (by omega) hkf hq0
        rw [if_pos hkf]
        cases lane
        · exact hw
        · exact hq
      · have hw := bankRepairDigitLeadWZeroSeg (by omega) (by omega) hw0
        have hq := bankRepairDigitLeadWZeroSeg (by omega) (by omega) hq0
        rw [if_neg hkf]
        cases lane
        · exact hw
        · exact hq
    obtain ⟨e1, _, e3⟩ := bankRepairDigitEndpointViewLane lane S (digitSite ring root k)
    dsimp only [DigitLastCarryInert]
    rw [e1, e3]
    exact hseg

/-- No edge increases the leading rank. -/
theorem bankRepairDigitLeadRankStep {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (hn : 2 ≤ n) (root : Fin n) (S : Fin n → ProjD c) (R first : Nat) (hR : 2 ≤ R)
    (hfn : first < n)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (hbeta : ∀ k, 0 < k → k < n →
      ((S (digitSite ring root k)).word.beta = true ↔ first ≤ k ∧ (k - first) % R = 0))
    (k : Nat) (hk : k < n)
    (hbX : (pairW (S (digitSite ring root k)).word (S (digitSite ring root (k + 1))).word).1.beta =
      (S (digitSite ring root k)).word.beta)
    (hbY : (pairW (S (digitSite ring root k)).word (S (digitSite ring root (k + 1))).word).2.beta =
      (S (digitSite ring root (k + 1))).word.beta) :
    bankRepairDigitLeadRankOf ring root R first (phiD ring S (digitSite ring root k)) ≤
      bankRepairDigitLeadRankOf ring root R first S := by
  obtain ⟨hPX, hPY, hPo⟩ := bankRepairDigitLeadEdgeSites ring hn root S k hk hbX hbY
  unfold bankRepairDigitLeadRankOf
  generalize phiD ring S (digitSite ring root k) = T at hPX hPY hPo ⊢
  have hsame : ∀ i, 0 < i → i < n → i ≠ k → i ≠ k + 1 →
      bankRepairDigitLeadSiteW R first i (T (digitSite ring root i)).top =
        bankRepairDigitLeadSiteW R first i (S (digitSite ring root i)).top := by
    intro i h1 h2 h3 h4
    rw [hPo i h1 h2 h3 h4]
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · -- the leader edge `(root, 1)`
    have hxl : (S (digitSite ring root k)).word.native.l = true :=
      (hroot _).2 (by rw [hk0]; rfl)
    have hz := (bankRepairDigitLeadResetD c (S (digitSite ring root k))
      (S (digitSite ring root (k + 1))) R first k (k + 1) (by rw [hxl]; rfl)).2
    apply bankRepairDigitSumCntMono
    intro i hi1 hi2
    try dsimp only
    by_cases hi : i = k + 1
    · subst hi
      rw [hPY, hz]
      exact Nat.zero_le _
    · exact Nat.le_of_eq (hsame i (by omega) (by omega) (by omega) hi)
  by_cases hkn : k + 1 = n
  · -- the leader edge `(n - 1, root)`
    have hyl : (S (digitSite ring root (k + 1))).word.native.l = true :=
      (hroot _).2 (by rw [hkn, bankRepairDigitSiteN])
    have hz := (bankRepairDigitLeadResetD c (S (digitSite ring root k))
      (S (digitSite ring root (k + 1))) R first k (k + 1) (by rw [hyl, Bool.or_true])).1
    apply bankRepairDigitSumCntMono
    intro i hi1 hi2
    try dsimp only
    by_cases hi : i = k
    · subst hi
      rw [hPX, hz]
      exact Nat.zero_le _
    · exact Nat.le_of_eq (hsame i (by omega) (by omega) hi (by omega))
  have hxl := bankRepairDigitSiteNonroot ring root S hroot k hk0 hk
  have hyl := bankRepairDigitSiteNonroot ring root S hroot (k + 1) (by omega) (by omega)
  have hout : ∀ i, 1 ≤ i → i < 1 + (min (first + R) n - 1) → i ≠ k → i ≠ k + 1 →
      bankRepairDigitLeadSiteW R first i (T (digitSite ring root i)).top ≤
        bankRepairDigitLeadSiteW R first i (S (digitSite ring root i)).top :=
    fun i h1 h2 h3 h4 => Nat.le_of_eq (hsame i (by omega) (by omega) h3 h4)
  by_cases ha : k + 1 < first
  · have hp := bankRepairDigitLeadPairPreD c _ _ R first k ha hxl hyl
      (bankRepairDigitLeadBetaFalse ring root S R first hbeta k hk0 hk
        (fun h => absurd h (by omega)))
      (bankRepairDigitLeadBetaFalse ring root S R first hbeta (k + 1) (by omega) (by omega)
        (fun h => absurd h (by omega)))
    refine Nat.le_trans (Nat.le_add_right _ 0)
      (bankRepairDigitSumCntPair _ _ 1 k 0 _ hout (by omega) (by omega) ?_)
    try dsimp only
    rw [hPX, hPY]
    omega
  by_cases hb : k + 1 = first
  · have hp := bankRepairDigitLeadPairIntoD c _ _ R first k hb hxl hyl
      (bankRepairDigitLeadBetaFalse ring root S R first hbeta k hk0 hk
        (fun h => absurd h (by omega)))
      (bankRepairDigitLeadBetaTrue ring root S R first hbeta (k + 1) (by omega) (by omega)
        (by omega) (by rw [show k + 1 - first = 0 by omega, Nat.zero_mod]))
    refine Nat.le_trans (Nat.le_add_right _ 0)
      (bankRepairDigitSumCntPair _ _ 1 k 0 _ hout (by omega) (by omega) ?_)
    try dsimp only
    rw [hPX, hPY]
    omega
  by_cases hc : k = first
  · have hp := bankRepairDigitLeadPairFromD c _ _ R first k hR hc hxl hyl
      (bankRepairDigitLeadBetaTrue ring root S R first hbeta k hk0 hk (by omega)
        (by rw [show k - first = 0 by omega, Nat.zero_mod]))
      (bankRepairDigitLeadBetaFalse ring root S R first hbeta (k + 1) (by omega) (by omega)
        (fun _ => by
          rw [show k + 1 - first = 1 by omega, Nat.mod_eq_of_lt (show 1 < R by omega)]
          omega))
    refine Nat.le_trans (Nat.le_add_right _ 0)
      (bankRepairDigitSumCntPair _ _ 1 k 0 _ hout (by omega) (by omega) ?_)
    try dsimp only
    rw [hPX, hPY]
    omega
  by_cases hd : k + 1 < min (first + R) n
  · have hp := bankRepairDigitLeadPairSegD c _ _ R first k (by omega) (by omega) hxl hyl
      (bankRepairDigitLeadBetaFalse ring root S R first hbeta k hk0 hk (fun _ => by
        rw [Nat.mod_eq_of_lt (show k - first < R by omega)]
        omega))
      (bankRepairDigitLeadBetaFalse ring root S R first hbeta (k + 1) (by omega) (by omega)
        (fun _ => by
          rw [Nat.mod_eq_of_lt (show k + 1 - first < R by omega)]
          omega))
    refine Nat.le_trans (Nat.le_add_right _ 0)
      (bankRepairDigitSumCntPair _ _ 1 k 0 _ hout (by omega) (by omega) ?_)
    try dsimp only
    rw [hPX, hPY]
    omega
  by_cases he : k + 1 = min (first + R) n
  · have hkR : k + 1 = first + R := by omega
    have hp := bankRepairDigitLeadOutOfSegD c _ _ R first k (by omega) hkR hxl hyl
      (bankRepairDigitLeadBetaFalse ring root S R first hbeta k hk0 hk (fun _ => by
        rw [Nat.mod_eq_of_lt (show k - first < R by omega)]
        omega))
      (bankRepairDigitLeadBetaTrue ring root S R first hbeta (k + 1) (by omega) (by omega)
        (by omega) (by rw [show k + 1 - first = R by omega, Nat.mod_self]))
    apply bankRepairDigitSumCntMono
    intro i hi1 hi2
    try dsimp only
    by_cases hi : i = k
    · subst hi
      rw [hPX]
      exact hp
    · exact Nat.le_of_eq (hsame i (by omega) (by omega) hi (by omega))
  · apply bankRepairDigitSumCntMono
    intro i hi1 hi2
    try dsimp only
    exact Nat.le_of_eq (hsame i (by omega) (by omega) (by omega) (by omega))

/-- Off the leading receipt, some edge drops the leading rank. -/
theorem bankRepairDigitLeadRankDrop {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (hn : 2 ≤ n) (root : Fin n) (S : Fin n → ProjD c) (R first : Nat) (hR : 2 ≤ R)
    (hf0 : 0 < first) (hfn : first < n)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (hbeta : ∀ k, 0 < k → k < n →
      ((S (digitSite ring root k)).word.beta = true ↔ first ≤ k ∧ (k - first) % R = 0))
    (hbXY : ∀ k, k < n →
      (pairW (S (digitSite ring root k)).word (S (digitSite ring root (k + 1))).word).1.beta =
        (S (digitSite ring root k)).word.beta ∧
      (pairW (S (digitSite ring root k)).word (S (digitSite ring root (k + 1))).word).2.beta =
        (S (digitSite ring root (k + 1))).word.beta)
    (hnot : ¬ DigitLeadingBoundary ring root S) :
    ∃ k, k < n ∧
      bankRepairDigitLeadRankOf ring root R first (phiD ring S (digitSite ring root k)) + 1 ≤
        bankRepairDigitLeadRankOf ring root R first S := by
  have hpos : ∃ i, 1 ≤ i ∧ i < 1 + (min (first + R) n - 1) ∧
      0 < bankRepairDigitLeadSiteW R first i (S (digitSite ring root i)).top := by
    refine Classical.byContradiction (fun hno => hnot ?_)
    refine bankRepairDigitLeadBoundaryOfZero ring root S R first hR hf0 hfn hbeta ?_
    intro i h1 h2
    exact Nat.eq_zero_of_not_pos (fun hp => hno ⟨i, h1, by omega, hp⟩)
  obtain ⟨k, hk1, hk2, hkpos, hkmax⟩ := bankRepairDigitRightmost
    (fun i => bankRepairDigitLeadSiteW R first i (S (digitSite ring root i)).top) 1 _ hpos
  try dsimp only at hkpos hkmax
  have hk : k < n := by omega
  obtain ⟨hbX, hbY⟩ := hbXY k hk
  refine ⟨k, hk, ?_⟩
  obtain ⟨hPX, hPY, hPo⟩ := bankRepairDigitLeadEdgeSites ring hn root S k hk hbX hbY
  unfold bankRepairDigitLeadRankOf
  generalize phiD ring S (digitSite ring root k) = T at hPX hPY hPo ⊢
  have hsame : ∀ i, 0 < i → i < n → i ≠ k → i ≠ k + 1 →
      bankRepairDigitLeadSiteW R first i (T (digitSite ring root i)).top =
        bankRepairDigitLeadSiteW R first i (S (digitSite ring root i)).top := by
    intro i h1 h2 h3 h4
    rw [hPo i h1 h2 h3 h4]
  have hxl := bankRepairDigitSiteNonroot ring root S hroot k (by omega) hk
  by_cases hkn : k + 1 = n
  · have hyl : (S (digitSite ring root (k + 1))).word.native.l = true :=
      (hroot _).2 (by rw [hkn, bankRepairDigitSiteN])
    have hz := (bankRepairDigitLeadResetD c (S (digitSite ring root k))
      (S (digitSite ring root (k + 1))) R first k (k + 1) (by rw [hyl, Bool.or_true])).1
    refine bankRepairDigitSumCntPoint _ _ 1 k 1 _ ?_ (by omega) (by omega) ?_
    · intro i hi1 hi2 hi
      try dsimp only
      exact Nat.le_of_eq (hsame i (by omega) (by omega) hi (by omega))
    · try dsimp only
      rw [hPX, hz]
      omega
  have hyl := bankRepairDigitSiteNonroot ring root S hroot (k + 1) (by omega) (by omega)
  have hout : ∀ i, 1 ≤ i → i < 1 + (min (first + R) n - 1) → i ≠ k → i ≠ k + 1 →
      bankRepairDigitLeadSiteW R first i (T (digitSite ring root i)).top ≤
        bankRepairDigitLeadSiteW R first i (S (digitSite ring root i)).top :=
    fun i h1 h2 h3 h4 => Nat.le_of_eq (hsame i (by omega) (by omega) h3 h4)
  by_cases ha : k + 1 < first
  · have hp := bankRepairDigitLeadPairPreStrictD c _ _ R first k ha hxl hyl
      (bankRepairDigitLeadBetaFalse ring root S R first hbeta k (by omega) hk
        (fun h => absurd h (by omega)))
      (bankRepairDigitLeadBetaFalse ring root S R first hbeta (k + 1) (by omega) (by omega)
        (fun h => absurd h (by omega)))
      hkpos (hkmax (k + 1) (by omega) (by omega))
    refine bankRepairDigitSumCntPair _ _ 1 k 1 _ hout (by omega) (by omega) ?_
    try dsimp only
    rw [hPX, hPY]
    exact hp
  by_cases hb : k + 1 = first
  · have hp := bankRepairDigitLeadPairIntoStrictD c _ _ R first k (by omega) hb hxl hyl
      (bankRepairDigitLeadBetaFalse ring root S R first hbeta k (by omega) hk
        (fun h => absurd h (by omega)))
      (bankRepairDigitLeadBetaTrue ring root S R first hbeta (k + 1) (by omega) (by omega)
        (by omega) (by rw [show k + 1 - first = 0 by omega, Nat.zero_mod]))
      hkpos (hkmax (k + 1) (by omega) (by omega))
    refine bankRepairDigitSumCntPair _ _ 1 k 1 _ hout (by omega) (by omega) ?_
    try dsimp only
    rw [hPX, hPY]
    exact hp
  by_cases hc : k = first
  · have hp := bankRepairDigitLeadPairFromStrictD c _ _ R first k hR hc hxl hyl
      (bankRepairDigitLeadBetaTrue ring root S R first hbeta k (by omega) hk (by omega)
        (by rw [show k - first = 0 by omega, Nat.zero_mod]))
      (bankRepairDigitLeadBetaFalse ring root S R first hbeta (k + 1) (by omega) (by omega)
        (fun _ => by
          rw [show k + 1 - first = 1 by omega, Nat.mod_eq_of_lt (show 1 < R by omega)]
          omega))
      hkpos (hkmax (k + 1) (by omega) (by omega))
    refine bankRepairDigitSumCntPair _ _ 1 k 1 _ hout (by omega) (by omega) ?_
    try dsimp only
    rw [hPX, hPY]
    exact hp
  by_cases hd : k + 1 < min (first + R) n
  · have hp := bankRepairDigitLeadPairSegStrictD c _ _ R first k (by omega) (by omega) hxl hyl
      (bankRepairDigitLeadBetaFalse ring root S R first hbeta k (by omega) hk (fun _ => by
        rw [Nat.mod_eq_of_lt (show k - first < R by omega)]
        omega))
      (bankRepairDigitLeadBetaFalse ring root S R first hbeta (k + 1) (by omega) (by omega)
        (fun _ => by
          rw [Nat.mod_eq_of_lt (show k + 1 - first < R by omega)]
          omega))
      hkpos (hkmax (k + 1) (by omega) (by omega))
    refine bankRepairDigitSumCntPair _ _ 1 k 1 _ hout (by omega) (by omega) ?_
    try dsimp only
    rw [hPX, hPY]
    exact hp
  · have hkR : k + 1 = first + R := by omega
    have hp := bankRepairDigitLeadOutOfSegStrictD c _ _ R first k (by omega) hkR hxl hyl
      (bankRepairDigitLeadBetaFalse ring root S R first hbeta k (by omega) hk (fun _ => by
        rw [Nat.mod_eq_of_lt (show k - first < R by omega)]
        omega))
      (bankRepairDigitLeadBetaTrue ring root S R first hbeta (k + 1) (by omega) (by omega)
        (by omega) (by rw [show k + 1 - first = R by omega, Nat.mod_self]))
      hkpos
    refine bankRepairDigitSumCntPoint _ _ 1 k 1 _ ?_ (by omega) (by omega) ?_
    · intro i hi1 hi2 hi
      try dsimp only
      exact Nat.le_of_eq (hsame i (by omega) (by omega) hi (by omega))
    · try dsimp only
      rw [hPX]
      exact hp

/-- The initial size of the leading rank. -/
theorem bankRepairDigitLeadRankOfBound {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → ProjD c) (R first : Nat) (hR : 1 ≤ R) (hf : 1 ≤ first) :
    bankRepairDigitLeadRankOf ring root R first S ≤
      2 * ((first - 1) * (bankRepairDigitTailW R (first - 1) + 2 * (first - 1) + R + 2) +
        R * (3 * R + 2)) := by
  unfold bankRepairDigitLeadRankOf
  have hext := bankRepairDigitSumCntExtend
    (fun k => bankRepairDigitLeadSiteW R first k (S (digitSite ring root k)).top)
    (bankRepairDigitLeadCapW R first) 1 (min (first + R) n - 1) (first - 1 + R) (by omega)
    (by
      intro i hi1 hi2
      try dsimp only
      unfold bankRepairDigitLeadSiteW bankRepairDigitLeadCapW
      by_cases hif : i < first
      · rw [if_pos hif]
        have h1 := bankRepairDigitLeadWLePre R first i (S (digitSite ring root i)).top.wOut
          (S (digitSite ring root i)).top.wIn (S (digitSite ring root i)).top.wCarry.isW hi1 hif
        have h2 := bankRepairDigitLeadWLePre R first i (S (digitSite ring root i)).top.qOut
          (S (digitSite ring root i)).top.qIn (S (digitSite ring root i)).top.qCarry.isL hi1 hif
        omega
      · rw [if_neg hif]
        have h1 := bankRepairDigitLeadWLeSeg R first i (S (digitSite ring root i)).top.wOut
          (S (digitSite ring root i)).top.wIn (S (digitSite ring root i)).top.wCarry.isW hR
          (by omega) (by omega)
        have h2 := bankRepairDigitLeadWLeSeg R first i (S (digitSite ring root i)).top.qOut
          (S (digitSite ring root i)).top.qIn (S (digitSite ring root i)).top.qCarry.isL hR
          (by omega) (by omega)
        omega)
  have hsplit := bankRepairDigitSumCntAdd (bankRepairDigitLeadCapW R first) 1 (first - 1) R
  have hb1 := bankRepairDigitSumCntBound (bankRepairDigitLeadCapW R first) 1
    (2 * (bankRepairDigitTailW R (first - 1) + 2 * (first - 1) + R + 2)) (first - 1)
    (fun i _ hi2 => Nat.le_of_eq (if_pos (show i < first by omega)))
  have hb2 := bankRepairDigitSumCntBound (bankRepairDigitLeadCapW R first) (1 + (first - 1))
    (2 * (3 * R + 2)) R
    (fun i hi1 _ => Nat.le_of_eq (if_neg (show ¬ i < first by omega)))
  have e1 := Nat.mul_left_comm (first - 1) 2
    (bankRepairDigitTailW R (first - 1) + 2 * (first - 1) + R + 2)
  have e2 := Nat.mul_left_comm R 2 (3 * R + 2)
  omega

/-! ### The leading rank on the BANK chain -/

/-- Layout data of the leading rank: fixed leader `root` and first delimiter `first`. -/
def BankRepairDigitLeadData {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (first : Nat)
    (z : BankReferenceState ring hbank) : Prop :=
  BankRepairDigitLayoutFixed ring hbank root z ∧ 0 < first ∧ first < n ∧
    ∀ k : Nat, 0 < k → k < n →
      ((piD z.val.1 (digitSite ring root k)).word.beta = true ↔
        first ≤ k ∧ (k - first) % digitSpan (compileAdvice (ceilLogTwo n)) = 0)

theorem bankRepairDigitLeadBankEdge {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n)
    (z : BankReferenceState ring hbank) (hz : BankRepairDigitLayoutFixed ring hbank root z)
    (e : Fin n) :
    piD (bankRepairNext ring hbank z e).val.1 = phiD ring (piD z.val.1) e ∧
    (∀ i, (piD z.val.1 i).word.native.l = true ↔ i = root) ∧
    (pairW (piD z.val.1 e).word (piD z.val.1 (ring.rightNeighbor e)).word).1.beta =
      (piD z.val.1 e).word.beta ∧
    (pairW (piD z.val.1 e).word (piD z.val.1 (ring.rightNeighbor e)).word).2.beta =
      (piD z.val.1 (ring.rightNeighbor e)).word.beta := by
  refine ⟨bankRepairDigitMaskedProjectionOfNoFire ring hbank z e
    (bankRepairDigitBoundaryNoFireOfSingleton ring hbank root z hz.1 e), ?_⟩
  have hnb := (AcceptedReceipts.qword_step ring _ hz.2 e).1
  have hvis : ∀ i, AcceptedReceipts.wordVisible (phiW ring (piW z.val.1) e) i =
      AcceptedReceipts.wordVisible (piW z.val.1) i := by
    intro i
    exact Classical.byContradiction (fun hne => hnb ⟨i, hne⟩)
  have hne : ring.rightNeighbor e ≠ e := bankRepairDigitRightNe ring (by omega) e
  have hbX := congrArg Prod.snd (hvis e)
  have hbY := congrArg Prod.snd (hvis (ring.rightNeighbor e))
  simp only [AcceptedReceipts.wordVisible, phiW, projectedEdge, if_pos rfl,
    if_neg hne] at hbX hbY
  refine ⟨fun i => ⟨fun hi => hz.1.2.2.1 i hi, ?_⟩, hbX, hbY⟩
  rintro rfl
  exact hz.1.2.1

theorem bankRepairDigitLeadDataStep {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (first : Nat)
    (z : BankReferenceState ring hbank) (hd : BankRepairDigitLeadData ring hbank root first z)
    (e : Fin n) :
    BankRepairDigitLeadData ring hbank root first (bankRepairNext ring hbank z e) := by
  obtain ⟨hL, h0, h1, hb⟩ := hd
  obtain ⟨heq, _, hbX, hbY⟩ := bankRepairDigitLeadBankEdge ring hn hbank root z hL e
  refine ⟨bankRepairDigitLayoutFixedStep ring hn hbank root z hL e, h0, h1, fun k hk0 hkn => ?_⟩
  rw [heq, (bankRepairDigitPhiDAt ring (by omega) (piD z.val.1) e hbX hbY).2.2.2]
  exact hb k hk0 hkn

theorem bankRepairDigitLeadDataUnique {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root root' : Fin n)
    (first first' : Nat) (z : BankReferenceState ring hbank)
    (h : BankRepairDigitLeadData ring hbank root first z)
    (h' : BankRepairDigitLeadData ring hbank root' first' z) :
    root' = root ∧ first' = first := by
  have hr : root' = root := h.1.1.2.2.1 root' h'.1.1.2.1
  subst hr
  obtain ⟨_, h0, h1, hb⟩ := h
  obtain ⟨_, h0', h1', hb'⟩ := h'
  have a := ((hb first' h0' h1').1 ((hb' first' h0' h1').2
    ⟨Nat.le_refl _, by rw [Nat.sub_self, Nat.zero_mod]⟩)).1
  have b := ((hb' first h0 h1).1 ((hb first h0 h1).2
    ⟨Nat.le_refl _, by rw [Nat.sub_self, Nat.zero_mod]⟩)).1
  exact ⟨rfl, by omega⟩

open Classical in
/-- The leading rank of a BANK state (zero off the layout class). -/
noncomputable def bankRepairDigitLeadRank {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Nat :=
  if h : ∃ (root : Fin n) (first : Nat), BankRepairDigitLeadData ring hbank root first z then
    bankRepairDigitLeadRankOf ring (Classical.choose h)
      (digitSpan (compileAdvice (ceilLogTwo n))) (Classical.choose (Classical.choose_spec h))
      (piD z.val.1)
  else 0

theorem bankRepairDigitLeadRankEq {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (first : Nat)
    (z : BankReferenceState ring hbank) (h : BankRepairDigitLeadData ring hbank root first z) :
    bankRepairDigitLeadRank ring hbank z =
      bankRepairDigitLeadRankOf ring root (digitSpan (compileAdvice (ceilLogTwo n))) first
        (piD z.val.1) := by
  have hex : ∃ (r : Fin n) (f : Nat), BankRepairDigitLeadData ring hbank r f z :=
    ⟨root, first, h⟩
  unfold bankRepairDigitLeadRank
  rw [dif_pos hex]
  obtain ⟨e1, e2⟩ := bankRepairDigitLeadDataUnique ring hbank _ _ _ _ z h
    (Classical.choose_spec (Classical.choose_spec hex))
  rw [e2, e1]

/-- The nominated edge: a dropping edge when one exists. -/
noncomputable def bankRepairDigitLeadChosen {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (e0 : Fin n)
    (z : BankReferenceState ring hbank) : Fin n :=
  if h : ∃ e : Fin n, bankRepairDigitLeadRank ring hbank (bankRepairNext ring hbank z e) + 1 ≤
      bankRepairDigitLeadRank ring hbank z then Classical.choose h else e0

theorem bankRepairDigitLeadChosenSpec {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (e0 : Fin n)
    (z : BankReferenceState ring hbank)
    (h : ∃ e : Fin n, bankRepairDigitLeadRank ring hbank (bankRepairNext ring hbank z e) + 1 ≤
      bankRepairDigitLeadRank ring hbank z) :
    bankRepairDigitLeadRank ring hbank
        (bankRepairNext ring hbank z (bankRepairDigitLeadChosen ring hbank e0 z)) + 1 ≤
      bankRepairDigitLeadRank ring hbank z := by
  unfold bankRepairDigitLeadChosen
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- In the BANK band the leading geometry fits in the ring: `t + (2^t - 1) ≤ n`. -/
theorem bankRepairDigitLeadWidth {n : Nat} (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    (compileAdvice (ceilLogTwo n)).t + digitSpan (compileAdvice (ceilLogTwo n)) ≤ n := by
  have hq : 80 ≤ ceilLogTwo n := bankRepairBankBand hbank
  have ht : (compileAdvice (ceilLogTwo n)).t = ceilLogTwo (ceilLogTwo n) :=
    compileAdvice_t_large _ (by omega)
  have hs : 7 ≤ ceilLogTwo (ceilLogTwo n) := bankRepairDigitWidthBank hbank
  have hpop := bankRepairDigitPopulationLower hn hbank
  unfold digitSpan
  rw [ht]
  unfold bankRepairDigitExponent at hpop
  generalize ceilLogTwo (ceilLogTwo n) = s at hs hpop ⊢
  have h2s : 2 ^ s = 2 * 2 ^ (s - 1) := by
    have := Nat.pow_add 2 (s - 1) 1
    rw [show s - 1 + 1 = s by omega, Nat.pow_one] at this
    omega
  have hE := bankRepairDigitPowLower (s - 1)
  generalize 2 ^ (s - 1) = E at h2s hpop hE
  have hE2 := bankRepairDigitPowLower (E - 2)
  have h4 : 2 ^ E = 2 ^ (E - 2) * 4 := by
    have := Nat.pow_add 2 (E - 2) 2
    rw [show E - 2 + 2 = E by omega] at this
    rw [this]
  omega

theorem bankRepairDigitLeadDataOfGone {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) (hz : BankRepairDigitGoneReachable ring hbank z) :
    ∃ (root : Fin n) (first : Nat), BankRepairDigitLeadData ring hbank root first z ∧
      first + 1 ≤ (compileAdvice (ceilLogTwo n)).t +
        digitSpan (compileAdvice (ceilLogTwo n)) := by
  obtain ⟨root, first, hL, ht, hf, hb⟩ :=
    bankRepairDigitGoneReachableDelimiters ring hn hbank z hz
  have hw := bankRepairDigitLeadWidth hn hbank
  have ht2 := compileAdvice_t_ge_two (ceilLogTwo n)
    (by have := bankRepairBankBand hbank; omega)
  exact ⟨root, first, ⟨hL.1, by omega, by omega, hb⟩, by omega⟩

theorem bankRepairDigitLeadSpanTwo {n : Nat}
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    2 ≤ digitSpan (compileAdvice (ceilLogTwo n)) := by
  have ht2 := compileAdvice_t_ge_two (ceilLogTwo n)
    (by have := bankRepairBankBand hbank; omega)
  have hp := bankRepairDigitPowLower (compileAdvice (ceilLogTwo n)).t
  unfold digitSpan
  omega

/-- STEP 3, leading region: the leading certificate at the paper's budget `2 J`. -/
theorem bankRepairDigitLeadingFlushTasksHold {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    :
    BankRepairDigitLeadingFlushTasks ring hbank
      (2 * bankRepairDigitBoundaryServices (ceilLogTwo (ceilLogTwo n))) := by
  have hR := bankRepairDigitLeadSpanTwo hbank
  unfold BankRepairDigitLeadingFlushTasks BankRepairDigitRegionTasks
  refine ⟨bankRepairDigitLeadRank ring hbank,
    bankRepairDigitLeadChosen ring hbank ⟨0, by omega⟩, ?_, ?_, ?_⟩
  · intro z₀ word hz₀ hnt
    have hz : BankRepairDigitGoneReachable ring hbank
        (word.foldl (bankRepairNext ring hbank) z₀) := ⟨z₀, word, hz₀, rfl⟩
    generalize word.foldl (bankRepairNext ring hbank) z₀ = z at hz hnt ⊢
    obtain ⟨root, first, hd, -⟩ := bankRepairDigitLeadDataOfGone ring hn hbank z hz
    apply bankRepairDigitLeadChosenSpec
    have hnb : ¬ DigitLeadingBoundary ring root (piD z.val.1) := fun hb =>
      hnt ⟨hz, root,
        bankRepairDigitBoundaryWFixedRootOfSingleton ring hn hbank root z hd.1.1 [], hb⟩
    have hedge := fun e => bankRepairDigitLeadBankEdge ring hn hbank root z hd.1 e
    obtain ⟨k, _, hdrop⟩ := bankRepairDigitLeadRankDrop ring (by omega) root (piD z.val.1)
      (digitSpan (compileAdvice (ceilLogTwo n))) first hR hd.2.1 hd.2.2.1 (hedge root).2.1
      hd.2.2.2
      (fun k _ => ⟨(hedge (digitSite ring root k)).2.2.1, (hedge (digitSite ring root k)).2.2.2⟩)
      hnb
    refine ⟨digitSite ring root k, ?_⟩
    rw [bankRepairDigitLeadRankEq ring hbank root first _
        (bankRepairDigitLeadDataStep ring hn hbank root first z hd _),
      bankRepairDigitLeadRankEq ring hbank root first z hd, (hedge _).1]
    exact hdrop
  · intro z₀ word hz₀ _ e
    have hz : BankRepairDigitGoneReachable ring hbank
        (word.foldl (bankRepairNext ring hbank) z₀) := ⟨z₀, word, hz₀, rfl⟩
    generalize word.foldl (bankRepairNext ring hbank) z₀ = z at hz ⊢
    obtain ⟨root, first, hd, -⟩ := bankRepairDigitLeadDataOfGone ring hn hbank z hz
    obtain ⟨k, hk, rfl⟩ := bankRepairDigitSiteSurj ring root e
    have hedge := fun e => bankRepairDigitLeadBankEdge ring hn hbank root z hd.1 e
    rw [bankRepairDigitLeadRankEq ring hbank root first _
        (bankRepairDigitLeadDataStep ring hn hbank root first z hd _),
      bankRepairDigitLeadRankEq ring hbank root first z hd, (hedge _).1]
    exact bankRepairDigitLeadRankStep ring (by omega) root (piD z.val.1)
      (digitSpan (compileAdvice (ceilLogTwo n))) first hR hd.2.2.1 (hedge root).2.1 hd.2.2.2
      k hk (hedge _).2.2.1 (hedge _).2.2.2
  · intro z hz
    obtain ⟨root, first, hd, hfle⟩ :=
      bankRepairDigitLeadDataOfGone ring hn hbank z ⟨z, [], hz, rfl⟩
    rw [bankRepairDigitLeadRankEq ring hbank root first z hd]
    have hq : 80 ≤ ceilLogTwo n := bankRepairBankBand hbank
    have ht : (compileAdvice (ceilLogTwo n)).t = ceilLogTwo (ceilLogTwo n) :=
      compileAdvice_t_large _ (by omega)
    have hspan : digitSpan (compileAdvice (ceilLogTwo n)) =
        bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n)) := by
      unfold digitSpan bankRepairDigitRadius
      rw [ht]
    have hb := bankRepairDigitLeadRankOfBound ring root (piD z.val.1)
      (digitSpan (compileAdvice (ceilLogTwo n))) first (by omega) hd.2.1
    rw [hspan] at hb hfle
    rw [ht] at hfle
    have hA : first - 1 ≤ bankRepairDigitLeadingRecords (ceilLogTwo (ceilLogTwo n)) := by
      unfold bankRepairDigitLeadingRecords
      omega
    rw [hspan]
    exact Nat.le_trans hb (bankRepairDigitLeadBudgetFits _ _ hA)

/-- With the leading region discharged, the flush clock at the remainder charge needs only
the final-region certificate. -/
theorem bankRepairDigitFlushClockOfFinalRegion {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hfin : BankRepairDigitFinalFlushTasks ring hbank
      (bankRepairDigitForwardCount (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) +
        bankRepairDigitReturnCount (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) +
        bankRepairDigitSettledCount (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) +
        bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n)))) :
    BankRepairDigitReceiptFlushClock ring hbank (bankRepairDigitFlushMicroCharge n) :=
  bankRepairDigitFlushClockOfPaperRegions ring hn hbank
    (bankRepairDigitLeadingFlushTasksHold ring hn hbank) hfin

/-- The first-zero clock with the receipt, from every W-stage entrance, conditional only on the
final-region certificate. -/
theorem bankRepairDigitFirstZeroReceiptOfFinalRegion {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (cuts : BankRepairDigitPreDrainCuts ring hbank)
    (hfin : BankRepairDigitFinalFlushTasks ring hbank
      (bankRepairDigitForwardCount (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) +
        bankRepairDigitReturnCount (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) +
        bankRepairDigitSettledCount (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) +
        bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))))
    (hzero : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairDigitBoundaryRetiredCut ring hbank) cuts.firstBlockZero
      (bankRepairDigitFirstZeroMicroCharge n)) :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairDigitWordStageEntrance ring hbank)
      (fun z => cuts.firstBlockZero z ∧ BankRepairDigitLeaderReceipt ring hbank z)
      (bankRepairDigitBoundaryMicroCharge n + bankRepairDigitFirstZeroMicroCharge n) :=
  bankRepairDigitFirstZeroReceiptOfRegions ring hn hbank cuts
    (bankRepairDigitLeadingFlushTasksHold ring hn hbank) hfin hzero

/-- The 201-half pre-drain from every W-stage entrance, conditional only on the final-region
certificate and the later value stages. -/
theorem bankRepairDigitPreDrain201OfFinalRegion {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (cuts : BankRepairDigitPreDrainCuts ring hbank)
    (preDrain : BankReferenceState ring hbank → Prop)
    (hfin : BankRepairDigitFinalFlushTasks ring hbank
      (bankRepairDigitForwardCount (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) +
        bankRepairDigitReturnCount (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) +
        bankRepairDigitSettledCount (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) +
        bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))))
    (hzero : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairDigitBoundaryRetiredCut ring hbank) cuts.firstBlockZero
      (bankRepairDigitFirstZeroMicroCharge n))
    (hwave : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      cuts.firstBlockZero cuts.successorValuesStable
      (bankRepairDigitValueWaveMicroCharge n))
    (hpair : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      cuts.successorValuesStable preDrain
      (bankRepairDigitComparisonMicroCharge n)) :
    BankRepairHalfStage (bankRepairNext ring hbank)
      (BankRepairDigitWordStageEntrance ring hbank) preDrain 201 :=
  bankRepairDigitPreDrain201OfRegions ring hn hbank cuts preDrain
    (bankRepairDigitLeadingFlushTasksHold ring hn hbank) hfin hzero hwave hpair

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankRepairDigitSumCntAdd
#print axioms L3.RenewalReferenceClock.bankRepairDigitSumCntMono
#print axioms L3.RenewalReferenceClock.bankRepairDigitSumCntPoint
#print axioms L3.RenewalReferenceClock.bankRepairDigitSumCntPair
#print axioms L3.RenewalReferenceClock.bankRepairDigitSumCntBound
#print axioms L3.RenewalReferenceClock.bankRepairDigitSumCntExtend
#print axioms L3.RenewalReferenceClock.bankRepairDigitRightmost
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadWPre
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadWDelim
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadWSeg
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadPairPre
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadPairPreStrict
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadPairInto
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadPairIntoStrict
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadPairFrom
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadPairFromStrict
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadPairSeg
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadPairSegStrict
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadOutOfSeg
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadOutOfSegStrict
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadReset
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadResetD
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadPairPreD
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadPairPreStrictD
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadPairIntoD
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadPairIntoStrictD
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadPairFromD
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadPairFromStrictD
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadPairSegD
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadPairSegStrictD
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadOutOfSegD
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadOutOfSegStrictD
#print axioms L3.RenewalReferenceClock.bankRepairDigitPreOutWZero
#print axioms L3.RenewalReferenceClock.bankRepairDigitSegInWZero
#print axioms L3.RenewalReferenceClock.bankRepairDigitLiveWZero
#print axioms L3.RenewalReferenceClock.bankRepairDigitDelimInWZero
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadWZeroPre
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadWZeroDelim
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadWZeroSeg
#print axioms L3.RenewalReferenceClock.bankRepairDigitTailWMono
#print axioms L3.RenewalReferenceClock.bankRepairDigitTailWUpper
#print axioms L3.RenewalReferenceClock.bankRepairDigitPreOutWLe
#print axioms L3.RenewalReferenceClock.bankRepairDigitSegInWLe
#print axioms L3.RenewalReferenceClock.bankRepairDigitLiveWLe
#print axioms L3.RenewalReferenceClock.bankRepairDigitDelimInWLe
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadWLePre
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadWLeSeg
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadBudgetArith
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadBudgetFits
#print axioms L3.RenewalReferenceClock.bankRepairDigitSiteSurj
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadEdgeSites
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadBetaFalse
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadBetaTrue
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadBoundaryOfZero
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadRankStep
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadRankDrop
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadRankOfBound
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadBankEdge
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadDataStep
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadDataUnique
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadRankEq
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadChosenSpec
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadWidth
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadDataOfGone
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadSpanTwo
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadingFlushTasksHold
#print axioms L3.RenewalReferenceClock.bankRepairDigitFlushClockOfFinalRegion
#print axioms L3.RenewalReferenceClock.bankRepairDigitFirstZeroReceiptOfFinalRegion
#print axioms L3.RenewalReferenceClock.bankRepairDigitPreDrain201OfFinalRegion
