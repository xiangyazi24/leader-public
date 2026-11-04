import Leader.L3.Bank.TrialProbability

/-!
C.5, comparator step (Appendix C, spatial-counter.tex, the paragraph
before (C.4)): "the comparator then propagates the conjunction of
equality with the hardwired bit theta_(j-1). Induction on the digit
index proves that, after digit j, its carried value is the conjunction
over l < j of [digit_l = theta_l]. The last-digit turn and the return
preserve this value."

On the local trial observer: from a LIVE, non-success state
whose root is in CSTART with no worker token on any digit, the
designated comparison word (launch at the root, CR outward over
G_1..G_(b-1), the top turn on G_(b-1), CL inward over G_(b-2)..G_1,
and the root decision on G_0) ends in WON exactly when the digit bits
spell theta; otherwise it ends LIVE and ARMED with the digits
unchanged and every token empty. The value is positive, as it is after
an increment; at value zero the CL0 return would be the LOST reset.
-/

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-! ### Binary words: digit weights and uniqueness of the b-bit sum -/

theorem bankTrialCmpWidth (q : Nat) : 11 ≤ (compileAdvice q).b := by
  change 11 ≤ (compileAdvice q).s + 11
  omega

/-- Weight of one binary digit `c` at position `d`. -/
def bankTrialCmpWeight (c : Bool) (d : Nat) : Nat := if c then 2 ^ d else 0

/-- `h 0 + ... + h (m-1)`, by recursion on the length. -/
def bankTrialCmpNatSum (h : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => bankTrialCmpNatSum h m + h m

theorem bankTrialCmpOfFnSum (h : Nat → Nat) (m : Nat) :
    (List.ofFn (fun j : Fin m => h j.val)).sum = bankTrialCmpNatSum h m := by
  induction m with
  | zero => simp [bankTrialCmpNatSum]
  | succ m ih =>
      rw [List.ofFn_succ_last, List.sum_append_nat]
      simp only [Fin.val_castSucc, Fin.val_last, List.sum_cons, List.sum_nil,
        Nat.add_zero]
      rw [ih]
      rfl

theorem bankTrialCmpBinLt (f : Nat → Bool) (m : Nat) :
    bankTrialCmpNatSum (fun d => bankTrialCmpWeight (f d) d) m < 2 ^ m := by
  induction m with
  | zero => show 0 < 2 ^ 0; decide
  | succ m ih =>
      have hp : 2 ^ (m + 1) = 2 ^ m * 2 := Nat.pow_succ 2 m
      show bankTrialCmpNatSum (fun d => bankTrialCmpWeight (f d) d) m +
        bankTrialCmpWeight (f m) m < 2 ^ (m + 1)
      cases hfm : f m with
      | false =>
          have h0 : bankTrialCmpWeight false m = 0 := rfl
          rw [h0]
          omega
      | true =>
          have h1 : bankTrialCmpWeight true m = 2 ^ m := rfl
          rw [h1]
          omega

/-- Two b-bit words with the same binary value agree digitwise. -/
theorem bankTrialCmpBinInj (f g : Nat → Bool) (m : Nat) :
    bankTrialCmpNatSum (fun d => bankTrialCmpWeight (f d) d) m =
      bankTrialCmpNatSum (fun d => bankTrialCmpWeight (g d) d) m →
    ∀ l, l < m → f l = g l := by
  induction m with
  | zero =>
      intro _ l hl
      exact absurd hl (Nat.not_lt_zero l)
  | succ m ih =>
      intro heq l hl
      have hF := bankTrialCmpBinLt f m
      have hG := bankTrialCmpBinLt g m
      have heq' : bankTrialCmpNatSum (fun d => bankTrialCmpWeight (f d) d) m +
          bankTrialCmpWeight (f m) m =
        bankTrialCmpNatSum (fun d => bankTrialCmpWeight (g d) d) m +
          bankTrialCmpWeight (g m) m := heq
      have h0 : bankTrialCmpWeight false m = 0 := rfl
      have h1 : bankTrialCmpWeight true m = 2 ^ m := rfl
      have hmm : f m = g m ∧
          bankTrialCmpNatSum (fun d => bankTrialCmpWeight (f d) d) m =
            bankTrialCmpNatSum (fun d => bankTrialCmpWeight (g d) d) m := by
        cases hfm : f m with
        | false =>
            cases hgm : g m with
            | false =>
                rw [hfm, hgm, h0] at heq'
                exact ⟨rfl, by omega⟩
            | true =>
                rw [hfm, hgm, h0, h1] at heq'
                exfalso
                omega
        | true =>
            cases hgm : g m with
            | false =>
                rw [hfm, hgm, h0, h1] at heq'
                exfalso
                omega
            | true =>
                rw [hfm, hgm, h1] at heq'
                exact ⟨rfl, by omega⟩
      by_cases hlm : l = m
      · subst hlm
        exact hmm.1
      · exact ih hmm.2 l (by omega)

theorem bankTrialCmpNatSumCongr (f g : Nat → Bool) (m : Nat) :
    (∀ l, l < m → f l = g l) →
    bankTrialCmpNatSum (fun d => bankTrialCmpWeight (f d) d) m =
      bankTrialCmpNatSum (fun d => bankTrialCmpWeight (g d) d) m := by
  induction m with
  | zero =>
      intro _
      rfl
  | succ m ih =>
      intro h
      show bankTrialCmpNatSum (fun d => bankTrialCmpWeight (f d) d) m +
          bankTrialCmpWeight (f m) m =
        bankTrialCmpNatSum (fun d => bankTrialCmpWeight (g d) d) m +
          bankTrialCmpWeight (g m) m
      rw [ih (fun l hl => h l (by omega)), h m (by omega)]

/-- Digit d (0-based, physical slot d+1) as a total function. -/
def bankTrialCmpBit {q : Nat}
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (d : Nat) : Bool :=
  if h : d < (compileAdvice q).b then (B.fields ⟨d + 1, by omega⟩).2.1 else false

theorem bankTrialCmpBitEq {q : Nat}
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (d : Nat) (hd : d < (compileAdvice q).b) :
    bankTrialCmpBit B d = (B.fields ⟨d + 1, by omega⟩).2.1 := by
  unfold bankTrialCmpBit
  rw [dif_pos hd]

theorem bankTrialCmpBinaryNatSum {q : Nat}
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b) :
    bankTrialLiveBinaryValue B =
      bankTrialCmpNatSum
        (fun d => bankTrialCmpWeight (bankTrialCmpBit B d) d)
        (compileAdvice q).b := by
  rw [← bankTrialCmpOfFnSum]
  unfold bankTrialLiveBinaryValue
  apply FiniteUniformStoppingTree.ofFn_sum_eq
  intro j
  rw [bankTrialCmpBitEq B j.val j.isLt]
  rfl

theorem bankTrialCmpThetaNatSum (q : Nat) :
    bankTrialLiveThetaBinary q =
      bankTrialCmpNatSum
        (fun d => bankTrialCmpWeight ((compileAdvice q).theta d) d)
        (compileAdvice q).b := by
  rw [← bankTrialCmpOfFnSum]
  rfl

/-- The binary value equals the theta value iff every digit is theta. -/
theorem bankTrialCmpBinaryIff {q : Nat}
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b) :
    bankTrialLiveBinaryValue B = bankTrialLiveThetaBinary q ↔
      ∀ l, l < (compileAdvice q).b →
        bankTrialCmpBit B l = (compileAdvice q).theta l := by
  rw [bankTrialCmpBinaryNatSum, bankTrialCmpThetaNatSum]
  exact ⟨bankTrialCmpBinInj _ _ _, bankTrialCmpNatSumCongr _ _ _⟩

theorem bankTrialCmpBinaryCongr {q : Nat}
    (A B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (h : ∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveBit A j = bankTrialLiveWaveBit B j) :
    bankTrialLiveBinaryValue A = bankTrialLiveBinaryValue B := by
  unfold bankTrialLiveBinaryValue
  apply FiniteUniformStoppingTree.ofFn_sum_eq
  intro j
  have hj : (A.fields ⟨j.val + 1, by omega⟩).2.1 =
      (B.fields ⟨j.val + 1, by omega⟩).2.1 := h j
  rw [hj]

/-! ### The carried comparator value -/

/-- The CR value after digit k: the conjunction over l <= k of
[digit l = theta l]. -/
def bankTrialCmpValue {q : Nat}
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b) :
    Nat → Bool
  | 0 => bankTrialCmpBit B 0 == (compileAdvice q).theta 0
  | k + 1 => bankTrialCmpValue B k &&
      (bankTrialCmpBit B (k + 1) == (compileAdvice q).theta (k + 1))

theorem bankTrialCmpValueIff {q : Nat}
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (k : Nat) :
    bankTrialCmpValue B k = true ↔
      ∀ l, l ≤ k → bankTrialCmpBit B l = (compileAdvice q).theta l := by
  induction k with
  | zero =>
      constructor
      · intro h l hl
        have hl0 : l = 0 := by omega
        subst hl0
        have h' : (bankTrialCmpBit B 0 == (compileAdvice q).theta 0) = true := h
        exact beq_iff_eq.mp h'
      · intro h
        exact beq_iff_eq.mpr (h 0 (Nat.le_refl 0))
  | succ k ih =>
      constructor
      · intro h l hl
        have h' : (bankTrialCmpValue B k &&
            (bankTrialCmpBit B (k + 1) == (compileAdvice q).theta (k + 1))) =
              true := h
        have h2 := Bool.and_eq_true_iff.mp h'
        by_cases hlk : l = k + 1
        · subst hlk
          exact beq_iff_eq.mp h2.2
        · exact ih.mp h2.1 l (by omega)
      · intro h
        show (bankTrialCmpValue B k &&
            (bankTrialCmpBit B (k + 1) == (compileAdvice q).theta (k + 1))) = true
        rw [ih.mpr (fun l hl => h l (by omega)),
          beq_iff_eq.mpr (h (k + 1) (Nat.le_refl _))]
        rfl

/-! ### Literal bankPair rows -/

theorem bankTrialCmpRawLaunch
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 ≤ b) (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false) (hm : x.mode = .CSTART)
    (ht : y.tok = .E) :
    (bankPair x y 1 b theta).1.mode = .CWAIT ∧
    (bankPair x y 1 b theta).2.tok =
      (if y.bit == theta 0 then .CR1 else .CR0) ∧
    (bankPair x y 1 b theta).2.bit = y.bit := by
  simp [bankPair, hx, hy, hg, hm, ht,
    hb, isRetTok, isWaitMode, Id.run_pure, Id.run_bind]

theorem bankTrialCmpRawCLZeroRootReturn
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 ≤ b) (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false) (hm : x.mode = .CWAIT)
    (ht : y.tok = .CL0) :
    (bankPair x y 1 b theta).1.mode = .ARMED ∧
    (bankPair x y 1 b theta).2.tok = .E ∧
    (bankPair x y 1 b theta).2.bit = y.bit := by
  simp [bankPair, hx, hy, hg, hm, ht,
    hb, isRetTok, isWaitMode, Id.run_pure, Id.run_bind]

theorem bankTrialCmpRawCRForward
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1) (c : Bool)
    (htx : x.tok = if c then .CR1 else .CR0) (hty : y.tok = .E) :
    (bankPair x y y.role b theta).1.tok = .E ∧
    (bankPair x y y.role b theta).1.bit = x.bit ∧
    (bankPair x y y.role b theta).2.tok =
      (if (c && (y.bit == theta (y.role - 1))) then .CR1 else .CR0) ∧
    (bankPair x y y.role b theta).2.bit = y.bit := by
  cases c with
  | false =>
      have h := bankTrialInteriorCRZeroForward b theta x y hx hlt hy htx hty
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  | true =>
      have h := bankTrialLiveRawCRForward b theta x y hx hlt hy htx hty
      exact ⟨h.1, h.2.2.1, h.2.1, h.2.2.2⟩

theorem bankTrialCmpRawTop
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (htop : y.role = b) (c : Bool)
    (hxt : x.tok = .E) (hyt : y.tok = if c then .CR1 else .CR0) :
    (bankPair x y y.role b theta).1.tok = (if c then .CL1 else .CL0) ∧
    (bankPair x y y.role b theta).1.bit = x.bit ∧
    (bankPair x y y.role b theta).2.tok = .E ∧
    (bankPair x y y.role b theta).2.bit = y.bit := by
  cases c with
  | false =>
      exact bankTrialInteriorCRZeroTop b theta x y hx hlt hy htop hxt hyt
  | true =>
      have hyt' : y.tok = .CR1 := hyt
      have hxn : x.role ≠ 0 := by omega
      have hxTop : x.role ≠ b := by omega
      have hyn : y.role ≠ 0 := by omega
      have hyPos : 1 ≤ y.role := by omega
      have hyLe : y.role ≤ b := by omega
      have hxLe : x.role ≤ b := by omega
      have hc1 : ¬ b < x.role + 1 := by omega
      have hc2 : x.role + 1 = b := by omega
      have hc3 : b ≠ 0 := by omega
      simp [bankPair, hc1, hc2, hc3, hx, hlt, hy, htop,
        hxn, hxTop, hyn, hyPos, hyLe, hxLe,
        hxt, hyt', Id.run_pure, Id.run_bind]

theorem bankTrialCmpRawCLReturn
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1) (c : Bool)
    (hxt : x.tok = .E) (hyt : y.tok = if c then .CL1 else .CL0) :
    (bankPair x y y.role b theta).1.tok = (if c then .CL1 else .CL0) ∧
    (bankPair x y y.role b theta).1.bit = x.bit ∧
    (bankPair x y y.role b theta).2.tok = .E ∧
    (bankPair x y y.role b theta).2.bit = y.bit := by
  cases c with
  | false =>
      exact bankTrialInteriorCLZeroReturn b theta x y hx hlt hy hxt hyt
  | true =>
      have h := bankTrialLiveRawCLReturn b theta x y hx hlt hy hxt hyt
      exact ⟨h.1, h.2.2.1, h.2.1, h.2.2.2⟩

/-! ### Selected services on the clamped reference -/

/-- Root outgoing service G_0: root takes bankPair.1, digit one
takes bankPair.2, every other digit is framed. -/
theorem bankTrialCmpRoot {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hf : B.success = false) :
    bankTrialLiveWaveRootMode
        (GrantBankReference.bankLocalReferenceStepClamped ring root B root) =
      (GrantBankReference.bankLocalReferenceInternalPair q B
        ⟨0, by have := bankTrialCmpWidth q; omega⟩).1.mode ∧
    ∀ k : Fin (compileAdvice q).b,
      (k.val = 0 →
        bankTrialLiveWaveBit
            (GrantBankReference.bankLocalReferenceStepClamped ring root B root) k =
          (GrantBankReference.bankLocalReferenceInternalPair q B
            ⟨0, by have := bankTrialCmpWidth q; omega⟩).2.bit ∧
        bankTrialLiveWaveToken
            (GrantBankReference.bankLocalReferenceStepClamped ring root B root) k =
          (GrantBankReference.bankLocalReferenceInternalPair q B
            ⟨0, by have := bankTrialCmpWidth q; omega⟩).2.tok) ∧
      (k.val ≠ 0 →
        bankTrialLiveWaveBit
            (GrantBankReference.bankLocalReferenceStepClamped ring root B root) k =
          bankTrialLiveWaveBit B k ∧
        bankTrialLiveWaveToken
            (GrantBankReference.bankLocalReferenceStepClamped ring root B root) k =
          bankTrialLiveWaveToken B k) := by
  have hw11 := bankTrialCmpWidth q
  have hn : 2 ≤ n := by
    unfold BankTrialLiveWindowNonalias at hw
    omega
  have hs : Counter.Support q ring root root :=
    Or.inr ⟨0, Nat.zero_le _, rfl⟩
  refine ⟨?_, ?_⟩
  · have h := (bankTrialLocalStepField ring root root B hs hf
      ⟨0, by omega⟩).trans (bankTrialLocalFieldRootOutgoing ring root B)
    exact congrArg (fun x : Mode × Bool × BTok × Nat => x.1) h
  · intro k
    constructor
    · intro hk
      have hkk : k = ⟨0, by omega⟩ := Fin.ext hk
      rw [hkk]
      have h := (bankTrialLocalStepField ring root root B hs hf
        ⟨1, by omega⟩).trans (bankTrialLocalFieldOneOutgoing ring root hn B)
      exact ⟨congrArg (fun x : Mode × Bool × BTok × Nat => x.2.1) h,
        congrArg (fun x : Mode × Bool × BTok × Nat => x.2.2.1) h⟩
    · intro hk
      have hx : ¬ (k.val + 1 < (compileAdvice q).b ∧
          root = Counter.site ring root (k.val + 1)) := by
        intro h
        have he : Counter.site ring root (k.val + 1) =
            Counter.site ring root 0 := h.2.symm
        have := bankTrialWindowSitesDistinct ring root hw
          (k.val + 1) 0 (by omega) (by omega) he
        omega
      have hy : ¬ (0 < k.val + 1 ∧
          root = Counter.site ring root (k.val + 1 - 1)) := by
        intro h
        have he : Counter.site ring root (k.val + 1 - 1) =
            Counter.site ring root 0 := h.2.symm
        have := bankTrialWindowSitesDistinct ring root hw
          (k.val + 1 - 1) 0 (by omega) (by omega) he
        omega
      have ht : ¬ (k.val + 1 = (compileAdvice q).b ∧
          root = Counter.site ring root (compileAdvice q).b) := by
        intro h
        have he : Counter.site ring root (compileAdvice q).b =
            Counter.site ring root 0 := h.2.symm
        have := bankTrialWindowSitesDistinct ring root hw
          (compileAdvice q).b 0 (by omega) (by omega) he
        omega
      have hr : ¬ (k.val + 1 = 0 ∧ ring.rightNeighbor root = root) := by
        intro h
        have h0 : k.val + 1 = 0 := h.1
        omega
      have h := bankTrialLiveCarryUnselectedField ring root root B hs hf
        ⟨k.val + 1, by omega⟩ hx hy ht hr
      exact ⟨congrArg (fun x : Mode × Bool × BTok × Nat => x.2.1) h,
        congrArg (fun x : Mode × Bool × BTok × Nat => x.2.2.1) h⟩

/-- Interior service G_j, 0 < j < b: slot j takes bankPair.1,
slot j+1 takes bankPair.2, every other slot is framed. -/
theorem bankTrialCmpInterior {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hf : B.success = false)
    (j : Nat) (hj0 : 0 < j) (hjb : j < (compileAdvice q).b) :
    (GrantBankReference.bankLocalReferenceStepClamped ring root B
      (Counter.site ring root j)).success = false ∧
    bankTrialLiveWaveRootMode
        (GrantBankReference.bankLocalReferenceStepClamped ring root B
          (Counter.site ring root j)) =
      bankTrialLiveWaveRootMode B ∧
    ∀ k : Fin (compileAdvice q).b,
      (k.val + 1 = j →
        bankTrialLiveWaveBit
            (GrantBankReference.bankLocalReferenceStepClamped ring root B
              (Counter.site ring root j)) k =
          (GrantBankReference.bankLocalReferenceInternalPair q B ⟨j, hjb⟩).1.bit ∧
        bankTrialLiveWaveToken
            (GrantBankReference.bankLocalReferenceStepClamped ring root B
              (Counter.site ring root j)) k =
          (GrantBankReference.bankLocalReferenceInternalPair q B ⟨j, hjb⟩).1.tok) ∧
      (k.val = j →
        bankTrialLiveWaveBit
            (GrantBankReference.bankLocalReferenceStepClamped ring root B
              (Counter.site ring root j)) k =
          (GrantBankReference.bankLocalReferenceInternalPair q B ⟨j, hjb⟩).2.bit ∧
        bankTrialLiveWaveToken
            (GrantBankReference.bankLocalReferenceStepClamped ring root B
              (Counter.site ring root j)) k =
          (GrantBankReference.bankLocalReferenceInternalPair q B ⟨j, hjb⟩).2.tok) ∧
      (k.val + 1 ≠ j → k.val ≠ j →
        bankTrialLiveWaveBit
            (GrantBankReference.bankLocalReferenceStepClamped ring root B
              (Counter.site ring root j)) k =
          bankTrialLiveWaveBit B k ∧
        bankTrialLiveWaveToken
            (GrantBankReference.bankLocalReferenceStepClamped ring root B
              (Counter.site ring root j)) k =
          bankTrialLiveWaveToken B k) := by
  refine ⟨bankTrialC5NonrootSuccessFrame ring root _ B hf
      (bankTrialWindowInteriorNotRoot ring root hw ⟨j, hjb⟩ hj0),
    bankTrialWindowInteriorRootModeFrame ring root hw B hf ⟨j, hjb⟩ hj0, ?_⟩
  intro k
  refine ⟨?_, ?_, ?_⟩
  · intro hk
    subst hk
    have h := bankTrialWindowInteriorSource ring root B hf ⟨k.val + 1, hjb⟩
    exact ⟨congrArg (fun x : Mode × Bool × BTok × Nat => x.2.1) h,
      congrArg (fun x : Mode × Bool × BTok × Nat => x.2.2.1) h⟩
  · intro hk
    subst hk
    have h := bankTrialWindowInteriorResponder ring root hw B hf ⟨k.val, hjb⟩
    exact ⟨congrArg (fun x : Mode × Bool × BTok × Nat => x.2.1) h,
      congrArg (fun x : Mode × Bool × BTok × Nat => x.2.2.1) h⟩
  · intro h1 h2
    have h := bankTrialWindowInteriorFrame ring root hw B hf ⟨j, hjb⟩ hj0
      ⟨k.val + 1, by omega⟩ h1 (by change k.val + 1 ≠ j + 1; omega)
    exact ⟨congrArg (fun x : Mode × Bool × BTok × Nat => x.2.1) h,
      congrArg (fun x : Mode × Bool × BTok × Nat => x.2.2.1) h⟩

/-! ### Observer phase -/

theorem bankTrialCmpStateEta {q : Nat} (z : BankTrialLocalState q)
    (begun : Bool) (h : z.phase = .live begun) :
    z = ⟨z.bank, .live begun⟩ := by
  cases z with
  | mk B phase =>
      change phase = .live begun at h
      subst h
      rfl

/-- An unlatched, non-Clean, non-RESET successor keeps LIVE. -/
theorem bankTrialCmpLiveNext {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool)
    (hs : (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).success = false)
    (hc : ¬ BankTrialLocalClean q
      (GrantBankReference.bankLocalReferenceStepClamped ring root B e))
    (hr : bankTrialLiveWaveRootMode
      (GrantBankReference.bankLocalReferenceStepClamped ring root B e) ≠
        .RESET) :
    ∃ nb : Bool,
      bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) e =
        ⟨GrantBankReference.bankLocalReferenceStepClamped ring root B e,
          .live nb⟩ := by
  have hzero : (0 : Fin ((compileAdvice q).b + 1)) =
      ⟨0, by omega⟩ := Fin.ext rfl
  have hr' : ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨0, by omega⟩).1 ≠ .RESET := hr
  have hr0 : ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields (0 : Fin ((compileAdvice q).b + 1))).1 ≠
        .RESET := by
    rw [hzero]
    exact hr'
  have hph : (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) e).phase =
        .live (begun || decide (e = root ∨ ring.rightNeighbor e = root)) := by
    simp [bankTrialLocalNext, hs, hc, hr0]
  refine ⟨begun || decide (e = root ∨ ring.rightNeighbor e = root), ?_⟩
  rw [bankTrialCmpStateEta _ _ hph, bankTrialLocalNextLiveBank]

theorem bankTrialCmpLiveCWait {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool)
    (hs : (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).success = false)
    (hm : bankTrialLiveWaveRootMode
      (GrantBankReference.bankLocalReferenceStepClamped ring root B e) =
        .CWAIT) :
    ∃ nb : Bool,
      bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) e =
        ⟨GrantBankReference.bankLocalReferenceStepClamped ring root B e,
          .live nb⟩ := by
  apply bankTrialCmpLiveNext ring root e B begun hs
  · intro hc
    have h2 : bankTrialLiveWaveRootMode
        (GrantBankReference.bankLocalReferenceStepClamped ring root B e) =
          .ARMED := hc.2.1
    rw [hm] at h2
    cases h2
  · rw [hm]
    intro h
    cases h

/-! ### Stage invariants of the comparator wave -/

/-- After k outward services: LIVE, unlatched, root CWAIT, digit
bits unchanged from O, and the only token is CR at wave index k
(physical digit k+1), carrying bankTrialCmpValue O k. -/
def BankTrialCmpCRStage {q : Nat}
    (O : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (k : Nat) (z : BankTrialLocalState q) : Prop :=
  (∃ begun : Bool, z.phase = .live begun) ∧
  z.bank.success = false ∧
  bankTrialLiveWaveRootMode z.bank = .CWAIT ∧
  k < (compileAdvice q).b ∧
  (∀ j : Fin (compileAdvice q).b,
    bankTrialLiveWaveBit z.bank j = bankTrialLiveWaveBit O j) ∧
  (∀ j : Fin (compileAdvice q).b,
    bankTrialLiveWaveToken z.bank j =
      if j.val = k then (if bankTrialCmpValue O k then .CR1 else .CR0)
      else .E)

/-- The inward analogue: the only token is CL at wave index k,
carrying the final comparator value c. -/
def BankTrialCmpCLStage {q : Nat}
    (O : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (c : Bool) (k : Nat) (z : BankTrialLocalState q) : Prop :=
  (∃ begun : Bool, z.phase = .live begun) ∧
  z.bank.success = false ∧
  bankTrialLiveWaveRootMode z.bank = .CWAIT ∧
  k < (compileAdvice q).b ∧
  (∀ j : Fin (compileAdvice q).b,
    bankTrialLiveWaveBit z.bank j = bankTrialLiveWaveBit O j) ∧
  (∀ j : Fin (compileAdvice q).b,
    bankTrialLiveWaveToken z.bank j =
      if j.val = k then (if c then .CL1 else .CL0) else .E)

/-- CSTART launch on G_0. -/
theorem bankTrialCmpLaunch {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (z : BankTrialLocalState q)
    (hlive : ∃ begun : Bool, z.phase = .live begun)
    (hf : z.bank.success = false)
    (hm : bankTrialLiveWaveRootMode z.bank = .CSTART)
    (htok : ∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken z.bank j = .E) :
    BankTrialCmpCRStage z.bank 0 (bankTrialLocalNext ring root z root) := by
  obtain ⟨begun, hph⟩ := hlive
  have hw11 := bankTrialCmpWidth q
  have hrow := bankTrialCmpRawLaunch (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell z.bank ⟨0, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell z.bank ⟨1, by omega⟩)
    (by omega) rfl rfl rfl hm (htok ⟨0, by omega⟩)
  obtain ⟨hmode, hwave⟩ := bankTrialCmpRoot ring root hw z.bank hf
  have hnot : (z.bank.fields ⟨0, by omega⟩).1 ≠ .CWAIT := by
    intro h
    have h2 : bankTrialLiveWaveRootMode z.bank = .CWAIT := h
    rw [hm] at h2
    cases h2
  have hs := bankTrialLocalUnlatchedNonCWaitNoWin ring root root z.bank hf hnot
  have hm' : bankTrialLiveWaveRootMode
      (GrantBankReference.bankLocalReferenceStepClamped ring root z.bank root) =
        .CWAIT := hmode.trans hrow.1
  obtain ⟨nb, hnext⟩ := bankTrialCmpLiveCWait ring root root z.bank begun hs hm'
  have hc : bankTrialCmpValue z.bank 0 =
      ((GrantBankReference.bankLocalReferenceCell z.bank ⟨1, by omega⟩).bit ==
        (compileAdvice q).theta 0) := by
    show (bankTrialCmpBit z.bank 0 == (compileAdvice q).theta 0) = _
    rw [bankTrialCmpBitEq z.bank 0 (by omega)]
    rfl
  have hz := bankTrialCmpStateEta z begun hph
  have hgoal : bankTrialLocalNext ring root z root =
      ⟨GrantBankReference.bankLocalReferenceStepClamped ring root z.bank root,
        .live nb⟩ :=
    (congrArg (fun x => bankTrialLocalNext ring root x root) hz).trans hnext
  rw [hgoal]
  refine ⟨⟨nb, rfl⟩, hs, hm', by omega, ?_, ?_⟩
  · intro k
    by_cases hk : k.val = 0
    · have hkk : k = ⟨0, by omega⟩ := Fin.ext hk
      rw [hkk]
      exact ((hwave ⟨0, by omega⟩).1 rfl).1.trans hrow.2.2
    · exact ((hwave k).2 hk).1
  · intro k
    by_cases hk : k.val = 0
    · rw [if_pos hk]
      have hkk : k = ⟨0, by omega⟩ := Fin.ext hk
      rw [hkk]
      refine ((hwave ⟨0, by omega⟩).1 rfl).2.trans (hrow.2.1.trans ?_)
      rw [hc]
    · rw [if_neg hk]
      exact ((hwave k).2 hk).2.trans (htok k)

/-- Outward CR service on G_(i+1). -/
theorem bankTrialCmpCRStep {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (O : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (i : Nat) (hi : i + 1 < (compileAdvice q).b)
    (z : BankTrialLocalState q)
    (hst : BankTrialCmpCRStage O i z) :
    BankTrialCmpCRStage O (i + 1)
      (bankTrialLocalNext ring root z (Counter.site ring root (i + 1))) := by
  obtain ⟨⟨begun, hph⟩, hf, hm, _, hbits, htoks⟩ := hst
  have hsrc : (GrantBankReference.bankLocalReferenceCell z.bank
      ⟨i + 1, by omega⟩).tok =
        (if bankTrialCmpValue O i then BTok.CR1 else BTok.CR0) :=
    (htoks ⟨i, by omega⟩).trans (if_pos rfl)
  have hdst : (GrantBankReference.bankLocalReferenceCell z.bank
      ⟨i + 1 + 1, by omega⟩).tok = .E :=
    (htoks ⟨i + 1, hi⟩).trans
      (if_neg (by intro h; change i + 1 = i at h; omega))
  have hrow := bankTrialCmpRawCRForward
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell z.bank ⟨i + 1, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell z.bank ⟨i + 1 + 1, by omega⟩)
    (by change 1 ≤ i + 1; omega)
    (by change i + 1 < (compileAdvice q).b; exact hi) rfl
    (bankTrialCmpValue O i) hsrc hdst
  have hnewTok :
      (if (bankTrialCmpValue O i &&
          ((GrantBankReference.bankLocalReferenceCell z.bank
            ⟨i + 1 + 1, by omega⟩).bit ==
            (compileAdvice q).theta
              ((GrantBankReference.bankLocalReferenceCell z.bank
                ⟨i + 1 + 1, by omega⟩).role - 1)))
        then BTok.CR1 else BTok.CR0) =
      (if bankTrialCmpValue O (i + 1) then BTok.CR1 else BTok.CR0) := by
    have hyb : (GrantBankReference.bankLocalReferenceCell z.bank
        ⟨i + 1 + 1, by omega⟩).bit = bankTrialCmpBit O (i + 1) := by
      rw [bankTrialCmpBitEq O (i + 1) hi]
      exact hbits ⟨i + 1, hi⟩
    have hrole : (GrantBankReference.bankLocalReferenceCell z.bank
        ⟨i + 1 + 1, by omega⟩).role - 1 = i + 1 := by
      show i + 1 + 1 - 1 = i + 1
      omega
    rw [hyb, hrole]
    rfl
  obtain ⟨hs', hrm, hk⟩ :=
    bankTrialCmpInterior ring root hw z.bank hf (i + 1) (by omega) hi
  obtain ⟨nb, hnext⟩ := bankTrialCmpLiveCWait ring root
    (Counter.site ring root (i + 1)) z.bank begun hs' (hrm.trans hm)
  have hz := bankTrialCmpStateEta z begun hph
  have hgoal : bankTrialLocalNext ring root z (Counter.site ring root (i + 1)) =
      ⟨GrantBankReference.bankLocalReferenceStepClamped ring root z.bank
        (Counter.site ring root (i + 1)), .live nb⟩ :=
    (congrArg (fun x => bankTrialLocalNext ring root x (Counter.site ring root (i + 1))) hz).trans hnext
  rw [hgoal]
  refine ⟨⟨nb, rfl⟩, hs', hrm.trans hm, hi, ?_, ?_⟩
  · intro k
    by_cases h1 : k.val + 1 = i + 1
    · have hkk : k = ⟨i, by omega⟩ := Fin.ext (show k.val = i by omega)
      rw [hkk]
      exact ((hk ⟨i, by omega⟩).1 rfl).1.trans
        (hrow.2.1.trans (hbits ⟨i, by omega⟩))
    · by_cases h2 : k.val = i + 1
      · have hkk : k = ⟨i + 1, hi⟩ := Fin.ext h2
        rw [hkk]
        exact ((hk ⟨i + 1, hi⟩).2.1 rfl).1.trans
          (hrow.2.2.2.trans (hbits ⟨i + 1, hi⟩))
      · exact ((hk k).2.2 h1 h2).1.trans (hbits k)
  · intro k
    by_cases h1 : k.val + 1 = i + 1
    · rw [if_neg (show ¬ k.val = i + 1 by omega)]
      exact ((hk k).1 h1).2.trans hrow.1
    · by_cases h2 : k.val = i + 1
      · rw [if_pos h2]
        exact ((hk k).2.1 h2).2.trans (hrow.2.2.1.trans hnewTok)
      · rw [if_neg h2]
        exact ((hk k).2.2 h1 h2).2.trans
          ((htoks k).trans (if_neg (show ¬ k.val = i by omega)))

/-- The top turn on G_(b-1): CR at digit b becomes CL at digit b-1. -/
theorem bankTrialCmpTop {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (O : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (m : Nat) (htopb : m + 2 = (compileAdvice q).b)
    (z : BankTrialLocalState q)
    (hst : BankTrialCmpCRStage O (m + 1) z) :
    BankTrialCmpCLStage O (bankTrialCmpValue O (m + 1)) m
      (bankTrialLocalNext ring root z (Counter.site ring root (m + 1))) := by
  obtain ⟨⟨begun, hph⟩, hf, hm, _, hbits, htoks⟩ := hst
  have hi : m + 1 < (compileAdvice q).b := by omega
  have hsrc : (GrantBankReference.bankLocalReferenceCell z.bank
      ⟨m + 1, by omega⟩).tok = .E :=
    (htoks ⟨m, by omega⟩).trans
      (if_neg (by intro h; change m = m + 1 at h; omega))
  have hdst : (GrantBankReference.bankLocalReferenceCell z.bank
      ⟨m + 1 + 1, by omega⟩).tok =
        (if bankTrialCmpValue O (m + 1) then BTok.CR1 else BTok.CR0) :=
    (htoks ⟨m + 1, hi⟩).trans (if_pos rfl)
  have hrow := bankTrialCmpRawTop
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell z.bank ⟨m + 1, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell z.bank ⟨m + 1 + 1, by omega⟩)
    (by change 1 ≤ m + 1; omega)
    (by change m + 1 < (compileAdvice q).b; exact hi) rfl
    (by change m + 1 + 1 = (compileAdvice q).b; omega)
    (bankTrialCmpValue O (m + 1)) hsrc hdst
  obtain ⟨hs', hrm, hk⟩ :=
    bankTrialCmpInterior ring root hw z.bank hf (m + 1) (by omega) hi
  obtain ⟨nb, hnext⟩ := bankTrialCmpLiveCWait ring root
    (Counter.site ring root (m + 1)) z.bank begun hs' (hrm.trans hm)
  have hz := bankTrialCmpStateEta z begun hph
  have hgoal : bankTrialLocalNext ring root z (Counter.site ring root (m + 1)) =
      ⟨GrantBankReference.bankLocalReferenceStepClamped ring root z.bank
        (Counter.site ring root (m + 1)), .live nb⟩ :=
    (congrArg (fun x => bankTrialLocalNext ring root x (Counter.site ring root (m + 1))) hz).trans hnext
  rw [hgoal]
  refine ⟨⟨nb, rfl⟩, hs', hrm.trans hm, by omega, ?_, ?_⟩
  · intro k
    by_cases h1 : k.val + 1 = m + 1
    · have hkk : k = ⟨m, by omega⟩ := Fin.ext (show k.val = m by omega)
      rw [hkk]
      exact ((hk ⟨m, by omega⟩).1 rfl).1.trans
        (hrow.2.1.trans (hbits ⟨m, by omega⟩))
    · by_cases h2 : k.val = m + 1
      · have hkk : k = ⟨m + 1, hi⟩ := Fin.ext h2
        rw [hkk]
        exact ((hk ⟨m + 1, hi⟩).2.1 rfl).1.trans
          (hrow.2.2.2.trans (hbits ⟨m + 1, hi⟩))
      · exact ((hk k).2.2 h1 h2).1.trans (hbits k)
  · intro k
    by_cases h1 : k.val + 1 = m + 1
    · rw [if_pos (show k.val = m by omega)]
      exact ((hk k).1 h1).2.trans hrow.1
    · by_cases h2 : k.val = m + 1
      · rw [if_neg (show ¬ k.val = m by omega)]
        exact ((hk k).2.1 h2).2.trans hrow.2.2.1
      · rw [if_neg (show ¬ k.val = m by omega)]
        exact ((hk k).2.2 h1 h2).2.trans
          ((htoks k).trans (if_neg (show ¬ k.val = m + 1 by omega)))

/-- Inward CL service on G_(m+1): CL moves from digit m+2 to m+1. -/
theorem bankTrialCmpCLStep {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (O : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (c : Bool) (m : Nat) (hi : m + 1 < (compileAdvice q).b)
    (z : BankTrialLocalState q)
    (hst : BankTrialCmpCLStage O c (m + 1) z) :
    BankTrialCmpCLStage O c m
      (bankTrialLocalNext ring root z (Counter.site ring root (m + 1))) := by
  obtain ⟨⟨begun, hph⟩, hf, hm, _, hbits, htoks⟩ := hst
  have hsrc : (GrantBankReference.bankLocalReferenceCell z.bank
      ⟨m + 1, by omega⟩).tok = .E :=
    (htoks ⟨m, by omega⟩).trans
      (if_neg (by intro h; change m = m + 1 at h; omega))
  have hdst : (GrantBankReference.bankLocalReferenceCell z.bank
      ⟨m + 1 + 1, by omega⟩).tok = (if c then BTok.CL1 else BTok.CL0) :=
    (htoks ⟨m + 1, hi⟩).trans (if_pos rfl)
  have hrow := bankTrialCmpRawCLReturn
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell z.bank ⟨m + 1, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell z.bank ⟨m + 1 + 1, by omega⟩)
    (by change 1 ≤ m + 1; omega)
    (by change m + 1 < (compileAdvice q).b; exact hi) rfl
    c hsrc hdst
  obtain ⟨hs', hrm, hk⟩ :=
    bankTrialCmpInterior ring root hw z.bank hf (m + 1) (by omega) hi
  obtain ⟨nb, hnext⟩ := bankTrialCmpLiveCWait ring root
    (Counter.site ring root (m + 1)) z.bank begun hs' (hrm.trans hm)
  have hz := bankTrialCmpStateEta z begun hph
  have hgoal : bankTrialLocalNext ring root z (Counter.site ring root (m + 1)) =
      ⟨GrantBankReference.bankLocalReferenceStepClamped ring root z.bank
        (Counter.site ring root (m + 1)), .live nb⟩ :=
    (congrArg (fun x => bankTrialLocalNext ring root x (Counter.site ring root (m + 1))) hz).trans hnext
  rw [hgoal]
  refine ⟨⟨nb, rfl⟩, hs', hrm.trans hm, by omega, ?_, ?_⟩
  · intro k
    by_cases h1 : k.val + 1 = m + 1
    · have hkk : k = ⟨m, by omega⟩ := Fin.ext (show k.val = m by omega)
      rw [hkk]
      exact ((hk ⟨m, by omega⟩).1 rfl).1.trans
        (hrow.2.1.trans (hbits ⟨m, by omega⟩))
    · by_cases h2 : k.val = m + 1
      · have hkk : k = ⟨m + 1, hi⟩ := Fin.ext h2
        rw [hkk]
        exact ((hk ⟨m + 1, hi⟩).2.1 rfl).1.trans
          (hrow.2.2.2.trans (hbits ⟨m + 1, hi⟩))
      · exact ((hk k).2.2 h1 h2).1.trans (hbits k)
  · intro k
    by_cases h1 : k.val + 1 = m + 1
    · rw [if_pos (show k.val = m by omega)]
      exact ((hk k).1 h1).2.trans hrow.1
    · by_cases h2 : k.val = m + 1
      · rw [if_neg (show ¬ k.val = m by omega)]
        exact ((hk k).2.1 h2).2.trans hrow.2.2.1
      · rw [if_neg (show ¬ k.val = m by omega)]
        exact ((hk k).2.2 h1 h2).2.trans
          ((htoks k).trans (if_neg (show ¬ k.val = m + 1 by omega)))

/-- The whole outward CR wave over G_1, ..., G_t. -/
theorem bankTrialCmpOutward {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (O : GrantBankReference.BankLocalReference (compileAdvice q).b) :
    ∀ t : Nat, t < (compileAdvice q).b →
      ∀ z : BankTrialLocalState q, BankTrialCmpCRStage O 0 z →
        BankTrialCmpCRStage O t
          (bankTrialLocalRun ring root (bankTrialC5OutwardEdges ring root t) z) := by
  intro t
  induction t with
  | zero =>
      intro _ z hz
      exact hz
  | succ t ih =>
      intro ht z hz
      have hlist : bankTrialC5OutwardEdges ring root (t + 1) =
          bankTrialC5OutwardEdges ring root t ++
            [Counter.site ring root (t + 1)] := by
        unfold bankTrialC5OutwardEdges
        rw [List.range_succ (n := t), List.map_append]
        rfl
      rw [hlist, bankTrialLocalRunAppend]
      exact bankTrialCmpCRStep ring root hw O t ht _ (ih (by omega) z hz)

/-- The whole inward CL return over G_m, ..., G_1, stopping just
before the root service G_0. -/
theorem bankTrialCmpInward {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (O : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (c : Bool) :
    ∀ m : Nat, m < (compileAdvice q).b →
      ∀ z : BankTrialLocalState q, BankTrialCmpCLStage O c m z →
        ∃ z' : BankTrialLocalState q, BankTrialCmpCLStage O c 0 z' ∧
          bankTrialLocalRun ring root
            ((List.range (m + 1)).reverse.map
              (fun i => Counter.site ring root i)) z =
            bankTrialLocalNext ring root z' root := by
  intro m
  induction m with
  | zero =>
      intro _ z hz
      exact ⟨z, hz, rfl⟩
  | succ m ih =>
      intro hm z hz
      have hlist : (List.range (m + 1 + 1)).reverse.map
          (fun i => Counter.site ring root i) =
          Counter.site ring root (m + 1) ::
            (List.range (m + 1)).reverse.map
              (fun i => Counter.site ring root i) := by
        rw [List.range_succ (n := m + 1), List.reverse_append]
        rfl
      rw [hlist]
      exact ih (by omega) _ (bankTrialCmpCLStep ring root hw O c m hm z hz)

/-- The root decision on G_0 from CL at digit one. -/
theorem bankTrialCmpRootDecision {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (O : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hpos : 0 < bankTrialLiveBinaryValue O)
    (c : Bool) (z : BankTrialLocalState q)
    (hst : BankTrialCmpCLStage O c 0 z) :
    (c = true → (bankTrialLocalNext ring root z root).phase = .won) ∧
    (c = false →
      (∃ begun : Bool, (bankTrialLocalNext ring root z root).phase =
        .live begun) ∧
      bankTrialLiveWaveRootMode (bankTrialLocalNext ring root z root).bank =
        .ARMED ∧
      (∀ j : Fin (compileAdvice q).b,
        bankTrialLiveWaveToken (bankTrialLocalNext ring root z root).bank j =
          .E) ∧
      (∀ j : Fin (compileAdvice q).b,
        bankTrialLiveWaveBit (bankTrialLocalNext ring root z root).bank j =
          bankTrialLiveWaveBit O j) ∧
      (bankTrialLocalNext ring root z root).bank.success = false) := by
  obtain ⟨⟨begun, hph⟩, hf, hm, _, hbits, htoks⟩ := hst
  have hw11 := bankTrialCmpWidth q
  have hz := bankTrialCmpStateEta z begun hph
  constructor
  · intro hc
    subst hc
    have ht : (z.bank.fields
        ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.2.1 = .CL1 :=
      ((htoks ⟨0, by omega⟩).trans (if_pos rfl)).trans (if_pos rfl)
    exact (congrArg (fun x => (bankTrialLocalNext ring root x root).phase) hz).trans
      (bankTrialProbabilityLiveReturnWon ring root z.bank begun hf hm ht)
  · intro hc
    subst hc
    have ht : (z.bank.fields ⟨1, by omega⟩).2.2.1 = .CL0 :=
      ((htoks ⟨0, by omega⟩).trans (if_pos rfl)).trans
        (if_neg Bool.false_ne_true)
    have hrow := bankTrialCmpRawCLZeroRootReturn
      (compileAdvice q).b (compileAdvice q).theta
      (GrantBankReference.bankLocalReferenceCell z.bank ⟨0, by omega⟩)
      (GrantBankReference.bankLocalReferenceCell z.bank ⟨1, by omega⟩)
      (by omega) rfl rfl rfl hm ht
    obtain ⟨hmode, hwave⟩ := bankTrialCmpRoot ring root hw z.bank hf
    have hs : Counter.Support q ring root root :=
      Or.inr ⟨0, Nat.zero_le _, rfl⟩
    have hev : GrantBankReference.bankLocalReferenceSuccessEvent
        ring root z.bank root = false := by
      unfold GrantBankReference.bankLocalReferenceSuccessEvent
      rw [if_pos rfl]
      change bankSuccess
        (GrantBankReference.bankLocalReferenceCell z.bank ⟨0, by omega⟩)
        (GrantBankReference.bankLocalReferenceCell z.bank ⟨1, by omega⟩)
        1 (compileAdvice q).b = false
      simp [bankSuccess, GrantBankReference.bankLocalReferenceCell, ht]
    have hsucc : (GrantBankReference.bankLocalReferenceStepClamped
        ring root z.bank root).success = false := by
      simp [GrantBankReference.bankLocalReferenceStepClamped, hs, hf, hev]
    have hm' : bankTrialLiveWaveRootMode
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root z.bank root) = .ARMED := hmode.trans hrow.1
    have hbits' : ∀ k : Fin (compileAdvice q).b,
        bankTrialLiveWaveBit (GrantBankReference.bankLocalReferenceStepClamped
          ring root z.bank root) k = bankTrialLiveWaveBit O k := by
      intro k
      by_cases hk : k.val = 0
      · have hkk : k = ⟨0, by omega⟩ := Fin.ext hk
        rw [hkk]
        exact ((hwave ⟨0, by omega⟩).1 rfl).1.trans
          (hrow.2.2.trans (hbits ⟨0, by omega⟩))
      · exact ((hwave k).2 hk).1.trans (hbits k)
    have htoks' : ∀ k : Fin (compileAdvice q).b,
        bankTrialLiveWaveToken (GrantBankReference.bankLocalReferenceStepClamped
          ring root z.bank root) k = .E := by
      intro k
      by_cases hk : k.val = 0
      · exact ((hwave k).1 hk).2.trans hrow.2.1
      · exact ((hwave k).2 hk).2.trans ((htoks k).trans (if_neg hk))
    have hnc : ¬ BankTrialLocalClean q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root z.bank root) := by
      intro hcl
      have h0 := bankTrialLiveBinaryClean _ hcl
      rw [bankTrialCmpBinaryCongr _ O hbits'] at h0
      omega
    have hnr : bankTrialLiveWaveRootMode
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root z.bank root) ≠ .RESET := by
      rw [hm']
      intro h
      cases h
    obtain ⟨nb, hnext⟩ :=
      bankTrialCmpLiveNext ring root root z.bank begun hsucc hnc hnr
    have hgoal : bankTrialLocalNext ring root z root =
        ⟨GrantBankReference.bankLocalReferenceStepClamped ring root z.bank root,
          .live nb⟩ :=
      (congrArg (fun x => bankTrialLocalNext ring root x root) hz).trans hnext
    rw [hgoal]
    exact ⟨⟨nb, rfl⟩, hm', htoks', hbits', hsucc⟩

/-- C.5 comparator correctness without the width or lock premises:
b = s + 11 (bankTrialCmpWidth), and the stage invariants track every
digit token exactly. The pinned statement below is a corollary. -/
theorem bankTrialC5ComparisonStrong {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (z : BankTrialLocalState q)
    (hlive : ∃ begun : Bool, z.phase = .live begun)
    (hf : z.bank.success = false)
    (hm : bankTrialLiveWaveRootMode z.bank = .CSTART)
    (htok : ∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken z.bank j = .E)
    (hpos : 0 < bankTrialLiveBinaryValue z.bank) :
    (bankTrialLiveBinaryValue z.bank = bankTrialLiveThetaBinary q →
      (bankTrialLocalRun ring root
        (bankTrialC5ComparisonWord ring root (compileAdvice q).b) z).phase =
          .won) ∧
    (bankTrialLiveBinaryValue z.bank ≠ bankTrialLiveThetaBinary q →
      (∃ begun : Bool,
        (bankTrialLocalRun ring root
          (bankTrialC5ComparisonWord ring root (compileAdvice q).b) z).phase =
            .live begun) ∧
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root
          (bankTrialC5ComparisonWord ring root (compileAdvice q).b) z).bank =
          .ARMED ∧
      (∀ j : Fin (compileAdvice q).b,
        bankTrialLiveWaveToken
          (bankTrialLocalRun ring root
            (bankTrialC5ComparisonWord ring root (compileAdvice q).b) z).bank j =
          .E) ∧
      (∀ j : Fin (compileAdvice q).b,
        bankTrialLiveWaveBit
          (bankTrialLocalRun ring root
            (bankTrialC5ComparisonWord ring root (compileAdvice q).b) z).bank j =
          bankTrialLiveWaveBit z.bank j) ∧
      (bankTrialLocalRun ring root
        (bankTrialC5ComparisonWord ring root (compileAdvice q).b) z).bank.success =
          false) := by
  have hw11 := bankTrialCmpWidth q
  have e1 : (compileAdvice q).b - 1 = (compileAdvice q).b - 2 + 1 := by omega
  have hrun : bankTrialLocalRun ring root
      (bankTrialC5ComparisonWord ring root (compileAdvice q).b) z =
    bankTrialLocalRun ring root
      ((List.range ((compileAdvice q).b - 2 + 1)).reverse.map
        (fun i => Counter.site ring root i))
      (bankTrialLocalNext ring root
        (bankTrialLocalRun ring root
          (bankTrialC5OutwardEdges ring root ((compileAdvice q).b - 2 + 1))
          (bankTrialLocalNext ring root z root))
        (Counter.site ring root ((compileAdvice q).b - 2 + 1))) := by
    unfold bankTrialC5ComparisonWord
    rw [e1, bankTrialLocalRunAppend, bankTrialLocalRunAppend,
      bankTrialLocalRunAppend]
    rfl
  have h1 := bankTrialCmpLaunch ring root hw z hlive hf hm htok
  have h2 := bankTrialCmpOutward ring root hw z.bank
    ((compileAdvice q).b - 2 + 1) (by omega) _ h1
  have h3 := bankTrialCmpTop ring root hw z.bank
    ((compileAdvice q).b - 2) (by omega) _ h2
  obtain ⟨z', h4, hz'⟩ := bankTrialCmpInward ring root hw z.bank _
    ((compileAdvice q).b - 2) (by omega) _ h3
  have hfin := bankTrialCmpRootDecision ring root hw z.bank hpos _ z' h4
  have hiff : bankTrialCmpValue z.bank ((compileAdvice q).b - 2 + 1) = true ↔
      bankTrialLiveBinaryValue z.bank = bankTrialLiveThetaBinary q := by
    rw [bankTrialCmpValueIff, bankTrialCmpBinaryIff]
    constructor
    · intro h l hl
      exact h l (by omega)
    · intro h l hl
      exact h l (by omega)
  have hall : bankTrialLocalRun ring root
      (bankTrialC5ComparisonWord ring root (compileAdvice q).b) z =
        bankTrialLocalNext ring root z' root := hrun.trans hz'
  rw [hall]
  refine ⟨fun heq => hfin.1 (hiff.mpr heq), fun hne => hfin.2 ?_⟩
  cases hv : bankTrialCmpValue z.bank ((compileAdvice q).b - 2 + 1) with
  | false => rfl
  | true => exact absurd (hiff.mp hv) hne

/-- C.5 comparator correctness on the local trial observer. -/
theorem bankTrialC5ComparisonCorrect {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hb : 2 ≤ (compileAdvice q).b)
    (z : BankTrialLocalState q)
    (hlock : BankTrialLiveNoResetLocked z)
    (hlive : ∃ begun : Bool, z.phase = .live begun)
    (hf : z.bank.success = false)
    (hm : bankTrialLiveWaveRootMode z.bank = .CSTART)
    (htok : ∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken z.bank j = .E)
    (hpos : 0 < bankTrialLiveBinaryValue z.bank) :
    (bankTrialLiveBinaryValue z.bank = bankTrialLiveThetaBinary q →
      (bankTrialLocalRun ring root
        (bankTrialC5ComparisonWord ring root (compileAdvice q).b) z).phase =
          .won) ∧
    (bankTrialLiveBinaryValue z.bank ≠ bankTrialLiveThetaBinary q →
      (∃ begun : Bool,
        (bankTrialLocalRun ring root
          (bankTrialC5ComparisonWord ring root (compileAdvice q).b) z).phase =
            .live begun) ∧
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root
          (bankTrialC5ComparisonWord ring root (compileAdvice q).b) z).bank =
          .ARMED ∧
      (∀ j : Fin (compileAdvice q).b,
        bankTrialLiveWaveToken
          (bankTrialLocalRun ring root
            (bankTrialC5ComparisonWord ring root (compileAdvice q).b) z).bank j =
          .E) ∧
      (∀ j : Fin (compileAdvice q).b,
        bankTrialLiveWaveBit
          (bankTrialLocalRun ring root
            (bankTrialC5ComparisonWord ring root (compileAdvice q).b) z).bank j =
          bankTrialLiveWaveBit z.bank j) ∧
      (bankTrialLocalRun ring root
        (bankTrialC5ComparisonWord ring root (compileAdvice q).b) z).bank.success =
          false) := by
  exact bankTrialC5ComparisonStrong ring root hw z hlive hf hm htok hpos

/-- The comparator Prop used by C3, discharged by the comparator theorem. -/
theorem bankTrialC5ComparisonCorrectHolds (n q : Nat)
    (ring : DirectedRing n) (root : Fin n) :
    BankTrialC5ComparisonCorrect n q ring root := by
  intro z hw _ _ hlive hf hm htok hpos
  have h := bankTrialC5ComparisonStrong ring root hw z hlive hf hm htok hpos
  by_cases heq : bankTrialLiveBinaryValue z.bank = bankTrialLiveThetaBinary q
  · rw [if_pos heq]
    exact h.1 heq
  · rw [if_neg heq]
    obtain ⟨⟨begun, hph⟩, hmode, htk, hbit, hs⟩ := h.2 heq
    exact ⟨begun, hph, hmode, htk, hbit, hs⟩

/-- C3 unconditionally: from a CLEAN seed, after k < K designated rounds the
observer is ARMED at value k, and after K rounds it is WON. -/
theorem bankTrialC5ConsecutiveArmedDecisionsHolds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hq : 3 ≤ q)
    (hw : BankTrialLiveWindowNonalias n q)
    (hclean : BankTrialLocalClean q S) :
    (∀ k : Nat, k < (compileAdvice q).K →
      BankTrialC5ArmedAt q
        (bankTrialC5CleanRun ring root S
          (bankTrialC5Rounds ring root
            (compileAdvice q).b bankTrialC5Trailing k)) k) ∧
    (bankTrialC5CleanRun ring root S
      (bankTrialC5Rounds ring root
        (compileAdvice q).b bankTrialC5Trailing
        (compileAdvice q).K)).phase = .won :=
  bankTrialC5ConsecutiveArmedDecisions ring root S hq hw
    (Nat.le_trans (by decide) (bankTrialCmpWidth q)) hclean
    (bankTrialC5ComparisonCorrectHolds n q ring root)

end L3

#print axioms L3.bankTrialC5ComparisonCorrect
#print axioms L3.bankTrialC5ComparisonStrong
#print axioms L3.bankTrialC5ConsecutiveArmedDecisionsHolds

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- First C.5 obligation: the clean seed is a locked ARMED gate. -/
def BankTrialProbabilityC5SeedReady {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Prop :=
  BankTrialC5ArmedAt q (bankTrialLocalStart S) 0 ∧
  BankTrialProbabilityArmedGate (bankTrialLocalStart S)

/-- The CLEAN seed really has the C3 initial certificate and gate. -/
theorem bankTrialProbabilityC5SeedReady {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S) :
    BankTrialProbabilityC5SeedReady ring root S := by
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  have ha :
      BankTrialC5ArmedAt q (bankTrialLocalStart S) 0 := by
    change BankTrialC5ArmedAt q
      (bankTrialC5CleanRun ring root S []) 0
    exact bankTrialC5SeedArmed ring root S hw hclean
  unfold BankTrialProbabilityC5SeedReady
  refine ⟨ha, ?_⟩
  obtain ⟨begun, hlive, hm, _, _, _, _⟩ := ha
  change
    (∃ begun : Bool,
      (bankTrialLocalStart S).phase = .live begun) ∧
      bankTrialLiveWaveRootMode S = .ARMED
  exact ⟨⟨begun, hlive⟩, hm⟩

/-- Next actual incident port is fair in the original n-edge
scheduler at every certified live ARMED cut. -/
def BankTrialProbabilityC5ArmedCutFair {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  2 * (compileAdvice q).bankLeaseCap ≤ n →
  ∀ z : BankTrialLocalState q,
    BankTrialLiveNoResetLocked z →
    BankTrialProbabilityArmedGate z →
    ∀ T : Nat,
      bankTrialProbabilityFirstIncidentMass
          root (ring.leftNeighbor root) true T =
        bankTrialProbabilityFirstIncidentMass
          root (ring.leftNeighbor root) false T

/-- The existing green original-clock first-incident theorem. -/
theorem bankTrialProbabilityC5ArmedCutFair {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    BankTrialProbabilityC5ArmedCutFair (q := q) ring root := by
  intro hlarge z hlock hgate T
  exact bankTrialProbabilityLockedArmedFirstIncidentFair
    ring root hlarge z hlock hgate T

/-- C3 supplies a real but individually rare designated word:
prefix k is ARMED at value k, and the Kth round is WON. -/
def BankTrialProbabilityC5DesignatedCompletion {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Prop :=
  (∀ k : Nat, k < (compileAdvice q).K →
    BankTrialC5ArmedAt q
      (bankTrialC5CleanRun ring root S
        (bankTrialC5Rounds ring root
          (compileAdvice q).b bankTrialC5Trailing k)) k) ∧
  (bankTrialC5CleanRun ring root S
    (bankTrialC5Rounds ring root
      (compileAdvice q).b bankTrialC5Trailing
      (compileAdvice q).K)).phase = .won

/-- Exact re-use of unconditional C1/C2/C3 from Compare. -/
theorem bankTrialProbabilityC5DesignatedCompletion {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S) :
    BankTrialProbabilityC5DesignatedCompletion ring root S := by
  have hq : 3 ≤ q := by
    have hsmall :
        (compileAdvice q).useSmall = decide (q ≤ qStar) := rfl
    rw [hsmall] at hsp
    have hnot : ¬ q ≤ qStar := of_decide_eq_false hsp
    change ¬ q ≤ 79 at hnot
    omega
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  exact bankTrialC5ConsecutiveArmedDecisionsHolds
    ring root S hq hw hclean

/-- One physical C.1 timeout numerator. -/
def bankTrialProbabilityC5WorkerNumerator (q : Nat) : Nat :=
  2 ^ (2 * (compileAdvice q).b + 2) *
    4 ^ (11 * (compileAdvice q).b + 24)

/-- One physical C.1 timeout denominator. -/
def bankTrialProbabilityC5WorkerDenominator (q : Nat) : Nat :=
  5 ^ (11 * (compileAdvice q).b + 24)

/-- NEW obligation: actual postservice worker origins carry
conditional rarity on the SAME physical scheduler suffix.
A separate adapter from the green physical CounterTrialLower
reset, increment and comparison rarities remains necessary. -/
def BankTrialProbabilityC5WorkerRarity {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    {O : Type}
    (starts : BankTrialLocalState q → Fin n → List O)
    (timeout : O → List (Fin n) → Bool) : Prop :=
  Prob.OriginRarity
    bankTrialLocalTerminal starts timeout
    (bankTrialProbabilityC5WorkerNumerator q)
    (bankTrialProbabilityC5WorkerDenominator q)

/-- NEW obligation: every actual CLEAN-start word has at most
2K+1 materialized tagged origins, not just active token slots. -/
def BankTrialProbabilityC5WorkerStartCap {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    {O : Type}
    (starts : BankTrialLocalState q → Fin n → List O) : Prop :=
  ∀ w : List (Fin n),
    Prob.originsWord
      (bankTrialLocalNext ring root) bankTrialLocalTerminal
      starts (bankTrialLocalStart S) w ≤
        2 * (compileAdvice q).K + 1

/-- Original-clock mass of some actual tagged worker timeout. -/
noncomputable def bankTrialProbabilityC5WorkerTimeoutMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    {O : Type}
    (starts : BankTrialLocalState q → Fin n → List O)
    (timeout : O → List (Fin n) → Bool) (T : Nat) : Nat :=
  Prob.originEventNumerator
    (bankTrialLocalNext ring root) bankTrialLocalTerminal
    starts timeout (bankTrialLocalStart S) T

/-- Numerically, all 2K+1 possible origin failures fit
strictly below the C.5 one-over-1024 allowance. -/
theorem bankTrialProbabilityC5WorkerBudget (q : Nat)
    (hsp : (compileAdvice q).useSmall = false)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b) :
    1024 * (2 * (compileAdvice q).K + 1) *
        bankTrialProbabilityC5WorkerNumerator q <
      bankTrialProbabilityC5WorkerDenominator q := by
  have hsmall := bankTrialProbabilitySpatialWatchdogTiny q hsp
  have hcount :
      2 * (compileAdvice q).K + 1 ≤
        2 ^ ((compileAdvice q).b + 1) + 1 := by
    rw [Nat.pow_succ]
    omega
  unfold bankTrialProbabilityC5WorkerNumerator
    bankTrialProbabilityC5WorkerDenominator
  calc
    1024 * (2 * (compileAdvice q).K + 1) *
        (2 ^ (2 * (compileAdvice q).b + 2) *
          4 ^ (11 * (compileAdvice q).b + 24)) ≤
      1024 * (2 ^ ((compileAdvice q).b + 1) + 1) *
        (2 ^ (2 * (compileAdvice q).b + 2) *
          4 ^ (11 * (compileAdvice q).b + 24)) :=
      Nat.mul_le_mul_right _
        (Nat.mul_le_mul_left 1024 hcount)
    _ < 5 ^ (11 * (compileAdvice q).b + 24) := by
      simpa only [Nat.mul_assoc] using hsmall

/-- The arithmetic step of the worker union bound, over opaque
naturals so that no numeral power is ever unfolded. -/
theorem bankTrialProbabilityC5WorkerTimeoutArith {D N K M X : Nat}
    (hD : 0 < D) (hun : D * M ≤ N * (X * K))
    (hb : 1024 * K * N < D) : 1024 * M ≤ X := by
  have h : D * (1024 * M) ≤ D * X := by
    calc
      D * (1024 * M) = 1024 * (D * M) := Nat.mul_left_comm D 1024 M
      _ ≤ 1024 * (N * (X * K)) := Nat.mul_le_mul_left 1024 hun
      _ = (1024 * K * N) * X := by
        simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      _ ≤ D * X := Nat.mul_le_mul_right X (Nat.le_of_lt hb)
  exact Nat.le_of_mul_le_mul_left h hD

/-- PROVED conditional worker union bound, without independence:
the actual observer origin rarity and all-word cap suffice. -/
theorem bankTrialProbabilityC5WorkerTimeoutTiny {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    {O : Type}
    (starts : BankTrialLocalState q → Fin n → List O)
    (timeout : O → List (Fin n) → Bool)
    (hsp : (compileAdvice q).useSmall = false)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (hrare : BankTrialProbabilityC5WorkerRarity
      ring root starts timeout)
    (hcap : BankTrialProbabilityC5WorkerStartCap
      ring root S starts)
    (T : Nat) :
    1024 * bankTrialProbabilityC5WorkerTimeoutMass
        ring root S starts timeout T ≤ n ^ T := by
  have hfirst := Prob.origin_counting_le
    (bankTrialLocalNext ring root) bankTrialLocalTerminal
    starts timeout
    (bankTrialProbabilityC5WorkerNumerator q)
    (bankTrialProbabilityC5WorkerDenominator q)
    hrare (bankTrialLocalStart S) T
  have hcount :
      Prob.originsNumerator
          (bankTrialLocalNext ring root) bankTrialLocalTerminal
          starts (bankTrialLocalStart S) T ≤
        n ^ T * (2 * (compileAdvice q).K + 1) := by
    change Prob.scheduleSum n T
        (Prob.originsWord
          (bankTrialLocalNext ring root) bankTrialLocalTerminal
          starts (bankTrialLocalStart S)) ≤
        n ^ T * (2 * (compileAdvice q).K + 1)
    calc
      _ ≤ Prob.scheduleSum n T
          (fun _ => 2 * (compileAdvice q).K + 1) := by
        apply bankTrialProbabilityScheduleSumMono
        intro w
        exact hcap w
      _ = n ^ T * (2 * (compileAdvice q).K + 1) :=
        bankTrialProbabilityScheduleSumConst
          n T (2 * (compileAdvice q).K + 1)
  have hunion :
      bankTrialProbabilityC5WorkerDenominator q *
        Prob.originEventNumerator
          (bankTrialLocalNext ring root) bankTrialLocalTerminal
          starts timeout (bankTrialLocalStart S) T ≤
      bankTrialProbabilityC5WorkerNumerator q *
        (n ^ T * (2 * (compileAdvice q).K + 1)) :=
    Nat.le_trans hfirst
      (Nat.mul_le_mul_left
        (bankTrialProbabilityC5WorkerNumerator q) hcount)
  have hbudget := bankTrialProbabilityC5WorkerBudget
    q hsp hwidth
  have hden : 0 < bankTrialProbabilityC5WorkerDenominator q := by
    unfold bankTrialProbabilityC5WorkerDenominator
    exact Nat.pow_pos (by omega)
  unfold bankTrialProbabilityC5WorkerTimeoutMass
  exact bankTrialProbabilityC5WorkerTimeoutArith hden hunion hbudget

/-- Actual K-head event and completed worker return. WON and
LIVE ARMED are distinguished: no success is assumed here. -/
noncomputable def bankTrialProbabilityC5CompletedHeadWord {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (w : List (Fin n)) : Prop :=
  bankTrialProbabilityHeadEvent ring root w
      (compileAdvice q).K (bankTrialLocalStart S) ∧
    ((bankTrialLocalRun ring root w
       (bankTrialLocalStart S)).phase = .won ∨
      ∃ begun : Bool,
        (bankTrialLocalRun ring root w
           (bankTrialLocalStart S)).phase = .live begun ∧
        bankTrialLiveWaveRootMode
          (bankTrialLocalRun ring root w
            (bankTrialLocalStart S)).bank = .ARMED)

/-- True original n-edge numerator of completed K-head words. -/
noncomputable def bankTrialProbabilityC5CompletedHeadMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T : Nat) : Nat :=
  Prob.scheduleSum n T (fun w =>
    if bankTrialProbabilityC5CompletedHeadWord ring root S w
    then 1 else 0)

/-- NEW all-word bridge, not proved by the single C3 schedule:
K adapted heads plus a completed return cannot be an
unsuccessful LIVE ARMED state. -/
def BankTrialProbabilityC5CompletedHeadSound {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Prop :=
  (compileAdvice q).useSmall = false →
  2 * (compileAdvice q).bankLeaseCap ≤ n →
  (compileAdvice q).K < 2 ^ (compileAdvice q).b →
  BankTrialLocalClean q S →
  ∀ w : List (Fin n),
    bankTrialProbabilityC5CompletedHeadWord ring root S w →
      (bankTrialLocalRun ring root w
        (bankTrialLocalStart S)).phase = .won

/-- NEW finite-horizon C.5 probability obligation. Repeated
adapted fair root races, at most 2K+1 worker starts,
conditional C.1 rarity and a common terminal horizon
must provide this inequality; the designated word alone
does not suffice. -/
def BankTrialProbabilityC5CompletedHeadMassLower {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Prop :=
  (compileAdvice q).useSmall = false →
  2 * (compileAdvice q).bankLeaseCap ≤ n →
  (compileAdvice q).K < 2 ^ (compileAdvice q).b →
  BankTrialLocalClean q S →
  ∃ T : Nat,
    1023 * n ^ T ≤
      1024 * 2 ^ (compileAdvice q).K *
        bankTrialProbabilityC5CompletedHeadMass ring root S T

/-- Conditional final implication to the EXISTING lower target.
Only CompletedHeadSound and CompletedHeadMassLower are
assumed as explicitly named Props, not asserted as theorems. -/
theorem bankTrialProbabilityThetaLowerOfCompletedHead {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsound : BankTrialProbabilityC5CompletedHeadSound
      ring root S)
    (hmass : BankTrialProbabilityC5CompletedHeadMassLower
      ring root S) :
    BankTrialProbabilityThetaLowerTarget ring root S := by
  intro hsp hlarge hwidth hclean
  obtain ⟨T, hlower⟩ := hmass hsp hlarge hwidth hclean
  refine ⟨T, ?_⟩
  have hsubset :
      bankTrialProbabilityC5CompletedHeadMass
          ring root S T ≤
        bankTrialProbabilityWinMass ring root S T := by
    unfold bankTrialProbabilityC5CompletedHeadMass
      bankTrialProbabilityWinMass
    apply bankTrialProbabilityScheduleSumMono
    intro w
    by_cases hg :
        bankTrialProbabilityC5CompletedHeadWord ring root S w
    · have hw := hsound hsp hlarge hwidth hclean w hg
      simp only [if_pos hg, if_pos hw]
      exact Nat.le_refl _
    · simp only [if_neg hg]
      exact Nat.zero_le _
  exact Nat.le_trans hlower
    (Nat.mul_le_mul_left
      (1024 * 2 ^ (compileAdvice q).K) hsubset)

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- An adapted head event requires at least the specified number of
actual OLD-LIVE-ARMED root-outgoing decisions. This is one direction
only: no claim about the final BANK comparison or WON phase. -/
theorem bankTrialProbabilityHeadEventCountLower {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (word : List (Fin n)) (k : Nat)
      (z : BankTrialLocalState q),
      bankTrialProbabilityHeadEvent ring root word k z →
        k ≤ bankTrialLiveHeadCount ring root word z := by
  intro word
  induction word with
  | nil =>
      intro k z h
      change k = 0 at h
      cases k with
      | zero =>
          exact Nat.le_refl 0
      | succ k =>
          cases h
  | cons e tail ih =>
      intro k z h
      cases k with
      | zero =>
          exact Nat.zero_le _
      | succ k =>
          by_cases hg : BankTrialProbabilityArmedGate z
          · by_cases he : e = root
            · have ht :
                bankTrialProbabilityHeadEvent ring root tail k
                  (bankTrialLocalNext ring root z e) := by
                simpa only [bankTrialProbabilityHeadEvent,
                  if_pos hg, if_pos he] using h
              have hh := ih k (bankTrialLocalNext ring root z e) ht
              change k + 1 ≤
                (if BankTrialProbabilityArmedGate z ∧ e = root
                  then 1 else 0) +
                  bankTrialLiveHeadCount ring root tail
                    (bankTrialLocalNext ring root z e)
              rw [if_pos ⟨hg, he⟩]
              omega
            · by_cases hi : ring.rightNeighbor e = root
              · have hf : False := by
                  simpa only [bankTrialProbabilityHeadEvent,
                    if_pos hg, if_neg he, if_pos hi] using h
                exact False.elim hf
              · have ht :
                  bankTrialProbabilityHeadEvent ring root tail (k + 1)
                    (bankTrialLocalNext ring root z e) := by
                  simpa only [bankTrialProbabilityHeadEvent,
                    if_pos hg, if_neg he, if_neg hi] using h
                have hh := ih (k + 1)
                  (bankTrialLocalNext ring root z e) ht
                have hzero :
                    ¬ (BankTrialProbabilityArmedGate z ∧ e = root) := by
                  intro ha
                  exact he ha.2
                change k + 1 ≤
                  (if BankTrialProbabilityArmedGate z ∧ e = root
                    then 1 else 0) +
                    bankTrialLiveHeadCount ring root tail
                      (bankTrialLocalNext ring root z e)
                rw [if_neg hzero]
                simpa only [Nat.zero_add] using hh
          · have ht :
              bankTrialProbabilityHeadEvent ring root tail (k + 1)
                (bankTrialLocalNext ring root z e) := by
              simpa only [bankTrialProbabilityHeadEvent,
                if_neg hg] using h
            have hh := ih (k + 1)
              (bankTrialLocalNext ring root z e) ht
            have hzero :
                ¬ (BankTrialProbabilityArmedGate z ∧ e = root) := by
              intro ha
              exact hg ha.1
            change k + 1 ≤
              (if BankTrialProbabilityArmedGate z ∧ e = root
                then 1 else 0) +
                bankTrialLiveHeadCount ring root tail
                  (bankTrialLocalNext ring root z e)
            rw [if_neg hzero]
            simpa only [Nat.zero_add] using hh

/-- Every completed-head word has paid at least K actual root heads.
The terminal alternative in CompletedHeadWord is not used here. -/
theorem bankTrialProbabilityC5CompletedHeadHasHeadCount {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (w : List (Fin n))
    (h : bankTrialProbabilityC5CompletedHeadWord ring root S w) :
    (compileAdvice q).K ≤
      bankTrialLiveHeadCount ring root w (bankTrialLocalStart S) := by
  obtain ⟨hhead, _⟩ := h
  exact bankTrialProbabilityHeadEventCountLower ring root w
    (compileAdvice q).K (bankTrialLocalStart S) hhead

/-- The existing G11b all-word potential yields only an upper
bound on current binary credit at a LIVE completed-head endpoint.
It is not an equality or a completed-comparator certificate. -/
theorem bankTrialProbabilityC5CompletedHeadLiveArmedBound {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (w : List (Fin n))
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (hword : bankTrialProbabilityC5CompletedHeadWord ring root S w)
    (begun : Bool)
    (hlive : (bankTrialLocalRun ring root w
      (bankTrialLocalStart S)).phase = .live begun) :
    (compileAdvice q).K ≤
        bankTrialLiveHeadCount ring root w (bankTrialLocalStart S) ∧
      bankTrialLiveBinaryValue
          (bankTrialLocalRun ring root w (bankTrialLocalStart S)).bank ≤
        bankTrialLiveHeadCount ring root w (bankTrialLocalStart S) := by
  have hcount := bankTrialProbabilityC5CompletedHeadHasHeadCount
    ring root S w hword
  have hwindow : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  have hledger := bankTrialProbabilityLockedCarryCleanWords
    ring root hwindow S hclean w
  exact ⟨hcount,
    Nat.le_trans (bankTrialLiveBinaryLeCarry
      ((bankTrialLocalRun ring root w
        (bankTrialLocalStart S)).bank))
      (hledger begun hlive)⟩

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- CLEAN-origin all-word invariant. In addition to the original
six fields, a LIVE state cannot be in RWAIT: reset-worker RR/RL
belongs to RECOVERY and may erase positive digit credit. The
seventh field is local to the BANK word, not a history oracle. -/
structure BankTrialC5CompletedHeadInvariant (q : Nat)
    (z : BankTrialLocalState q) (heads : Nat) : Prop where
  liveBound :
    ∀ begun : Bool, z.phase = .live begun →
      heads ≤ (compileAdvice q).K
  liveCarry :
    ∀ begun : Bool, z.phase = .live begun →
      bankTrialLiveCarryValue z.bank = heads
  armedStrict :
    ∀ begun : Bool, z.phase = .live begun →
      bankTrialLiveWaveRootMode z.bank = .ARMED →
        heads < (compileAdvice q).K
  crZeroWitness :
    ∀ begun : Bool, z.phase = .live begun →
      ∀ j : Fin (compileAdvice q).b,
        bankTrialLiveWaveToken z.bank j = .CR0 →
          ∃ i : Fin (compileAdvice q).b,
            i.val ≤ j.val ∧
            bankTrialLiveWaveBit z.bank i ≠
              (compileAdvice q).theta i.val
  clZeroWitness :
    ∀ begun : Bool, z.phase = .live begun →
      ∀ j : Fin (compileAdvice q).b,
        bankTrialLiveWaveToken z.bank j = .CL0 →
          bankTrialLiveBinaryValue z.bank ≠
            bankTrialLiveThetaBinary q
  locked : BankTrialLiveNoResetLocked z
  noRWAIT :
    ∀ begun : Bool, z.phase = .live begun →
      bankTrialLiveWaveRootMode z.bank ≠ .RWAIT

/-- Every genuine CLEAN state seeds the strengthened invariant.
The additional RWAIT exclusion follows from the literal ARMED
root mode; no lease hypothesis is needed beyond CLEAN. -/
theorem bankTrialC5CompletedHeadInvariantStart {q : Nat}
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hK : 0 < (compileAdvice q).K)
    (hclean : BankTrialLocalClean q S) :
    BankTrialC5CompletedHeadInvariant q
      (bankTrialLocalStart S) 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro begun hlive
    exact Nat.zero_le _
  · intro begun hlive
    exact bankTrialLiveCarryClean S hclean
  · intro begun hlive hmode
    exact hK
  · intro begun hlive j htok
    have he : bankTrialLiveWaveToken S j = .E :=
      (hclean.2.2.1 (j.val + 1) (by omega) (by omega)).2
    change bankTrialLiveWaveToken S j = .CR0 at htok
    rw [he] at htok
    cases htok
  · intro begun hlive j htok
    have he : bankTrialLiveWaveToken S j = .E :=
      (hclean.2.2.1 (j.val + 1) (by omega) (by omega)).2
    change bankTrialLiveWaveToken S j = .CL0 at htok
    rw [he] at htok
    cases htok
  · exact bankTrialLiveNoResetLockedStart S hclean
  · intro begun hlive hrwait
    change (S.fields ⟨0, by omega⟩).1 = .RWAIT at hrwait
    rw [hclean.2.1] at hrwait
    cases hrwait

/-- The remaining source-edge-table obligation, scoped to the
actual CLEAN-reachable prefixes and the nonalias/width regime.
This is a named OPEN Prop, NOT a proven step theorem. -/
def BankTrialC5CompletedHeadEdgePreservation {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Prop :=
  2 * (compileAdvice q).bankLeaseCap ≤ n →
  (compileAdvice q).K < 2 ^ (compileAdvice q).b →
  BankTrialLocalClean q S →
  ∀ (pre : List (Fin n)) (e : Fin n),
    BankTrialC5CompletedHeadInvariant q
      (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
      (bankTrialLiveHeadCount ring root pre (bankTrialLocalStart S)) →
    BankTrialC5CompletedHeadInvariant q
      (bankTrialLocalRun ring root (pre ++ [e])
        (bankTrialLocalStart S))
      (bankTrialLiveHeadCount ring root (pre ++ [e])
        (bankTrialLocalStart S))

/-- Reachability induction: an authenticated one-edge invariant
extends to every actual original-scheduler word. -/
theorem bankTrialC5CompletedHeadInvariantWordsOfStep {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hbase : BankTrialC5CompletedHeadInvariant q
      (bankTrialLocalStart S) 0)
    (hstep : BankTrialC5CompletedHeadEdgePreservation
      ring root S) (word : List (Fin n)) :
    BankTrialC5CompletedHeadInvariant q
      (bankTrialLocalRun ring root word (bankTrialLocalStart S))
      (bankTrialLiveHeadCount ring root word
        (bankTrialLocalStart S)) := by
  have hreverse : ∀ rev : List (Fin n),
      BankTrialC5CompletedHeadInvariant q
        (bankTrialLocalRun ring root rev.reverse
          (bankTrialLocalStart S))
        (bankTrialLiveHeadCount ring root rev.reverse
          (bankTrialLocalStart S)) := by
    intro rev
    induction rev with
    | nil =>
        change BankTrialC5CompletedHeadInvariant q
          (bankTrialLocalStart S) 0
        exact hbase
    | cons e rest ih =>
        rw [List.reverse_cons]
        exact hstep hlarge hwidth hclean rest.reverse e ih
  have h := hreverse word.reverse
  simpa only [List.reverse_reverse] using h

/-- Completed-head soundness follows from the precise remaining
one-edge preservation obligation, without assuming that the C3
designated word authenticates arbitrary schedules. -/
theorem bankTrialProbabilityC5CompletedHeadSoundOfEdgePreservation
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hstep : BankTrialC5CompletedHeadEdgePreservation
      ring root S) :
    BankTrialProbabilityC5CompletedHeadSound ring root S := by
  intro hsp hlarge hwidth hclean word hcompleted
  have hsmall :
      (compileAdvice q).useSmall = decide (q ≤ qStar) := rfl
  rw [hsmall] at hsp
  have hnot : ¬ q ≤ qStar := of_decide_eq_false hsp
  have hK : 0 < (compileAdvice q).K := by
    change ¬ q ≤ 79 at hnot
    change 0 < 2 * q + productionKappa q
    omega
  have hbase := bankTrialC5CompletedHeadInvariantStart
    S hK hclean
  have hinvariant := bankTrialC5CompletedHeadInvariantWordsOfStep
    ring root S hlarge hwidth hclean hbase hstep word
  rcases hcompleted with ⟨hevent, hterminal⟩
  have hcount : (compileAdvice q).K ≤
      bankTrialLiveHeadCount ring root word
        (bankTrialLocalStart S) :=
    bankTrialProbabilityHeadEventCountLower ring root word
      (compileAdvice q).K (bankTrialLocalStart S) hevent
  rcases hterminal with hwon | ⟨begun, hlive, hmode⟩
  · exact hwon
  · have hstrict := hinvariant.armedStrict begun hlive hmode
    omega

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- One appended original scheduler edge, not a surrogate step. -/
theorem bankTrialC5StrengthenedSnocRun {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankTrialLocalState q)
    (pre : List (Fin n)) (e : Fin n) :
    bankTrialLocalRun ring root (pre ++ [e]) z =
      bankTrialLocalNext ring root
        (bankTrialLocalRun ring root pre z) e := by
  rw [bankTrialLocalRunAppend ring root pre [e] z]
  rfl

/-- The paid-head count changes by exactly the old gate indicator. -/
theorem bankTrialC5StrengthenedSnocHeads {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankTrialLocalState q)
    (pre : List (Fin n)) (e : Fin n) :
    bankTrialLiveHeadCount ring root (pre ++ [e]) z =
      bankTrialLiveHeadCount ring root pre z +
        (if BankTrialProbabilityArmedGate
              (bankTrialLocalRun ring root pre z) ∧
              e = root then 1 else 0) := by
  have h := bankTrialLiveHeadCountAppend ring root pre [e] z
  simpa only [bankTrialLiveHeadCount, Nat.add_zero] using h

/-- An active LIVE successor cannot come from an inactive phase. -/
theorem bankTrialC5StrengthenedOldLive {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialLocalState q) (nextBegun : Bool)
    (hnext : (bankTrialLocalNext ring root z e).phase =
      .live nextBegun) :
    ∃ begun : Bool, z.phase = .live begun := by
  cases z with
  | mk B phase =>
      cases phase with
      | live begun => exact ⟨begun, rfl⟩
      | recovery =>
          simp [bankTrialLocalNext] at hnext <;>
            (repeat' split at hnext) <;> cases hnext
      | won =>
          simp [bankTrialLocalNext] at hnext
      | lost =>
          simp [bankTrialLocalNext] at hnext

/-- The first of the original counting fields is inductive on
its own: only an old ARMED root-outgoing service increments heads,
and its old armedStrict certificate makes room for that unit. -/
theorem bankTrialC5StrengthenedLiveBoundNext {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialLocalState q) (heads : Nat)
    (hInv : BankTrialC5CompletedHeadInvariant q z heads)
    (nextBegun : Bool)
    (hnext : (bankTrialLocalNext ring root z e).phase =
      .live nextBegun) :
    heads +
      (if BankTrialProbabilityArmedGate z ∧ e = root
       then 1 else 0) ≤ (compileAdvice q).K := by
  obtain ⟨begun, hlive⟩ :=
    bankTrialC5StrengthenedOldLive ring root e z nextBegun hnext
  have hbound := hInv.liveBound begun hlive
  by_cases hgate : BankTrialProbabilityArmedGate z
  · by_cases he : e = root
    · have hstrict := hInv.armedStrict begun hlive hgate.2
      rw [if_pos ⟨hgate, he⟩]
      omega
    · have hzero :
          ¬ (BankTrialProbabilityArmedGate z ∧ e = root) := by
        intro h
        exact he h.2
      rw [if_neg hzero, Nat.add_zero]
      exact hbound
  · have hzero :
        ¬ (BankTrialProbabilityArmedGate z ∧ e = root) := by
      intro h
      exact hgate h.1
    rw [if_neg hzero, Nat.add_zero]
    exact hbound

/-- The requested actual CLEAN-prefix preservation of liveBound. -/
theorem bankTrialC5StrengthenedLiveBoundStep {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (e : Fin n)
    (hInv : BankTrialC5CompletedHeadInvariant q
      (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
      (bankTrialLiveHeadCount ring root pre (bankTrialLocalStart S))) :
    ∀ nextBegun : Bool,
      (bankTrialLocalRun ring root (pre ++ [e])
        (bankTrialLocalStart S)).phase = .live nextBegun →
      bankTrialLiveHeadCount ring root (pre ++ [e])
        (bankTrialLocalStart S) ≤ (compileAdvice q).K := by
  intro nextBegun hnext
  rw [bankTrialC5StrengthenedSnocRun] at hnext
  have h := bankTrialC5StrengthenedLiveBoundNext
    ring root e
    (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
    (bankTrialLiveHeadCount ring root pre (bankTrialLocalStart S))
    hInv nextBegun hnext
  rw [bankTrialC5StrengthenedSnocHeads]
  exact h

/-- Raw root owner cannot manufacture RWAIT from any old mode
except RESET or RWAIT. Unlike the previous six-field invariant,
the strengthened LIVE envelope excludes both sources. -/
private theorem bankTrialC5StrengthenedRawRootNoRWAIT
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 < b)
    (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false)
    (hnr : x.mode ≠ .RESET) (hnw : x.mode ≠ .RWAIT) :
    (bankPair x y 1 b theta).1.mode ≠ .RWAIT := by
  have hbpos : 1 ≤ b := by omega
  have hbnot : b ≠ 1 := by omega
  cases hm : x.mode with
  | RESET => exact False.elim (hnr hm)
  | RWAIT => exact False.elim (hnw hm)
  | ARMED =>
      cases ht : y.tok <;>
        cases hbit : y.bit <;>
        simp [bankPair, hx, hy, hg, hm, ht, hbit,
          hbpos, hbnot, isRetTok, isWaitMode,
          Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp
  | CSTART =>
      cases ht : y.tok <;>
        cases htheta : theta 0 <;>
        simp [bankPair, hx, hy, hg, hm, ht, htheta,
          hbpos, hbnot, isRetTok, isWaitMode,
          Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp
  | IWAIT =>
      cases ht : y.tok <;>
        by_cases hl : 1 < x.lease <;>
        simp [bankPair, hx, hy, hg, hm, ht, hl,
          hbpos, hbnot, isRetTok, isWaitMode,
          Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp
  | CWAIT =>
      cases ht : y.tok <;>
        by_cases hl : 1 < x.lease <;>
        simp [bankPair, hx, hy, hg, hm, ht, hl,
          hbpos, hbnot, isRetTok, isWaitMode,
          Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp

/-- The unmodified canonical BANK root step inherits the raw
RWAIT-exclusion row via the public root projection. -/
theorem bankTrialC5StrengthenedRootNoRWAIT {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hnr : bankTrialLiveWaveRootMode B ≠ .RESET)
    (hnw : bankTrialLiveWaveRootMode B ≠ .RWAIT) :
    bankTrialLiveWaveRootMode
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B root) ≠ .RWAIT := by
  have hraw := bankTrialC5StrengthenedRawRootNoRWAIT
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨0, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨1, by have := bankTrialCmpWidth q; omega⟩)
    (by change 1 < (compileAdvice q).s + 11; omega)
    rfl rfl rfl hnr hnw
  change (GrantBankReference.bankLocalReferenceInternalPair q B
    ⟨0, by have := bankTrialCmpWidth q; omega⟩).1.mode ≠ .RWAIT at hraw
  have hproj := (bankTrialCmpRoot ring root hw B hf).1
  rw [hproj]
  exact hraw

/-- The incoming-root unary owner either preserves the old
mode or writes RESET, never a new RWAIT from another mode. -/
private theorem bankTrialC5StrengthenedIncomingCellNoRWAIT
    (q : Nat) (x : BankCell)
    (hnw : x.mode ≠ .RWAIT) :
    (GrantBankReference.bankLocalReferenceClampedQuad q
      (GrantBankReference.incomingRootBankMap x)).1 ≠ .RWAIT := by
  have hraw :
      (GrantBankReference.incomingRootBankMap x).mode ≠
        .RWAIT := by
    cases hm : x.mode with
    | RWAIT => exact False.elim (hnw hm)
    | RESET =>
        simp [GrantBankReference.incomingRootBankMap,
          isWaitMode, hm]
    | ARMED =>
        simp [GrantBankReference.incomingRootBankMap,
          isWaitMode, hm]
    | IWAIT =>
        by_cases hl : 1 < x.lease <;>
          simp [GrantBankReference.incomingRootBankMap,
            isWaitMode, hm, hl]
    | CSTART =>
        simp [GrantBankReference.incomingRootBankMap,
          isWaitMode, hm]
    | CWAIT =>
        by_cases hl : 1 < x.lease <;>
          simp [GrantBankReference.incomingRootBankMap,
            isWaitMode, hm, hl]
  have hcopy :
      (GrantBankReference.bankLocalReferenceClampedQuad q
        (GrantBankReference.incomingRootBankMap x)).1 =
        (GrantBankReference.incomingRootBankMap x).mode := by
    simp [GrantBankReference.bankLocalReferenceClampedQuad,
      GrantBankReference.bankAgentLeaseQuad, copyBank]
  rw [hcopy]
  exact hraw

/-- The incoming-root row, with both previous selector guards
excluded, has the same no-new-RWAIT property. -/
theorem bankTrialC5StrengthenedIncomingNoRWAIT {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hne : e ≠ root)
    (hin : ring.rightNeighbor e = root)
    (hnw : bankTrialLiveWaveRootMode B ≠ .RWAIT) :
    bankTrialLiveWaveRootMode
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) ≠ .RWAIT := by
  have hx : ¬ (0 < (compileAdvice q).b ∧
      e = Counter.site ring root 0) := by
    intro h
    exact hne (by simpa [Counter.site] using h.2)
  have hy : ¬ (0 < (0 : Nat) ∧
      e = Counter.site ring root (0 - 1)) := by
    intro h
    omega
  have ht : ¬ ((0 : Nat) = (compileAdvice q).b ∧
      e = Counter.site ring root (compileAdvice q).b) := by
    intro h
    have hb : 0 < (compileAdvice q).b := by
      change 0 < (compileAdvice q).s + 11
      omega
    omega
  have hselect := bankTrialLiveCarryIncomingSelected
    ring root e B (Or.inl hin) hf
      ⟨0, by omega⟩ hx hy ht ⟨rfl, hin⟩
  change ((GrantBankReference.bankLocalReferenceStepClamped
    ring root B e).fields ⟨0, by omega⟩).1 ≠ .RWAIT
  rw [hselect]
  exact bankTrialC5StrengthenedIncomingCellNoRWAIT q
    (GrantBankReference.bankLocalReferenceCell B
      ⟨0, by omega⟩) hnw

/-- Exhaustive root/outside/incoming classification for the NEW
local noRWAIT field; ordinary interior and top edges are both
covered by the public nonincident-root frame theorem. -/
theorem bankTrialC5StrengthenedNoRWAITLiveNext {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (begun nextBegun : Bool)
    (hlock : BankTrialLiveNoResetLocked
      (⟨B, .live begun⟩ : BankTrialLocalState q))
    (hnw : bankTrialLiveWaveRootMode B ≠ .RWAIT)
    (hnext : (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) e).phase =
        .live nextBegun) :
    bankTrialLiveWaveRootMode
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) e).bank ≠
          .RWAIT := by
  have hf := bankTrialWindowLiveOldNotLatched
    ring root e B begun nextBegun hnext
  have hnr := hlock.2 begun rfl
  rw [bankTrialLocalNextLiveBank]
  by_cases he : e = root
  · subst e
    exact bankTrialC5StrengthenedRootNoRWAIT
      ring root hw B hf hnr hnw
  · by_cases hin : ring.rightNeighbor e = root
    · exact bankTrialC5StrengthenedIncomingNoRWAIT
        ring root e B hf he hin hnw
    · have hframe := bankTrialLocalRootNonincidentFrame
        ring root e B hf he hin
      change ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨0, by omega⟩).1 ≠ .RWAIT
      rw [hframe]
      exact hnw

/-- The seventh invariant field is preserved on every actual
observer edge. RECOVERY and terminal phases cannot reenter LIVE. -/
theorem bankTrialC5StrengthenedNoRWAITNext {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (z : BankTrialLocalState q) (heads : Nat)
    (hInv : BankTrialC5CompletedHeadInvariant q z heads) :
    ∀ nextBegun : Bool,
      (bankTrialLocalNext ring root z e).phase = .live nextBegun →
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root z e).bank ≠ .RWAIT := by
  intro nextBegun hnext
  cases z with
  | mk B phase =>
      cases phase with
      | live begun =>
          exact bankTrialC5StrengthenedNoRWAITLiveNext
            ring root e hw B begun nextBegun hInv.locked
            (hInv.noRWAIT begun rfl) hnext
      | recovery =>
          simp [bankTrialLocalNext] at hnext <;>
            (repeat' split at hnext) <;> cases hnext
      | won =>
          simp [bankTrialLocalNext] at hnext
      | lost =>
          simp [bankTrialLocalNext] at hnext

/-- The requested CLEAN-prefix one-edge preservation of the
added local mode field; no unproved row Prop is introduced. -/
theorem bankTrialC5StrengthenedNoRWAITStep {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (e : Fin n)
    (hInv : BankTrialC5CompletedHeadInvariant q
      (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
      (bankTrialLiveHeadCount ring root pre (bankTrialLocalStart S))) :
    ∀ nextBegun : Bool,
      (bankTrialLocalRun ring root (pre ++ [e])
        (bankTrialLocalStart S)).phase = .live nextBegun →
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root (pre ++ [e])
          (bankTrialLocalStart S)).bank ≠ .RWAIT := by
  intro nextBegun hnext
  rw [bankTrialC5StrengthenedSnocRun] at hnext ⊢
  exact bankTrialC5StrengthenedNoRWAITNext
    ring root e (bankTrialProbabilityUpperWindow hlarge)
    (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
    (bankTrialLiveHeadCount ring root pre (bankTrialLocalStart S))
    hInv nextBegun hnext

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The seventh field rules out both RESET-worker token kinds
from every LIVE word, using the existing mode-specific lock. -/
theorem bankTrialC5NoResetWorkerInLive {q : Nat}
    (z : BankTrialLocalState q) (heads : Nat)
    (hInv : BankTrialC5CompletedHeadInvariant q z heads)
    (begun : Bool) (hlive : z.phase = .live begun)
    (j : Fin (compileAdvice q).b) :
    bankTrialLiveWaveToken z.bank j ≠ .RR ∧
      bankTrialLiveWaveToken z.bank j ≠ .RL := by
  have hc : BankTrialLiveWaveCertificate q z.bank :=
    hInv.locked.1 begun hlive
  have hReset := hInv.locked.2 begun hlive
  have hRWAIT := hInv.noRWAIT begun hlive
  cases hm : bankTrialLiveWaveRootMode z.bank with
  | RESET => exact False.elim (hReset hm)
  | RWAIT => exact False.elim (hRWAIT hm)
  | ARMED =>
      have ht := hc.headClear j (Or.inl hm)
      constructor
      · intro h
        rw [ht] at h
        cases h
      · intro h
        rw [ht] at h
        cases h
  | CSTART =>
      have ht := hc.headClear j (Or.inr hm)
      constructor
      · intro h
        rw [ht] at h
        cases h
      · intro h
        rw [ht] at h
        cases h
  | IWAIT =>
      rcases hc.iwaitTokens j hm with ht | ht | ht
      · constructor
        · intro h
          rw [ht] at h
          cases h
        · intro h
          rw [ht] at h
          cases h
      · constructor
        · intro h
          rw [ht] at h
          cases h
        · intro h
          rw [ht] at h
          cases h
      · constructor
        · intro h
          rw [ht] at h
          cases h
        · intro h
          rw [ht] at h
          cases h
  | CWAIT =>
      rcases hc.cwaitTokens j hm with ht | ht
      · constructor
        · intro h
          rw [ht] at h
          cases h
        · intro h
          rw [ht] at h
          cases h
      · rcases ht with ht | ht | ht | ht
        · constructor
          · intro h
            rw [ht] at h
            cases h
          · intro h
            rw [ht] at h
            cases h
        · constructor
          · intro h
            rw [ht] at h
            cases h
          · intro h
            rw [ht] at h
            cases h
        · constructor
          · intro h
            rw [ht] at h
            cases h
          · intro h
            rw [ht] at h
            cases h
        · constructor
          · intro h
            rw [ht] at h
            cases h
          · intro h
            rw [ht] at h
            cases h

/-- A single coordinate of a nonnegative Fin-indexed sum cannot
exceed its complete sum. This is core Lean, with no Finset. -/
private theorem bankTrialC5OfFnPointLe :
    ∀ {m : Nat} (f : Fin m → Nat) (i : Fin m),
      f i ≤ (List.ofFn f).sum := by
  intro m
  induction m with
  | zero =>
      intro f i
      exact Fin.elim0 i
  | succ m ih =>
      intro f i
      rw [List.ofFn_succ, List.sum_cons]
      by_cases hi : i = 0
      · subst i
        exact Nat.le_add_right _ _
      · have hiv : i.val ≠ 0 := by
          intro hz
          exact hi (Fin.ext hz)
        obtain ⟨j, hj⟩ :
            ∃ j : Fin m, j.succ = i := by
          refine ⟨⟨i.val - 1, by have hh := i.isLt; omega⟩, ?_⟩
          apply Fin.ext
          change i.val - 1 + 1 = i.val
          omega
        have htail := ih (fun k : Fin m => f k.succ) j
        rw [hj] at htail
        omega

/-- The TOP IR token has credit 2^b and therefore cannot be
present at any LIVE state whose exact carry is at most K<2^b.
This is the specific hypothesis missing from the old top-erasure
inequality, independently of any reachability history. -/
theorem bankTrialC5NoTopIRInLive {q : Nat}
    (z : BankTrialLocalState q) (heads : Nat)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hInv : BankTrialC5CompletedHeadInvariant q z heads)
    (begun : Bool) (hlive : z.phase = .live begun) :
    bankTrialLiveWaveToken z.bank
      ⟨(compileAdvice q).b - 1,
        by have hb := bankTrialCmpWidth q; omega⟩ ≠ .IR := by
  intro hIR
  have hbpos : 0 < (compileAdvice q).b := by
    have hb := bankTrialCmpWidth q
    omega
  have hlast : (compileAdvice q).b - 1 + 1 =
      (compileAdvice q).b := by omega
  have hpoint := bankTrialC5OfFnPointLe
    (fun j : Fin (compileAdvice q).b =>
      bankTrialLiveSlotPotential j.val
        (z.bank.fields ⟨j.val + 1, by omega⟩).2.1
        (z.bank.fields ⟨j.val + 1, by omega⟩).2.2.1)
    (⟨(compileAdvice q).b - 1, by omega⟩ :
      Fin (compileAdvice q).b)
  have htop :
      2 ^ (compileAdvice q).b ≤
        bankTrialLiveSlotPotential ((compileAdvice q).b - 1)
          (z.bank.fields
            ⟨(compileAdvice q).b, by omega⟩).2.1 .IR := by
    unfold bankTrialLiveSlotPotential
    rw [if_pos (rfl : BTok.IR = BTok.IR), hlast]
    exact Nat.le_add_left _ _
  have hlocal :
      2 ^ (compileAdvice q).b ≤
        bankTrialLiveCarryValue z.bank := by
    unfold bankTrialLiveCarryValue
    have hv :
        (z.bank.fields
          ⟨((compileAdvice q).b - 1) + 1, by omega⟩).2.2.1 =
          .IR := by
      change (z.bank.fields
        ⟨((compileAdvice q).b - 1) + 1, by omega⟩).2.2.1 = .IR at hIR
      exact hIR
    have hp :
        bankTrialLiveSlotPotential ((compileAdvice q).b - 1)
          (z.bank.fields
            ⟨((compileAdvice q).b - 1) + 1, by omega⟩).2.1
          (z.bank.fields
            ⟨((compileAdvice q).b - 1) + 1, by omega⟩).2.2.1 =
        bankTrialLiveSlotPotential ((compileAdvice q).b - 1)
          (z.bank.fields
            ⟨(compileAdvice q).b, by omega⟩).2.1 .IR := by
      have hfin : (⟨(compileAdvice q).b - 1 + 1, by omega⟩ :
          Fin ((compileAdvice q).b + 1)) =
          ⟨(compileAdvice q).b, by omega⟩ := Fin.ext hlast
      rw [hfin] at hv ⊢
      rw [hv]
    exact Nat.le_trans htop (by
      rw [← hp]
      exact hpoint)
  have hcarry := hInv.liveCarry begun hlive
  have hbound := hInv.liveBound begun hlive
  rw [hcarry] at hlocal
  omega

/-- The canonical incoming-root unary map preserves bit; the
physical clamp also preserves bit and token. -/
theorem bankTrialC5IncomingBitFrame (q : Nat)
    (x : BankCell) :
    (GrantBankReference.bankLocalReferenceClampedQuad q
      (GrantBankReference.incomingRootBankMap x)).2.1 =
        x.bit := by
  have hclamp := (bankTrialLiveClampBitToken q
    (GrantBankReference.incomingRootBankMap x)).1
  rw [hclamp]
  exact bankTrialLiveIncomingPreservesBit x

/-- Top unary erasure preserves the entire bit/token projection
whenever its old token is not IR. -/
theorem bankTrialC5TopBitTokenFrame (q : Nat)
    (x : BankCell) (hIR : x.tok ≠ .IR) :
    (GrantBankReference.bankLocalReferenceClampedQuad q
      (GrantBankReference.topBoundaryBankMap x)).2.1 = x.bit ∧
    (GrantBankReference.bankLocalReferenceClampedQuad q
      (GrantBankReference.topBoundaryBankMap x)).2.2.1 = x.tok := by
  have h := bankTrialLiveClampBitToken q
    (GrantBankReference.topBoundaryBankMap x)
  constructor
  · rw [h.1]
    rfl
  · rw [h.2]
    simp [GrantBankReference.topBoundaryBankMap, hIR]

/-- On an unsupported scheduler edge, the *whole seven-field*
invariant is preserved. No restriction on the old observer phase
and no new trace premise are required. -/
theorem bankTrialC5CompletedHeadOutsideNext {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (z : BankTrialLocalState q) (heads : Nat)
    (hInv : BankTrialC5CompletedHeadInvariant q z heads)
    (hout : ¬ Counter.Support q ring root e) :
    BankTrialC5CompletedHeadInvariant q
      (bankTrialLocalNext ring root z e)
      (heads +
        (if BankTrialProbabilityArmedGate z ∧ e = root
         then 1 else 0)) := by
  have hne : e ≠ root := by
    intro he
    subst e
    exact hout (Or.inr ⟨0, Nat.zero_le _, rfl⟩)
  have hzero :
      ¬ (BankTrialProbabilityArmedGate z ∧ e = root) := by
    intro h
    exact hne h.2
  rw [if_neg hzero, Nat.add_zero]
  have hOld :
      ∀ newBegun : Bool,
        (bankTrialLocalNext ring root z e).phase =
          .live newBegun →
        ∃ oldBegun : Bool, z.phase = .live oldBegun := by
    intro newBegun hnext
    exact bankTrialC5StrengthenedOldLive
      ring root e z newBegun hnext
  have hFrame :
      ∀ newBegun : Bool,
        (bankTrialLocalNext ring root z e).phase =
          .live newBegun →
        (bankTrialLocalNext ring root z e).bank = z.bank := by
    intro newBegun hnext
    obtain ⟨oldBegun, hlive⟩ := hOld newBegun hnext
    have hshape := bankTrialCmpStateEta z oldBegun hlive
    have hr := bankTrialLiveOutsideBankFrame
      ring root e z.bank oldBegun hout
    rw [← hshape] at hr
    exact hr
  have hLocked :
      BankTrialLiveNoResetLocked
        (bankTrialLocalNext ring root z e) := by
    change BankTrialLiveNoResetLocked
      (bankTrialLocalRun ring root [e] z)
    exact bankTrialC5LockedArbitraryWord
      ring root hw [e] z hInv.locked
  refine {
    liveBound := ?_
    liveCarry := ?_
    armedStrict := ?_
    crZeroWitness := ?_
    clZeroWitness := ?_
    locked := hLocked
    noRWAIT := ?_
  }
  · intro newBegun hnext
    obtain ⟨oldBegun, hlive⟩ := hOld newBegun hnext
    exact hInv.liveBound oldBegun hlive
  · intro newBegun hnext
    obtain ⟨oldBegun, hlive⟩ := hOld newBegun hnext
    rw [hFrame newBegun hnext]
    exact hInv.liveCarry oldBegun hlive
  · intro newBegun hnext hmode
    obtain ⟨oldBegun, hlive⟩ := hOld newBegun hnext
    rw [hFrame newBegun hnext] at hmode
    exact hInv.armedStrict oldBegun hlive hmode
  · intro newBegun hnext j htok
    obtain ⟨oldBegun, hlive⟩ := hOld newBegun hnext
    rw [hFrame newBegun hnext] at htok ⊢
    exact hInv.crZeroWitness oldBegun hlive j htok
  · intro newBegun hnext j htok
    obtain ⟨oldBegun, hlive⟩ := hOld newBegun hnext
    rw [hFrame newBegun hnext] at htok ⊢
    exact hInv.clZeroWitness oldBegun hlive j htok
  · intro newBegun hnext hmode
    obtain ⟨oldBegun, hlive⟩ := hOld newBegun hnext
    rw [hFrame newBegun hnext] at hmode
    exact hInv.noRWAIT oldBegun hlive hmode

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Raw outgoing-root owner: under the locked LIVE palette and
the added no-RWAIT field, the first digit's IR-aware credit is
exactly conserved except for a single ARMED head. -/
theorem bankTrialC5RootRawCarryExact
    (b : Nat) (theta : Nat → Bool)
    (x y : BankCell)
    (hb : 1 < b)
    (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false)
    (hnr : x.mode ≠ .RESET) (hnw : x.mode ≠ .RWAIT)
    (hhead : (x.mode = .ARMED ∨ x.mode = .CSTART) →
      y.tok = .E)
    (hiwait : x.mode = .IWAIT →
      y.tok = .E ∨ y.tok = .IR ∨ y.tok = .AL)
    (hcwait : x.mode = .CWAIT →
      y.tok = .E ∨ y.tok = .CR0 ∨ y.tok = .CR1 ∨
        y.tok = .CL0 ∨ y.tok = .CL1) :
    bankTrialLiveSlotPotential 0
        (bankPair x y 1 b theta).2.bit
        (bankPair x y 1 b theta).2.tok =
      bankTrialLiveSlotPotential 0 y.bit y.tok +
        (if x.mode = .ARMED then 1 else 0) := by
  have hbpos : 1 ≤ b := by omega
  have hbne : b ≠ 1 := by omega
  cases hm : x.mode with
  | RESET => exact False.elim (hnr hm)
  | RWAIT => exact False.elim (hnw hm)
  | ARMED =>
      have ht := hhead (Or.inl hm)
      cases hbit : y.bit <;>
        simp [bankPair, hx, hy, hg, hm, ht, hbit,
          hbpos, hbne, bankTrialLiveSlotPotential,
          isRetTok, isWaitMode, Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;>
        simp [bankTrialLiveSlotPotential] <;> omega
  | CSTART =>
      have ht := hhead (Or.inr hm)
      cases hbit : y.bit <;>
        cases htheta : theta 0 <;>
          simp [bankPair, hx, hy, hg, hm, ht, hbit,
            htheta, hbpos, hbne, bankTrialLiveSlotPotential,
            isRetTok, isWaitMode, Id.run_pure, Id.run_bind] <;>
          (repeat' split) <;>
          simp [bankTrialLiveSlotPotential] <;> omega
  | IWAIT =>
      rcases hiwait hm with ht | ht | ht <;>
        by_cases hlease : 1 < x.lease <;>
        cases hbit : y.bit <;>
        simp [bankPair, hx, hy, hg, hm, ht, hlease, hbit,
          hbpos, hbne, bankTrialLiveSlotPotential,
          isRetTok, isWaitMode, Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;>
        simp [bankTrialLiveSlotPotential] <;> omega
  | CWAIT =>
      rcases hcwait hm with ht | ht | ht | ht | ht <;>
        by_cases hlease : 1 < x.lease <;>
        cases hbit : y.bit <;>
        simp [bankPair, hx, hy, hg, hm, ht, hlease, hbit,
          hbpos, hbne, bankTrialLiveSlotPotential,
          isRetTok, isWaitMode, Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;>
        simp [bankTrialLiveSlotPotential] <;> omega

/-- One-coordinate replacement identity for a Nat List.ofFn sum.
This uses the canonical core List.ofFn_succ decomposition. -/
private theorem bankTrialC5SumSwapOne :
    ∀ {m : Nat} (f g : Fin m → Nat) (i : Fin m),
      (∀ j : Fin m, j ≠ i → f j = g j) →
      (List.ofFn f).sum + g i =
        (List.ofFn g).sum + f i := by
  intro m
  induction m with
  | zero =>
      intro f g i h
      exact Fin.elim0 i
  | succ m ih =>
      intro f g i h
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      by_cases hi : i = 0
      · subst i
        have ht :
            (List.ofFn (fun j : Fin m => f j.succ)).sum =
            (List.ofFn (fun j : Fin m => g j.succ)).sum := by
          apply FiniteUniformStoppingTree.ofFn_sum_eq
          intro j
          apply h
          intro hz
          have hv := congrArg Fin.val hz
          change j.val + 1 = 0 at hv
          omega
        rw [ht]
        omega
      · have hiv : i.val ≠ 0 := by
          intro hz
          exact hi (Fin.ext hz)
        obtain ⟨j, hj⟩ :
            ∃ j : Fin m, j.succ = i := by
          refine ⟨⟨i.val - 1, by have hh := i.isLt; omega⟩, ?_⟩
          apply Fin.ext
          change i.val - 1 + 1 = i.val
          omega
        have hmatch : ∀ k : Fin m, k ≠ j →
            f k.succ = g k.succ := by
          intro k hk
          apply h
          intro heq
          apply hk
          apply Fin.ext
          have hv := congrArg Fin.val heq
          have hjv := congrArg Fin.val hj
          change k.val + 1 = i.val at hv
          change j.val + 1 = i.val at hjv
          omega
        have htail := ih
          (fun k : Fin m => f k.succ)
          (fun k : Fin m => g k.succ) j hmatch
        have hhead := h 0 (Ne.symm hi)
        simp only [hj] at htail
        omega

/-- Lift the raw root equality to the actual clamped source
service, using the public root field projection. Every higher
digit is framed; no historical reachability premise is used. -/
theorem bankTrialC5RootCarryExact {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (hnr : bankTrialLiveWaveRootMode B ≠ .RESET)
    (hnw : bankTrialLiveWaveRootMode B ≠ .RWAIT) :
    bankTrialLiveCarryValue
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B root) =
    bankTrialLiveCarryValue B +
      (if bankTrialLiveWaveRootMode B = .ARMED
       then 1 else 0) := by
  have hzero : 0 < (compileAdvice q).b :=
    bankTrialWindowWidthPos q
  have hsource :
      (GrantBankReference.bankLocalReferenceCell B
        ⟨0, by omega⟩).mode ≠ .RESET := hnr
  have hsourceWait :
      (GrantBankReference.bankLocalReferenceCell B
        ⟨0, by omega⟩).mode ≠ .RWAIT := hnw
  have hhead :
      ((GrantBankReference.bankLocalReferenceCell B
        ⟨0, by omega⟩).mode = .ARMED ∨
       (GrantBankReference.bankLocalReferenceCell B
        ⟨0, by omega⟩).mode = .CSTART) →
       (GrantBankReference.bankLocalReferenceCell B
        ⟨1, by omega⟩).tok = .E := by
    intro hm
    exact hc.headClear ⟨0, by omega⟩ hm
  have hiwait :
      (GrantBankReference.bankLocalReferenceCell B
        ⟨0, by omega⟩).mode = .IWAIT →
      (GrantBankReference.bankLocalReferenceCell B
        ⟨1, by omega⟩).tok = .E ∨
      (GrantBankReference.bankLocalReferenceCell B
        ⟨1, by omega⟩).tok = .IR ∨
      (GrantBankReference.bankLocalReferenceCell B
        ⟨1, by omega⟩).tok = .AL := by
    intro hm
    exact hc.iwaitTokens ⟨0, by omega⟩ hm
  have hcwait :
      (GrantBankReference.bankLocalReferenceCell B
        ⟨0, by omega⟩).mode = .CWAIT →
      (GrantBankReference.bankLocalReferenceCell B
        ⟨1, by omega⟩).tok = .E ∨
      (GrantBankReference.bankLocalReferenceCell B
        ⟨1, by omega⟩).tok = .CR0 ∨
      (GrantBankReference.bankLocalReferenceCell B
        ⟨1, by omega⟩).tok = .CR1 ∨
      (GrantBankReference.bankLocalReferenceCell B
        ⟨1, by omega⟩).tok = .CL0 ∨
      (GrantBankReference.bankLocalReferenceCell B
        ⟨1, by omega⟩).tok = .CL1 := by
    intro hm
    rcases hc.cwaitTokens ⟨0, by omega⟩ hm with ht | ht
    · exact Or.inl ht
    · rcases ht with ht | ht | ht | ht
      · exact Or.inr (Or.inl ht)
      · exact Or.inr (Or.inr (Or.inl ht))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ht)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ht)))
  have hraw := bankTrialC5RootRawCarryExact
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B ⟨0, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B ⟨1, by omega⟩)
    (by have hh := bankTrialCmpWidth q; omega)
    rfl rfl rfl hsource hsourceWait hhead hiwait hcwait
  have hfirstRaw :
      bankTrialLiveSlotPotential 0
        (GrantBankReference.bankLocalReferenceInternalPair q B
          ⟨0, by omega⟩).2.bit
        (GrantBankReference.bankLocalReferenceInternalPair q B
          ⟨0, by omega⟩).2.tok =
      bankTrialLiveSlotPotential 0
        (bankTrialLiveWaveBit B ⟨0, by omega⟩)
        (bankTrialLiveWaveToken B ⟨0, by omega⟩) +
        (if bankTrialLiveWaveRootMode B = .ARMED
         then 1 else 0) := by
    exact hraw
  have hproj := bankTrialCmpRoot ring root hw B hf
  have hfirst :
      bankTrialLiveSlotPotential 0
        (bankTrialLiveWaveBit
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B root) ⟨0, by omega⟩)
        (bankTrialLiveWaveToken
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B root) ⟨0, by omega⟩) =
      bankTrialLiveSlotPotential 0
        (bankTrialLiveWaveBit B ⟨0, by omega⟩)
        (bankTrialLiveWaveToken B ⟨0, by omega⟩) +
        (if bankTrialLiveWaveRootMode B = .ARMED
         then 1 else 0) := by
    have hp := (hproj.2 (⟨0, by omega⟩ :
      Fin (compileAdvice q).b)).1 rfl
    rw [hp.1, hp.2]
    exact hfirstRaw
  have hframe :
      ∀ j : Fin (compileAdvice q).b,
        j ≠ ⟨0, by omega⟩ →
        bankTrialLiveSlotPotential j.val
          (bankTrialLiveWaveBit
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root B root) j)
          (bankTrialLiveWaveToken
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root B root) j) =
        bankTrialLiveSlotPotential j.val
          (bankTrialLiveWaveBit B j)
          (bankTrialLiveWaveToken B j) := by
    intro j hj
    have hjv : j.val ≠ 0 := by
      intro hz
      exact hj (Fin.ext hz)
    have hp := (hproj.2 j).2 hjv
    rw [hp.1, hp.2]
  have hswap := bankTrialC5SumSwapOne
    (fun j : Fin (compileAdvice q).b =>
      bankTrialLiveSlotPotential j.val
        (bankTrialLiveWaveBit
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B root) j)
        (bankTrialLiveWaveToken
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B root) j))
    (fun j : Fin (compileAdvice q).b =>
      bankTrialLiveSlotPotential j.val
        (bankTrialLiveWaveBit B j)
        (bankTrialLiveWaveToken B j))
    ⟨0, by omega⟩ hframe
  change bankTrialLiveCarryValue
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B root) +
      bankTrialLiveSlotPotential 0
        (bankTrialLiveWaveBit B ⟨0, by omega⟩)
        (bankTrialLiveWaveToken B ⟨0, by omega⟩) =
    bankTrialLiveCarryValue B +
      bankTrialLiveSlotPotential 0
        (bankTrialLiveWaveBit
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B root) ⟨0, by omega⟩)
        (bankTrialLiveWaveToken
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B root) ⟨0, by omega⟩) at hswap
  rw [hfirst] at hswap
  omega

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Proper interior IR/E owner is an *equality*, not merely the
previous G11b nonincrease inequality. It flips one destination
digit and moves its binary weight into (or out of) IR credit. -/
theorem bankTrialC5InteriorIRPairExact
    (j b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : x.role = j + 1) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hxt : x.tok = .IR) (hyt : y.tok = .E) :
    bankTrialLiveSlotPotential j
        (bankPair x y y.role b theta).1.bit
        (bankPair x y y.role b theta).1.tok +
      bankTrialLiveSlotPotential (j + 1)
        (bankPair x y y.role b theta).2.bit
        (bankPair x y y.role b theta).2.tok =
      bankTrialLiveSlotPotential j x.bit x.tok +
        bankTrialLiveSlotPotential (j + 1) y.bit y.tok := by
  have hpos : 1 ≤ x.role := by omega
  have hxn : x.role ≠ 0 := by omega
  have hxTop : x.role ≠ b := by omega
  have hyn : y.role ≠ 0 := by omega
  have hyPos : 1 ≤ y.role := by omega
  have hyLe : y.role ≤ b := by omega
  have hxLe : x.role ≤ b := by omega
  have hsource :
      (bankPair x y y.role b theta).1.bit = x.bit := by
    simp [bankPair, hpos, hlt, hy, hxn, hxTop,
      hyn, hyPos, hyLe, hxLe, hxt, hyt,
      Id.run_pure, Id.run_bind]
  have hrow := bankTrialInteriorIRForward
    b theta x y hpos hlt hy hxt hyt
  rw [hsource, hrow.1, hrow.2.1, hrow.2.2, hxt, hyt]
  exact bankTrialLiveIRForwardArithmetic j x.bit y.bit

/-- A returning AL travels left without changing either digit's
weight. The AL token is a zero-credit acknowledgment. -/
theorem bankTrialC5InteriorALPairExact
    (j b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : x.role = j + 1) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hxt : x.tok = .E) (hyt : y.tok = .AL) :
    bankTrialLiveSlotPotential j
        (bankPair x y y.role b theta).1.bit
        (bankPair x y y.role b theta).1.tok +
      bankTrialLiveSlotPotential (j + 1)
        (bankPair x y y.role b theta).2.bit
        (bankPair x y y.role b theta).2.tok =
      bankTrialLiveSlotPotential j x.bit x.tok +
        bankTrialLiveSlotPotential (j + 1) y.bit y.tok := by
  have hpos : 1 ≤ x.role := by omega
  have hrow := bankTrialInteriorALReturn
    b theta x y hpos hlt hy hxt hyt
  rw [hrow.1, hrow.2.1, hrow.2.2.1,
    hrow.2.2.2, hxt, hyt]
  rfl

/-- Failed CR0 forwarding also conserves both ordinary digit
weights; its token carries no IR credit. -/
theorem bankTrialC5InteriorCRZeroPairExact
    (j b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : x.role = j + 1) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hxt : x.tok = .CR0) (hyt : y.tok = .E) :
    bankTrialLiveSlotPotential j
        (bankPair x y y.role b theta).1.bit
        (bankPair x y y.role b theta).1.tok +
      bankTrialLiveSlotPotential (j + 1)
        (bankPair x y y.role b theta).2.bit
        (bankPair x y y.role b theta).2.tok =
      bankTrialLiveSlotPotential j x.bit x.tok +
        bankTrialLiveSlotPotential (j + 1) y.bit y.tok := by
  have hpos : 1 ≤ x.role := by omega
  have hrow := bankTrialInteriorCRZeroForward
    b theta x y hpos hlt hy hxt hyt
  rw [hrow.1, hrow.2.1, hrow.2.2.1,
    hrow.2.2.2, hxt, hyt]
  rfl

/-- Failed CL0 return conserves both digit weights and has zero
extra credit. It is the only return that can re-arm the root. -/
theorem bankTrialC5InteriorCLZeroPairExact
    (j b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : x.role = j + 1) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hxt : x.tok = .E) (hyt : y.tok = .CL0) :
    bankTrialLiveSlotPotential j
        (bankPair x y y.role b theta).1.bit
        (bankPair x y y.role b theta).1.tok +
      bankTrialLiveSlotPotential (j + 1)
        (bankPair x y y.role b theta).2.bit
        (bankPair x y y.role b theta).2.tok =
      bankTrialLiveSlotPotential j x.bit x.tok +
        bankTrialLiveSlotPotential (j + 1) y.bit y.tok := by
  have hpos : 1 ≤ x.role := by omega
  have hrow := bankTrialInteriorCLZeroReturn
    b theta x y hpos hlt hy hxt hyt
  rw [hrow.1, hrow.2.1, hrow.2.2.1,
    hrow.2.2.2, hxt, hyt]
  rfl

/-- CR0 at the top turns into CL0 without changing the sum of
the two adjacent bit weights. -/
theorem bankTrialC5InteriorTopCRZeroExact
    (j b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : x.role = j + 1) (hlt : x.role < b)
    (hy : y.role = x.role + 1) (htop : y.role = b)
    (hxt : x.tok = .E) (hyt : y.tok = .CR0) :
    bankTrialLiveSlotPotential j
        (bankPair x y y.role b theta).1.bit
        (bankPair x y y.role b theta).1.tok +
      bankTrialLiveSlotPotential (j + 1)
        (bankPair x y y.role b theta).2.bit
        (bankPair x y y.role b theta).2.tok =
      bankTrialLiveSlotPotential j x.bit x.tok +
        bankTrialLiveSlotPotential (j + 1) y.bit y.tok := by
  have hpos : 1 ≤ x.role := by omega
  have hrow := bankTrialInteriorCRZeroTop
    b theta x y hpos hlt hy htop hxt hyt
  rw [hrow.1, hrow.2.1, hrow.2.2.1,
    hrow.2.2.2, hxt, hyt]
  rfl

/-- A complete digit frame preserves the numerical witness for
a CL0 mismatch. There is no dependence on the worker position. -/
theorem bankTrialC5CLZeroWitnessBitFrame {q : Nat}
    (oldB newB : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hbits : ∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveBit newB j =
        bankTrialLiveWaveBit oldB j)
    (hMismatch :
      bankTrialLiveBinaryValue oldB ≠ bankTrialLiveThetaBinary q) :
    bankTrialLiveBinaryValue newB ≠
      bankTrialLiveThetaBinary q := by
  have hval := bankTrialCmpBinaryCongr newB oldB hbits
  rw [hval]
  exact hMismatch

/-- A CR0 prefix witness survives any changed token position
to its right when all earlier compared digits are framed. -/
theorem bankTrialC5CRZeroWitnessPrefixFrame {q : Nat}
    (oldB newB : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (oldJ newJ : Fin (compileAdvice q).b)
    (horder : oldJ.val ≤ newJ.val)
    (hWitness : ∃ i : Fin (compileAdvice q).b,
      i.val ≤ oldJ.val ∧
      bankTrialLiveWaveBit oldB i ≠
        (compileAdvice q).theta i.val)
    (hbits : ∀ i : Fin (compileAdvice q).b,
      i.val ≤ oldJ.val →
        bankTrialLiveWaveBit newB i =
          bankTrialLiveWaveBit oldB i) :
    ∃ i : Fin (compileAdvice q).b,
      i.val ≤ newJ.val ∧
      bankTrialLiveWaveBit newB i ≠
        (compileAdvice q).theta i.val := by
  obtain ⟨i, hi, hbad⟩ := hWitness
  refine ⟨i, (by omega), ?_⟩
  rw [hbits i hi]
  exact hbad

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- This is the precise still-open *local* source-row interface for
the four unsolved fields. It has no scheduler word and no CLEAN
quantifier. All other fields already have unconditional one-edge
proofs under the strengthened invariant. -/
def BankTrialC5RemainingLiveRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ (z : BankTrialLocalState q) (heads : Nat)
      (e : Fin n),
    BankTrialC5CompletedHeadInvariant q z heads →
    ∀ nextBegun : Bool,
      (bankTrialLocalNext ring root z e).phase = .live nextBegun →
      (bankTrialLiveCarryValue
          (bankTrialLocalNext ring root z e).bank =
        heads +
          (if BankTrialProbabilityArmedGate z ∧ e = root
           then 1 else 0)) ∧
      (bankTrialLiveWaveRootMode
          (bankTrialLocalNext ring root z e).bank = .ARMED →
        heads +
          (if BankTrialProbabilityArmedGate z ∧ e = root
           then 1 else 0) < (compileAdvice q).K) ∧
      (∀ j : Fin (compileAdvice q).b,
        bankTrialLiveWaveToken
          (bankTrialLocalNext ring root z e).bank j = .CR0 →
        ∃ i : Fin (compileAdvice q).b,
          i.val ≤ j.val ∧
          bankTrialLiveWaveBit
            (bankTrialLocalNext ring root z e).bank i ≠
            (compileAdvice q).theta i.val) ∧
      (∀ j : Fin (compileAdvice q).b,
        bankTrialLiveWaveToken
          (bankTrialLocalNext ring root z e).bank j = .CL0 →
        bankTrialLiveBinaryValue
          (bankTrialLocalNext ring root z e).bank ≠
          bankTrialLiveThetaBinary q)

/-- Assembly of all seven fields once the four remaining
source-row properties above are proved. The earlier independent
liveBound, lock and noRWAIT lemmas close the other three fields.
No new invariant hypothesis is invented. -/
theorem bankTrialC5CompletedHeadEdgePreservationOfRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hRows : BankTrialC5RemainingLiveRows (q := q) ring root) :
    BankTrialC5CompletedHeadEdgePreservation ring root S := by
  intro hlarge hwidth hclean pre e hInv
  rw [bankTrialC5StrengthenedSnocRun,
    bankTrialC5StrengthenedSnocHeads]
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  have hLocked : BankTrialLiveNoResetLocked
      (bankTrialLocalNext ring root
        (bankTrialLocalRun ring root pre (bankTrialLocalStart S)) e) := by
    change BankTrialLiveNoResetLocked
      (bankTrialLocalRun ring root [e]
        (bankTrialLocalRun ring root pre
          (bankTrialLocalStart S)))
    exact bankTrialC5LockedArbitraryWord
      ring root hw [e]
      (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
      hInv.locked
  have hNewNoRWAIT := bankTrialC5StrengthenedNoRWAITNext
    ring root e hw
    (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
    (bankTrialLiveHeadCount ring root pre
      (bankTrialLocalStart S)) hInv
  have hRemaining := hRows
    (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
    (bankTrialLiveHeadCount ring root pre
      (bankTrialLocalStart S)) e hInv
  refine {
    liveBound := ?_
    liveCarry := ?_
    armedStrict := ?_
    crZeroWitness := ?_
    clZeroWitness := ?_
    locked := hLocked
    noRWAIT := ?_
  }
  · intro nextBegun hnext
    exact bankTrialC5StrengthenedLiveBoundNext
      ring root e
      (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
      (bankTrialLiveHeadCount ring root pre
        (bankTrialLocalStart S))
      hInv nextBegun hnext
  · intro nextBegun hnext
    exact (hRemaining nextBegun hnext).1
  · intro nextBegun hnext hmode
    exact (hRemaining nextBegun hnext).2.1 hmode
  · intro nextBegun hnext j htok
    exact (hRemaining nextBegun hnext).2.2.1 j htok
  · intro nextBegun hnext j htok
    exact (hRemaining nextBegun hnext).2.2.2 j htok
  · intro nextBegun hnext
    exact hNewNoRWAIT nextBegun hnext

/-- The original probability soundness theorem is now reduced to
a single explicit all-edge local row interface, not an arbitrary
completed-word or designated-schedule assumption. -/
theorem bankTrialProbabilityC5CompletedHeadSoundOfRemainingRows
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hRows : BankTrialC5RemainingLiveRows (q := q) ring root) :
    BankTrialProbabilityC5CompletedHeadSound ring root S := by
  exact bankTrialProbabilityC5CompletedHeadSoundOfEdgePreservation
    ring root S
    (bankTrialC5CompletedHeadEdgePreservationOfRows
      ring root S hRows)

end L3
