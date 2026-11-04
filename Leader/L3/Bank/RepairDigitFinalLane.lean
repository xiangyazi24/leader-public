import Leader.L3.Bank.RepairDigitFinalRank

/-!
# T18: the final-region rank on one lane, shape facts

Lane coordinates: `out i` (`i < R`) are the previous block's output shapes, `inp j`, `lv j`
(`j < m`) the final block's input shapes and carry-live bits. Position `0` of each block is
its delimiter.

* `bankRepairDigitStartOf`: a stuck settled run starts at `k ≥ 1`;
* `bankRepairDigitNeedOf`: deliveries still owed;
* `bankRepairDigitPhiOf`: distance of the previous block's next delivery;
* `bankRepairDigitLamOf`: local weights (packets weigh only while a start exists).
-/

namespace L3.RenewalReferenceClock

set_option autoImplicit false

/-! ### Definitions -/

def bankRepairDigitStartOf (inp : Nat → BankRepairDigitInSh) (lv : Nat → Bool) : Nat → Bool
  | 0 => false
  | k + 1 => bankRepairDigitClsOS (inp (k + 1)) (lv (k + 1)) &&
      bankRepairDigitClsEP (inp k) (lv k)

def bankRepairDigitNeedG (inp : Nat → BankRepairDigitInSh) (lv : Nat → Bool) (k : Nat) : Nat :=
  (if bankRepairDigitStartOf inp lv k = true then k else 0) +
    (if bankRepairDigitClsOP (inp k) (lv k) = true then 0 else 1)

def bankRepairDigitLastStart (m : Nat) (inp : Nat → BankRepairDigitInSh) (lv : Nat → Bool) :
    Nat :=
  bankRepairDigitLastOf (bankRepairDigitStartOf inp lv) m

def bankRepairDigitNeedOf (m : Nat) (inp : Nat → BankRepairDigitInSh) (lv : Nat → Bool) :
    Nat :=
  bankRepairDigitSumCnt (bankRepairDigitNeedG inp lv) 0 (bankRepairDigitLastStart m inp lv)

def bankRepairDigitPhiW (R i : Nat) : BankRepairDigitOutSh → Nat
  | .D _ => 2 * (R - 1 - i)
  | .U => 2 * (R - 1 - i) + 1
  | .E => 2 * R

def bankRepairDigitMinCnt (f : Nat → Nat) (cap : Nat) : Nat → Nat
  | 0 => cap
  | k + 1 => min (bankRepairDigitMinCnt f cap k) (f k)

def bankRepairDigitPhiOf (R : Nat) (out : Nat → BankRepairDigitOutSh) : Nat :=
  bankRepairDigitMinCnt (fun i => bankRepairDigitPhiW R i (out i)) (2 * R) R

def bankRepairDigitLamIn (m j : Nat) (s : Bool) : BankRepairDigitInSh → Nat
  | .E => 0
  | .X => m - j
  | .P _ => if s then m - j + 2 else 0
  | .S T => if j = 0 then m + 1 else if T then m - j + 1 else 0

def bankRepairDigitLam (m j : Nat) (s : Bool) (i : BankRepairDigitInSh) (k : Bool) : Nat :=
  (if k then m - j else 0) + bankRepairDigitLamIn m j s i

def bankRepairDigitLamOf (m : Nat) (s : Bool) (inp : Nat → BankRepairDigitInSh)
    (lv : Nat → Bool) : Nat :=
  bankRepairDigitSumCnt (fun j => bankRepairDigitLam m j s (inp j) (lv j)) 0 m

/-- The lane rank `(2 R + m + 3) * need + [start] * Φ + Λ`. -/
def bankRepairDigitLaneRank (R m : Nat) (out : Nat → BankRepairDigitOutSh)
    (inp : Nat → BankRepairDigitInSh) (lv : Nat → Bool) : Nat :=
  (2 * R + m + 3) * bankRepairDigitNeedOf m inp lv +
    (if 0 < bankRepairDigitLastStart m inp lv then bankRepairDigitPhiOf R out else 0) +
    bankRepairDigitLamOf m (decide (0 < bankRepairDigitLastStart m inp lv)) inp lv

/-- Edges of the final block that strictly lower the local weights. -/
def bankRepairDigitFinActive (s bx : Bool) (x : BankRepairDigitInSh) (kx : Bool)
    (y : BankRepairDigitInSh) (ky : Bool) : Bool :=
  kx || match x with
    | .E => false
    | .X => true
    | .S T => bx || T
    | .P _ => s && !ky && (match y with | .E => true | .S _ => true | _ => false)

def bankRepairDigitSettleSh : BankRepairDigitInSh → BankRepairDigitInSh
  | .P T => .S T
  | i => i

def bankRepairDigitIsPSh : BankRepairDigitInSh → Bool
  | .P _ => true
  | _ => false

def bankRepairDigitIsSSh : BankRepairDigitInSh → Bool
  | .S _ => true
  | _ => false

/-- Receipt condition at final position `k` on shapes. -/
def bankRepairDigitFinOKSh (m k : Nat) (i : BankRepairDigitInSh) (b : Bool) : Prop :=
  (k + 1 = m ∧ b = true) ∨ bankRepairDigitClsEP i b = true

/-! ### Shape classification of the final-block step -/

theorem bankRepairDigitFinStepCls (bx : Bool) (x : BankRepairDigitInSh) (kx : Bool)
    (y : BankRepairDigitInSh) (ky : Bool) :
    ((bankRepairDigitClsOS (bankRepairDigitFinStep bx x kx y ky).1
          (bankRepairDigitFinStep bx x kx y ky).2.1 = true →
        bankRepairDigitClsOS x kx = true) ∧
      (bankRepairDigitClsOS (bankRepairDigitFinStep bx x kx y ky).2.2.1
          (bankRepairDigitFinStep bx x kx y ky).2.2.2 = true →
        bankRepairDigitClsEP (bankRepairDigitFinStep bx x kx y ky).1
          (bankRepairDigitFinStep bx x kx y ky).2.1 = true →
        bankRepairDigitClsOS y ky = true ∧ bankRepairDigitClsEP x kx = true) ∧
      (bankRepairDigitClsEP (bankRepairDigitFinStep bx x kx y ky).2.2.1
          (bankRepairDigitFinStep bx x kx y ky).2.2.2 = true →
        bankRepairDigitClsEP y ky = true) ∧
      (bankRepairDigitClsOP x kx = true →
        bankRepairDigitClsOP (bankRepairDigitFinStep bx x kx y ky).1
          (bankRepairDigitFinStep bx x kx y ky).2.1 = true) ∧
      (bankRepairDigitClsOP y ky = true →
        bankRepairDigitClsOP (bankRepairDigitFinStep bx x kx y ky).2.2.1
          (bankRepairDigitFinStep bx x kx y ky).2.2.2 = true)) ∨
    (bankRepairDigitIsPSh x = true ∧ kx = false ∧ y = .E ∧ ky = false ∧
      (bankRepairDigitFinStep bx x kx y ky).1 = .E ∧
      (bankRepairDigitFinStep bx x kx y ky).2.1 = false ∧
      (bankRepairDigitFinStep bx x kx y ky).2.2.1 = x ∧
      (bankRepairDigitFinStep bx x kx y ky).2.2.2 = false) ∨
    (bankRepairDigitIsPSh x = true ∧ kx = false ∧ bankRepairDigitIsSSh y = true ∧ ky = false ∧
      (bankRepairDigitFinStep bx x kx y ky).1 = bankRepairDigitSettleSh x ∧
      (bankRepairDigitFinStep bx x kx y ky).2.1 = false ∧
      (bankRepairDigitFinStep bx x kx y ky).2.2.1 = y ∧
      (bankRepairDigitFinStep bx x kx y ky).2.2.2 = false) := by
  cases bx <;> rcases x with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> cases kx <;>
    rcases y with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> cases ky <;> decide

/-- The local weights of a final-block edge (fixed packet switch `s`). -/
theorem bankRepairDigitFinLamLocal (m j : Nat) (s : Bool) (hj : j + 1 < m)
    (x : BankRepairDigitInSh) (kx : Bool) (y : BankRepairDigitInSh) (ky : Bool)
    (hs : bankRepairDigitClsOP x kx = true → bankRepairDigitClsOS y ky = true → s = true) :
    bankRepairDigitLam m j s (bankRepairDigitFinStep (decide (j = 0)) x kx y ky).1
        (bankRepairDigitFinStep (decide (j = 0)) x kx y ky).2.1 +
      bankRepairDigitLam m (j + 1) s (bankRepairDigitFinStep (decide (j = 0)) x kx y ky).2.2.1
        (bankRepairDigitFinStep (decide (j = 0)) x kx y ky).2.2.2 +
      (if bankRepairDigitFinActive s (decide (j = 0)) x kx y ky = true then 1 else 0) ≤
    bankRepairDigitLam m j s x kx + bankRepairDigitLam m (j + 1) s y ky := by
  by_cases hj0 : j = 0
  · subst hj0
    rcases x with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> cases kx <;>
      rcases y with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> cases ky <;> cases s <;>
      simp [bankRepairDigitFinStep, bankRepairDigitLam, bankRepairDigitLamIn,
        bankRepairDigitFinActive, bankRepairDigitClsOP, bankRepairDigitClsOS] at hs ⊢ <;> omega
  · rcases x with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> cases kx <;>
      rcases y with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> cases ky <;> cases s <;>
      simp [bankRepairDigitFinStep, bankRepairDigitLam, bankRepairDigitLamIn,
        bankRepairDigitFinActive, bankRepairDigitClsOP, bankRepairDigitClsOS, hj0] at hs ⊢ <;>
      omega

/-! ### Delivery and pipeline shapes -/

def bankRepairDigitIsDSh : BankRepairDigitOutSh → Bool
  | .D _ => true
  | _ => false

def bankRepairDigitDeliverSh : BankRepairDigitOutSh → BankRepairDigitInSh
  | .D T => .P T
  | _ => .E

theorem bankRepairDigitDelStepCls (o : BankRepairDigitOutSh) (i : BankRepairDigitInSh)
    (k : Bool) :
    (bankRepairDigitIsDSh o = true ∧ i = .E ∧ k = false ∧
      (bankRepairDigitDelStep o i k).2.1 = bankRepairDigitDeliverSh o ∧
      (bankRepairDigitDelStep o i k).2.2 = false) ∨
    (((bankRepairDigitDelStep o i k).2.1 = i ∨
        (k = true ∧ (bankRepairDigitDelStep o i k).2.1 = .E)) ∧
      (bankRepairDigitDelStep o i k).2.2 = k ∧
      ((bankRepairDigitDelStep o i k).1 = o ∨
        (o = .U ∧ (bankRepairDigitDelStep o i k).1 = .D false))) := by
  rcases o with _ | _ | ⟨_ | _⟩ <;> rcases i with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> cases k <;>
    decide

theorem bankRepairDigitPipePhiLocal (R i : Nat) (hi : i + 1 < R) (bx : Bool)
    (o1 o2 : BankRepairDigitOutSh) :
    min (bankRepairDigitPhiW R i (bankRepairDigitPipeStep bx o1 o2).1)
        (bankRepairDigitPhiW R (i + 1) (bankRepairDigitPipeStep bx o1 o2).2) ≤
      min (bankRepairDigitPhiW R i o1) (bankRepairDigitPhiW R (i + 1) o2) := by
  rcases o1 with _ | _ | ⟨_ | _⟩ <;> rcases o2 with _ | _ | ⟨_ | _⟩ <;> cases bx <;>
    simp [bankRepairDigitPipeStep, bankRepairDigitPhiW] <;> omega

/-! ### Minimum over a range -/

theorem bankRepairDigitMinCntLe (f : Nat → Nat) (cap : Nat) :
    ∀ cnt i, i < cnt → bankRepairDigitMinCnt f cap cnt ≤ f i
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | cnt + 1, i, h => by
      show min (bankRepairDigitMinCnt f cap cnt) (f cnt) ≤ f i
      by_cases hi : i = cnt
      · subst hi; exact Nat.min_le_right _ _
      · exact Nat.le_trans (Nat.min_le_left _ _)
          (bankRepairDigitMinCntLe f cap cnt i (by omega))

theorem bankRepairDigitMinCntCap (f : Nat → Nat) (cap : Nat) :
    ∀ cnt, bankRepairDigitMinCnt f cap cnt ≤ cap
  | 0 => Nat.le_refl _
  | cnt + 1 => Nat.le_trans (Nat.min_le_left _ _) (bankRepairDigitMinCntCap f cap cnt)

theorem bankRepairDigitMinCntAttain (f : Nat → Nat) (cap : Nat) :
    ∀ cnt, bankRepairDigitMinCnt f cap cnt = cap ∨
      ∃ i, i < cnt ∧ bankRepairDigitMinCnt f cap cnt = f i
  | 0 => Or.inl rfl
  | cnt + 1 => by
      show min (bankRepairDigitMinCnt f cap cnt) (f cnt) = cap ∨
        ∃ i, i < cnt + 1 ∧ min (bankRepairDigitMinCnt f cap cnt) (f cnt) = f i
      rcases Nat.le_total (bankRepairDigitMinCnt f cap cnt) (f cnt) with h | h
      · rw [Nat.min_eq_left h]
        rcases bankRepairDigitMinCntAttain f cap cnt with h1 | ⟨i, hi, h1⟩
        · exact Or.inl h1
        · exact Or.inr ⟨i, by omega, h1⟩
      · rw [Nat.min_eq_right h]
        exact Or.inr ⟨cnt, by omega, rfl⟩

theorem bankRepairDigitMinCntGe (f : Nat → Nat) (cap b : Nat) (hb : b ≤ cap) :
    ∀ cnt, (∀ i, i < cnt → b ≤ f i) → b ≤ bankRepairDigitMinCnt f cap cnt := by
  intro cnt h
  rcases bankRepairDigitMinCntAttain f cap cnt with h1 | ⟨i, hi, h1⟩
  · rw [h1]; exact hb
  · rw [h1]; exact h i hi

theorem bankRepairDigitMinCntMono (f g : Nat → Nat) (cap cnt : Nat)
    (h : ∀ i, i < cnt → f i ≤ g i) :
    bankRepairDigitMinCnt f cap cnt ≤ bankRepairDigitMinCnt g cap cnt := by
  rcases bankRepairDigitMinCntAttain g cap cnt with h1 | ⟨i, hi, h1⟩
  · rw [h1]; exact bankRepairDigitMinCntCap f cap cnt
  · rw [h1]; exact Nat.le_trans (bankRepairDigitMinCntLe f cap cnt i hi) (h i hi)

theorem bankRepairDigitMinCntPair (f g : Nat → Nat) (cap cnt k : Nat) (hk : k + 1 < cnt)
    (h : ∀ i, i < cnt → i ≠ k → i ≠ k + 1 → f i = g i)
    (hp : min (f k) (f (k + 1)) ≤ min (g k) (g (k + 1))) :
    bankRepairDigitMinCnt f cap cnt ≤ bankRepairDigitMinCnt g cap cnt := by
  have a1 := bankRepairDigitMinCntLe f cap cnt k (by omega)
  have a2 := bankRepairDigitMinCntLe f cap cnt (k + 1) hk
  rcases bankRepairDigitMinCntAttain g cap cnt with h1 | ⟨i, hi, h1⟩
  · rw [h1]; exact bankRepairDigitMinCntCap f cap cnt
  · rw [h1]
    by_cases hik : i = k
    · subst hik; omega
    · by_cases hik1 : i = k + 1
      · subst hik1; omega
      · rw [← h i hi hik hik1]
        exact bankRepairDigitMinCntLe f cap cnt i hi

theorem bankRepairDigitMinCntCongr (f g : Nat → Nat) (cap cnt : Nat)
    (h : ∀ i, i < cnt → f i = g i) :
    bankRepairDigitMinCnt f cap cnt = bankRepairDigitMinCnt g cap cnt :=
  Nat.le_antisymm (bankRepairDigitMinCntMono f g cap cnt (fun i hi => Nat.le_of_eq (h i hi)))
    (bankRepairDigitMinCntMono g f cap cnt (fun i hi => Nat.le_of_eq (h i hi).symm))

/-! ### Sums -/

/-- One point may rise by `δ`. -/
theorem bankRepairDigitSumCntPointUp (f g : Nat → Nat) (lo k δ : Nat) :
    ∀ cnt, (∀ i, lo ≤ i → i < lo + cnt → i ≠ k → f i ≤ g i) → f k ≤ g k + δ →
      bankRepairDigitSumCnt f lo cnt ≤ bankRepairDigitSumCnt g lo cnt + δ
  | 0, _, _ => Nat.zero_le _
  | cnt + 1, h, hk => by
      show bankRepairDigitSumCnt f lo cnt + f (lo + cnt) ≤
        bankRepairDigitSumCnt g lo cnt + g (lo + cnt) + δ
      by_cases hc : k = lo + cnt
      · subst hc
        have := bankRepairDigitSumCntMono f g lo cnt
          (fun i h1 h2 => h i h1 (by omega) (by omega))
        omega
      · have ih := bankRepairDigitSumCntPointUp f g lo k δ cnt
          (fun i h1 h2 h3 => h i h1 (by omega) h3) hk
        have hl := h (lo + cnt) (by omega) (by omega) (fun h' => hc h'.symm)
        omega

theorem bankRepairDigitSumCntCongr (f g : Nat → Nat) (lo cnt : Nat)
    (h : ∀ i, lo ≤ i → i < lo + cnt → f i = g i) :
    bankRepairDigitSumCnt f lo cnt = bankRepairDigitSumCnt g lo cnt :=
  Nat.le_antisymm (bankRepairDigitSumCntMono f g lo cnt (fun i h1 h2 => Nat.le_of_eq (h i h1 h2)))
    (bankRepairDigitSumCntMono g f lo cnt (fun i h1 h2 => Nat.le_of_eq (h i h1 h2).symm))

/-! ### Weights: monotonicity and bounds -/

theorem bankRepairDigitLamMono (m j : Nat) (s s' : Bool) (h : s' = true → s = true)
    (i : BankRepairDigitInSh) (k : Bool) :
    bankRepairDigitLam m j s' i k ≤ bankRepairDigitLam m j s i k := by
  cases s <;> cases s' <;> rcases i with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    simp_all [bankRepairDigitLam, bankRepairDigitLamIn]

theorem bankRepairDigitLamOfMono (m : Nat) (s s' : Bool) (h : s' = true → s = true)
    (inp : Nat → BankRepairDigitInSh) (lv : Nat → Bool) :
    bankRepairDigitLamOf m s' inp lv ≤ bankRepairDigitLamOf m s inp lv :=
  bankRepairDigitSumCntMono _ _ 0 m (fun j _ _ => bankRepairDigitLamMono m j s s' h _ _)

theorem bankRepairDigitLamLe (m j : Nat) (s : Bool) (i : BankRepairDigitInSh) (k : Bool) :
    bankRepairDigitLam m j s i k ≤ 2 * m + 2 := by
  rcases i with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> cases s <;> cases k <;>
    simp [bankRepairDigitLam, bankRepairDigitLamIn] <;> (try split) <;> omega

theorem bankRepairDigitLamEOff (m j : Nat) (s : Bool) :
    bankRepairDigitLam m j s .E false = 0 := by
  simp [bankRepairDigitLam, bankRepairDigitLamIn]

theorem bankRepairDigitNeedGLe (inp : Nat → BankRepairDigitInSh) (lv : Nat → Bool) (k : Nat) :
    bankRepairDigitNeedG inp lv k ≤ k + 1 := by
  unfold bankRepairDigitNeedG
  split <;> split <;> omega

theorem bankRepairDigitClsOPEP (i : BankRepairDigitInSh) (k : Bool)
    (h : bankRepairDigitClsOP i k = true) : bankRepairDigitClsEP i k = true := by
  rcases i with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> cases k <;> simp_all [bankRepairDigitClsOP,
    bankRepairDigitClsEP]

theorem bankRepairDigitStartOfCongr (inp inp' : Nat → BankRepairDigitInSh) (lv lv' : Nat → Bool)
    (k : Nat) (h0 : inp' k = inp k) (h1 : lv' k = lv k) (h2 : inp' (k + 1) = inp (k + 1))
    (h3 : lv' (k + 1) = lv (k + 1)) :
    bankRepairDigitStartOf inp' lv' (k + 1) = bankRepairDigitStartOf inp lv (k + 1) := by
  simp only [bankRepairDigitStartOf, h0, h1, h2, h3]

/-! ### Assembling a lane rank inequality -/

theorem bankRepairDigitLaneRankAssemble (R m : Nat) (out out' : Nat → BankRepairDigitOutSh)
    (inp inp' : Nat → BankRepairDigitInSh) (lv lv' : Nat → Bool) (δ1 δ2 : Nat)
    (hneed : bankRepairDigitNeedOf m inp' lv' ≤ bankRepairDigitNeedOf m inp lv)
    (hlast : bankRepairDigitLastStart m inp' lv' ≤ bankRepairDigitLastStart m inp lv)
    (hphi : (if 0 < bankRepairDigitLastStart m inp' lv' then bankRepairDigitPhiOf R out' else 0)
      + δ1 ≤ (if 0 < bankRepairDigitLastStart m inp lv then bankRepairDigitPhiOf R out else 0))
    (hlam : bankRepairDigitLamOf m (decide (0 < bankRepairDigitLastStart m inp lv)) inp' lv' +
      δ2 ≤ bankRepairDigitLamOf m (decide (0 < bankRepairDigitLastStart m inp lv)) inp lv) :
    bankRepairDigitLaneRank R m out' inp' lv' + (δ1 + δ2) ≤
      bankRepairDigitLaneRank R m out inp lv := by
  unfold bankRepairDigitLaneRank
  have h1 := Nat.mul_le_mul_left (2 * R + m + 3) hneed
  have h2 := bankRepairDigitLamOfMono m (decide (0 < bankRepairDigitLastStart m inp lv))
    (decide (0 < bankRepairDigitLastStart m inp' lv'))
    (fun h => by simp only [decide_eq_true_eq] at h ⊢; omega) inp' lv'
  omega

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankRepairDigitFinStepCls
#print axioms L3.RenewalReferenceClock.bankRepairDigitFinLamLocal
#print axioms L3.RenewalReferenceClock.bankRepairDigitDelStepCls
#print axioms L3.RenewalReferenceClock.bankRepairDigitPipePhiLocal
#print axioms L3.RenewalReferenceClock.bankRepairDigitMinCntLe
#print axioms L3.RenewalReferenceClock.bankRepairDigitMinCntCap
#print axioms L3.RenewalReferenceClock.bankRepairDigitMinCntAttain
#print axioms L3.RenewalReferenceClock.bankRepairDigitMinCntGe
#print axioms L3.RenewalReferenceClock.bankRepairDigitMinCntMono
#print axioms L3.RenewalReferenceClock.bankRepairDigitMinCntPair
#print axioms L3.RenewalReferenceClock.bankRepairDigitMinCntCongr
#print axioms L3.RenewalReferenceClock.bankRepairDigitSumCntPointUp
#print axioms L3.RenewalReferenceClock.bankRepairDigitSumCntCongr
#print axioms L3.RenewalReferenceClock.bankRepairDigitLamMono
#print axioms L3.RenewalReferenceClock.bankRepairDigitLamOfMono
#print axioms L3.RenewalReferenceClock.bankRepairDigitLamLe
#print axioms L3.RenewalReferenceClock.bankRepairDigitLamEOff
#print axioms L3.RenewalReferenceClock.bankRepairDigitNeedGLe
#print axioms L3.RenewalReferenceClock.bankRepairDigitClsOPEP
#print axioms L3.RenewalReferenceClock.bankRepairDigitStartOfCongr
#print axioms L3.RenewalReferenceClock.bankRepairDigitLaneRankAssemble
