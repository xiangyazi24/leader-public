import Leader.L3.Small.FinishClean

/-!
SMALL clean finish: the debt and request half-stages on the guard.

Census of the BANK drain proofs (`bankFinishCleanDebtStage`,
`bankRepairRequestHalfOnDrainProved`): every use of `hbank` is through
the drain class (grant bits false, the native step `nativeE`, closure of
the class) or through the selected-pair formulas of the masked step,
which are the same for the SMALL cut.  No width fact is used: the debt
potential and the request front depend only on n.  On SMALL the drain is
`SmallRepairGuard` (rooted, seen-complete, grant-free), its native step
is `smallReferenceGrantFreeNativeStep`, its closure `smallRepairGuardStep`
(this is where `useSmall = true` enters), and the clean receipt closures
are `smallCleanReceiptPreservationOnGuard`.
-/

namespace L3.SmallFinishCleanDrain

open L3
open L3.HeadlineRenewal
open L3.SmallRenewal
open L3.SmallFinishRepair
open L3.SmallRepairStages
open L3.SmallFinishClean
open L3.SmallCandidatePreparation
open L3.RenewalReferenceClock
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- One masked BANK edge from a Reader ∧ Digit state: both endpoints
leave with EU = ED = false, every other site is unchanged.
Consumer: `bankFinishCleanDebtStep`, `bankFinishCleanDebtBitStep`. -/
theorem smallCleanDebtEndpoints {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (z : RenewalSmallReference n)
    (hreader : SmallCleanReader ring z)
    (hdigit : SmallCleanDigit ring z) (e : Fin n) :
    ((renewalSmallNext ring z e).1 e).EU = false ∧
      ((renewalSmallNext ring z e).1 e).ED = false ∧
      ((renewalSmallNext ring z e).1 (ring.rightNeighbor e)).EU = false ∧
      ((renewalSmallNext ring z e).1 (ring.rightNeighbor e)).ED = false ∧
      (∀ i : Fin n, i ≠ e → i ≠ ring.rightNeighbor e →
        (renewalSmallNext ring z e).1 i = z.1 i) := by
  have hne := clockNeighborDifferent ring (by omega) e
  have hQReader : AcceptedReceipts.QReader ring (piR z.1) :=
    AcceptedReceipts.accepted_reader_qreader ring
      (CleanWord ring)
      (Closure.readerFoldValid (ceilLogTwo n) n)
      (piR z.1) hreader
  have hQDigit : AcceptedReceipts.QDigit ring (piD z.1) :=
    AcceptedReceipts.barred_digit_qdigit ring
      (CleanWordAtRoot ring)
      (piD z.1) hdigit
  have hev := Closure.certificateEventQuietFromSafe
    (by omega) ring z.1 e hQReader hQDigit
  have hq := bankFinishCleanQuietDcc (z.1 e) (z.1 (ring.rightNeighbor e))
  have hx := Closure.transitionDebtSourceFormula
    (compileAdvice (ceilLogTwo n))
    (z.1 e) (z.1 (ring.rightNeighbor e))
  have hy := Closure.transitionDebtDestinationFormula
    (compileAdvice (ceilLogTwo n))
    (z.1 e) (z.1 (ring.rightNeighbor e))
  rw [hev] at hx hy
  rw [hq.1, hq.2.1] at hx
  rw [hq.2.2.1, hq.2.2.2] at hy
  have hmaskX :
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalSmallCut ring z.1 z.2 e)
        (z.1 e) (z.1 (ring.rightNeighbor e))).1.EU = false ∧
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalSmallCut ring z.1 z.2 e)
        (z.1 e) (z.1 (ring.rightNeighbor e))).1.ED = false := by
    cases hm : renewalSmallCut ring z.1 z.2 e with
    | false => simpa [renewalMaskedPair, hm] using hx
    | true => simpa [renewalMaskedPair, hm] using hx
  have hmaskY :
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalSmallCut ring z.1 z.2 e)
        (z.1 e) (z.1 (ring.rightNeighbor e))).2.EU = false ∧
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalSmallCut ring z.1 z.2 e)
        (z.1 e) (z.1 (ring.rightNeighbor e))).2.ED = false := by
    cases hm : renewalSmallCut ring z.1 z.2 e with
    | false => simpa [renewalMaskedPair, hm] using hy
    | true => simpa [renewalMaskedPair, hm] using hy
  have hstep : ∀ i : Fin n, (renewalSmallNext ring z e).1 i =
      (if i = e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalSmallCut ring z.1 z.2 e)
          (z.1 e) (z.1 (ring.rightNeighbor e))).1
       else if i = ring.rightNeighbor e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalSmallCut ring z.1 z.2 e)
          (z.1 e) (z.1 (ring.rightNeighbor e))).2
       else z.1 i) := fun i => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [hstep, ↓reduceIte]; exact hmaskX.1
  · simp only [hstep, ↓reduceIte]; exact hmaskX.2
  · simp only [hstep, if_neg hne, ↓reduceIte]; exact hmaskY.1
  · simp only [hstep, if_neg hne, ↓reduceIte]; exact hmaskY.2
  · intro i hi hj
    simp only [hstep, if_neg hi]
    exact if_neg hj

/-- One debt bit per site.  Consumer: `smallCleanDebtCount`. -/
def smallCleanDebtBit {n : Nat}
    (ring : DirectedRing n)
    (z : RenewalSmallReference n) (i : Fin n) : Nat :=
  if ((z.1 i).EU || (z.1 i).ED) = true then 1 else 0

/-- Number of debt sites.  Consumer: `smallCleanDebtHalfProved`. -/
def smallCleanDebtCount {n : Nat}
    (ring : DirectedRing n)
    (z : RenewalSmallReference n) : Nat :=
  (List.ofFn (smallCleanDebtBit ring z)).sum

/-- Each debt site is cleared by its two incident edges and no site
gains debt: summed over all n edges, the next debt counts are at most
(n-2) times the current one.  Consumer: `smallCleanDebtDrift`. -/
theorem smallCleanDebtCountStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (z : RenewalSmallReference n)
    (hreader : SmallCleanReader ring z)
    (hdigit : SmallCleanDigit ring z) :
    (List.ofFn (fun e : Fin n =>
        smallCleanDebtCount ring (renewalSmallNext ring z e))).sum +
      2 * smallCleanDebtCount ring z ≤
      n * smallCleanDebtCount ring z := by
  have hsite : ∀ i : Fin n,
      (List.ofFn (fun e : Fin n =>
          smallCleanDebtBit ring (renewalSmallNext ring z e) i)).sum +
        2 * smallCleanDebtBit ring z i ≤
        n * smallCleanDebtBit ring z i := by
    intro i
    have hcell : ∀ e : Fin n,
        smallCleanDebtBit ring (renewalSmallNext ring z e) i ≤
          (if e = i then 0 else if e = ring.leftNeighbor i then 0
            else smallCleanDebtBit ring z i) := by
      intro e
      obtain ⟨h1, h2, h3, h4, hother⟩ :=
        smallCleanDebtEndpoints ring hn z hreader hdigit e
      by_cases hei : e = i
      · subst hei
        simp [smallCleanDebtBit, h1, h2]
      · rw [if_neg hei]
        by_cases hel : e = ring.leftNeighbor i
        · rw [if_pos hel]
          have hj : ring.rightNeighbor e = i := by
            rw [hel]; exact bankFinishCleanRightOfLeft ring i
          rw [← hj]
          simp [smallCleanDebtBit, h3, h4]
        · rw [if_neg hel]
          have hij : i ≠ ring.rightNeighbor e := by
            intro h
            apply hel
            have hl : ring.leftNeighbor (ring.rightNeighbor e) = e := by
              apply Fin.ext
              show ((((e.val + 1) % n) + n - 1) % n) = e.val
              have hn' := ring.hn
              have he := e.isLt
              by_cases hlast : e.val + 1 < n
              · rw [Nat.mod_eq_of_lt hlast,
                  show e.val + 1 + n - 1 = e.val + n by omega,
                  Nat.add_mod_right]
                exact Nat.mod_eq_of_lt he
              · have hev : e.val + 1 = n := by omega
                rw [hev, Nat.mod_self, show 0 + n - 1 = e.val by omega]
                exact Nat.mod_eq_of_lt he
            rw [h, hl]
          unfold smallCleanDebtBit
          rw [hother i (Ne.symm hei) hij]
          exact Nat.le_refl _
    have hsum := ofFn_sum_le _ _ hcell
    have hli : ring.leftNeighbor i ≠ i := by
      intro h
      have := clockNeighborDifferent ring (by omega) (ring.leftNeighbor i)
      rw [bankFinishCleanRightOfLeft ring i] at this
      exact this h.symm
    have htwo := bankRepairCloseSumTwoCells
      (fun _ : Fin n => smallCleanDebtBit ring z i)
      (fun e : Fin n => if e = i then 0 else if e = ring.leftNeighbor i then 0
        else smallCleanDebtBit ring z i)
      i (ring.leftNeighbor i) hli
      (fun e he hel => by simp [he, hel])
    simp only [↓reduceIte, if_neg hli] at htwo
    rw [ofFn_sum_const] at htwo
    have hcomm := Nat.mul_comm (smallCleanDebtBit ring z i) n
    omega
  have hall := ofFn_sum_le _ _ hsite
  rw [ofFn_sum_add] at hall
  have hswap := bankFinishCleanSumSwap
    (fun e i => smallCleanDebtBit ring (renewalSmallNext ring z e) i)
  unfold smallCleanDebtCount
  rw [hswap]
  rw [ofFn_sum_mul_left, ofFn_sum_mul_left] at hall
  exact hall

/-- Debt count zero is exactly the debt-free target.
Consumer: `smallCleanDebtHalfProved`. -/
theorem smallCleanDebtZeroOfCount {n : Nat}
    (ring : DirectedRing n)
    (z : RenewalSmallReference n)
    (h : ¬ RepairDebtZero smallRepairView z) :
    1 ≤ smallCleanDebtCount ring z := by
  have hex : ∃ i : Fin n, smallCleanDebtBit ring z i = 1 := by
    apply Classical.byContradiction
    intro hno
    apply h
    intro i
    show (z.1 i).EU = false ∧ (z.1 i).ED = false
    have hb : smallCleanDebtBit ring z i ≠ 1 := fun hb => hno ⟨i, hb⟩
    unfold smallCleanDebtBit at hb
    cases hu : (z.1 i).EU <;> cases hd : (z.1 i).ED <;> simp_all
  obtain ⟨i, hi⟩ := hex
  have hcell := bankRepairCloseSumExchange
    (smallCleanDebtBit ring z)
    (fun j => if j = i then 0 else smallCleanDebtBit ring z j) i
    (fun j hj => by simp [hj])
  simp only [↓reduceIte] at hcell
  unfold smallCleanDebtCount
  omega

/-- At most n debt sites.  Consumer: `smallCleanDebtHalfProved`. -/
theorem smallCleanDebtCountLe {n : Nat}
    (ring : DirectedRing n)
    (z : RenewalSmallReference n) :
    smallCleanDebtCount ring z ≤ n := by
  have h := ofFn_sum_le (smallCleanDebtBit ring z) (fun _ => 1)
    (fun i => by unfold smallCleanDebtBit; split <;> omega)
  rw [ofFn_sum_const] at h
  unfold smallCleanDebtCount
  omega

/-- The Bellman drift of the debt potential on the drain-DBarred class.
Consumer: `smallCleanDebtHalfProved`. -/
theorem smallCleanDebtDrift {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (z : RenewalSmallReference n)
    (hreader : SmallCleanReader ring z)
    (hdigit : SmallCleanDigit ring z)
    (hnot : ¬ RepairDebtZero smallRepairView z) :
    n + (List.ofFn (fun e : Fin n => bankFinishCleanDebtPotential n
        (smallCleanDebtCount ring (renewalSmallNext ring z e)))).sum ≤
      n * bankFinishCleanDebtPotential n (smallCleanDebtCount ring z) := by
  let d := smallCleanDebtCount ring z
  let de := fun e : Fin n =>
    smallCleanDebtCount ring (renewalSmallNext ring z e)
  let a := n / (2 * d) + 1
  have hd1 : 1 ≤ d := smallCleanDebtZeroOfCount ring z hnot
  have hcount := smallCleanDebtCountStep ring hn z hreader hdigit
  have hle : ∀ e, de e ≤ d := by
    intro e
    have hstep := smallCleanDebtCountStep ring hn z hreader hdigit
    -- pointwise: every site's bit does not increase
    have hbit : ∀ i, smallCleanDebtBit ring (renewalSmallNext ring z e) i ≤
        smallCleanDebtBit ring z i := by
      intro i
      obtain ⟨h1, h2, h3, h4, hother⟩ :=
        smallCleanDebtEndpoints ring hn z hreader hdigit e
      by_cases hie : i = e
      · subst hie; simp [smallCleanDebtBit, h1, h2]
      · by_cases hij : i = ring.rightNeighbor e
        · subst hij; simp [smallCleanDebtBit, h3, h4]
        · unfold smallCleanDebtBit; rw [hother i hie hij]; exact Nat.le_refl _
    exact ofFn_sum_le _ _ hbit
  have hper : ∀ e, bankFinishCleanDebtPotential n (de e) + (d - de e) * a ≤
      bankFinishCleanDebtPotential n d := by
    intro e
    have h := bankFinishCleanPotentialConcave n d (d - de e) (by omega)
    rw [show d - (d - de e) = de e by have := hle e; omega] at h
    exact h
  have hsum := ofFn_sum_le _ _ hper
  rw [ofFn_sum_add, ofFn_sum_const] at hsum
  have hdrop : (List.ofFn (fun e => (d - de e) * a)).sum =
      (List.ofFn (fun e => d - de e)).sum * a := by
    have hfun : (fun e => (d - de e) * a) = (fun e => a * (d - de e)) :=
      funext (fun e => Nat.mul_comm _ _)
    rw [hfun, ofFn_sum_mul_left, Nat.mul_comm]
  have hsplit : (List.ofFn (fun e => d - de e)).sum + (List.ofFn de).sum = n * d := by
    rw [← ofFn_sum_add]
    have : (fun e => d - de e + de e) = fun _ => d := by
      funext e; have := hle e; omega
    rw [this, ofFn_sum_const]
  have htwo : 2 * d ≤ (List.ofFn (fun e => d - de e)).sum := by
    have := hcount
    change (List.ofFn de).sum + 2 * d ≤ n * d at this
    omega
  have hka : n ≤ (2 * d) * a := by
    have h := Nat.div_add_mod n (2 * d)
    have h2 := Nat.mod_lt n (show 0 < 2 * d by omega)
    show n ≤ (2 * d) * (n / (2 * d) + 1)
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hmul : (2 * d) * a ≤ (List.ofFn (fun e => d - de e)).sum * a :=
    Nat.mul_le_mul_right a htwo
  rw [hdrop] at hsum
  change n + (List.ofFn (fun e => bankFinishCleanDebtPotential n (de e))).sum ≤
    n * bankFinishCleanDebtPotential n d
  omega

/-- repair.tex 5367-5374 on the drain: old EU/ED debt clears within
n²/2 (one half-unit).  Consumer: `bankFinishMaskedRepairBoundClean`. -/
theorem smallCleanDebtHalfProved {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    SmallCleanDebtHalf ring := by
  have hpres := smallCleanReceiptPreservationOnGuard ring hn
  have hclosed : ∀ (z : RenewalSmallReference n),
      SmallCleanDBarredOnGuard ring z → ∀ e : Fin n,
      SmallCleanDBarredOnGuard ring (renewalSmallNext ring z e) :=
    fun z hz e => ⟨smallRepairGuardStep ring hn hsmall z hz.1 e,
      hpres.2.2.2.1 z hz.1 hz.2 e⟩
  let S := {z : RenewalSmallReference n // SmallCleanDBarredOnGuard ring z}
  let nextS : S → Fin n → S := fun x e =>
    ⟨renewalSmallNext ring x.1 e, hclosed x.1 x.2 e⟩
  intro z hz T
  have hpot := Prob.costNumerator_le_of_potential nextS
    (fun x : S => RepairDebtZero smallRepairView x.1)
    (fun x : S => bankFinishCleanDebtPotential n
      (smallCleanDebtCount ring x.1))
    (fun x hx => smallCleanDebtDrift ring hn x.1
      x.2.2.1.2 x.2.2.2 hx)
    ⟨z, hz⟩ T
  have hmap := costNumerator_map_eq nextS (renewalSmallNext ring)
    (fun x : S => x.1) (fun _ _ => rfl) (RepairDebtZero smallRepairView) T ⟨z, hz⟩
  rw [hmap] at hpot
  have hhalf := bankFinishCleanPotentialHalf n hn
    (smallCleanDebtCount ring z)
    (smallCleanDebtCountLe ring z)
  have h2 := Nat.mul_le_mul_left 2 hpot
  calc
    2 * costNumerator (renewalSmallNext ring)
        (RepairDebtZero smallRepairView) z T ≤
      2 * (n ^ T * bankFinishCleanDebtPotential n
        (smallCleanDebtCount ring z)) := h2
    _ = n ^ T * (2 * bankFinishCleanDebtPotential n
        (smallCleanDebtCount ring z)) := by ac_rfl
    _ ≤ n ^ T * (n ^ 2) := Nat.mul_le_mul_left _ hhalf
    _ = n ^ T * (1 * n ^ 2) := by rw [Nat.one_mul]

/-- One masked BANK edge from a drain DebtCleared state: the initiator
leaves with no request, the responder's request is
`!l' ∧ (req_j ∨ (req_e ∧ !l_e))`, and every other site is unchanged.
Consumer: `smallCleanRequestFrontStep`. -/
theorem smallCleanRequestStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (z : RenewalSmallReference n)
    (hD : SmallRepairGuard ring z)
    (hC : SmallCleanDebtCleared ring z) (e : Fin n) :
    ((renewalSmallNext ring z e).1 e).req = false ∧
      ((renewalSmallNext ring z e).1 (ring.rightNeighbor e)).req =
        (!((renewalSmallNext ring z e).1 (ring.rightNeighbor e)).l &&
          ((z.1 (ring.rightNeighbor e)).req ||
            ((z.1 e).req && !(z.1 e).l))) ∧
      (∀ i : Fin n, i ≠ e → i ≠ ring.rightNeighbor e →
        (renewalSmallNext ring z e).1 i = z.1 i) := by
  have hne := clockNeighborDifferent ring (by omega) e
  have hQReader : AcceptedReceipts.QReader ring (piR z.1) :=
    AcceptedReceipts.accepted_reader_qreader ring
      (CleanWord ring)
      (Closure.readerFoldValid (ceilLogTwo n) n)
      (piR z.1) hC.1.1.2
  have hQDigit : AcceptedReceipts.QDigit ring (piD z.1) :=
    AcceptedReceipts.barred_digit_qdigit ring
      (CleanWordAtRoot ring)
      (piD z.1) hC.1.2
  have hev := Closure.certificateEventQuietFromSafe
    (by omega) ring z.1 e hQReader hQDigit
  have hg := hD.2.2
  have hdebt := hC.2
  have hnative := smallReferenceGrantFreeNativeStep ring (by omega : 3 ≤ n) z hD e
  change nativeProjection (renewalSmallNext ring z e).1 =
    nativeE ring (nativeProjection z.1) e at hnative
  have hstep : ∀ i : Fin n, (renewalSmallNext ring z e).1 i =
      (if i = e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalSmallCut ring z.1 z.2 e)
          (z.1 e) (z.1 (ring.rightNeighbor e))).1
       else if i = ring.rightNeighbor e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalSmallCut ring z.1 z.2 e)
          (z.1 e) (z.1 (ring.rightNeighbor e))).2
       else z.1 i) := fun i => rfl
  have hxe : (renewalSmallNext ring z e).1 e =
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalSmallCut ring z.1 z.2 e)
        (z.1 e) (z.1 (ring.rightNeighbor e))).1 :=
    (hstep e).trans (if_pos rfl)
  have hxj : (renewalSmallNext ring z e).1 (ring.rightNeighbor e) =
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalSmallCut ring z.1 z.2 e)
        (z.1 e) (z.1 (ring.rightNeighbor e))).2 :=
    (hstep (ring.rightNeighbor e)).trans ((if_neg hne).trans (if_pos rfl))
  have hNe : nativeE ring (nativeProjection z.1) e e =
      (certLiteralEPair (z.1 e).certNative
        (z.1 (ring.rightNeighbor e)).certNative).1 := by
    simp [nativeE, nativeProjection]
  have hNj : nativeE ring (nativeProjection z.1) e (ring.rightNeighbor e) =
      (certLiteralEPair (z.1 e).certNative
        (z.1 (ring.rightNeighbor e)).certNative).2 := by
    simp [nativeE, nativeProjection, hne]
  have hle : ((renewalSmallNext ring z e).1 e).l =
      (certLiteralEPair (z.1 e).certNative
        (z.1 (ring.rightNeighbor e)).certNative).1.l := by
    have h := congrFun hnative e
    rw [hNe] at h
    exact congrArg CertNative.l h
  have hlj : ((renewalSmallNext ring z e).1 (ring.rightNeighbor e)).l =
      (certLiteralEPair (z.1 e).certNative
        (z.1 (ring.rightNeighbor e)).certNative).2.l := by
    have h := congrFun hnative (ring.rightNeighbor e)
    rw [hNj] at h
    exact congrArg CertNative.l h
  have hmaskL : ∀ s : Bool,
      (renewalMaskedPair (compileAdvice (ceilLogTwo n)) s
        (z.1 e) (z.1 (ring.rightNeighbor e))).1.l =
        (transition (compileAdvice (ceilLogTwo n))
          (z.1 e) (z.1 (ring.rightNeighbor e))).1.l ∧
      (renewalMaskedPair (compileAdvice (ceilLogTwo n)) s
        (z.1 e) (z.1 (ring.rightNeighbor e))).2.l =
        (transition (compileAdvice (ceilLogTwo n))
          (z.1 e) (z.1 (ring.rightNeighbor e))).2.l := by
    intro s
    cases s <;> exact ⟨rfl, rfl⟩
  have hl1 : (transition (compileAdvice (ceilLogTwo n))
      (z.1 e) (z.1 (ring.rightNeighbor e))).1.l =
      (certLiteralEPair (z.1 e).certNative
        (z.1 (ring.rightNeighbor e)).certNative).1.l := by
    rw [← (hmaskL (renewalSmallCut ring z.1 z.2 e)).1, ← hxe, hle]
  have hl2 : (transition (compileAdvice (ceilLogTwo n))
      (z.1 e) (z.1 (ring.rightNeighbor e))).2.l =
      (certLiteralEPair (z.1 e).certNative
        (z.1 (ring.rightNeighbor e)).certNative).2.l := by
    rw [← (hmaskL (renewalSmallCut ring z.1 z.2 e)).2, ← hxj, hlj]
  have hpair := bankRequestCloseMaskedPair (compileAdvice (ceilLogTwo n))
    (renewalSmallCut ring z.1 z.2 e)
    (z.1 e) (z.1 (ring.rightNeighbor e))
    (hg e) (hg (ring.rightNeighbor e))
    (hdebt e).1 (hdebt e).2
    (hdebt (ring.rightNeighbor e)).1 (hdebt (ring.rightNeighbor e)).2
    hev hl1 hl2
  refine ⟨?_, ?_, ?_⟩
  · rw [hxe]; exact hpair.1
  · rw [hlj, hxj]; exact hpair.2
  · intro i hi hj
    rw [hstep]
    simp only [if_neg hi]
    exact if_neg hj

/-- The class of the request stage, with its leader site named.
Consumer: `smallCleanRequestHalfProved`. -/
def SmallCleanRequestClass {n : Nat}
    (ring : DirectedRing n)
    (p : Fin n) (z : RenewalSmallReference n) : Prop :=
  SmallRepairGuard ring z ∧
    SmallCleanDebtCleared ring z ∧ (z.1 p).l = true

/-- Core names a unique leader.  Consumer: `smallCleanRequestClassStep`,
`smallCleanRequestFrontStep`. -/
theorem smallCleanRequestLeaderUnique {n : Nat}
    (ring : DirectedRing n)
    (z : RenewalSmallReference n)
    (hc : SmallRepairCore ring z) (p : Fin n)
    (hp : (z.1 p).l = true) (i : Fin n)
    (hi : (z.1 i).l = true) : i = p := by
  have hone : OneNativeLeader (nativeProjection z.1) := hc.1.1
  obtain ⟨q, _, hqu⟩ := hone
  have h1 : i = q := hqu i hi
  have h2 : p = q := hqu p hp
  rw [h1, h2]

/-- The leader site survives every drain edge.
Consumer: `smallCleanRequestClassStep`. -/
theorem smallCleanRequestLeaderStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (z : RenewalSmallReference n)
    (hD : SmallRepairGuard ring z)
    (hc : SmallRepairCore ring z)
    (hc' : ∀ e, SmallRepairCore ring (renewalSmallNext ring z e))
    (p : Fin n) (hp : (z.1 p).l = true) (e : Fin n) :
    ((renewalSmallNext ring z e).1 p).l = true := by
  have hnative := smallReferenceGrantFreeNativeStep ring (by omega : 3 ≤ n) z hD e
  change nativeProjection (renewalSmallNext ring z e).1 =
    nativeE ring (nativeProjection z.1) e at hnative
  have hone : OneNativeLeader
      (nativeProjection (renewalSmallNext ring z e).1) := (hc' e).1.1
  obtain ⟨q, hq, _⟩ := hone
  have hq' : (nativeE ring (nativeProjection z.1) e q).l = true := by
    rw [← hnative]; exact hq
  have hold := Closure.nativeENoNewLeader (by omega) ring
    (nativeProjection z.1) e q hq'
  have hqp : q = p := smallCleanRequestLeaderUnique ring z hc p hp q hold
  rw [← hqp]
  exact hq

/-- The named class is closed.  Consumer:
`smallCleanRequestHalfProved`. -/
theorem smallCleanRequestClassStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (p : Fin n) (z : RenewalSmallReference n)
    (hz : SmallCleanRequestClass ring p z) (e : Fin n) :
    SmallCleanRequestClass ring p (renewalSmallNext ring z e) := by
  have hpres := smallCleanReceiptPreservationOnGuard ring hn
  have hC' : ∀ e, SmallCleanDebtCleared ring (renewalSmallNext ring z e) :=
    fun e => hpres.2.2.2.2 z hz.1 hz.2.1 e
  exact ⟨smallRepairGuardStep ring hn hsmall z hz.1 e, hC' e,
    smallCleanRequestLeaderStep ring hn z hz.1 hz.2.1.1.1.1.1
      (fun e => (hC' e).1.1.1.1) p hz.2.2 e⟩

/-- Distance of a request site, zero elsewhere.
Consumer: `smallCleanRequestFront`. -/
def smallCleanRequestSiteValue {n : Nat}
    (ring : DirectedRing n)
    (p : Fin n) (z : RenewalSmallReference n) (i : Fin n) : Nat :=
  if (z.1 i).req then bankRequestCloseDist p i else 0

/-- The request front: largest distance to the leader of a request.
Consumer: `smallCleanRequestHalfProved`. -/
def smallCleanRequestFront {n : Nat}
    (ring : DirectedRing n)
    (p : Fin n) (z : RenewalSmallReference n) : Nat :=
  bankRequestCloseMax (smallCleanRequestSiteValue ring p z)

/-- Consumer: `smallCleanRequestHalfProved`. -/
theorem smallCleanRequestFrontLe {n : Nat}
    (ring : DirectedRing n)
    (p : Fin n) (z : RenewalSmallReference n) :
    smallCleanRequestFront ring p z ≤ n := by
  apply bankRequestCloseMaxLe
  intro i
  unfold smallCleanRequestSiteValue
  split
  · exact (bankRequestCloseDistBounds p i).2
  · exact Nat.zero_le _

/-- A live request makes the front positive.
Consumer: `smallCleanRequestDrift`. -/
theorem smallCleanRequestFrontPositive {n : Nat}
    (ring : DirectedRing n)
    (p : Fin n) (z : RenewalSmallReference n)
    (hz : ¬ RepairRequestZero smallRepairView z) :
    0 < smallCleanRequestFront ring p z := by
  have hex : ∃ i : Fin n, (z.1 i).req = true := by
    apply Classical.byContradiction
    intro hno
    apply hz
    intro i
    show (z.1 i).req = false
    cases h : (z.1 i).req with
    | false => rfl
    | true => exact absurd ⟨i, h⟩ hno
  obtain ⟨i, hi⟩ := hex
  have hv : smallCleanRequestSiteValue ring p z i =
      bankRequestCloseDist p i := by
    unfold smallCleanRequestSiteValue
    rw [hi]; rfl
  have h1 := bankRequestCloseLeMax (smallCleanRequestSiteValue ring p z) i
  have h2 := (bankRequestCloseDistBounds p i).1
  unfold smallCleanRequestFront
  omega

/-- One edge: every site value after the edge is at most the front, and
strictly below it when the edge leaves a front site.
Consumer: `smallCleanRequestDrift`. -/
theorem smallCleanRequestFrontStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (p : Fin n) (z : RenewalSmallReference n)
    (hz : SmallCleanRequestClass ring p z) (e : Fin n) (slack : Nat)
    (hslack : slack = 0 ∨
      (slack = 1 ∧ smallCleanRequestSiteValue ring p z e =
        smallCleanRequestFront ring p z ∧
        0 < smallCleanRequestFront ring p z)) :
    smallCleanRequestFront ring p (renewalSmallNext ring z e) + slack ≤
      smallCleanRequestFront ring p z := by
  have hne := clockNeighborDifferent ring (by omega) e
  obtain ⟨hreqE, hreqJ, hother⟩ :=
    smallCleanRequestStep ring hn z hz.1 hz.2.1 e
  have hz' := smallCleanRequestClassStep ring hn hsmall p z hz e
  have hlead : ∀ i, (z.1 i).l = true → i = p :=
    smallCleanRequestLeaderUnique ring z hz.2.1.1.1.1.1 p hz.2.2
  have hlead' : ∀ i, ((renewalSmallNext ring z e).1 i).l = true → i = p :=
    smallCleanRequestLeaderUnique ring _ hz'.2.1.1.1.1.1 p hz'.2.2
  -- the front value
  have hle : ∀ i, smallCleanRequestSiteValue ring p z i ≤
      smallCleanRequestFront ring p z :=
    fun i => bankRequestCloseLeMax _ i
  -- a site other than e with the front value is impossible under slack 1
  have hbelow : ∀ i, i ≠ e → slack = 1 →
      smallCleanRequestSiteValue ring p z i + 1 ≤
        smallCleanRequestFront ring p z := by
    intro i hie hs1
    rcases hslack with h0 | ⟨_, hfe, hpos⟩
    · omega
    · have hvi := hle i
      unfold smallCleanRequestSiteValue at hvi ⊢
      unfold smallCleanRequestSiteValue at hfe
      by_cases hri : (z.1 i).req = true
      · rw [if_pos hri] at hvi ⊢
        by_cases hre : (z.1 e).req = true
        · rw [if_pos hre] at hfe
          have hd : bankRequestCloseDist p i ≠ bankRequestCloseDist p e :=
            fun h => hie (bankRequestCloseDistInjective p i e h)
          omega
        · rw [if_neg hre] at hfe
          omega
      · rw [if_neg hri]
        omega
  have hsF : slack ≤ smallCleanRequestFront ring p z := by
    rcases hslack with h0 | ⟨h1, _, hpos⟩ <;> omega
  have hs1 : slack ≤ 1 := by
    rcases hslack with h0 | ⟨h1, _, _⟩ <;> omega
  have hsite : ∀ i, smallCleanRequestSiteValue ring p
      (renewalSmallNext ring z e) i + slack ≤
        smallCleanRequestFront ring p z := by
    intro i
    by_cases hie : i = e
    · subst hie
      unfold smallCleanRequestSiteValue
      simp only [hreqE, Bool.false_eq_true, ↓reduceIte]
      omega
    · by_cases hij : i = ring.rightNeighbor e
      · subst hij
        unfold smallCleanRequestSiteValue
        by_cases hr : ((renewalSmallNext ring z e).1
            (ring.rightNeighbor e)).req = true
        · rw [if_pos hr]
          rw [hreqJ] at hr
          obtain ⟨hl', hor⟩ := bankRequestCloseBoolRow _ _ _ _ hr
          have hjp : ring.rightNeighbor e ≠ p := by
            intro h
            have hlp := hz'.2.2
            rw [← h, hl'] at hlp
            exact Bool.noConfusion hlp
          rcases hor with hrj | ⟨hre, hle'⟩
          · have hv := hle (ring.rightNeighbor e)
            unfold smallCleanRequestSiteValue at hv
            rw [if_pos hrj] at hv
            rcases hslack with h0 | ⟨h1, _, _⟩
            · omega
            · have hb := hbelow (ring.rightNeighbor e) hie h1
              unfold smallCleanRequestSiteValue at hb
              rw [if_pos hrj] at hb
              omega
          · have hep : e ≠ p := by
              intro h
              have hlp := hz.2.2
              rw [← h, hle'] at hlp
              exact Bool.noConfusion hlp
            have hd := bankRequestCloseDistStep ring p e hep hjp
            have hv := hle e
            unfold smallCleanRequestSiteValue at hv
            rw [if_pos hre] at hv
            omega
        · rw [if_neg hr]
          omega
      · have hv' : smallCleanRequestSiteValue ring p
            (renewalSmallNext ring z e) i =
            smallCleanRequestSiteValue ring p z i := by
          unfold smallCleanRequestSiteValue
          rw [hother i hie hij]
        rw [hv']
        rcases hslack with h0 | ⟨h1, _, _⟩
        · have := hle i
          omega
        · exact h1 ▸ hbelow i hie h1
  have hmax := bankRequestCloseMaxLe
    (smallCleanRequestSiteValue ring p (renewalSmallNext ring z e))
    (smallCleanRequestFront ring p z - slack)
    (fun i => by have := hsite i; omega)
  have hmax' : smallCleanRequestFront ring p (renewalSmallNext ring z e) ≤
      smallCleanRequestFront ring p z - slack := hmax
  omega

/-- Drift of the scaled front.  Consumer:
`smallCleanRequestHalfProved`. -/
theorem smallCleanRequestDrift {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (p : Fin n) (z : RenewalSmallReference n)
    (hz : SmallCleanRequestClass ring p z)
    (hnz : ¬ RepairRequestZero smallRepairView z) :
    n + (List.ofFn (fun e : Fin n => n *
        smallCleanRequestFront ring p (renewalSmallNext ring z e))).sum ≤
      n * (n * smallCleanRequestFront ring p z) := by
  have hpos := smallCleanRequestFrontPositive ring p z hnz
  obtain ⟨i, hi⟩ := bankRequestCloseMaxAttained
    (smallCleanRequestSiteValue ring p z) hpos
  have hall : ∀ e, n * smallCleanRequestFront ring p
      (renewalSmallNext ring z e) ≤ n * smallCleanRequestFront ring p z := by
    intro e
    have h := smallCleanRequestFrontStep ring hn hsmall p z hz e 0 (Or.inl rfl)
    exact Nat.mul_le_mul_left n (by omega)
  have hspec : n * smallCleanRequestFront ring p
      (renewalSmallNext ring z i) + n ≤
        n * smallCleanRequestFront ring p z := by
    have h := smallCleanRequestFrontStep ring hn hsmall p z hz i 1
      (Or.inr ⟨rfl, hi, hpos⟩)
    have h2 := Nat.mul_le_mul_left n h
    rw [Nat.mul_add, Nat.mul_one] at h2
    exact h2
  have hsum := bankRequestCloseSumSpike
    (fun e : Fin n => n *
      smallCleanRequestFront ring p (renewalSmallNext ring z e))
    i (n * smallCleanRequestFront ring p z) n hall hspec
  omega

/-- repair.tex 5374-5380 on the drain: requests reach the protected
root within n² (two half-units).  Consumer:
`bankFinishReferenceFinishRequestClosed`. -/
theorem smallCleanRequestHalfProved {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    SmallCleanRequestHalf ring := by
  intro z hz T
  have hone : OneNativeLeader (nativeProjection z.1) := hz.2.1.1.1.1.1.1
  obtain ⟨p, hp, _⟩ := hone
  have hI : SmallCleanRequestClass ring p z := ⟨hz.1, hz.2, hp⟩
  have hpot : costNumerator (renewalSmallNext ring)
      (RepairRequestZero smallRepairView) z T ≤
        n ^ T * (n * smallCleanRequestFront ring p z) :=
    L3.Prob.costNumerator_le_of_potential_on (renewalSmallNext ring)
      (RepairRequestZero smallRepairView) (SmallCleanRequestClass ring p)
      (fun x => n * smallCleanRequestFront ring p x)
      (fun x hx _ e => smallCleanRequestClassStep ring hn hsmall p x hx e)
      (fun x hx hnz => smallCleanRequestDrift ring hn hsmall p x hx hnz)
      z hI T
  have hF := smallCleanRequestFrontLe ring p z
  have h1 : n * smallCleanRequestFront ring p z ≤ n * n :=
    Nat.mul_le_mul_left n hF
  have h2 : n ^ T * (n * smallCleanRequestFront ring p z) ≤
      n ^ T * (n * n) := Nat.mul_le_mul_left _ h1
  have h3 : n ^ T * (2 * n ^ 2) = 2 * (n ^ T * (n * n)) := by
    rw [Nat.pow_two]
    exact Nat.mul_left_comm _ _ _
  rw [h3]
  omega

/-- The SMALL clean finish with the debt and request stages discharged:
the four remaining premises are the W clock, the resident retirement
clock, the fold soundness and the digit half-stage.  Consumer: the SMALL
branch of the clean R14. -/
theorem smallCleanFinishReferenceOfReader {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hword : SmallCleanWordClock ring)
    (hretirement : SmallCleanResidentRetirementClock ring)
    (hfold : SmallCleanReaderFoldSound ring)
    (hdigit : SmallCleanDigitHalf ring) :
    StageReferenceGeneratedFinish
      (renewalSmallNext ring)
      (SmallPreparedAtSomeRoot ring)
      (smallCleanStop ring)
      (headlineReferenceFinishRate (ceilLogTwo n)) :=
  smallCleanFinishReferenceOfStages ring hn hsmall hword hretirement
    hfold hdigit (smallCleanDebtHalfProved ring hn hsmall)
    (smallCleanRequestHalfProved ring hn hsmall)

end L3.SmallFinishCleanDrain

#print axioms L3.SmallFinishCleanDrain.smallCleanDebtEndpoints
#print axioms L3.SmallFinishCleanDrain.smallCleanDebtCountStep
#print axioms L3.SmallFinishCleanDrain.smallCleanDebtZeroOfCount
#print axioms L3.SmallFinishCleanDrain.smallCleanDebtCountLe
#print axioms L3.SmallFinishCleanDrain.smallCleanDebtDrift
#print axioms L3.SmallFinishCleanDrain.smallCleanDebtHalfProved
#print axioms L3.SmallFinishCleanDrain.smallCleanRequestStep
#print axioms L3.SmallFinishCleanDrain.smallCleanRequestLeaderUnique
#print axioms L3.SmallFinishCleanDrain.smallCleanRequestLeaderStep
#print axioms L3.SmallFinishCleanDrain.smallCleanRequestClassStep
#print axioms L3.SmallFinishCleanDrain.smallCleanRequestFrontLe
#print axioms L3.SmallFinishCleanDrain.smallCleanRequestFrontPositive
#print axioms L3.SmallFinishCleanDrain.smallCleanRequestFrontStep
#print axioms L3.SmallFinishCleanDrain.smallCleanRequestDrift
#print axioms L3.SmallFinishCleanDrain.smallCleanRequestHalfProved
#print axioms L3.SmallFinishCleanDrain.smallCleanFinishReferenceOfReader
