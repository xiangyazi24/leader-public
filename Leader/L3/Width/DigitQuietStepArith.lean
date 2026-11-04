import Leader.L3.Width.DigitQuiet
import Leader.L3.Width.DigitComparisonValuesArith

/-!
# The quiet class: the block successor, digit by digit

`DigitValuesCorrect` says `valueBlockID target = (valueBlockID source + 1) % topA ^ R` for the pair
of complete blocks.  The launch and advance rows of the top machine write `(D'_h + c_h) mod A` with
the carry `c_h` into offset `h` (`carryInto`).  For the writes to be idempotent on the quiet class the
successor relation is needed digit by digit:

* `digitsVal_inj`: two digit strings below the radix with the same value are equal;
* `digitwise_of_succ`: if the target string is the successor of the source string modulo `A^m`, then
  every target digit is `(D'_h + carryInto D' h) mod A`;
* `values_digitwise`: the same for the digits of a pair of complete blocks of `DigitValuesCorrect`.

Consumer: the write-idempotence part of `QuietStepLaw` (digits kept), research/lean-l3/ledgers/
R10c-quiet-law-notes.md.
-/

namespace L3.DigitQuiet

open L3
open L3.AcceptedReceipts

set_option autoImplicit false

/-- Two digit strings below the radix with the same value are equal.  Consumer:
`digitwise_of_succ`. -/
theorem digitsVal_inj (a : Nat) (f g : Nat → Nat) (hf : ∀ j, f j < a) (hg : ∀ j, g j < a) :
    ∀ m, digitsVal a f m = digitsVal a g m → ∀ j, j < m → f j = g j := by
  intro m
  induction m with
  | zero => intro _ j hj; exact absurd hj (Nat.not_lt_zero _)
  | succ m ih =>
    intro h j hj
    rw [digitsVal_succ, digitsVal_succ] at h
    have ha : 0 < a := by have := hf 0; omega
    have hP : 0 < a ^ m := Nat.pow_pos ha
    have hx := digitsVal_lt a f hf m
    have hy := digitsVal_lt a g hg m
    have e1 : (digitsVal a f m + a ^ m * f m) % a ^ m = digitsVal a f m := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
    have e2 : (digitsVal a g m + a ^ m * g m) % a ^ m = digitsVal a g m := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy]
    have e3 : (digitsVal a f m + a ^ m * f m) / a ^ m = f m := by
      rw [Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hx, Nat.zero_add]
    have e4 : (digitsVal a g m + a ^ m * g m) / a ^ m = g m := by
      rw [Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hy, Nat.zero_add]
    have hlow : digitsVal a f m = digitsVal a g m := by rw [← e1, ← e2, h]
    have hhigh : f m = g m := by rw [← e3, ← e4, h]
    by_cases hjm : j = m
    · subst hjm; exact hhigh
    · exact ih hlow j (by omega)

/-- **The successor, digit by digit.**  If the target string is the successor of the source string
modulo `a^m` then every target digit is the source digit plus the carry into it, modulo `a`.
Consumer: `values_digitwise`. -/
theorem digitwise_of_succ (a : Nat) (s t : Nat → Nat) (hs : ∀ j, s j < a) (ht : ∀ j, t j < a)
    (cin : Nat → Bool) (h0 : cin 0 = true)
    (hc : ∀ j, cin (j + 1) = (cin j && decide (s j + 1 = a))) (m : Nat)
    (hval : digitsVal a t m = (digitsVal a s m + 1) % a ^ m) :
    ∀ h, h < m → t h = (s h + (if cin h then 1 else 0)) % a := by
  have hmod := carry_chain_mod a s cin hs h0 hc m
  exact digitsVal_inj a t (fun j => (s j + (if cin j then 1 else 0)) % a) ht
    (fun j => Nat.mod_lt _ (by have := hs j; omega)) m (by rw [hval, hmod])

/-- **`DigitValuesCorrect` digit by digit**: for a pair of complete blocks the digit of the target at
offset `h` is the source digit plus the carry into `h`, modulo `topA`.  Consumer: the write
idempotence of the launch and advance rows. -/
theorem values_digitwise {n : Nat} {c : Compiled} (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjD c) (hv : DigitValuesCorrect ring root (digitValueView S))
    (source target : Nat) (hsrc : completeValueBlock ring root (digitValueView S) source)
    (htg : target = source + digitSpan c)
    (hT : completeValueBlock ring root (digitValueView S) target) :
    ∀ h, h < digitSpan c →
      ((S (digitSite ring root (target + h))).top.d).val =
        (((S (digitSite ring root (source + h))).top.d).val +
          (if carryInto (fun i => (S (digitSite ring root (source + i))).top.d) h then 1 else 0)) %
          c.topA := by
  have hrel := hv.2.2 source target hsrc htg hT
  have hA : 0 < c.topA := c.topA_pos
  have hrel' : digitsVal c.topA (fun i => ((S (digitSite ring root (target + i))).top.d).val)
      (digitSpan c) =
      (digitsVal c.topA (fun i => ((S (digitSite ring root (source + i))).top.d).val)
        (digitSpan c) + 1) % c.topA ^ digitSpan c := hrel
  exact digitwise_of_succ c.topA (fun i => ((S (digitSite ring root (source + i))).top.d).val)
    (fun i => ((S (digitSite ring root (target + i))).top.d).val)
    (fun j => ((S (digitSite ring root (source + j))).top.d).isLt)
    (fun j => ((S (digitSite ring root (target + j))).top.d).isLt)
    (fun i => carryInto (fun i => (S (digitSite ring root (source + i))).top.d) i) rfl
    (fun j => by
      show (carryInto _ j && decide (((S (digitSite ring root (source + j))).top.d).val + 1 =
        c.topA)) = _
      rfl)
    (digitSpan c) hrel'

end L3.DigitQuiet

#print axioms L3.DigitQuiet.digitsVal_inj
#print axioms L3.DigitQuiet.digitwise_of_succ
#print axioms L3.DigitQuiet.values_digitwise
