import Leader.Wu.ZeroDivisible.MultiReaderDrain

/-!
# Arithmetic support for the multi-reader traffic rank

These lemmas use the exact `readerRank` in the finite MultiReader driver.
They prove positivity, the decrement and equality-turnaround identities,
a bounded-position upper estimate, and the conversion from a lexicographic
Nat-pair decrease to a scalar decrease. No pipeline transition or traffic
inequality is assumed or proved by this module.
-/

namespace PPLLAstraR5TrafficArithmetic
open PPLLAstraR5MultiReader
set_option autoImplicit false

/-- Every raw token has positive rho, even without reader or payload bounds. -/
theorem readerRank_pos (ψ : Nat) (t : Path2Info) : 0 < readerRank ψ t := by
  unfold readerRank
  omega

/-- A positive-position A1/A2 movement pays exactly one rho unit. -/
theorem readerRank_dec (ψ : Nat) (t : Path2Info)
    (ha : t.action = 1 ∨ t.action = 2) (hp : 0 < t.position) :
    readerRank ψ (PPLLFableDesignR1.dec t) + 1 = readerRank ψ t := by
  simp only [PPLLFableDesignR1.dec, if_pos ha, readerRank]
  omega

/-- Authentic A2 landing preserves its saved label; the emitted A1 bit is
irrelevant to rho. This arithmetic identity needs no bound on that label. -/
theorem backward_turnaround (ψ label oldBit newBit : Nat) :
    readerRank ψ (token 1 label newBit ψ) =
      readerRank ψ (token 2 label oldBit 0) := by
  rfl

/-- A nonterminal authentic A1 equality advances the saved label by one.
The strict label hypothesis is essential for the Nat-subtraction identity. -/
theorem forward_turnaround (ψ label bit : Nat) (hl : label < ψ - 1) :
    readerRank ψ (token 2 (label+1) 0 (ψ-1)) =
      readerRank ψ (token 1 label bit 0) := by
  have hg : ψ-1-label = (ψ-1-(label+1))+1 := by omega
  simp only [readerRank, token]
  simp only [Nat.reduceBEq, Bool.false_eq_true, if_false, if_true,
    Nat.add_zero]
  rw [hg, Nat.mul_add, Nat.mul_one]
  omega

/-- The requested legal-reader estimate actually needs only the position
bound: larger raw labels truncate the residual term, and either action
contributes at most psi. No legal-label or A1/A2 premise is necessary. -/
theorem readerRank_le (ψ : Nat) (t : Path2Info) (hψ : 4 ≤ ψ)
    (hp : t.position ≤ ψ) : readerRank ψ t ≤ 2*ψ^2-ψ+2 := by
  have hgap : ψ-1-t.label ≤ ψ-1 := Nat.sub_le _ _
  have hm := Nat.mul_le_mul_left (2*ψ-1) hgap
  have ho : (if t.action == 2 then ψ else 0) ≤ ψ := by split <;> omega
  have hc : (2*ψ-1)+1 = 2*ψ := by omega
  have hb : (ψ-1)+1 = ψ := by omega
  have hmul1 := congrArg (fun a : Nat => a*(ψ-1)) hc
  have hmul2 := congrArg (fun a : Nat => (2*ψ)*a) hb
  simp only [Nat.add_mul, Nat.one_mul, Nat.mul_assoc] at hmul1
  simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc] at hmul2
  simp only [readerRank, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  omega

/-- If Z' is bounded by m, a strict lexicographic decrease in (P,Z)
strictly decreases Q_m=(m+1)P+Z. The old Z needs no upper bound here.
This is scalar arithmetic, not a proof of any protocol-row inequality. -/
theorem scalar_of_lex (m P Z P' Z' : Nat)
    (hlex : P' < P ∨ (P' = P ∧ Z' < Z)) (hz : Z' ≤ m) :
    (m+1)*P'+Z' < (m+1)*P+Z := by
  rcases hlex with h | ⟨h, hZ⟩
  · have hP : P'+1 ≤ P := by omega
    have hm := Nat.mul_le_mul_left (m+1) hP
    simp only [Nat.mul_add, Nat.mul_one] at hm
    omega
  · subst P'
    omega

#print axioms readerRank_pos
#print axioms readerRank_dec
#print axioms backward_turnaround
#print axioms forward_turnaround
#print axioms readerRank_le
#print axioms scalar_of_lex
end PPLLAstraR5TrafficArithmetic
