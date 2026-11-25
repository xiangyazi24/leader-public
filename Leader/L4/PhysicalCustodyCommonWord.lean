import Leader.L4.PhysicalCustodyCommutation
import Leader.L4.BStarRecoveryPass

namespace L4.PhysicalCustodyCommonWord
open AllSizeProtocol BStarTrace PhysicalCustody

theorem commute_suffix {n : Nat} (p : List (Fin n)) {u v : List (Fin n)}
    (H : Commuted u v) : Commuted (u++p) (v++p) := by
  induction H with
  | refl => exact .refl _
  | trans _ _ A B => exact .trans A B
  | swap u v a b H =>
    simpa only [List.append_assoc,List.cons_append] using Commuted.swap u (v++p) a b H

theorem commute_append {n : Nat} {u u' v v' : List (Fin n)}
    (U : Commuted u u') (V : Commuted v v') : Commuted (u++v) (u'++v') :=
  .trans (commute_suffix v U) (commute_prefix u' V)

local notation "C" => BStarRecoveryPass.Credit

/-- Credits refer to the supplied chronological replay. The sampled tape
is identified only at the complete cuts, not assumed to contain those
same event segments in that order. -/
theorem replay_two_passes {s n : Nat} {Owner : Type}
    (x : Raw s n) (owners : List Owner) (u v u' v' tail : List (Fin n))
    (U : Commuted u u') (V : Commuted v v')
    (E F : Owner → Raw s n → List (Fin n) → Prop)
    (first : ∀ o∈owners, ∃ a b, a<b ∧ C (rawNext s) E o x u' a b)
    (second : ∀ o∈owners, ∃ a b, a<b ∧
      C (rawNext s) F o (rawRun x u) v' a b) :
    rawRun x u = rawRun x u' ∧
    rawRun x ((u++v)++tail)=rawRun x ((u'++v')++tail) ∧
    (∀ o∈owners, ∃ a b, a<b ∧ b≤u'.length ∧ C (rawNext s) E o x ((u'++v')++tail) a b) ∧
    (∀ o∈owners, ∃ a b, u'.length≤a ∧ a<b ∧ b≤(u'++v').length ∧
      C (rawNext s) F o x ((u'++v')++tail) a b) := by
  have mid := rawRun_of_commuted x U
  refine ⟨mid,rawRun_of_commuted x (commute_suffix tail (commute_append U V)),?_,?_⟩
  · intro o H
    obtain ⟨a,b,L,H⟩ := first o H
    exact ⟨a,b,L,(BStarRecoveryPass.credit_bounds _ H).2,
      BStarRecoveryPass.credit_append _ (BStarRecoveryPass.credit_append _ H v') tail⟩
  · intro o H
    obtain ⟨a,b,L,H⟩ := second o H
    rw [mid] at H
    have shifted := BStarRecoveryPass.credit_shift (rawNext s) u' H
    have le := (BStarRecoveryPass.credit_bounds _ shifted).2
    exact ⟨u'.length+a,u'.length+b,by omega,by omega,le,
      BStarRecoveryPass.credit_append _ shifted tail⟩

#print axioms commute_append
#print axioms replay_two_passes
end L4.PhysicalCustodyCommonWord
