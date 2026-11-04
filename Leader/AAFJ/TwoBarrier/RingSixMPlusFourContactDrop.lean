import Leader.AAFJ.TwoBarrier.RingSixMPlusFourChildTable

set_option autoImplicit false
set_option Elab.async false

/-!
# A literal contact-prefix / six-drop cylinder for `n = 6m+4`

This consumer leaves the accepted child table frozen.  It packages its three
live-state classifications into a variable-length contact-prefix family, then
splices the certified six-interaction collision word immediately after contact.
Every trailing raw scheduler word is allowed: global barrier-count monotonicity
keeps the strict drop true.
-/

namespace AAFJPK.N6m4ContactDropCylinder

open BarrierAlgebra
open OriginalNonbarrierWord
open N6m4ColoredChildTable

private theorem hk3 : 0 < 3 := by decide
private theorem N_pos {m : Nat} : 0 < N m := by simp [N]
private theorem N_ne_one {m : Nat} : N m ≠ 1 := by simp [N]
private theorem N_ne_two {m : Nat} : N m ≠ 2 := by simp [N]

/-- On every size `6*m+4`, the constructive least nondivisor is three. -/
theorem leastNonDivisor_N {m : Nat} :
    AAFJExactN.leastNonDivisor (N m) = 3 := by
  have hs := AAFJExactN.leastNonDivisor_spec (N m) N_pos
  have h2dvd : 2 ∣ N m := by
    refine ⟨3 * m + 2, ?_⟩
    simp [N]
    omega
  have h3nd : ¬ 3 ∣ N m := by
    rintro ⟨c, hc⟩
    simp [N] at hc
    omega
  have hle : AAFJExactN.leastNonDivisor (N m) ≤ 3 := by
    apply Nat.le_of_not_lt
    intro h
    exact h3nd (hs.2.2 3 (by omega) h)
  have hne2 : AAFJExactN.leastNonDivisor (N m) ≠ 2 := by
    intro h
    apply hs.2.1
    simpa [h] using h2dvd
  omega

/-- The exact-family protocol on `6*m+4` is the literal `P₃` protocol. -/
theorem protocolFor_N_eq_p3 {m : Nat} :
    AAFJExactFamily.protocolFor (N m) N_pos = AAFJPK.protocol 3 hk3 := by
  have hlarge := AAFJExactFamily.protocolFor_large
    (n := N m) N_pos N_ne_one N_ne_two
  simpa only [leastNonDivisor_N] using hlarge

private theorem rawRun_append {m : Nat}
    (C : Fin (N m) → State 3) (u w : List (Fin (N m))) :
    rawRun hk3 (ring m) C (u ++ w) =
      rawRun hk3 (ring m) (rawRun hk3 (ring m) C u) w := by
  induction u generalizing C with
  | nil => rfl
  | cons e es ih =>
      simp only [List.cons_append, rawRun]
      exact ih ((protocol 3 hk3).step (ring m) C e)

/-- Barrier count is monotone along every literal physical suffix. -/
private theorem barrierCount_rawRun_le {m : Nat}
    (C : Fin (N m) → State 3) (w : List (Fin (N m))) :
    barrierCount hk3 (ring m) (labelsOf (rawRun hk3 (ring m) C w)) ≤
      barrierCount hk3 (ring m) (labelsOf C) := by
  induction w generalizing C with
  | nil => simp [rawRun]
  | cons e es ih =>
      have hstep := protocol_step_barrierCount_le hk3 (ring m)
        (by simp [N]) C e
      have htail := ih ((protocol 3 hk3).step (ring m) C e)
      exact Nat.le_trans (by simpa [rawRun] using htail) hstep

private theorem rawRun_S0_noise {m : Nat} (hm : 1 ≤ m)
    (w : List (Fin (N m)))
    (hw : ∀ e ∈ w, e ≠ v0 m ∧ e ≠ v2 m) :
    rawRun hk3 (ring m) S0 w = S0 := by
  induction w with
  | nil => rfl
  | cons e es ih =>
      rw [rawRun, raw_S0_quiet hm e
        (hw e (by simp)).1 (hw e (by simp)).2]
      exact ih (fun x hx => hw x (by simp [hx]))

private theorem rawRun_S1_noise {m : Nat} (hm : 1 ≤ m)
    (w : List (Fin (N m)))
    (hw : ∀ e ∈ w, e ≠ v1 m ∧ e ≠ v2 m) :
    rawRun hk3 (ring m) S1 w = S1 := by
  induction w with
  | nil => rfl
  | cons e es ih =>
      rw [rawRun, raw_S1_quiet hm e
        (hw e (by simp)).1 (hw e (by simp)).2]
      exact ih (fun x hx => hw x (by simp [hx]))

private theorem rawRun_S2_noise {m : Nat} (hm : 1 ≤ m)
    (w : List (Fin (N m)))
    (hw : ∀ e ∈ w, e ≠ v0 m ∧ e ≠ v2 m) :
    rawRun hk3 (ring m) S2 w = S2 := by
  induction w with
  | nil => rfl
  | cons e es ih =>
      rw [rawRun, raw_S2_quiet hm e
        (hw e (by simp)).1 (hw e (by simp)).2]
      exact ih (fun x hx => hw x (by simp [hx]))

/-- Three stage-dependent noise gaps separated by the progress letters
`0,1,0`.  At each stage the front-exit edge `2` and the progress edge are
excluded, leaving exactly the intended `n-2` literal identity choices. -/
def ContactPrefix {m : Nat} (w : List (Fin (N m))) : Prop :=
  ∃ w0 w1 w2,
    (∀ e ∈ w0, e ≠ v0 m ∧ e ≠ v2 m) ∧
    (∀ e ∈ w1, e ≠ v1 m ∧ e ≠ v2 m) ∧
    (∀ e ∈ w2, e ≠ v0 m ∧ e ≠ v2 m) ∧
    w = w0 ++ [v0 m] ++ w1 ++ [v1 m] ++ w2 ++ [v0 m]

/-- Every contact prefix reaches the same actual state `H`. -/
theorem ContactPrefix.rawRun_eq_H {m : Nat} (hm : 1 ≤ m)
    {w : List (Fin (N m))} (hw : ContactPrefix w) :
    rawRun hk3 (ring m) S0 w = H := by
  rcases hw with ⟨w0, w1, w2, h0, h1, h2, rfl⟩
  simp only [List.append_assoc, rawRun_append]
  rw [rawRun_S0_noise hm w0 h0]
  simp only [rawRun, raw_S0_zero]
  rw [rawRun_S1_noise hm w1 h1]
  simp only [rawRun, raw_S1_one]
  rw [rawRun_S2_noise hm w2 h2]
  simp only [rawRun, raw_S2_zero]

/-- The fixed six-interaction family certified by the frozen child table. -/
def SixDropWord {m : Nat} (w : List (Fin (N m))) : Prop :=
  w = adjacentDropWord m

theorem SixDropWord.length {m : Nat} {w : List (Fin (N m))}
    (hw : SixDropWord w) : w.length = 6 := by
  subst w
  rfl

theorem SixDropWord.strict {m : Nat} (hm : 1 ≤ m)
    {w : List (Fin (N m))} (hw : SixDropWord w) :
    barrierCount hk3 (ring m) (labelsOf (rawRun hk3 (ring m) H w)) <
      barrierCount hk3 (ring m) (labelsOf H) := by
  subst w
  exact adjacentDropWord_strict hm

private theorem barrierCount_eq_two_of_support {m : Nat}
    (C : Fin (N m) → State 3) (a b : Fin (N m)) (hab : a ≠ b)
    (hs : ∀ e, BarrierAt hk3 (ring m) (labelsOf C) e ↔ e = a ∨ e = b) :
    barrierCount hk3 (ring m) (labelsOf C) = 2 := by
  have hnodup : [a, b].Nodup := by simp [hab]
  have hlo : [a, b] ⊆ barrierSupport hk3 (ring m) (labelsOf C) := by
    intro x hx
    simp at hx
    rcases hx with h | h
    · subst x
      exact (mem_barrierSupport_iff hk3 (ring m) (labelsOf C) a).2
        ((hs a).2 (Or.inl rfl))
    · subst x
      exact (mem_barrierSupport_iff hk3 (ring m) (labelsOf C) b).2
        ((hs b).2 (Or.inr rfl))
  have hlow : 2 ≤ (barrierSupport hk3 (ring m) (labelsOf C)).length := by
    simpa using hnodup.length_le_of_subset hlo
  have hhi : barrierSupport hk3 (ring m) (labelsOf C) ⊆ [a, b] := by
    intro x hx
    have hxbar := (mem_barrierSupport_iff hk3 (ring m) (labelsOf C) x).1 hx
    rcases (hs x).1 hxbar with h | h
    · subst x; simp
    · subst x; simp
  have hupp :
      (barrierSupport hk3 (ring m) (labelsOf C)).length ≤ [a, b].length :=
    (barrierSupport_nodup hk3 (ring m) (labelsOf C)).length_le_of_subset hhi
  unfold barrierCount
  simpa using Nat.le_antisymm (by simpa using hupp) hlow

private theorem S0_count_two {m : Nat} (hm : 1 ≤ m) :
    barrierCount hk3 (ring m) (labelsOf S0) = 2 :=
  barrierCount_eq_two_of_support S0 (v0 m) (v2 m)
    (by simp [v0, v2, v, Fin.ext_iff]) (S0_support hm)

private theorem H_count_two {m : Nat} (hm : 1 ≤ m) :
    barrierCount hk3 (ring m) (labelsOf H) = 2 :=
  barrierCount_eq_two_of_support H (v1 m) (v2 m)
    (by simp [v1, v2, v, Fin.ext_iff]) (H_support hm)

/-- Exact length-`9n` contact/six-drop cylinders, with every remaining letter
after the six-drop block free. -/
def ContactSixDropCylinder (m : Nat) (w : List (Fin (N m))) : Prop :=
  ∃ contact drop suffix,
    ContactPrefix contact ∧ SixDropWord drop ∧
    w = contact ++ drop ++ suffix ∧ w.length = 9 * N m

theorem ContactSixDropCylinder.length {m : Nat} {w : List (Fin (N m))}
    (hw : ContactSixDropCylinder m w) : w.length = 9 * N m := by
  rcases hw with ⟨_, _, _, _, _, _, hlen⟩
  exact hlen

/-- Every family member is an actual strict drop under literal `rawRun`.
The final suffix is physical, rather than absorbed bookkeeping. -/
theorem ContactSixDropCylinder.strict {m : Nat} (hm : 1 ≤ m)
    {w : List (Fin (N m))} (hw : ContactSixDropCylinder m w) :
    barrierCount hk3 (ring m) (labelsOf (rawRun hk3 (ring m) S0 w)) <
      barrierCount hk3 (ring m) (labelsOf S0) := by
  rcases hw with ⟨contact, drop, suffix, hc, hd, rfl, _⟩
  have hcontact := ContactPrefix.rawRun_eq_H hm hc
  have hprefix :
      rawRun hk3 (ring m) S0 (contact ++ drop) =
        rawRun hk3 (ring m) H drop := by
    rw [rawRun_append, hcontact]
  have hfull :
      rawRun hk3 (ring m) S0 ((contact ++ drop) ++ suffix) =
        rawRun hk3 (ring m) (rawRun hk3 (ring m) H drop) suffix := by
    rw [rawRun_append, hprefix]
  rw [hfull]
  have hdrop := SixDropWord.strict hm hd
  have hsuffix := barrierCount_rawRun_le
    (rawRun hk3 (ring m) H drop) suffix
  have heq : barrierCount hk3 (ring m) (labelsOf H) =
      barrierCount hk3 (ring m) (labelsOf S0) := by
    rw [H_count_two hm, S0_count_two hm]
  rw [heq] at hdrop
  omega

/-! ## Denominator arithmetic -/

/-- The final advertised denominator follows from the stronger
`185/200704` lower bound.  This keeps the remaining gap purely in the family
cardinality theorem: no rational or integer coercions are needed. -/
theorem mass_1085_of_mass_185_200704 {D X : Nat}
    (h : 185 * X ≤ 200704 * D) : X ≤ 1085 * D := by
  omega

#print axioms leastNonDivisor_N
#print axioms protocolFor_N_eq_p3
#print axioms ContactPrefix.rawRun_eq_H
#print axioms SixDropWord.strict
#print axioms ContactSixDropCylinder.strict
#print axioms mass_1085_of_mass_185_200704

end AAFJPK.N6m4ContactDropCylinder
