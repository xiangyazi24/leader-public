import Leader.Core.PredictablePairHitCounterFiniteTree
import Leader.Core.PayloadFiniteStoppingTree

set_option autoImplicit false

namespace PredictableColoredSixFiniteTree

open FiniteUniformStoppingTree PredictableTwoTargetFiniteTree
open PredictablePairHitCounterFiniteTree PayloadFiniteStoppingTree

abbrev A (S : Type) := ActivePairHitState S 6

def gstep {S : Type} {n : Nat}
    (good bad : S → Fin n) (next : S → Fin n → S) :
    A S → Fin n → PayloadNode (A S) S S
  | st, e =>
      let y := next st.payload e
      if hg : e = good st.payload then
        if hd : st.hits + 1 = 6 then
          .success y
        else
          .active
            { payload := y
              hits := st.hits + 1
              hits_lt := by
                have := st.hits_lt
                omega }
      else if hb : e = bad st.payload then
        .failure y
      else
        .active
          { payload := y
            hits := st.hits
            hits_lt := st.hits_lt }

private def pm (n : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | T + 1, h =>
      if h + 1 = 6 then
        2 * n ^ T + (n - 2) * pm n T h
      else
        2 * pm n T (h + 1) + (n - 2) * pm n T h

private def gm (n : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | T + 1, h =>
      if h + 1 = 6 then
        n ^ T + (n - 2) * gm n T h
      else
        gm n T (h + 1) + (n - 2) * gm n T h

private theorem pair_eq_pm
    {S : Type} {n : Nat}
    (good bad : S → Fin n) (next : S → Fin n → S)
    (hne : ∀ s, good s ≠ bad s) :
    ∀ T (st : A S),
      successCount (pairHitCounterStep (d := 6) good bad next)
          (.active st) T =
        pm n T st.hits := by
  intro T
  induction T with
  | zero =>
      intro st
      rfl
  | succ T ih =>
      intro st
      let p := pairHitCounterStep (d := 6) good bad next
      let c := pm n T st.hits
      have hs := ofFn_sum_two_values_else_const
        (good st.payload) (bad st.payload)
        (fun e : Fin n => successCount p (p st e) T) c
        (hne st.payload) (by
          intro e hg hb
          let q : A S :=
            { payload := next st.payload e
              hits := st.hits
              hits_lt := st.hits_lt }
          simpa [p, pairHitCounterStep, hg, hb, c, q] using ih q)
      change
        (List.ofFn (fun e : Fin n =>
          successCount p (p st e) T)).sum =
            pm n (T + 1) st.hits
      rw [hs]
      by_cases hd : st.hits + 1 = 6
      · simp [p, pairHitCounterStep, pm, hd, c,
          successCount, treeWeight_success, successWeight,
          (hne st.payload).symm] <;> omega
      · simp [p, pairHitCounterStep, pm, hd, c, ih,
          (hne st.payload).symm] <;> omega

private theorem good_eq_gm
    {S : Type} {n : Nat}
    (good bad : S → Fin n) (next : S → Fin n → S)
    (hne : ∀ s, good s ≠ bad s) :
    ∀ T (st : A S),
      successMass (gstep good bad next) (.active st) T =
        gm n T st.hits := by
  intro T
  induction T with
  | zero =>
      intro st
      rfl
  | succ T ih =>
      intro st
      let g := gstep good bad next
      let c := gm n T st.hits
      have hs := ofFn_sum_two_values_else_const
        (good st.payload) (bad st.payload)
        (fun e : Fin n => successMass g (g st e) T) c
        (hne st.payload) (by
          intro e hg hb
          let q : A S :=
            { payload := next st.payload e
              hits := st.hits
              hits_lt := st.hits_lt }
          simpa [g, gstep, hg, hb, c, q] using ih q)
      change
        (List.ofFn (fun e : Fin n =>
          successMass g (g st e) T)).sum =
            gm n (T + 1) st.hits
      rw [hs]
      by_cases hd : st.hits + 1 = 6
      · simp [g, gstep, gm, hd, c, (hne st.payload).symm]
      · simp [g, gstep, gm, hd, c, ih,
          (hne st.payload).symm]

private theorem pm_eq (n : Nat) :
    ∀ T h, h < 6 →
      pm n T h = 2 ^ (6 - h) * gm n T h := by
  intro T
  induction T with
  | zero =>
      intro h hh
      simp [pm, gm]
  | succ T ih =>
      intro h hh
      by_cases hd : h + 1 = 6
      · have hh5 : h = 5 := by omega
        subst h
        have hi := ih 5 (by omega)
        simp only [pm, gm]
        simp only [if_true]
        rw [hi]
        change
          2 * n ^ T + (n - 2) * (2 * gm n T 5) =
            2 * (n ^ T + (n - 2) * gm n T 5)
        rw [Nat.mul_add]
        ac_rfl
      · have hn : h + 1 < 6 := by omega
        have hi0 := ih h hh
        have hi1 := ih (h + 1) hn
        have hp :
            2 ^ (6 - h) =
              2 * 2 ^ (6 - (h + 1)) := by
          have he : 6 - h = (6 - (h + 1)) + 1 := by omega
          rw [he, Nat.pow_succ]
          ac_rfl
        simp only [pm, gm]
        rw [if_neg hd, if_neg hd, hi0, hi1, hp, Nat.mul_add]
        ac_rfl

theorem six_colored_success_exact_pair_completion
    {S : Type} {n : Nat}
    (good bad : S → Fin n) (next : S → Fin n → S)
    (hne : ∀ s, good s ≠ bad s) (s : S) (T : Nat) :
    successCount
        (pairHitCounterStep (d := 6) good bad next)
        (.active (initialState s 6 (by omega))) T =
      64 *
        successMass (gstep good bad next)
          (.active (initialState s 6 (by omega))) T := by
  let st := initialState s 6 (by omega)
  have hp := pair_eq_pm good bad next hne T st
  have hg := good_eq_gm good bad next hne T st
  have hp0 :
      successCount
          (pairHitCounterStep (d := 6) good bad next)
          (.active st) T =
        pm n T 0 := by
    simpa [st, initialState] using hp
  have hg0 :
      successMass (gstep good bad next) (.active st) T =
        gm n T 0 := by
    simpa [st, initialState] using hg
  have hf := pm_eq n T 0 (by omega)
  have h64 : 2 ^ (6 - 0) = 64 := by decide
  calc
    successCount
        (pairHitCounterStep (d := 6) good bad next)
        (.active st) T =
        pm n T 0 := hp0
    _ = 2 ^ (6 - 0) * gm n T 0 := hf
    _ = 64 * gm n T 0 := by rw [h64]
    _ = 64 *
        successMass (gstep good bad next) (.active st) T := by
      rw [hg0]

#print axioms six_colored_success_exact_pair_completion

end PredictableColoredSixFiniteTree
