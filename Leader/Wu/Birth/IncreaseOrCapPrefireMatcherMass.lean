import Leader.Wu.Birth.IncreaseOrCapPrefireRestartFree
import Leader.Wu.Birth.WaitClockMassMatcher

namespace BirthPhaseB3PrefireMatcherMass

open FiniteUniformStoppingTree PredictableTwoTargetFiniteTree
open BirthShortDoneTerminalPassiveLocal3
open BirthWaitClockMass.Matcher

set_option autoImplicit false
set_option Elab.async false

variable {n : Nat}

private theorem p2_ne_leftCross (hn : 4 <= n) :
    p2 hn != leftCross hn := by
  simpa only [bne_iff_ne] using
    (Fin.ne_of_val_ne (by simp [p2, leftCross]; omega) :
      p2 hn ≠ leftCross hn)

def rawMatcher (hn : 4 <= n)
    (p : Pending (p2 hn)) (e : Fin n) : StopNode (Pending (p2 hn)) :=
  if e = leftCross hn then .failure else
    BirthWaitClockMass.Matcher.raw p e

def controlledMatcher (hn : 4 <= n)
    (p : Pending (p2 hn)) (e : Fin n) : StopNode (Pending (p2 hn)) :=
  if e = leftCross hn then advance p else
    BirthWaitClockMass.Matcher.controlled p e

private def ports (hn : 4 <= n) (p : Pending (p2 hn))
    (hleft : leftCross hn ∉ p.word) : ThreePortSerialCount.Ports n where
  a := p.head
  b := p2 hn
  c := leftCross hn
  ab := p.distinct
  ac := by
    intro h
    apply hleft
    simp [Pending.word, h]
  bc := by
    simpa only [bne_iff_ne] using p2_ne_leftCross hn

private theorem sum_spike (a : Fin n) (v : Nat) :
    (List.ofFn (fun e : Fin n => if e = a then v else 0)).sum = v := by
  have h := ofFn_sum_one_value_else_const a
    (fun e : Fin n => if e = a then v else 0) 0 (by
      intro e he
      simp [he])
  simpa using h

private theorem sum_three (p : ThreePortSerialCount.Ports n) (hn : 3 <= n)
    (f : Fin n -> Nat) (q : Nat)
    (ho : forall e, e != p.a -> e != p.b -> e != p.c -> f e = q) :
    (List.ofFn f).sum = f p.a + f p.b + f p.c + (n - 3) * q := by
  have hp : forall e : Fin n,
      f e + (if e = p.a then q else 0) + (if e = p.b then q else 0) +
          (if e = p.c then q else 0) =
        q + (if e = p.a then f p.a else 0) +
          (if e = p.b then f p.b else 0) +
          (if e = p.c then f p.c else 0) := by
    intro e
    by_cases ha : e = p.a
    · subst e; simp [p.ab, p.ac, Nat.add_comm]
    · by_cases hb : e = p.b
      · subst e; simp [p.ab.symm, p.bc, Nat.add_comm]
      · by_cases hc : e = p.c
        · subst e; simp [p.ac.symm, p.bc.symm, Nat.add_comm]
        · simp [ha, hb, hc, ho e (by simpa using ha) (by simpa using hb)
            (by simpa using hc)]
  have hs := ofFn_sum_eq _ _ hp
  simp only [ofFn_sum_add, sum_spike, ofFn_sum_const] at hs
  have hm : n * q = (n - 3) * q + 3 * q := by
    calc
      n * q = ((n - 3) + 3) * q := by
        rw [show (n - 3) + 3 = n by omega]
      _ = (n - 3) * q + 3 * q := Nat.add_mul _ _ _
  omega

theorem success_count_eq_three_pow_mul_raw
    (hn : 4 <= n) (p : Pending (p2 hn))
    (hleft : leftCross hn ∉ p.word) (T : Nat) :
    successCount (controlledMatcher hn) (.active p) T =
      3 ^ p.length * successCount (rawMatcher hn) (.active p) T := by
  induction T generalizing p with
  | zero => simp [successCount, treeWeight, successWeight]
  | succ T ih =>
      have hc := sum_three (ports hn p hleft) (by omega)
        (fun e => successCount (controlledMatcher hn)
          (controlledMatcher hn p e) T)
        (successCount (controlledMatcher hn) (.active p) T) (by
          intro e ha hb hc
          dsimp [ports] at ha hb hc
          simp only [bne_iff_ne, ne_eq] at ha hb hc
          simp [controlledMatcher, BirthWaitClockMass.Matcher.controlled,
            ha, hb, hc])
      have hr := sum_three (ports hn p hleft) (by omega)
        (fun e => successCount (rawMatcher hn) (rawMatcher hn p e) T)
        (successCount (rawMatcher hn) (.active p) T) (by
          intro e ha hb hc
          dsimp [ports] at ha hb hc
          simp only [bne_iff_ne, ne_eq] at ha hb hc
          simp [rawMatcher, BirthWaitClockMass.Matcher.raw, ha, hb, hc])
      have hnext :
          3 * successCount (controlledMatcher hn) (advance p) T =
            3 ^ p.length * successCount (rawMatcher hn) (advance p) T := by
        cases ht : p.tail with
        | nil =>
            rw [advance_nil p ht]
            simp [ht, Pending.length, Pending.word, successCount,
              treeWeight_success, successWeight]
        | cons a rest =>
            let q : Pending (p2 hn) := ⟨a, rest, by
              intro hm
              exact p.avoid
                (List.mem_cons_of_mem p.head (by simpa [ht] using hm))⟩
            have hleftq : leftCross hn ∉ q.word := by
              change leftCross hn ∉ a :: rest
              intro hm
              apply hleft
              change leftCross hn ∈ p.head :: p.tail
              rw [ht]
              exact List.mem_cons_of_mem _ hm
            have he : p.length = q.length + 1 := by
              simp [Pending.length, Pending.word, ht, q]
            rw [advance_cons p a rest ht]
            change 3 * successCount (controlledMatcher hn) (.active q) T =
              3 ^ p.length * successCount (rawMatcher hn) (.active q) T
            rw [ih q hleftq, he, Nat.pow_succ]
            ac_rfl
      change (List.ofFn (fun e : Fin n => successCount (controlledMatcher hn)
          (controlledMatcher hn p e) T)).sum =
        3 ^ p.length * (List.ofFn (fun e : Fin n => successCount (rawMatcher hn)
          (rawMatcher hn p e) T)).sum
      rw [hc, hr]
      dsimp only [ports]
      have hd := p.distinct
      have hk : p2 hn ≠ leftCross hn := by
        simpa only [bne_iff_ne] using p2_ne_leftCross hn
      have hl : p.head ≠ leftCross hn := by
        intro h
        apply hleft
        simp [Pending.word, h]
      simp only [controlledMatcher, rawMatcher,
        BirthWaitClockMass.Matcher.controlled, BirthWaitClockMass.Matcher.raw,
        hd, hk, hl, if_false, if_true, true_or, or_true,
        successCount, treeWeight_failure, successWeight,
        Nat.mul_zero, Nat.add_zero]
      have h3 (x : Nat) : x + x + x = 3 * x := by omega
      rw [h3]
      change 3 * successCount (controlledMatcher hn) (advance p) T +
          (n - 3) * successCount (controlledMatcher hn) (.active p) T =
        3 ^ p.length *
          (successCount (rawMatcher hn) (advance p) T +
            (n - 3) * successCount (rawMatcher hn) (.active p) T)
      rw [hnext, ih p hleft, Nat.mul_add]
      ac_rfl

theorem six_stage_fiber
    (hn : 4 <= n) (p : Pending (p2 hn))
    (hleft : leftCross hn ∉ p.word) (hlen : p.length = 6) (T : Nat) :
    successCount (controlledMatcher hn) (.active p) T =
      3 ^ 6 * successCount (rawMatcher hn) (.active p) T := by
  rw [success_count_eq_three_pow_mul_raw hn p hleft T, hlen]

end BirthPhaseB3PrefireMatcherMass

#print axioms BirthPhaseB3PrefireMatcherMass.six_stage_fiber
