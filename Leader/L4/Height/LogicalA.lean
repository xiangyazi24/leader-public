import Leader.L4.Height.Couple
import Leader.L4.Height.Quarter

namespace L4.Height

open Classical

/-- Local copy of the assignment-indicator sum, since the corresponding
helpers in Couple are intentionally private to that module. -/
noncomputable def logicalEventSum {β : Type} {n : Nat}
    (P : β → List (Fin n) → Prop) :
    List β → List (Fin n) → Nat
  | [], _ => 0
  | a :: as, u => (if P a u then 1 else 0) + logicalEventSum P as u

private theorem logicalWordSumEventSum {β : Type} {n : Nat}
    (P : β → List (Fin n) → Prop) (as : List β) (t : Nat) :
    wordSum (logicalEventSum P as) t =
      (as.map (fun a =>
        wordSum (fun u => if P a u then 1 else 0) t)).sum := by
  classical
  induction as with
  | nil => simp [logicalEventSum, wordSum_zero]
  | cons a as ih =>
      simp only [logicalEventSum, List.map_cons, List.sum_cons]
      rw [wordSum_add_fun, ih]

private theorem logicalOneLeEventSum {β : Type} {n : Nat}
    (P : β → List (Fin n) → Prop)
    {a : β} {as : List β} {u : List (Fin n)}
    (ha : a ∈ as) (hp : P a u) :
    1 ≤ logicalEventSum P as u := by
  classical
  induction as with
  | nil => simp at ha
  | cons b bs ih =>
      simp only [List.mem_cons] at ha
      rcases ha with hba | ha
      · subst b
        simp [logicalEventSum, hp]
      · have htail := ih ha
        by_cases hb : P b u
        · simp [logicalEventSum, hb]
        · simpa [logicalEventSum, hb] using htail

private theorem logicalWordSumMono {n : Nat}
    (f g : List (Fin n) → Nat) :
    ∀ t, (∀ u, u.length = t → f u ≤ g u) →
      wordSum f t ≤ wordSum g t := by
  intro t
  induction t generalizing f g with
  | zero =>
      intro h
      exact h [] rfl
  | succ t ih =>
      intro h
      simp only [wordSum]
      apply sum_ofFn_le
      intro e
      apply ih
      intro u hu
      apply h
      simp [hu]

private theorem logicalListScaledSumLe {β : Type}
    (p T : Nat) (f : β → Nat) :
    ∀ as : List β,
      (∀ a, a ∈ as → p * f a ≤ T) →
      p * (as.map f).sum ≤ as.length * T := by
  intro as
  induction as with
  | nil =>
      intro h
      simp
  | cons a as ih =>
      intro h
      have ha := h a (by simp)
      have htail : ∀ b, b ∈ as → p * f b ≤ T := by
        intro b hb
        exact h b (by simp [hb])
      have hi := ih htail
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Nat.mul_add, Nat.succ_mul]
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Nat.add_le_add ha hi)

open L4.Height.Couple

/-- The adaptive quarter transfer does not need full coverage: on an event
word, it is enough that every selected coordinate is actually revealed.
The resulting read vector labels a prescribed fiber, and each such fiber
has the usual adaptive upper bound. -/
theorem adaptive_quarter_transfer_partial
    {α : Type} {n K : Nat}
    (S : PairedSource α (Fin K) n) (x : α) (t : Nat)
    (E : List (Fin n) → Prop)
    (F : (Fin K → Bool) → Prop)
    (bad : List (Fin K → Bool))
    (hbadDistinct : bad.Nodup)
    (hbad : ∀ a, a ∈ bad ↔ F a)
    (hquarter : 4 * bad.length ≤ 2 ^ K)
    (hlogical : ∀ u, u.length = t → E u →
      (∀ k, firstReveal S k x u ≠ none) ∧ F (readVector S x u)) :
    4 * wordSum (fun u => if E u then 1 else 0) t ≤ n ^ t := by
  classical
  let P : (Fin K → Bool) → List (Fin n) → Prop :=
    fun a u => FirstPrescribed S a x (List.finRange K) u
  let eventMass : Nat :=
    wordSum (fun u => if E u then 1 else 0) t
  let fiberMass : (Fin K → Bool) → Nat := fun a =>
    wordSum (fun u => if P a u then 1 else 0) t
  have hpoint : ∀ u, u.length = t →
      (if E u then 1 else 0) ≤ logicalEventSum P bad u := by
    intro u hu
    by_cases he : E u
    · have hdata := hlogical u hu he
      have hF := hdata.2
      have hmem : readVector S x u ∈ bad :=
        (hbad (readVector S x u)).2 hF
      have hpres : P (readVector S x u) u := by
        intro k hk
        have hne := hdata.1 k
        cases hfirst : firstReveal S k x u with
        | none => exact False.elim (hne hfirst)
        | some v =>
            simpa [readVector, hfirst]
      have hone := logicalOneLeEventSum P hmem hpres
      simpa [he] using hone
    · simp [he]
  have hmass :
      eventMass ≤ (bad.map fiberMass).sum := by
    unfold eventMass fiberMass
    calc
      wordSum (fun u => if E u then 1 else 0) t ≤
          wordSum (logicalEventSum P bad) t :=
            logicalWordSumMono _ _ t hpoint
      _ = (bad.map (fun a =>
            wordSum (fun u => if P a u then 1 else 0) t)).sum :=
              logicalWordSumEventSum P bad t
  have hfiber : ∀ a, a ∈ bad →
      2 ^ K * fiberMass a ≤ n ^ t := by
    intro a ha
    dsimp [fiberMass, P]
    simpa only [List.length_finRange] using
      (Couple.adaptive_prescribed S a x (List.finRange K)
        (List.nodup_finRange K) t)
  have hsum :
      2 ^ K * (bad.map fiberMass).sum ≤ bad.length * n ^ t :=
    logicalListScaledSumLe (2 ^ K) (n ^ t) fiberMass bad hfiber
  have hpull :
      2 ^ K * eventMass ≤ bad.length * n ^ t :=
    Nat.le_trans (Nat.mul_le_mul_left (2 ^ K) hmass) hsum
  have hscaled :
      (4 * eventMass) * (2 ^ K) ≤
        (4 * bad.length) * n ^ t := by
    calc
      (4 * eventMass) * (2 ^ K) =
          4 * ((2 ^ K) * eventMass) := by ac_rfl
      _ ≤ 4 * (bad.length * n ^ t) :=
        Nat.mul_le_mul_left 4 hpull
      _ = (4 * bad.length) * n ^ t := by ac_rfl
  have hproduct :
      (4 * eventMass) * (2 ^ K) ≤ (n ^ t) * (2 ^ K) := by
    calc
      (4 * eventMass) * (2 ^ K) ≤
          (4 * bad.length) * n ^ t := hscaled
      _ ≤ (2 ^ K) * n ^ t :=
        Nat.mul_le_mul_right (n ^ t) hquarter
      _ = (n ^ t) * (2 ^ K) := Nat.mul_comm _ _
  have hpow : 0 < (2 : Nat) ^ K := Nat.pow_pos (by decide)
  have hfinal := Nat.le_of_mul_le_mul_right hproduct hpow
  simpa [eventMass] using hfinal

end L4.Height

