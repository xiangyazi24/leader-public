import Leader.L4.Height.Window

namespace L4.Height

open Classical

/-- `wordSum` only inspects words of the stated length, so pointwise
comparison on that slice is enough. -/
theorem wordSum_mono_on_length {n : Nat}
    (f g : List (Fin n) → Nat) :
    ∀ k, (∀ w, w.length = k → f w ≤ g w) →
      wordSum f k ≤ wordSum g k := by
  intro k
  induction k generalizing f g with
  | zero =>
      intro h
      exact h [] rfl
  | succ k ih =>
      intro h
      simp only [wordSum]
      apply sum_ofFn_le
      intro e
      apply ih
      intro w hw
      apply h
      simp only [List.length_cons, hw]

/-- Congruence for word sums. -/
theorem wordSum_congr_fun {n : Nat}
    (f g : List (Fin n) → Nat) (k : Nat)
    (h : ∀ w, f w = g w) :
    wordSum f k = wordSum g k := by
  exact wordSum_congr f g h k

/-- The all-zero word function has zero mass. -/
theorem wordSum_const_zero {n : Nat} (k : Nat) :
    wordSum (fun _ : List (Fin n) => 0) k = 0 := by
  exact wordSum_zero (n := n) k

/-- The total stopped time over words of length `k` is at most
`k * n^k`. -/
theorem wordSum_stoppedTime_le {α : Type} {n : Nat}
    (next : α → Fin n → α) (stop : α → Prop)
    (x : α) (k : Nat) :
    wordSum (stoppedTime next stop x) k ≤ k * n ^ k := by
  calc
    wordSum (stoppedTime next stop x) k
        ≤ wordSum (fun _ : List (Fin n) => k) k := by
            apply wordSum_mono_on_length
            intro w hw
            have h := stoppedTime_le_length next stop x w
            simpa [hw] using h
    _ = k * n ^ k := by
      have h := wordSum_mul_left (n := n) k
        (fun _ : List (Fin n) => 1) k
      rw [wordSum_const_one] at h
      simpa using h

/-- If the stopped endpoint is not a stop state, every letter was consumed. -/
theorem stoppedTime_eq_length_of_not_stopped {α : Type} {n : Nat}
    (next : α → Fin n → α) (stop : α → Prop) :
    ∀ (x : α) (w : List (Fin n)),
      ¬ stop (stoppedRun next stop x w) →
        stoppedTime next stop x w = w.length := by
  intro x w
  induction w generalizing x with
  | nil =>
      intro h
      rfl
  | cons e w ih =>
      intro hfinal
      by_cases hx : stop x
      · exfalso
        apply hfinal
        simpa [stoppedRun, hx] using hx
      · simp only [stoppedRun, hx, if_false] at hfinal
        simp only [stoppedTime, hx, if_false, List.length_cons]
        exact congrArg Nat.succ (ih (next x e) hfinal)

/-- Markov's inequality in exact word-count form. -/
theorem markov_survivors {α : Type} {n : Nat}
    (next : α → Fin n → α) (stop : α → Prop)
    (x : α) (A t : Nat)
    (hmean : IIDExpectedHittingTimeAtMost next stop x A) :
    t * wordSum
        (fun u => if stop (stoppedRun next stop x u) then 0 else 1) t ≤
      A * n ^ t := by
  have hcost := hmean t
  rw [iidHitCost_eq_wordSum] at hcost
  calc
    t * wordSum
        (fun u => if stop (stoppedRun next stop x u) then 0 else 1) t =
      wordSum
        (fun u => t *
          (if stop (stoppedRun next stop x u) then 0 else 1)) t := by
            symm
            exact wordSum_mul_left (n := n) t
              (fun u =>
                if stop (stoppedRun next stop x u) then 0 else 1) t
    _ ≤ wordSum (stoppedTime next stop x) t := by
      apply wordSum_mono_on_length
      intro w hw
      by_cases hs : stop (stoppedRun next stop x w)
      · simp [hs]
      · have hfull :=
          stoppedTime_eq_length_of_not_stopped next stop x w hs
        simpa [hs, hfull, hw]
    _ ≤ A * n ^ t := hcost

/-- Two quarter-mass bad events have union mass at most one half. -/
theorem union_failure {n D : Nat}
    (F₁ F₂ : List (Fin n) → Prop)
    (hfirst :
      4 * wordSum (fun u => if F₁ u then 1 else 0) D ≤ n ^ D)
    (hsecond :
      4 * wordSum (fun u => if F₂ u then 1 else 0) D ≤ n ^ D) :
    2 * wordSum
        (fun u => if F₁ u ∨ F₂ u then 1 else 0) D ≤ n ^ D := by
  have hu :
      wordSum (fun u => if F₁ u ∨ F₂ u then 1 else 0) D ≤
        wordSum
          (fun u =>
            (if F₁ u then 1 else 0) + (if F₂ u then 1 else 0)) D := by
    apply wordSum_mono
    intro w
    by_cases h₁ : F₁ w
    · by_cases h₂ : F₂ w
      · simp [h₁, h₂]
      · simp [h₁, h₂]
    · by_cases h₂ : F₂ w
      · simp [h₁, h₂]
      · simp [h₁, h₂]
  rw [wordSum_add_fun] at hu
  omega

/-- Raw execution respects concatenation. -/
theorem runWord_append {α : Type} {n : Nat}
    (next : α → Fin n → α) (x : α)
    (u v : List (Fin n)) :
    runWord next x (u ++ v) =
      runWord next (runWord next x u) v := by
  simp only [runWord, List.foldl_append]

/-- A forward-closed predicate remains true along every raw word. -/
theorem runWord_of_closed {α : Type} {n : Nat}
    (next : α → Fin n → α) (P : α → Prop)
    (hclosed : ∀ x e, P x → P (next x e)) :
    ∀ (x : α) (w : List (Fin n)), P x → P (runWord next x w) := by
  intro x w
  induction w generalizing x with
  | nil =>
      intro hx
      simpa [runWord] using hx
  | cons e w ih =>
      intro hx
      simpa [runWord] using
        (ih (next x e) (hclosed x e hx))

/-- For a forward-closed target, raw and stopped endpoints agree on
membership in the target. -/
theorem stoppedRun_mem_iff_runWord_mem {α : Type} {n : Nat}
    (next : α → Fin n → α) (P : α → Prop)
    (hclosed : ∀ x e, P x → P (next x e)) :
    ∀ (x : α) (w : List (Fin n)),
      P (stoppedRun next P x w) ↔ P (runWord next x w) := by
  intro x w
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
      by_cases hx : P x
      · have hrun : P (runWord next x (e :: w)) :=
          runWord_of_closed next P hclosed x (e :: w) hx
        constructor
        · intro h
          exact hrun
        · intro h
          simpa [stoppedRun, hx] using hx
      · simpa [stoppedRun, runWord, hx] using
          (ih (next x e))

/-- Restrict a transition system to a forward-closed predicate. -/
def closedNext {α : Type} {n : Nat}
    (next : α → Fin n → α) (G : α → Prop)
    (hG : ∀ x e, G x → G (next x e))
    (x : {y : α // G y}) (e : Fin n) : {y : α // G y} :=
  ⟨next x.1 e, hG x.1 e x.2⟩

/-- Restriction does not change the underlying raw trajectory. -/
theorem runWord_closedNext_val {α : Type} {n : Nat}
    (next : α → Fin n → α) (G : α → Prop)
    (hG : ∀ x e, G x → G (next x e)) :
    ∀ (x : {y : α // G y}) (w : List (Fin n)),
      (runWord (closedNext next G hG) x w).1 =
        runWord next x.1 w := by
  intro x w
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
      simpa [runWord, closedNext] using
        (ih (closedNext next G hG x e))

/-- Truncated hitting costs are unchanged after restriction to a closed
state predicate. -/
theorem iidHitCost_closedNext {α : Type} {n : Nat}
    (next : α → Fin n → α) (G : α → Prop)
    (hG : ∀ x e, G x → G (next x e)) (R : α → Prop) :
    ∀ t (x : {y : α // G y}),
      iidHitCost (closedNext next G hG) (fun y => R y.1) t x =
        iidHitCost next R t x.1 := by
  intro t
  induction t with
  | zero =>
      intro x
      rfl
  | succ t ih =>
      intro x
      by_cases hx : R x.1
      · simp [iidHitCost, hx]
      · simp only [iidHitCost, hx, if_false]
        apply congrArg (fun z : Nat => n ^ (t + 1) + z)
        apply sum_ofFn_eq
        intro e
        simpa [closedNext] using
          (ih (closedNext next G hG x e))

/-- A one-half success chance in every fixed window gives mean restart
cost at most twice the window length. -/
theorem restart_mean {α : Type} {n D : Nat}
    (next : α → Fin n → α) (R G : α → Prop)
    (hR : ∀ x e, R x → R (next x e))
    (hG : ∀ x e, G x → G (next x e))
    (hfail : ∀ x, G x → ¬ R x →
      2 * wordSum
        (fun u => if R (runWord next x u) then 0 else 1) D ≤ n ^ D)
    (x : α) (hxG : G x) :
    IIDExpectedHittingTimeAtMost next R x (2 * D) := by
  unfold IIDExpectedHittingTimeAtMost
  by_cases hzero : D = 0
  · subst D
    have hxR : R x := by
      by_cases h : R x
      · exact h
      · have hbad := hfail x hxG h
        have hcontra : (2 : Nat) ≤ 1 := by
          simpa [wordSum, runWord, h] using hbad
        omega
    intro t
    rw [iidHitCost_of_target next R x hxR t]
    simp
  · have hD : 1 ≤ D := by omega
    let nextG : {y : α // G y} → Fin n → {y : α // G y} :=
      closedNext next G hG
    let stopG : {y : α // G y} → Prop := fun y => R y.1
    let V : {y : α // G y} → Nat :=
      fun y => if stopG y then 0 else 2 * D
    have hRsub : ∀ y e, stopG y → stopG (nextG y e) := by
      intro y e hy
      simpa [stopG, nextG, closedNext] using
        (hR y.1 e hy)
    have hwindow :
        ∀ y : {z : α // G z}, ¬ stopG y →
          1 * wordSum (stoppedTime nextG stopG y) D +
              wordSum (fun u => V (stoppedRun nextG stopG y u)) D ≤
            V y * n ^ D := by
      intro y hy
      have hyR : ¬ R y.1 := by
        simpa [stopG] using hy
      have htime := wordSum_stoppedTime_le nextG stopG y D
      have hend :
          wordSum (fun u => V (stoppedRun nextG stopG y u)) D =
            (2 * D) * wordSum
              (fun u => if R (runWord next y.1 u) then 0 else 1) D := by
        rw [← wordSum_mul_left (n := n) (2 * D)
          (fun u => if R (runWord next y.1 u) then 0 else 1) D]
        apply wordSum_congr_fun
        intro u
        have hiffBase :=
          stoppedRun_mem_iff_runWord_mem nextG stopG hRsub y u
        have hval := runWord_closedNext_val next G hG y u
        have hiff :
            R (stoppedRun nextG stopG y u).1 ↔
              R (runWord next y.1 u) := by
          change stopG (stoppedRun nextG stopG y u) ↔
            R (runWord next y.1 u)
          rw [hiffBase]
          change R (runWord nextG y u).1 ↔ R (runWord next y.1 u)
          rw [hval]
        by_cases hr : R (runWord next y.1 u)
        · have hs := hiff.mpr hr
          simp [V, stopG, hs, hr]
        · have hs : ¬ R (stoppedRun nextG stopG y u).1 := by
            intro hs'
            exact hr (hiff.mp hs')
          simp [V, stopG, hs, hr]
      have hfailY := hfail y.1 y.2 hyR
      have hmass :
          (2 * D) * wordSum
              (fun u => if R (runWord next y.1 u) then 0 else 1) D ≤
            D * n ^ D := by
        calc
          (2 * D) * wordSum
              (fun u => if R (runWord next y.1 u) then 0 else 1) D =
            D * (2 * wordSum
              (fun u => if R (runWord next y.1 u) then 0 else 1) D) := by
                simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          _ ≤ D * n ^ D := Nat.mul_le_mul_left D hfailY
      have htotal :
          wordSum (stoppedTime nextG stopG y) D +
              wordSum (fun u => V (stoppedRun nextG stopG y u)) D ≤
            (2 * D) * n ^ D := by
        rw [hend]
        calc
          wordSum (stoppedTime nextG stopG y) D +
              (2 * D) * wordSum
                (fun u => if R (runWord next y.1 u) then 0 else 1) D
              ≤ D * n ^ D + D * n ^ D :=
                Nat.add_le_add htime hmass
          _ = (D + D) * n ^ D :=
                (Nat.add_mul D D (n ^ D)).symm
          _ = (2 * D) * n ^ D := by
                apply congrArg (fun q : Nat => q * n ^ D)
                omega
      simpa [V, stopG, hyR] using htotal
    have hsub :=
      expected_of_window nextG stopG V (fun _ => D) 1
        (by
          intro y hy
          exact hD)
        hwindow
    intro t
    by_cases hxR : R x
    · rw [iidHitCost_of_target next R x hxR t]
      simp
    · let y : {z : α // G z} := ⟨x, hxG⟩
      have hs := hsub t y
      have hs' :
          iidHitCost nextG stopG t y ≤ (2 * D) * n ^ t := by
        simpa [V, stopG, y, hxR] using hs
      have heq :
          iidHitCost nextG stopG t y = iidHitCost next R t x := by
        simpa [nextG, stopG, y] using
          (iidHitCost_closedNext next G hG R t
            (⟨x, hxG⟩ : {z : α // G z}))
      rw [heq] at hs'
      exact hs'

/-- The same restart hypothesis gives the exact geometric tail after
`j` windows. -/
theorem restart_tail {α : Type} {n D : Nat}
    (next : α → Fin n → α) (R G : α → Prop)
    (hR : ∀ x e, R x → R (next x e))
    (hG : ∀ x e, G x → G (next x e))
    (hfail : ∀ x, G x → ¬ R x →
      2 * wordSum
        (fun u => if R (runWord next x u) then 0 else 1) D ≤ n ^ D)
    (x : α) (hxG : G x) (j : Nat) :
    2 ^ j * wordSum
        (fun u => if R (runWord next x u) then 0 else 1) (j * D) ≤
      n ^ (j * D) := by
  let miss : α → List (Fin n) → Nat :=
    fun y u => if R (runWord next y u) then 0 else 1
  have hblock : ∀ y, G y →
      2 * wordSum (miss y) D ≤
        n ^ D * (if R y then 0 else 1) := by
    intro y hy
    by_cases hr : R y
    · have hzero : wordSum (miss y) D = 0 := by
        calc
          wordSum (miss y) D =
              wordSum (fun _ : List (Fin n) => 0) D := by
                apply wordSum_congr_fun
                intro u
                have hru := runWord_of_closed next R hR y u hr
                simp [miss, hru]
          _ = 0 := wordSum_const_zero D
      simp [hzero, hr]
    · simpa [miss, hr] using hfail y hy hr
  change 2 ^ j * wordSum (miss x) (j * D) ≤ n ^ (j * D)
  induction j with
  | zero =>
      by_cases hr : R x
      · simp [miss, wordSum, runWord, hr]
      · simp [miss, wordSum, runWord, hr]
  | succ j ih =>
      have hmul : Nat.succ j * D = j * D + D := by
        exact Nat.succ_mul j D
      have hrec :
          2 * wordSum (miss x) ((Nat.succ j) * D) ≤
            n ^ D * wordSum (miss x) (j * D) := by
        rw [hmul]
        rw [wordSum_add (miss x) (j * D) D]
        rw [← wordSum_mul_left (n := n) 2
          (fun u => wordSum (fun v => miss x (u ++ v)) D) (j * D)]
        rw [← wordSum_mul_left (n := n) (n ^ D) (miss x) (j * D)]
        apply wordSum_mono
        intro u
        have hyG := runWord_of_closed next G hG x u hxG
        have hb := hblock (runWord next x u) hyG
        simpa [miss, runWord_append] using hb
      calc
        2 ^ (Nat.succ j) * wordSum (miss x) ((Nat.succ j) * D) =
            2 ^ j *
              (2 * wordSum (miss x) ((Nat.succ j) * D)) := by
                simp only [Nat.pow_succ, Nat.mul_assoc]
        _ ≤ 2 ^ j *
              (n ^ D * wordSum (miss x) (j * D)) :=
                Nat.mul_le_mul_left (2 ^ j) hrec
        _ = n ^ D *
              (2 ^ j * wordSum (miss x) (j * D)) := by
                simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ ≤ n ^ D * n ^ (j * D) :=
                Nat.mul_le_mul_left (n ^ D) ih
        _ = n ^ ((Nat.succ j) * D) := by
                rw [hmul, Nat.pow_add]
                exact Nat.mul_comm _ _

/-- Two quarter-failure estimates imply the one-half raw restart estimate. -/
theorem trial_from_two {α : Type} {n D : Nat}
    (next : α → Fin n → α) (R : α → Prop) (x : α)
    (F₁ F₂ : List (Fin n) → Prop)
    (hfirst :
      4 * wordSum (fun u => if F₁ u then 1 else 0) D ≤ n ^ D)
    (hsecond :
      4 * wordSum (fun u => if F₂ u then 1 else 0) D ≤ n ^ D)
    (hcover : ∀ u, u.length = D → ¬ F₁ u → ¬ F₂ u →
      R (runWord next x u)) :
    2 * wordSum
        (fun u => if R (runWord next x u) then 0 else 1) D ≤ n ^ D := by
  have hunion := union_failure F₁ F₂ hfirst hsecond
  have hmass :
      wordSum (fun u => if R (runWord next x u) then 0 else 1) D ≤
        wordSum (fun u => if F₁ u ∨ F₂ u then 1 else 0) D := by
    apply wordSum_mono_on_length
    intro u hu
    by_cases hr : R (runWord next x u)
    · simp [hr]
    · have hor : F₁ u ∨ F₂ u := by
        by_cases h₁ : F₁ u
        · exact Or.inl h₁
        · by_cases h₂ : F₂ u
          · exact Or.inr h₂
          · exact False.elim (hr (hcover u hu h₁ h₂))
      simp [hr, hor]
  exact Nat.le_trans (Nat.mul_le_mul_left 2 hmass) hunion

end L4.Height
