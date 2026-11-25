import Leader.L4.Height.Core

namespace L4.Height

open Classical

/-- Execute a finite scheduler word without stopping. -/
def runWord {α : Type} {n : Nat}
    (next : α → Fin n → α) (x : α) (w : List (Fin n)) : α :=
  w.foldl next x

/-- Execute a word, freezing as soon as the current state is in the stop set.
The stop test is made before consuming the next letter. -/
noncomputable def stoppedRun {α : Type} {n : Nat}
    (next : α → Fin n → α) (stop : α → Prop) :
    α → List (Fin n) → α
  | x, [] => x
  | x, e :: w =>
      if stop x then x else stoppedRun next stop (next x e) w

/-- Number of letters consumed before the first stop state. -/
noncomputable def stoppedTime {α : Type} {n : Nat}
    (next : α → Fin n → α) (stop : α → Prop) :
    α → List (Fin n) → Nat
  | x, [] => 0
  | x, e :: w =>
      if stop x then 0 else Nat.succ (stoppedTime next stop (next x e) w)

/-- Sum a function over all words of a fixed length. -/
def wordSum {n : Nat} (f : List (Fin n) → Nat) : Nat → Nat
  | 0 => f []
  | k + 1 =>
      (List.ofFn (fun e : Fin n => wordSum (fun v => f (e :: v)) k)).sum

/-- Sum monotonicity for an ordinary list, proved without Mathlib. -/
theorem list_sum_mono {β : Type} (l : List β) (f g : β → Nat)
    (h : ∀ a, a ∈ l → f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil =>
      simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      apply Nat.add_le_add
      · exact h a (by simp)
      · apply ih
        intro b hb
        exact h b (by simp [hb])

/-- Additivity of list sums, proved without unavailable List.sum_map_add. -/
theorem list_sum_add {β : Type} (l : List β) (f g : β → Nat) :
    (l.map (fun a => f a + g a)).sum =
      (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil =>
      simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      omega

/-- Constant multiplication can be pulled through a list sum. -/
theorem list_sum_mul_left {β : Type} (l : List β) (c : Nat)
    (f : β → Nat) :
    (l.map (fun a => c * f a)).sum =
      c * (l.map f).sum := by
  induction l with
  | nil =>
      simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, Nat.mul_add]

/-- Congruence for sums over a mapped list. -/
theorem list_sum_congr {β : Type} (l : List β) (f g : β → Nat)
    (h : ∀ a, a ∈ l → f a = g a) :
    (l.map f).sum = (l.map g).sum := by
  induction l with
  | nil =>
      simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [h a (by simp)]
      apply congrArg
      apply ih
      intro b hb
      exact h b (by simp [hb])

/-- Congruence of sums indexed by `Fin n`. -/
theorem sum_ofFn_eq {n : Nat} (f g : Fin n → Nat)
    (hfg : ∀ i, f i = g i) :
    (List.ofFn f).sum = (List.ofFn g).sum := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, hfg 0]
      exact congrArg (g 0 + ·)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))

/-- Monotonicity of sums indexed by `Fin n`. -/
theorem sum_ofFn_le {n : Nat} (f g : Fin n → Nat)
    (hfg : ∀ i, f i ≤ g i) :
    (List.ofFn f).sum ≤ (List.ofFn g).sum := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      exact Nat.add_le_add (hfg 0)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))

/-- Additivity of sums indexed by `Fin n`. -/
theorem sum_ofFn_add {n : Nat} (f g : Fin n → Nat) :
    (List.ofFn (fun i => f i + g i)).sum =
      (List.ofFn f).sum + (List.ofFn g).sum := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, ih]
      omega

/-- Pull a constant left factor through a `Fin n` sum. -/
theorem sum_ofFn_mul_left {n : Nat} (c : Nat) (f : Fin n → Nat) :
    (List.ofFn (fun i => c * f i)).sum =
      c * (List.ofFn f).sum := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, ih, Nat.mul_add]

/-- Sum of a constant over `Fin n`. -/
theorem sum_ofFn_const (n c : Nat) :
    (List.ofFn (fun _ : Fin n => c)).sum = n * c := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, ih]
      rw [Nat.succ_mul]
      exact Nat.add_comm _ _

theorem wordSum_mono {n : Nat} (f g : List (Fin n) → Nat) :
    (∀ w, f w ≤ g w) → ∀ k, wordSum f k ≤ wordSum g k := by
  intro h k
  induction k generalizing f g with
  | zero =>
      exact h []
  | succ k ih =>
      simp only [wordSum]
      apply sum_ofFn_le
      intro e
      exact ih
        (fun v => f (e :: v))
        (fun v => g (e :: v))
        (fun v => h (e :: v))

/-- Pointwise equality gives equality of word sums. -/
theorem wordSum_congr {n : Nat} (f g : List (Fin n) → Nat)
    (h : ∀ w, f w = g w) :
    ∀ k, wordSum f k = wordSum g k := by
  intro k
  induction k generalizing f g with
  | zero =>
      exact h []
  | succ k ih =>
      simp only [wordSum]
      apply sum_ofFn_eq
      intro e
      exact ih
        (fun v => f (e :: v))
        (fun v => g (e :: v))
        (fun v => h (e :: v))

theorem wordSum_add_fun {n : Nat} (f g : List (Fin n) → Nat) (k : Nat) :
    wordSum (fun w => f w + g w) k =
      wordSum f k + wordSum g k := by
  induction k generalizing f g with
  | zero =>
      rfl
  | succ k ih =>
      simp only [wordSum]
      calc
        (List.ofFn (fun e : Fin n =>
          wordSum (fun v => f (e :: v) + g (e :: v)) k)).sum =
            (List.ofFn (fun e : Fin n =>
              wordSum (fun v => f (e :: v)) k +
                wordSum (fun v => g (e :: v)) k)).sum := by
                  apply sum_ofFn_eq
                  intro e
                  exact ih (fun v => f (e :: v))
                    (fun v => g (e :: v))
        _ =
            (List.ofFn (fun e : Fin n =>
              wordSum (fun v => f (e :: v)) k)).sum +
            (List.ofFn (fun e : Fin n =>
              wordSum (fun v => g (e :: v)) k)).sum :=
              sum_ofFn_add
                (fun e : Fin n => wordSum (fun v => f (e :: v)) k)
                (fun e : Fin n => wordSum (fun v => g (e :: v)) k)

theorem wordSum_mul_left {n : Nat} (c : Nat)
    (f : List (Fin n) → Nat) (k : Nat) :
    wordSum (fun w => c * f w) k =
      c * wordSum f k := by
  induction k generalizing f with
  | zero =>
      simp [wordSum]
  | succ k ih =>
      simp only [wordSum]
      calc
        (List.ofFn (fun e : Fin n =>
          wordSum (fun v => c * f (e :: v)) k)).sum =
            (List.ofFn (fun e : Fin n =>
              c * wordSum (fun v => f (e :: v)) k)).sum := by
                apply sum_ofFn_eq
                intro e
                exact ih (fun v => f (e :: v))
        _ = c *
            (List.ofFn (fun e : Fin n =>
              wordSum (fun v => f (e :: v)) k)).sum :=
                sum_ofFn_mul_left c
                  (fun e : Fin n => wordSum (fun v => f (e :: v)) k)

/-- Pull a constant right factor through a word sum. -/
theorem wordSum_mul_right {n : Nat} (f : List (Fin n) → Nat)
    (c k : Nat) :
    wordSum (fun w => f w * c) k = wordSum f k * c := by
  calc
    wordSum (fun w => f w * c) k =
        wordSum (fun w => c * f w) k := by
          apply wordSum_congr
          intro w
          exact Nat.mul_comm _ _
    _ = c * wordSum f k := wordSum_mul_left c f k
    _ = wordSum f k * c := Nat.mul_comm _ _

/-- Sum of a constant over all words of length `k`. -/
theorem wordSum_const {n : Nat} (c k : Nat) :
    wordSum (fun _ : List (Fin n) => c) k = n ^ k * c := by
  induction k with
  | zero =>
      simp [wordSum]
  | succ k ih =>
      simp only [wordSum]
      calc
        (List.ofFn (fun _ : Fin n =>
          wordSum (fun _ : List (Fin n) => c) k)).sum =
            (List.ofFn (fun _ : Fin n => n ^ k * c)).sum := by
              apply sum_ofFn_eq
              intro e
              exact ih
        _ = n * (n ^ k * c) := sum_ofFn_const n (n ^ k * c)
        _ = (n ^ k * n) * c := by
              rw [← Nat.mul_assoc, Nat.mul_comm n (n ^ k)]
        _ = n ^ (k + 1) * c := by
              rw [Nat.pow_succ]

theorem wordSum_const_one {n : Nat} (k : Nat) :
    wordSum (fun _ : List (Fin n) => 1) k = n ^ k := by
  simpa using (wordSum_const (n := n) 1 k)

theorem wordSum_zero {n : Nat} (k : Nat) :
    wordSum (fun _ : List (Fin n) => 0) k = 0 := by
  simpa using (wordSum_const (n := n) 0 k)

/-- Summing over words of length `a+b` is prefix sum followed by suffix sum. -/
theorem wordSum_add {n : Nat} (f : List (Fin n) → Nat) (a b : Nat) :
    wordSum f (a + b) =
      wordSum (fun u => wordSum (fun v => f (u ++ v)) b) a := by
  induction a generalizing f with
  | zero =>
      simp [wordSum]
  | succ a ih =>
      rw [Nat.succ_add]
      simp only [wordSum]
      apply sum_ofFn_eq
      intro e
      simpa only [List.cons_append] using
        (ih (fun z => f (e :: z)))

theorem stoppedTime_le_length {α : Type} {n : Nat}
    (next : α → Fin n → α) (stop : α → Prop) :
    ∀ (x : α) (w : List (Fin n)),
      stoppedTime next stop x w ≤ w.length := by
  intro x w
  induction w generalizing x with
  | nil =>
      simp [stoppedTime]
  | cons e w ih =>
      by_cases h : stop x
      · simp [stoppedTime, h]
      · simp [stoppedTime, h]
        exact ih (next x e)

theorem stoppedRun_of_stop {α : Type} {n : Nat}
    (next : α → Fin n → α) (stop : α → Prop) (x : α)
    (hx : stop x) (w : List (Fin n)) :
    stoppedRun next stop x w = x := by
  cases w with
  | nil =>
      rfl
  | cons e w =>
      simp [stoppedRun, hx]

theorem stoppedTime_of_stop {α : Type} {n : Nat}
    (next : α → Fin n → α) (stop : α → Prop) (x : α)
    (hx : stop x) (w : List (Fin n)) :
    stoppedTime next stop x w = 0 := by
  cases w with
  | nil =>
      rfl
  | cons e w =>
      simp [stoppedTime, hx]

theorem stoppedTime_append {α : Type} {n : Nat}
    (next : α → Fin n → α) (stop : α → Prop) :
    ∀ (x : α) (u v : List (Fin n)),
      stoppedTime next stop x (u ++ v) =
        stoppedTime next stop x u +
          stoppedTime next stop (stoppedRun next stop x u) v := by
  intro x u
  induction u generalizing x with
  | nil =>
      intro v
      simp [stoppedRun, stoppedTime]
  | cons e u ih =>
      intro v
      by_cases hx : stop x
      · simp only [List.cons_append, stoppedTime, stoppedRun,
          hx, if_pos, Nat.zero_add]
        exact (stoppedTime_of_stop next stop x hx v).symm
      · simp only [List.cons_append, stoppedTime, stoppedRun,
          hx, if_false]
        rw [ih (next x e) v]
        omega

/-- Sum of truncated first-hit times over the n^t length-t scheduler words.
Outside the target every word pays one step, then its suffix pays recursively.
The target is tested at time zero, even on the empty word. -/
noncomputable def iidHitCost {α : Type} {n : Nat}
    (next : α → Fin n → α) (target : α → Prop) : Nat → α → Nat
  | 0, _ => 0
  | t + 1, x =>
      if target x then 0
      else n ^ (t + 1) +
        (List.ofFn (fun e : Fin n =>
          iidHitCost next target t (next x e))).sum

/-- Starting inside the target has zero expected cost at every horizon. -/
theorem iidHitCost_of_target {α : Type} {n : Nat}
    (next : α → Fin n → α) (target : α → Prop) (x : α)
    (hx : target x) (t : Nat) :
    iidHitCost next target t x = 0 := by
  cases t with
  | zero =>
      rfl
  | succ t =>
      simp [iidHitCost, hx]

/-- The truncated cost is exactly the word sum of stopped elapsed times. -/
theorem iidHitCost_eq_wordSum {α : Type} {n : Nat}
    (next : α → Fin n → α) (target : α → Prop) :
    ∀ t x, iidHitCost next target t x =
      wordSum (stoppedTime next target x) t := by
  intro t
  induction t with
  | zero =>
      intro x
      rfl
  | succ t ih =>
      intro x
      by_cases hx : target x
      · rw [iidHitCost_of_target next target x hx (t + 1)]
        symm
        calc
          wordSum (stoppedTime next target x) (t + 1) =
              wordSum (fun _ : List (Fin n) => 0) (t + 1) := by
                apply wordSum_congr
                intro w
                exact stoppedTime_of_stop next target x hx w
          _ = 0 := wordSum_zero (n := n) (t + 1)
      · simp only [iidHitCost, hx, if_false, wordSum]
        have hpow : n ^ (t + 1) = n * n ^ t := by
          rw [Nat.pow_succ, Nat.mul_comm]
        rw [hpow]
        rw [← sum_ofFn_const n (n ^ t)]
        rw [← sum_ofFn_add]
        apply sum_ofFn_eq
        intro e
        rw [ih (next x e)]
        rw [← wordSum_const_one (n := n) t]
        rw [← wordSum_add_fun]
        apply wordSum_congr
        intro v
        simp only [stoppedTime, hx, if_false]
        omega

/-- Splitting the truncated cost at a cut not beyond the horizon. -/
theorem iidHitCost_split {α : Type} {n : Nat}
    (next : α → Fin n → α) (stop : α → Prop) :
    ∀ t w x, w ≤ t →
      iidHitCost next stop t x =
        n ^ (t - w) *
          wordSum (stoppedTime next stop x) w +
        wordSum (fun u => iidHitCost next stop (t - w)
          (stoppedRun next stop x u)) w := by
  intro t w x hwt
  calc
    iidHitCost next stop t x =
        wordSum (stoppedTime next stop x) t :=
          iidHitCost_eq_wordSum next stop t x
    _ = wordSum (fun u =>
          wordSum (fun v => stoppedTime next stop x (u ++ v))
            (t - w)) w := by
          have hwa : w + (t - w) = t := by omega
          simpa only [hwa] using
            (wordSum_add (n := n) (stoppedTime next stop x)
              w (t - w))
    _ = wordSum (fun u =>
          n ^ (t - w) * stoppedTime next stop x u +
            iidHitCost next stop (t - w)
              (stoppedRun next stop x u)) w := by
          apply wordSum_congr
          intro u
          calc
            wordSum
                (fun v => stoppedTime next stop x (u ++ v))
                (t - w) =
              wordSum
                (fun v => stoppedTime next stop x u +
                  stoppedTime next stop
                    (stoppedRun next stop x u) v)
                (t - w) := by
                  apply wordSum_congr
                  intro v
                  exact stoppedTime_append next stop x u v
            _ = wordSum
                  (fun _ : List (Fin n) => stoppedTime next stop x u)
                  (t - w) +
                wordSum
                  (stoppedTime next stop
                    (stoppedRun next stop x u))
                  (t - w) :=
                    wordSum_add_fun
                      (fun _ : List (Fin n) => stoppedTime next stop x u)
                      (stoppedTime next stop
                        (stoppedRun next stop x u))
                      (t - w)
            _ = n ^ (t - w) * stoppedTime next stop x u +
                iidHitCost next stop (t - w)
                  (stoppedRun next stop x u) := by
                    rw [wordSum_const]
                    rw [← iidHitCost_eq_wordSum next stop
                      (t - w) (stoppedRun next stop x u)]
    _ = n ^ (t - w) *
          wordSum (stoppedTime next stop x) w +
        wordSum (fun u => iidHitCost next stop (t - w)
          (stoppedRun next stop x u)) w := by
            rw [wordSum_add_fun, wordSum_mul_left]

/-- Uniform bounds on the truncated IID expectations. -/
def IIDExpectedHittingTimeAtMost {α : Type} {n : Nat}
    (next : α → Fin n → α) (target : α → Prop)
    (x : α) (bound : Nat) : Prop :=
  ∀ t : Nat, iidHitCost next target t x ≤ bound * n ^ t

theorem expected_of_window {α : Type} {n : Nat}
    (next : α → Fin n → α) (stop : α → Prop)
    (V len : α → Nat) (c : Nat)
    (hlen : ∀ x, ¬ stop x → 1 ≤ len x)
    (H : ∀ x, ¬ stop x →
      c * wordSum (stoppedTime next stop x) (len x) +
        wordSum (fun u => V (stoppedRun next stop x u)) (len x) ≤
          V x * n ^ (len x)) :
    ∀ t x, c * iidHitCost next stop t x ≤ V x * n ^ t := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
      intro x
      by_cases hx : stop x
      · rw [iidHitCost_of_target next stop x hx t]
        simp
      · by_cases hn : n = 0
        · subst n
          cases t with
          | zero =>
              simp [iidHitCost]
          | succ t =>
              simp [iidHitCost, hx]
        · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
          by_cases htw : t ≤ len x
          · have hsplit :=
              iidHitCost_split next stop (len x) t x htw
            have hcostle :
                n ^ (len x - t) * iidHitCost next stop t x ≤
                  wordSum (stoppedTime next stop x) (len x) := by
              rw [← iidHitCost_eq_wordSum next stop (len x) x]
              rw [hsplit]
              rw [iidHitCost_eq_wordSum next stop t x]
              omega
            have hH := H x hx
            have hleft :
                (c * iidHitCost next stop t x) * n ^ (len x - t) ≤
                  V x * n ^ (len x) := by
              calc
                (c * iidHitCost next stop t x) * n ^ (len x - t) =
                    c * (n ^ (len x - t) *
                      iidHitCost next stop t x) := by
                        rw [Nat.mul_assoc,
                          Nat.mul_comm (iidHitCost next stop t x)
                            (n ^ (len x - t))]
                _ ≤ c * wordSum (stoppedTime next stop x) (len x) :=
                      Nat.mul_le_mul_left c hcostle
                _ ≤ c * wordSum (stoppedTime next stop x) (len x) +
                      wordSum (fun u => V (stoppedRun next stop x u))
                        (len x) := by
                          omega
                _ ≤ V x * n ^ (len x) := hH
            have hexp : t + (len x - t) = len x := by omega
            have hpow :
                n ^ (len x) = n ^ t * n ^ (len x - t) := by
              calc
                n ^ (len x) = n ^ (t + (len x - t)) :=
                  congrArg (fun q => n ^ q) hexp.symm
                _ = n ^ t * n ^ (len x - t) := by
                  rw [Nat.pow_add]
            have hscaled :
                (c * iidHitCost next stop t x) * n ^ (len x - t) ≤
                  (V x * n ^ t) * n ^ (len x - t) := by
              calc
                (c * iidHitCost next stop t x) * n ^ (len x - t) ≤
                    V x * n ^ (len x) := hleft
                _ = (V x * n ^ t) * n ^ (len x - t) := by
                    rw [hpow, ← Nat.mul_assoc]
            exact Nat.le_of_mul_le_mul_right hscaled
              (Nat.pow_pos hnpos)
          · have hlt : len x < t := Nat.lt_of_not_ge htw
            have hw : 1 ≤ len x := hlen x hx
            have hklt : t - len x < t := by omega
            have hsplit := iidHitCost_split next stop t (len x) x
              (Nat.le_of_lt hlt)
            have hIH : ∀ u,
                c * iidHitCost next stop (t - len x)
                    (stoppedRun next stop x u) ≤
                  V (stoppedRun next stop x u) *
                    n ^ (t - len x) := by
              intro u
              exact ih (t - len x) hklt
                (stoppedRun next stop x u)
            have hsum0 := wordSum_mono
              (fun u => c * iidHitCost next stop (t - len x)
                (stoppedRun next stop x u))
              (fun u => V (stoppedRun next stop x u) *
                n ^ (t - len x)) hIH (len x)
            have hsum :
                c * wordSum
                    (fun u => iidHitCost next stop (t - len x)
                      (stoppedRun next stop x u)) (len x) ≤
                  n ^ (t - len x) *
                    wordSum (fun u => V (stoppedRun next stop x u))
                      (len x) := by
              calc
                c * wordSum
                    (fun u => iidHitCost next stop (t - len x)
                      (stoppedRun next stop x u)) (len x) =
                  wordSum
                    (fun u => c * iidHitCost next stop (t - len x)
                      (stoppedRun next stop x u)) (len x) :=
                    (wordSum_mul_left c
                      (fun u => iidHitCost next stop (t - len x)
                        (stoppedRun next stop x u)) (len x)).symm
                _ ≤ wordSum
                    (fun u => V (stoppedRun next stop x u) *
                      n ^ (t - len x)) (len x) := hsum0
                _ = wordSum (fun u => V (stoppedRun next stop x u))
                      (len x) * n ^ (t - len x) :=
                    wordSum_mul_right
                      (fun u => V (stoppedRun next stop x u))
                      (n ^ (t - len x)) (len x)
                _ = n ^ (t - len x) *
                    wordSum (fun u => V (stoppedRun next stop x u))
                      (len x) := Nat.mul_comm _ _
            have hH := H x hx
            have hexp : (t - len x) + len x = t := by omega
            have hpow :
                n ^ t = n ^ (t - len x) * n ^ (len x) := by
              calc
                n ^ t = n ^ ((t - len x) + len x) :=
                  congrArg (fun q => n ^ q) hexp.symm
                _ = n ^ (t - len x) * n ^ (len x) := by
                  rw [Nat.pow_add]
            calc
              c * iidHitCost next stop t x =
                  c * (n ^ (t - len x) *
                      wordSum (stoppedTime next stop x) (len x) +
                    wordSum
                      (fun u => iidHitCost next stop (t - len x)
                        (stoppedRun next stop x u)) (len x)) := by
                          rw [hsplit]
              _ = c * (n ^ (t - len x) *
                      wordSum (stoppedTime next stop x) (len x)) +
                    c * wordSum
                      (fun u => iidHitCost next stop (t - len x)
                        (stoppedRun next stop x u)) (len x) := by
                          rw [Nat.mul_add]
              _ = n ^ (t - len x) *
                      (c * wordSum (stoppedTime next stop x) (len x)) +
                    c * wordSum
                      (fun u => iidHitCost next stop (t - len x)
                        (stoppedRun next stop x u)) (len x) := by
                          apply congrArg (fun z => z +
                            c * wordSum
                              (fun u => iidHitCost next stop (t - len x)
                                (stoppedRun next stop x u)) (len x))
                          rw [← Nat.mul_assoc,
                            Nat.mul_comm c (n ^ (t - len x)),
                            Nat.mul_assoc]
              _ ≤ n ^ (t - len x) *
                      (c * wordSum (stoppedTime next stop x) (len x)) +
                    n ^ (t - len x) *
                      wordSum (fun u => V (stoppedRun next stop x u))
                        (len x) :=
                          Nat.add_le_add_left hsum _
              _ = n ^ (t - len x) *
                    (c * wordSum (stoppedTime next stop x) (len x) +
                      wordSum (fun u => V (stoppedRun next stop x u))
                        (len x)) := by
                          rw [Nat.mul_add]
              _ ≤ n ^ (t - len x) * (V x * n ^ (len x)) :=
                    Nat.mul_le_mul_left _ hH
              _ = V x * n ^ t := by
                    rw [hpow]
                    rw [← Nat.mul_assoc,
                      Nat.mul_comm (n ^ (t - len x)) (V x),
                      Nat.mul_assoc]

/-- The c=1 consequence in the repository's expected-hitting-time predicate. -/
theorem expectedHittingTimeAtMost_of_window {α : Type} {n : Nat}
    (next : α → Fin n → α) (stop : α → Prop)
    (V len : α → Nat)
    (hlen : ∀ x, ¬ stop x → 1 ≤ len x)
    (H : ∀ x, ¬ stop x →
      wordSum (stoppedTime next stop x) (len x) +
        wordSum (fun u => V (stoppedRun next stop x u)) (len x) ≤
          V x * n ^ (len x)) :
    ∀ x, IIDExpectedHittingTimeAtMost next stop x (V x) := by
  intro x
  unfold IIDExpectedHittingTimeAtMost
  intro t
  have hmain := expected_of_window next stop V len 1 hlen
    (by
      intro y hy
      simpa using H y hy)
  simpa using hmain t x

/-- The one-step specialization of the window theorem. -/
theorem expected_of_window_one {α : Type} {n : Nat}
    (next : α → Fin n → α) (stop : α → Prop)
    (V : α → Nat)
    (H : ∀ x, ¬ stop x →
      wordSum (stoppedTime next stop x) 1 +
        wordSum (fun u => V (stoppedRun next stop x u)) 1 ≤ V x * n) :
    ∀ t x, iidHitCost next stop t x ≤ V x * n ^ t := by
  have hmain := expected_of_window next stop V (fun _ => 1) 1
    (by
      intro x hx
      omega)
    (by
      intro x hx
      simpa using H x hx)
  intro t x
  simpa using hmain t x

/-- The one-step budget lemma follows from the window theorem. -/
theorem iidHitCost_le_of_budget {α : Type} {n : Nat}
    (next : α → Fin n → α) (target : α → Prop) (budget : α → Nat)
    (h : ∀ x, ¬ target x →
      n + (List.ofFn (fun e => budget (next x e))).sum ≤ n * budget x) :
    ∀ t x, iidHitCost next target t x ≤ budget x * n ^ t := by
  apply expected_of_window_one next target budget
  intro x hx
  have hb := h x hx
  simp only [wordSum, stoppedTime, stoppedRun, hx, if_false]
  rw [sum_ofFn_const n 1]
  simpa [Nat.pow_succ, Nat.mul_comm] using hb

#print axioms list_sum_mono
#print axioms list_sum_add
#print axioms list_sum_mul_left
#print axioms list_sum_congr
#print axioms sum_ofFn_eq
#print axioms sum_ofFn_le
#print axioms sum_ofFn_add
#print axioms sum_ofFn_mul_left
#print axioms sum_ofFn_const
#print axioms wordSum_mono
#print axioms wordSum_congr
#print axioms wordSum_add_fun
#print axioms wordSum_mul_left
#print axioms wordSum_mul_right
#print axioms wordSum_const
#print axioms wordSum_const_one
#print axioms wordSum_zero
#print axioms wordSum_add
#print axioms stoppedTime_le_length
#print axioms stoppedRun_of_stop
#print axioms stoppedTime_of_stop
#print axioms stoppedTime_append
#print axioms iidHitCost_of_target
#print axioms iidHitCost_eq_wordSum
#print axioms iidHitCost_split
#print axioms expected_of_window
#print axioms expectedHittingTimeAtMost_of_window
#print axioms expected_of_window_one
#print axioms iidHitCost_le_of_budget

end L4.Height
