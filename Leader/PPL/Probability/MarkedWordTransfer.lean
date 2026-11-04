import Leader.PPL.Modes.StoppedClockInterfaces
import Leader.PPL.Modes.ClockSuffixBridge
import Leader.PPL.Probability.LotteryMoment
import Leader.Core.PredictableTwoTargetFiniteTree

set_option autoImplicit false
set_option Elab.async false

namespace PPL.Probability

open FiniteUniformStoppingTree

/-- A predicate on marked words remains true after adding more marked letters. -/
def ExtensionMonotone (P : List Bool -> Bool) : Prop :=
  forall u v, P u = true -> P (u ++ v) = true

/-- Number of binary completions of length r that make P true after pre. -/
def binaryCompletionCount
    (P : List Bool -> Bool) (pre : List Bool) (r : Nat) : Nat :=
  (allHTWords r).countP (fun tail => P (pre ++ tail))

theorem binaryCompletionCount_succ
    (P : List Bool -> Bool) (pre : List Bool) (r : Nat) :
    binaryCompletionCount P pre (r + 1) =
      binaryCompletionCount P (pre ++ [false]) r +
        binaryCompletionCount P (pre ++ [true]) r := by
  unfold binaryCompletionCount
  rw [allHTWords, List.countP_append, List.countP_map, List.countP_map]
  simp only [Function.comp_def]
  simp [List.append_assoc]

private theorem binaryCompletionCount_all_of_mono
    (P : List Bool -> Bool) (hmono : ExtensionMonotone P)
    (pre : List Bool) (r : Nat) (hp : P pre = true) :
    binaryCompletionCount P pre r = 2 ^ r := by
  unfold binaryCompletionCount
  rw [List.countP_eq_length.mpr, allHTWords_length]
  intro tail _
  exact hmono pre tail hp

/-- Harmonic completion weight after observing the marked prefix bits.
Only the first E marks matter. -/
def completionPotential
    (E : Nat) (P : List Bool -> Bool) (bits : List Bool) : Nat :=
  let pre := bits.take E
  2 ^ pre.length * binaryCompletionCount P pre (E - pre.length)

private theorem take_append_singleton_of_le
    {A : Type} (E : Nat) (xs : List A) (a : A)
    (hE : E <= xs.length) :
    (xs ++ [a]).take E = xs.take E := by
  rw [List.take_append]
  have hz : E - xs.length = 0 := Nat.sub_eq_zero_of_le hE
  rw [hz]
  simp

private theorem completionPotential_append_of_full
    (E : Nat) (P : List Bool -> Bool) (bits : List Bool) (b : Bool)
    (hE : E <= bits.length) :
    completionPotential E P (bits ++ [b]) =
      completionPotential E P bits := by
  unfold completionPotential
  rw [take_append_singleton_of_le E bits b hE]

private theorem completionPotential_split
    (E : Nat) (P : List Bool -> Bool) (bits : List Bool)
    (hshort : bits.length < E) :
    completionPotential E P (bits ++ [true]) +
        completionPotential E P (bits ++ [false]) =
      2 * completionPotential E P bits := by
  have htake : bits.take E = bits :=
    List.take_of_length_le (Nat.le_of_lt hshort)
  have htakeH : (bits ++ [true]).take E = bits ++ [true] :=
    List.take_of_length_le (by simp; omega)
  have htakeT : (bits ++ [false]).take E = bits ++ [false] :=
    List.take_of_length_le (by simp; omega)
  have hr :
      E - bits.length =
        (E - (bits.length + 1)) + 1 := by
    omega
  have hrec :
      binaryCompletionCount P bits (E - bits.length) =
        binaryCompletionCount P (bits ++ [false])
            (E - (bits.length + 1)) +
          binaryCompletionCount P (bits ++ [true])
            (E - (bits.length + 1)) := by
    rw [hr]
    exact binaryCompletionCount_succ P bits (E - (bits.length + 1))
  unfold completionPotential
  rw [htake, htakeH, htakeT]
  simp only [List.length_append, List.length_singleton]
  rw [show E - (bits.length + 1) =
      E - (bits.length + 1) by rfl]
  rw [hrec, Nat.pow_succ]
  simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  ac_rfl

private theorem completionPotential_eq_twoPow_of_full
    (E : Nat) (P : List Bool -> Bool) (bits : List Bool)
    (hE : E <= bits.length) (hp : P (bits.take E) = true) :
    completionPotential E P bits = 2 ^ E := by
  have hlen : (bits.take E).length = E := by
    rw [List.length_take]
    omega
  dsimp only [completionPotential]
  rw [hlen]
  simp [binaryCompletionCount, allHTWords, hp]

private theorem completionPotential_eq_twoPow_of_padded
    (E : Nat) (P : List Bool -> Bool) (hmono : ExtensionMonotone P)
    (bits : List Bool) (hE : bits.length <= E) (hp : P bits = true) :
    completionPotential E P bits = 2 ^ E := by
  have htake : bits.take E = bits := List.take_of_length_le hE
  dsimp only [completionPotential]
  rw [htake, binaryCompletionCount_all_of_mono P hmono bits
      (E - bits.length) hp]
  rw [<- Nat.pow_add]
  congr 1
  omega

/-- Ghost state for the stopped marked-word tree. pre is the exact consumed
scheduler prefix; bits are precisely the marks retained before the stop. -/
structure MarkedWordState (n : Nat) where
  pre : DetSchedule n
  bits : List Bool
  stopped : Bool

def stoppedMarkedStart (n : Nat) : MarkedWordState n :=
  { pre := [], bits := [], stopped := false }

/-- One raw scheduler child. A prefix stop suppresses the current and all later
marks. Otherwise the current host's left incident edge is H=true, its outgoing
edge is T=false, and every other scheduler letter is cold. -/
def stoppedMarkedStep {n : Nat}
    (ring : DirectedRing n)
    (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool) :
    MarkedWordState n -> Fin n -> MarkedWordState n :=
  fun s e =>
    let pre' := s.pre ++ [e]
    if s.stopped then
      { pre := pre', bits := s.bits, stopped := true }
    else if stop s.pre then
      { pre := pre', bits := s.bits, stopped := true }
    else
      match incidentBit ring (host s.pre) e with
      | none =>
          { pre := pre', bits := s.bits, stopped := false }
      | some b =>
          { pre := pre', bits := s.bits ++ [b], stopped := false }

def stoppedMarkedRun {n : Nat}
    (ring : DirectedRing n)
    (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool) :
    MarkedWordState n -> DetSchedule n -> MarkedWordState n
  | s, [] => s
  | s, e :: rest =>
      stoppedMarkedRun ring host stop
        (stoppedMarkedStep ring host stop s e) rest

theorem stoppedMarkedRun_append {n : Nat}
    (ring : DirectedRing n)
    (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool)
    (s : MarkedWordState n) (u v : DetSchedule n) :
    stoppedMarkedRun ring host stop s (u ++ v) =
      stoppedMarkedRun ring host stop
        (stoppedMarkedRun ring host stop s u) v := by
  induction u generalizing s with
  | nil => rfl
  | cons e u ih =>
      simp only [List.cons_append, stoppedMarkedRun]
      exact ih (stoppedMarkedStep ring host stop s e)

private theorem stoppedMarkedRun_bits {n : Nat}
    (ring : DirectedRing n)
    (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool)
    (s : MarkedWordState n) (word : DetSchedule n) :
    (stoppedMarkedRun ring host stop s word).bits =
      if s.stopped then s.bits
      else s.bits ++
        stoppedEncounterBitsAux ring host stop s.pre word := by
  induction word generalizing s with
  | nil =>
      cases hs : s.stopped <;>
        simp [stoppedMarkedRun, stoppedEncounterBitsAux, hs]
  | cons e rest ih =>
      cases hs : s.stopped with
      | true =>
          simp [stoppedMarkedRun, stoppedMarkedStep,
            stoppedEncounterBitsAux, hs, ih]
      | false =>
          by_cases hp : stop s.pre
          · simp [stoppedMarkedRun, stoppedMarkedStep,
              stoppedEncounterBitsAux, hs, hp, ih]
          · cases hm : incidentBit ring (host s.pre) e with
            | none =>
                simp [stoppedMarkedRun, stoppedMarkedStep,
                  stoppedEncounterBitsAux, hs, hp, hm, ih]
            | some b =>
                simp [stoppedMarkedRun, stoppedMarkedStep,
                  stoppedEncounterBitsAux, hs, hp, hm, ih,
                  List.append_assoc]

theorem stoppedMarkedRun_start_bits {n : Nat}
    (ring : DirectedRing n)
    (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool)
    (word : DetSchedule n) :
    (stoppedMarkedRun ring host stop
        (stoppedMarkedStart n) word).bits =
      stoppedEncounterBits ring host stop word := by
  simpa [stoppedMarkedStart, stoppedEncounterBits] using
    (stoppedMarkedRun_bits ring host stop
      (stoppedMarkedStart n) word)

private theorem leftNeighbor_ne_self_marked {n : Nat}
    (ring : DirectedRing n) (hn2 : 2 <= n) (x : Fin n) :
    ring.leftNeighbor x ≠ x := by
  intro h
  have hv := congrArg Fin.val h
  change (x.val + n - 1) % n = x.val at hv
  rcases Nat.eq_zero_or_pos x.val with h0 | hpos
  · have h1 : (x.val + n - 1) % n = n - 1 := by
      rw [h0, Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1, h0] at hv
    omega
  · have h1 : (x.val + n - 1) % n = x.val - 1 := by
      rw [show x.val + n - 1 = (x.val - 1) + n by omega,
        Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1] at hv
    omega

def markedStatePotential {n : Nat}
    (E : Nat) (P : List Bool -> Bool)
    (s : MarkedWordState n) : Nat :=
  completionPotential E P s.bits

/-- The one-step identity. This is the load-bearing counting fact: the H and T
children split the binary-completion count, while all n-2 cold children keep
the current completion weight. -/
theorem stoppedMarkedPotential_child_sum {n : Nat}
    (hn3 : 3 <= n) (ring : DirectedRing n)
    (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool)
    (E : Nat) (P : List Bool -> Bool)
    (s : MarkedWordState n) :
    (List.ofFn (fun e : Fin n =>
      markedStatePotential E P
        (stoppedMarkedStep ring host stop s e))).sum =
      n * markedStatePotential E P s := by
  by_cases hs : s.stopped
  · calc
      (List.ofFn (fun e : Fin n =>
        markedStatePotential E P
          (stoppedMarkedStep ring host stop s e))).sum =
          (List.ofFn (fun _ : Fin n =>
            markedStatePotential E P s)).sum := by
            apply ofFn_sum_eq
            intro e
            simp [stoppedMarkedStep, hs, markedStatePotential]
      _ = n * markedStatePotential E P s :=
        ofFn_sum_const n _
  · by_cases hp : stop s.pre
    · calc
        (List.ofFn (fun e : Fin n =>
          markedStatePotential E P
            (stoppedMarkedStep ring host stop s e))).sum =
            (List.ofFn (fun _ : Fin n =>
              markedStatePotential E P s)).sum := by
              apply ofFn_sum_eq
              intro e
              simp [stoppedMarkedStep, hs, hp, markedStatePotential]
        _ = n * markedStatePotential E P s :=
          ofFn_sum_const n _
    · by_cases hfull : E <= s.bits.length
      · have hpoint : forall e : Fin n,
            markedStatePotential E P
                (stoppedMarkedStep ring host stop s e) =
              markedStatePotential E P s := by
          intro e
          cases hm : incidentBit ring (host s.pre) e with
          | none =>
              simp [stoppedMarkedStep, hs, hp, hm,
                markedStatePotential]
          | some b =>
              simp [stoppedMarkedStep, hs, hp, hm,
                markedStatePotential,
                completionPotential_append_of_full E P s.bits b hfull]
        calc
          (List.ofFn (fun e : Fin n =>
            markedStatePotential E P
              (stoppedMarkedStep ring host stop s e))).sum =
              (List.ofFn (fun _ : Fin n =>
                markedStatePotential E P s)).sum := by
                  apply ofFn_sum_eq
                  exact hpoint
          _ = n * markedStatePotential E P s :=
            ofFn_sum_const n _
      · have hshort : s.bits.length < E := by omega
        let a := ring.leftNeighbor (host s.pre)
        let b := host s.pre
        let f : Fin n -> Nat := fun e =>
          markedStatePotential E P
            (stoppedMarkedStep ring host stop s e)
        let c : Nat := markedStatePotential E P s
        have hab : a ≠ b := by
          dsimp [a, b]
          exact leftNeighbor_ne_self_marked ring (by omega) (host s.pre)
        have hba : b ≠ a := Ne.symm hab
        have ha :
            f a = completionPotential E P (s.bits ++ [true]) := by
          have hm :
              incidentBit ring (host s.pre) a = some true := by
            simp [a, incidentBit]
          simp [f, stoppedMarkedStep, hs, hp, hm,
            markedStatePotential]
        have hb :
            f b = completionPotential E P (s.bits ++ [false]) := by
          have hm :
              incidentBit ring (host s.pre) b = some false := by
            simp [a, b, incidentBit, hba]
          simp [f, stoppedMarkedStep, hs, hp, hm,
            markedStatePotential]
        have hother :
            forall e, e ≠ a -> e ≠ b -> f e = c := by
          intro e hea heb
          have hm :
              incidentBit ring (host s.pre) e = none := by
            simp [a, b, incidentBit, hea, heb]
          simp [f, c, stoppedMarkedStep, hs, hp, hm,
            markedStatePotential]
        have hpair : f a + f b = 2 * c := by
          rw [ha, hb]
          exact completionPotential_split E P s.bits hshort
        have hsum :=
          PredictableTwoTargetFiniteTree.ofFn_sum_two_values_else_const
            a b f c hab hother
        calc
          (List.ofFn (fun e : Fin n =>
            markedStatePotential E P
              (stoppedMarkedStep ring host stop s e))).sum =
              f a + f b + (n - 2) * c := by
                simpa [f] using hsum
          _ = 2 * c + (n - 2) * c := by rw [hpair]
          _ = n * c := by
            rw [← Nat.add_mul]
            congr 1
            omega
          _ = n * markedStatePotential E P s := rfl

def stoppedMarkedPotentialSum {n : Nat}
    (ring : DirectedRing n)
    (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool)
    (E T : Nat) (P : List Bool -> Bool) : Nat :=
  ((allSchedules n T).map (fun word =>
    markedStatePotential E P
      (stoppedMarkedRun ring host stop
        (stoppedMarkedStart n) word))).sum

private theorem sum_map_flatMap
    {A B : Type} (xs : List A) (ys : A -> List B)
    (f : B -> Nat) :
    ((xs.flatMap ys).map f).sum =
      (xs.map (fun x => ((ys x).map f).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem sum_map_mul_left
    {A : Type} (xs : List A) (c : Nat) (f : A -> Nat) :
    (xs.map (fun x => c * f x)).sum =
      c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.mul_add]

/-- Exact harmonic identity on the raw n-ary scheduler tree. -/
theorem stoppedMarkedPotential_exact {n : Nat}
    (hn3 : 3 <= n) (ring : DirectedRing n)
    (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool)
    (E T : Nat) (P : List Bool -> Bool) :
    stoppedMarkedPotentialSum ring host stop E T P =
      n ^ T * (allHTWords E).countP P := by
  induction T with
  | zero =>
      simp [stoppedMarkedPotentialSum, allSchedules,
        stoppedMarkedRun, stoppedMarkedStart, markedStatePotential,
        completionPotential, binaryCompletionCount]
  | succ T ih =>
      unfold stoppedMarkedPotentialSum at ih ⊢
      rw [allSchedules, sum_map_flatMap]
      have hinner :
          forall pre : DetSchedule n,
            ((List.ofFn (fun e : Fin n => pre ++ [e])).map
              (fun word =>
                markedStatePotential E P
                  (stoppedMarkedRun ring host stop
                    (stoppedMarkedStart n) word))).sum =
              n * markedStatePotential E P
                (stoppedMarkedRun ring host stop
                  (stoppedMarkedStart n) pre) := by
        intro pre
        rw [List.map_ofFn]
        calc
          (List.ofFn (fun e : Fin n =>
            markedStatePotential E P
              (stoppedMarkedRun ring host stop
                (stoppedMarkedStart n) (pre ++ [e])))).sum =
              (List.ofFn (fun e : Fin n =>
                markedStatePotential E P
                  (stoppedMarkedStep ring host stop
                    (stoppedMarkedRun ring host stop
                      (stoppedMarkedStart n) pre) e))).sum := by
                apply ofFn_sum_eq
                intro e
                rw [stoppedMarkedRun_append]
                rfl
          _ = n * markedStatePotential E P
                (stoppedMarkedRun ring host stop
                  (stoppedMarkedStart n) pre) :=
            stoppedMarkedPotential_child_sum hn3 ring host stop E P _
      calc
        ((allSchedules n T).map
          (fun pre =>
            ((List.ofFn (fun e : Fin n => pre ++ [e])).map
              (fun word =>
                markedStatePotential E P
                  (stoppedMarkedRun ring host stop
                    (stoppedMarkedStart n) word))).sum)).sum =
            ((allSchedules n T).map
              (fun pre =>
                n * markedStatePotential E P
                  (stoppedMarkedRun ring host stop
                    (stoppedMarkedStart n) pre))).sum := by
              apply congrArg List.sum
              apply List.map_congr_left
              intro pre _
              exact hinner pre
        _ = n * ((allSchedules n T).map
              (fun pre =>
                markedStatePotential E P
                  (stoppedMarkedRun ring host stop
                    (stoppedMarkedStart n) pre))).sum :=
          sum_map_mul_left _ n _
        _ = n * (n ^ T * (allHTWords E).countP P) := by
          rw [ih]
        _ = n ^ (T + 1) * (allHTWords E).countP P := by
          rw [Nat.pow_succ]
          ac_rfl

private theorem countP_mul_le_sum
    {A : Type} (xs : List A) (p : A -> Bool)
    (c : Nat) (f : A -> Nat)
    (h : forall x, x ∈ xs -> p x = true -> c <= f x) :
    xs.countP p * c <= (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have ht := ih (fun y hy hpy => h y (by simp [hy]) hpy)
      rw [List.countP_cons, List.map_cons, List.sum_cons]
      cases hp : p x with
      | false =>
          simp [hp] at *
          omega
      | true =>
          have hx := h x (by simp) hp
          simp [hp, Nat.succ_mul] at *
          omega

private theorem countP_mono_marked
    {A : Type} (xs : List A) (p q : A -> Bool)
    (hpq : forall x, p x = true -> q x = true) :
    xs.countP p <= xs.countP q := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.countP_cons, List.countP_cons]
      have htail := ih
      cases hp : p x with
      | false =>
          cases hq : q x <;> simp [hp, hq] <;> omega
      | true =>
          have hqx : q x = true := hpq x hp
          simp [hp, hqx]
          omega

/-- Exact event in the statement: the stop was never reached, at least E marks
were seen, and P holds on the first E marks. -/
def stoppedMarkedExactCount {n : Nat}
    (ring : DirectedRing n)
    (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool)
    (T E : Nat) (P : List Bool -> Bool) : Nat :=
  (allSchedules n T).countP (fun word =>
    let bits := stoppedEncounterBits ring host stop word
    decide
      (And (stopReached stop word = false)
        (And (E <= bits.length)
          (P (bits.take E) = true))))

/-- Padded event: the stopped marked stream has length at most E and P already
holds on it. This form needs extension monotonicity. -/
def stoppedMarkedPaddedCount {n : Nat}
    (ring : DirectedRing n)
    (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool)
    (T E : Nat) (P : List Bool -> Bool) : Nat :=
  (allSchedules n T).countP (fun word =>
    let bits := stoppedEncounterBits ring host stop word
    decide
      (And (bits.length <= E) (P bits = true)))

/-- Stopped marked-word transfer, exact-E form. -/
theorem stoppedMarkedWordTransfer {n : Nat}
    (hn3 : 3 <= n) (ring : DirectedRing n)
    (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool)
    (T E : Nat) (P : List Bool -> Bool) :
    stoppedMarkedExactCount ring host stop T E P * 2 ^ E <=
      n ^ T * (allHTWords E).countP P := by
  have hdom :
      stoppedMarkedExactCount ring host stop T E P * 2 ^ E <=
        stoppedMarkedPotentialSum ring host stop E T P := by
    unfold stoppedMarkedExactCount stoppedMarkedPotentialSum
    apply countP_mul_le_sum
    intro word _ hgood
    dsimp only at hgood
    have hg :
        And (stopReached stop word = false)
          (And
            (E <= (stoppedEncounterBits ring host stop word).length)
            (P ((stoppedEncounterBits ring host stop word).take E) =
              true)) :=
      of_decide_eq_true hgood
    have hbits :=
      stoppedMarkedRun_start_bits ring host stop word
    have hp :=
      completionPotential_eq_twoPow_of_full E P
        (stoppedEncounterBits ring host stop word) hg.2.1 hg.2.2
    change
      2 ^ E <=
        markedStatePotential E P
          (stoppedMarkedRun ring host stop
            (stoppedMarkedStart n) word)
    unfold markedStatePotential
    rw [hbits, hp]
    exact Nat.le_refl _
  exact Nat.le_trans hdom
    (Nat.le_of_eq (stoppedMarkedPotential_exact hn3 ring host stop E T P))

/-- Stopped marked-word transfer, padded form. -/
theorem stoppedMarkedWordTransfer_padded {n : Nat}
    (hn3 : 3 <= n) (ring : DirectedRing n)
    (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool)
    (T E : Nat) (P : List Bool -> Bool)
    (hmono : ExtensionMonotone P) :
    stoppedMarkedPaddedCount ring host stop T E P * 2 ^ E <=
      n ^ T * (allHTWords E).countP P := by
  have hdom :
      stoppedMarkedPaddedCount ring host stop T E P * 2 ^ E <=
        stoppedMarkedPotentialSum ring host stop E T P := by
    unfold stoppedMarkedPaddedCount stoppedMarkedPotentialSum
    apply countP_mul_le_sum
    intro word _ hgood
    dsimp only at hgood
    have hg :
        And ((stoppedEncounterBits ring host stop word).length <= E)
          (P (stoppedEncounterBits ring host stop word) = true) :=
      of_decide_eq_true hgood
    have hbits :=
      stoppedMarkedRun_start_bits ring host stop word
    have hp :=
      completionPotential_eq_twoPow_of_padded E P hmono
        (stoppedEncounterBits ring host stop word) hg.1 hg.2
    change
      2 ^ E <=
        markedStatePotential E P
          (stoppedMarkedRun ring host stop
            (stoppedMarkedStart n) word)
    unfold markedStatePotential
    rw [hbits, hp]
    exact Nat.le_refl _
  exact Nat.le_trans hdom
    (Nat.le_of_eq (stoppedMarkedPotential_exact hn3 ring host stop E T P))

/-- First StoppedClockInterfaces consumer: the lower lottery event on the first
E encounter bits is bounded by the exact binary at-most count. -/
theorem stoppedEncounterLotteryAtMost_transfer {n : Nat}
    (hn3 : 3 <= n) (k h : Nat) (ring : DirectedRing n)
    (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool)
    (T E M : Nat) :
    stoppedLotteryLowerFailureCount
          k h ring host stop T E M * 2 ^ E <=
      n ^ T * lotteryAtMostWordCount k h E M := by
  have htransfer :=
    stoppedMarkedWordTransfer hn3 ring host stop T E
      (fun bits =>
        decide ((lotteryRun k (lotteryOffset h) bits).wins <= M))
  simpa [stoppedMarkedExactCount, stoppedLotteryLowerFailureCount,
    lotteryAtMostWordCount, lotteryPredWordCount,
    decide_eq_true_eq] using htransfer

private theorem lotteryRun_append
    (k : Nat) (s : LotteryState) (u v : List Bool) :
    lotteryRun k s (u ++ v) =
      lotteryRun k (lotteryRun k s u) v := by
  induction u generalizing s with
  | nil => rfl
  | cons b u ih =>
      simp only [List.cons_append, lotteryRun]
      exact ih (lotteryStep k s b)

private theorem lotteryStep_wins_le
    (k : Nat) (s : LotteryState) (b : Bool) :
    s.wins <= (lotteryStep k s b).wins := by
  cases b with
  | false => simp [lotteryStep]
  | true =>
      simp only [lotteryStep, if_true]
      split <;> simp_all <;> omega

private theorem lotteryRun_wins_ge_start
    (k : Nat) (s : LotteryState) (word : List Bool) :
    s.wins <= (lotteryRun k s word).wins := by
  induction word generalizing s with
  | nil => exact Nat.le_refl _
  | cons b word ih =>
      exact Nat.le_trans (lotteryStep_wins_le k s b)
        (ih (lotteryStep k s b))

private theorem lotteryAtLeast_extensionMonotone
    (k h M : Nat) :
    ExtensionMonotone
      (fun bits =>
        decide (M <= (lotteryRun k (lotteryOffset h) bits).wins)) := by
  intro u v hu
  have hu' :
      M <= (lotteryRun k (lotteryOffset h) u).wins :=
    of_decide_eq_true hu
  have htail :=
    lotteryRun_wins_ge_start k
      (lotteryRun k (lotteryOffset h) u) v
  change decide
    (M <= (lotteryRun k (lotteryOffset h) (u ++ v)).wins) = true
  rw [lotteryRun_append]
  exact decide_eq_true (Nat.le_trans hu' htail)

/-- Second StoppedClockInterfaces consumer: an upper event already true on a
stopped prefix can be padded to E binary letters without losing the event. -/
theorem stoppedEncounterLotteryAtLeast_padded_transfer {n : Nat}
    (hn3 : 3 <= n) (k h : Nat) (ring : DirectedRing n)
    (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool)
    (T E M : Nat) :
    stoppedMarkedPaddedCount ring host stop T E
          (fun bits =>
            decide (M <=
              (lotteryRun k (lotteryOffset h) bits).wins)) *
        2 ^ E <=
      n ^ T * lotteryAtLeastWordCount k h E M := by
  have htransfer :=
    stoppedMarkedWordTransfer_padded hn3 ring host stop T E
      (fun bits =>
        decide (M <=
          (lotteryRun k (lotteryOffset h) bits).wins))
      (lotteryAtLeast_extensionMonotone k h M)
  simpa [lotteryAtLeastWordCount, lotteryPredWordCount] using htransfer

/-- Direct first-leader specialization used by EarlyLeaderStopBounds. -/
theorem firstLeaderStopLotteryAtMost_transfer
    {n psi kappa : Nat}
    (hn3 : 3 <= n) (h : Nat) (ring : DirectedRing n)
    (C0 : PPLConfig n psi kappa)
    (host : List (Fin n) -> Fin n)
    (T E M : Nat) :
    stoppedLotteryLowerFailureCount
          psi h ring host (firstLeaderStop ring C0) T E M *
        2 ^ E <=
      n ^ T * lotteryAtMostWordCount psi h E M :=
  stoppedEncounterLotteryAtMost_transfer
    hn3 psi h ring host (firstLeaderStop ring C0) T E M

/-- The binary L8 bound now composes directly with the stopped marked transfer.
This is the lottery half at the frozen L8 parameters. -/
theorem firstLeaderStopLotteryL8_tail
    {n psi kappa : Nat}
    (hn3 : 3 <= n) (hpsi : 1 <= psi) (c : Nat) (hc : 1 <= c)
    (ring : DirectedRing n) (C0 : PPLConfig n psi kappa)
    (host : List (Fin n) -> Fin n) (T : Nat) :
    2 ^ (c * psi) *
        stoppedLotteryLowerFailureCount
          psi 0 ring host (firstLeaderStop ring C0) T
            (lotteryL8Horizon psi c) (lotteryTarget psi c) <=
      n ^ T := by
  let E := lotteryL8Horizon psi c
  let M := lotteryTarget psi c
  let A :=
    stoppedLotteryLowerFailureCount
      psi 0 ring host (firstLeaderStop ring C0) T E M
  let B := lotteryAtMostWordCount psi 0 E M
  have ht : A * 2 ^ E <= n ^ T * B := by
    dsimp [A, B, E, M]
    exact firstLeaderStopLotteryAtMost_transfer
      hn3 0 ring C0 host T
        (lotteryL8Horizon psi c) (lotteryTarget psi c)
  have hb : 2 ^ (c * psi) * B <= 2 ^ E := by
    dsimp [B, E, M]
    exact (PPL.Probability.lotteryCountBounds psi c hpsi hc).2
  have h1 := Nat.mul_le_mul_left (2 ^ (c * psi)) ht
  have h2 := Nat.mul_le_mul_left (n ^ T) hb
  have hscaled :
      (2 ^ (c * psi) * A) * 2 ^ E <=
        n ^ T * 2 ^ E := by
    calc
      (2 ^ (c * psi) * A) * 2 ^ E =
          2 ^ (c * psi) * (A * 2 ^ E) := by ac_rfl
      _ <= 2 ^ (c * psi) * (n ^ T * B) := h1
      _ = n ^ T * (2 ^ (c * psi) * B) := by ac_rfl
      _ <= n ^ T * 2 ^ E := h2
  exact Nat.le_of_mul_le_mul_right hscaled
    (Nat.pow_pos (by decide : 0 < 2))

end PPL.Probability

#print axioms PPL.Probability.binaryCompletionCount_succ
#print axioms PPL.Probability.stoppedMarkedRun_append
#print axioms PPL.Probability.stoppedMarkedRun_start_bits
#print axioms PPL.Probability.stoppedMarkedPotential_child_sum
#print axioms PPL.Probability.stoppedMarkedPotential_exact
#print axioms PPL.Probability.stoppedMarkedWordTransfer
#print axioms PPL.Probability.stoppedMarkedWordTransfer_padded
#print axioms PPL.Probability.stoppedEncounterLotteryAtMost_transfer
#print axioms PPL.Probability.stoppedEncounterLotteryAtLeast_padded_transfer
#print axioms PPL.Probability.firstLeaderStopLotteryAtMost_transfer
#print axioms PPL.Probability.firstLeaderStopLotteryL8_tail
