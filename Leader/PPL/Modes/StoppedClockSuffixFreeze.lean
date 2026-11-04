import Leader.PPL.Modes.StoppedClockSuffixCorrected
import Leader.PPL.Modes.EarlyLeaderStop
import Leader.PPL.Probability.MarkedWordTransfer

namespace PPL.Probability

set_option autoImplicit false
set_option Elab.async false

open FiniteUniformStoppingTree

private theorem leftNeighbor_ne_self_freeze
    {n : Nat} (ring : DirectedRing n) (hn2 : 2 ≤ n) (x : Fin n) :
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

private theorem leftNeighbor_rightNeighbor_freeze
    {n : Nat} (ring : DirectedRing n) (i : Fin n) :
    ring.leftNeighbor (ring.rightNeighbor i) = i := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hi : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hi]
    have heq : i.val + 1 + n - 1 = n + i.val := by omega
    rw [heq]
    simp [Nat.add_mod, Nat.mod_eq_of_lt i.isLt]
  · have hie : i.val + 1 = n := by omega
    rw [hie, Nat.mod_self]
    have hlt : n - 1 < n := by omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    omega

private theorem rightNeighbor_leftNeighbor_freeze
    {n : Nat} (ring : DirectedRing n) (i : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor i) = i := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hi : i.val = 0
  · rw [hi]
    have hlt : n - 1 < n := by omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    have hs : n - 1 + 1 = n := by omega
    rw [hs, Nat.mod_self]
  · have heq : i.val + n - 1 = n + (i.val - 1) := by omega
    have hlt : i.val - 1 < n := by omega
    have hleft : (i.val + n - 1) % n = i.val - 1 := by
      rw [heq]
      simp [Nat.add_mod, Nat.mod_eq_of_lt hlt]
    rw [hleft]
    have hs : i.val - 1 + 1 = i.val := by omega
    rw [hs, Nat.mod_eq_of_lt i.isLt]

private theorem reset_edge_incident_freeze
    {n psi kappa : Nat} (ring : DirectedRing n)
    (C : PPLConfig n psi kappa) (x e : Fin n)
    (hreset : clockResetAt ring C x e = true) :
    incidentBit ring x e ≠ none := by
  have hp := of_decide_eq_true hreset
  unfold clockResetAt at hp
  have hp' : (x = e ∨ x = ring.rightNeighbor e) := hp.1
  rcases hp' with hx | hx
  · subst x
    unfold incidentBit
    split <;> simp
  · have he : e = ring.leftNeighbor x := by
      have hh := congrArg ring.leftNeighbor hx
      rw [leftNeighbor_rightNeighbor_freeze] at hh
      exact hh.symm
    simp [incidentBit, he]

private theorem take_append_singleton_of_le_freeze
    {A : Type} (E : Nat) (xs : List A) (a : A)
    (hE : E ≤ xs.length) :
    (xs ++ [a]).take E = xs.take E := by
  rw [List.take_append]
  have hz : E - xs.length = 0 := Nat.sub_eq_zero_of_le hE
  rw [hz]
  simp

private theorem completionPotential_append_of_full_freeze
    (E : Nat) (P : List Bool → Bool) (bits : List Bool) (b : Bool)
    (hE : E ≤ bits.length) :
    completionPotential E P (bits ++ [b]) = completionPotential E P bits := by
  unfold completionPotential
  rw [take_append_singleton_of_le_freeze E bits b hE]

private theorem completionPotential_split_freeze
    (E : Nat) (P : List Bool → Bool) (bits : List Bool)
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
  have hr : E - bits.length = (E - (bits.length + 1)) + 1 := by omega
  have hrec :
      binaryCompletionCount P bits (E - bits.length) =
        binaryCompletionCount P (bits ++ [false]) (E - (bits.length + 1)) +
          binaryCompletionCount P (bits ++ [true]) (E - (bits.length + 1)) := by
    rw [hr]
    exact binaryCompletionCount_succ P bits (E - (bits.length + 1))
  unfold completionPotential
  rw [htake, htakeH, htakeT]
  simp only [List.length_append, List.length_singleton]
  rw [show E - (bits.length + 1) = E - (bits.length + 1) by rfl]
  rw [hrec, Nat.pow_succ]
  simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  ac_rfl

private theorem binaryCompletionCount_all_of_mono_freeze
    (P : List Bool → Bool) (hmono : ExtensionMonotone P)
    (pre : List Bool) (r : Nat) (hp : P pre = true) :
    binaryCompletionCount P pre r = 2 ^ r := by
  unfold binaryCompletionCount
  rw [List.countP_eq_length.mpr, allHTWords_length]
  intro tail _
  exact hmono pre tail hp

private theorem completionPotential_eq_twoPow_of_padded_freeze
    (E : Nat) (P : List Bool → Bool) (hmono : ExtensionMonotone P)
    (bits : List Bool) (hE : bits.length ≤ E) (hp : P bits = true) :
    completionPotential E P bits = 2 ^ E := by
  have htake : bits.take E = bits := List.take_of_length_le hE
  dsimp only [completionPotential]
  rw [htake, binaryCompletionCount_all_of_mono_freeze
    P hmono bits (E - bits.length) hp]
  rw [← Nat.pow_add]
  congr 1
  omega

private theorem completionPotential_eq_twoPow_of_full_freeze
    (E : Nat) (P : List Bool → Bool) (bits : List Bool)
    (hE : E ≤ bits.length) (hp : P (bits.take E) = true) :
    completionPotential E P bits = 2 ^ E := by
  have hlen : (bits.take E).length = E := by
    rw [List.length_take]
    omega
  dsimp only [completionPotential]
  rw [hlen]
  simp [binaryCompletionCount, allHTWords, hp]

private theorem lotteryRun_append_freeze
    (k : Nat) (s : LotteryState) (u v : List Bool) :
    lotteryRun k s (u ++ v) = lotteryRun k (lotteryRun k s u) v := by
  induction u generalizing s with
  | nil => rfl
  | cons b u ih =>
      simp only [List.cons_append, lotteryRun]
      exact ih (lotteryStep k s b)

private theorem lotteryStep_wins_le_freeze
    (k : Nat) (s : LotteryState) (b : Bool) :
    s.wins ≤ (lotteryStep k s b).wins := by
  cases b with
  | false => simp [lotteryStep]
  | true =>
      simp only [lotteryStep, if_true]
      split <;> simp_all <;> omega

private theorem lotteryRun_wins_ge_start_freeze
    (k : Nat) (s : LotteryState) (word : List Bool) :
    s.wins ≤ (lotteryRun k s word).wins := by
  induction word generalizing s with
  | nil => exact Nat.le_refl _
  | cons b word ih =>
      exact Nat.le_trans (lotteryStep_wins_le_freeze k s b)
        (ih (lotteryStep k s b))

private theorem lotteryAtLeast_extensionMonotone_freeze
    (k h M : Nat) :
    ExtensionMonotone
      (fun bits => decide (M ≤ (lotteryRun k (lotteryOffset h) bits).wins)) := by
  intro u v hu
  have hu' : M ≤ (lotteryRun k (lotteryOffset h) u).wins := of_decide_eq_true hu
  have htail := lotteryRun_wins_ge_start_freeze k
    (lotteryRun k (lotteryOffset h) u) v
  change decide (M ≤ (lotteryRun k (lotteryOffset h) (u ++ v)).wins) = true
  rw [lotteryRun_append_freeze]
  exact decide_eq_true (Nat.le_trans hu' htail)

private structure StoppedClockFreezeState (n psi kappa : Nat) where
  config : PPLConfig n psi kappa
  bits : List Bool
  frozen : Bool

private def stoppedClockFreezeStart {n psi kappa : Nat}
    (C : PPLConfig n psi kappa) : StoppedClockFreezeState n psi kappa :=
  ⟨C, [], false⟩

private def stoppedClockFreezeStep {n psi kappa : Nat}
    (ring : DirectedRing n) (x : Fin n) :
    StoppedClockFreezeState n psi kappa → Fin n → StoppedClockFreezeState n psi kappa
  | s, e =>
      let C' := pplStep ring s.config e
      if s.frozen then
        ⟨C', s.bits, true⟩
      else if clockResetAt ring s.config x e then
        ⟨C', s.bits, true⟩
      else
        match incidentBit ring x e with
        | none => ⟨C', s.bits, false⟩
        | some b => ⟨C', s.bits ++ [b], false⟩

private def stoppedClockFreezeRun {n psi kappa : Nat}
    (ring : DirectedRing n) (x : Fin n) :
    StoppedClockFreezeState n psi kappa → DetSchedule n → StoppedClockFreezeState n psi kappa
  | s, [] => s
  | s, e :: rest =>
      stoppedClockFreezeRun ring x (stoppedClockFreezeStep ring x s e) rest

private theorem stoppedClockFreezeRun_append {n psi kappa : Nat}
    (ring : DirectedRing n) (x : Fin n)
    (s : StoppedClockFreezeState n psi kappa) (u v : DetSchedule n) :
    stoppedClockFreezeRun ring x s (u ++ v) =
      stoppedClockFreezeRun ring x (stoppedClockFreezeRun ring x s u) v := by
  induction u generalizing s with
  | nil => rfl
  | cons e u ih =>
      simp only [List.cons_append, stoppedClockFreezeRun]
      exact ih (stoppedClockFreezeStep ring x s e)

private def stoppedClockFreezePotential
    {n psi kappa : Nat} (E : Nat) (P : List Bool → Bool)
    (s : StoppedClockFreezeState n psi kappa) : Nat :=
  if s.frozen then
    if s.bits.length ≤ E ∧ P s.bits = true then 2 ^ E else 0
  else completionPotential E P s.bits

private theorem stoppedClockFreezeRun_bitsAux
    {n psi kappa : Nat} (ring : DirectedRing n) (x : Fin n)
    (s : StoppedClockFreezeState n psi kappa) (word : DetSchedule n) :
    (stoppedClockFreezeRun ring x s word).bits =
      if s.frozen then s.bits
      else s.bits ++ clockSuffixBitsAux ring x s.config word := by
  induction word generalizing s with
  | nil =>
      cases hs : s.frozen <;>
        simp [stoppedClockFreezeRun, clockSuffixBitsAux, hs]
  | cons e rest ih =>
      cases hs : s.frozen with
      | true =>
          simp [stoppedClockFreezeRun, stoppedClockFreezeStep, hs, ih]
      | false =>
          cases hr : clockResetAt ring s.config x e with
          | true =>
              simp [stoppedClockFreezeRun, stoppedClockFreezeStep,
                clockSuffixBitsAux, hs, hr, ih]
          | false =>
              cases hm : incidentBit ring x e with
              | none =>
                  simp [stoppedClockFreezeRun, stoppedClockFreezeStep,
                    clockSuffixBitsAux, hs, hr, hm, ih]
              | some b =>
                  simp [stoppedClockFreezeRun, stoppedClockFreezeStep,
                    clockSuffixBitsAux, hs, hr, hm, ih, List.append_assoc]

private theorem stoppedClockFreezeRun_start_bits
    {n psi kappa : Nat} (ring : DirectedRing n)
    (C : PPLConfig n psi kappa) (x : Fin n) (word : DetSchedule n) :
    (stoppedClockFreezeRun ring x (stoppedClockFreezeStart C) word).bits =
      clockSuffixBits ring C x word := by
  simpa [stoppedClockFreezeStart, clockSuffixBits] using
    (stoppedClockFreezeRun_bitsAux ring x (stoppedClockFreezeStart C) word)

private def clockFreezeOrdinaryBits
    {n : Nat} (ring : DirectedRing n) (x : Fin n)
    (bits : List Bool) (e : Fin n) : List Bool :=
  match incidentBit ring x e with
  | none => bits
  | some b => bits ++ [b]

private theorem terminalPotential_le_ordinaryChild
    {n : Nat} (hn2 : 2 ≤ n) (ring : DirectedRing n) (x : Fin n)
    (E : Nat) (P : List Bool → Bool) (hmono : ExtensionMonotone P)
    (bits : List Bool) (e : Fin n) :
    (if bits.length ≤ E ∧ P bits = true then 2 ^ E else 0) ≤
      completionPotential E P (clockFreezeOrdinaryBits ring x bits e) := by
  by_cases hev : bits.length ≤ E ∧ P bits = true
  · rcases hev with ⟨hlen, hp⟩
    have hweight :
        (if bits.length ≤ E ∧ P bits = true then 2 ^ E else 0) = 2 ^ E := by
      simp [hlen, hp]
    by_cases hfull : E ≤ bits.length
    · have heq : bits.length = E := Nat.le_antisymm hlen hfull
      have htake : bits.take E = bits :=
        List.take_of_length_le hlen
      have hpref : P (bits.take E) = true := by simpa [htake] using hp
      have hparent := completionPotential_eq_twoPow_of_full_freeze
        E P bits hfull hpref
      cases hm : incidentBit ring x e with
      | none =>
          rw [hweight]
          simpa [clockFreezeOrdinaryBits, hm, hparent]
      | some b =>
          have happ := completionPotential_append_of_full_freeze
            E P bits b hfull
          rw [hweight]
          simpa [clockFreezeOrdinaryBits, hm, happ, hparent]
    · have hshort : bits.length < E := by omega
      cases hm : incidentBit ring x e with
      | none =>
          have hparent := completionPotential_eq_twoPow_of_padded_freeze
            E P hmono bits (Nat.le_of_lt hshort) hp
          rw [hweight]
          simpa [clockFreezeOrdinaryBits, hm, hparent]
      | some b =>
          have hp' : P (bits ++ [b]) = true := by
            exact hmono bits [b] hp
          have hlen' : (bits ++ [b]).length ≤ E := by simp; omega
          have happ := completionPotential_eq_twoPow_of_padded_freeze
            E P hmono (bits ++ [b]) hlen' hp'
          rw [hweight]
          simpa [clockFreezeOrdinaryBits, hm, happ]
  · simp only [if_neg hev]
    exact Nat.zero_le _

private theorem stoppedClockFreezePotential_step_le_ordinary
    {n psi kappa : Nat} (hn2 : 2 ≤ n) (ring : DirectedRing n)
    (x : Fin n) (E : Nat) (P : List Bool → Bool)
    (hmono : ExtensionMonotone P)
    (s : StoppedClockFreezeState n psi kappa) (e : Fin n) :
    stoppedClockFreezePotential E P (stoppedClockFreezeStep ring x s e) ≤
      completionPotential E P (clockFreezeOrdinaryBits ring x s.bits e) := by
  cases hs : s.frozen with
  | true =>
      have ht := terminalPotential_le_ordinaryChild
        hn2 ring x E P hmono s.bits e
      simpa [stoppedClockFreezeStep, stoppedClockFreezePotential, hs] using ht
  | false =>
      cases hr : clockResetAt ring s.config x e with
      | true =>
          have hinc := reset_edge_incident_freeze ring s.config x e hr
          have ht := terminalPotential_le_ordinaryChild
            hn2 ring x E P hmono s.bits e
          simpa [stoppedClockFreezeStep, stoppedClockFreezePotential,
            hs, hr] using ht
      | false =>
          cases hm : incidentBit ring x e with
          | none =>
              simp [stoppedClockFreezeStep, stoppedClockFreezePotential,
                clockFreezeOrdinaryBits, hs, hr, hm]
          | some b =>
              simp [stoppedClockFreezeStep, stoppedClockFreezePotential,
                clockFreezeOrdinaryBits, hs, hr, hm]

private theorem clockFreezeOrdinaryChild_sum
    {n : Nat} (hn2 : 2 ≤ n) (ring : DirectedRing n) (x : Fin n)
    (E : Nat) (P : List Bool → Bool) (bits : List Bool) :
    (List.ofFn (fun e : Fin n =>
      completionPotential E P (clockFreezeOrdinaryBits ring x bits e))).sum =
        n * completionPotential E P bits := by
  by_cases hfull : E ≤ bits.length
  · have hpoint : ∀ e : Fin n,
        completionPotential E P (clockFreezeOrdinaryBits ring x bits e) =
          completionPotential E P bits := by
      intro e
      cases hm : incidentBit ring x e with
      | none => simp [clockFreezeOrdinaryBits, hm]
      | some b =>
          simp [clockFreezeOrdinaryBits, hm,
            completionPotential_append_of_full_freeze E P bits b hfull]
    calc
      (List.ofFn (fun e : Fin n =>
        completionPotential E P (clockFreezeOrdinaryBits ring x bits e))).sum =
          (List.ofFn (fun _ : Fin n => completionPotential E P bits)).sum := by
            apply ofFn_sum_eq
            exact hpoint
      _ = n * completionPotential E P bits := ofFn_sum_const n _
  · have hshort : bits.length < E := by omega
    let a := ring.leftNeighbor x
    let b := x
    let f : Fin n → Nat := fun e =>
      completionPotential E P (clockFreezeOrdinaryBits ring x bits e)
    let c : Nat := completionPotential E P bits
    have hab : a ≠ b := by
      dsimp [a, b]
      exact leftNeighbor_ne_self_freeze ring hn2 x
    have hba : b ≠ a := Ne.symm hab
    have ha : f a = completionPotential E P (bits ++ [true]) := by
      have hm : incidentBit ring x a = some true := by simp [a, incidentBit]
      simp [f, clockFreezeOrdinaryBits, hm]
    have hb : f b = completionPotential E P (bits ++ [false]) := by
      have hm : incidentBit ring x b = some false := by
        simp [a, b, incidentBit, hba]
      simp [f, clockFreezeOrdinaryBits, hm]
    have hother : ∀ e, e ≠ a → e ≠ b → f e = c := by
      intro e hea heb
      have hm : incidentBit ring x e = none := by
        simp [a, b, incidentBit, hea, heb]
      simp [f, c, clockFreezeOrdinaryBits, hm]
    have hpair : f a + f b = 2 * c := by
      rw [ha, hb]
      exact completionPotential_split_freeze E P bits hshort
    have hsum :=
      PredictableTwoTargetFiniteTree.ofFn_sum_two_values_else_const
        a b f c hab hother
    calc
      (List.ofFn (fun e : Fin n =>
        completionPotential E P (clockFreezeOrdinaryBits ring x bits e))).sum =
          f a + f b + (n - 2) * c := by simpa [f] using hsum
      _ = 2 * c + (n - 2) * c := by rw [hpair]
      _ = n * c := by
        rw [← Nat.add_mul]
        congr 1
        omega
      _ = n * completionPotential E P bits := rfl

private theorem ofFn_sum_le_ofFn_sum_freeze
    {A : Type} (f g : A → Nat) (xs : List A)
    (hfg : ∀ x, x ∈ xs → f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := hfg x (by simp)
      have ht := ih (fun y hy => hfg y (by simp [hy]))
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add hx ht

private theorem stoppedClockFreezePotential_child_sum_le
    {n psi kappa : Nat} (hn2 : 2 ≤ n) (ring : DirectedRing n)
    (x : Fin n) (E : Nat) (P : List Bool → Bool)
    (hmono : ExtensionMonotone P)
    (s : StoppedClockFreezeState n psi kappa) :
    (List.ofFn (fun e : Fin n =>
      stoppedClockFreezePotential E P
        (stoppedClockFreezeStep ring x s e))).sum ≤
      n * stoppedClockFreezePotential E P s := by
  cases hs : s.frozen with
  | true =>
      have hpoint : ∀ e : Fin n,
          stoppedClockFreezePotential E P (stoppedClockFreezeStep ring x s e) =
            stoppedClockFreezePotential E P s := by
        intro e
        simp [stoppedClockFreezeStep, stoppedClockFreezePotential, hs]
      calc
        (List.ofFn (fun e : Fin n =>
          stoppedClockFreezePotential E P
            (stoppedClockFreezeStep ring x s e))).sum =
            (List.ofFn (fun _ : Fin n =>
              stoppedClockFreezePotential E P s)).sum := by
                apply ofFn_sum_eq
                exact hpoint
        _ = n * stoppedClockFreezePotential E P s := ofFn_sum_const n _
        _ ≤ n * stoppedClockFreezePotential E P s := Nat.le_refl _
  | false =>
      have hdom :
          (List.ofFn (fun e : Fin n =>
            stoppedClockFreezePotential E P
              (stoppedClockFreezeStep ring x s e))).sum ≤
            (List.ofFn (fun e : Fin n =>
              completionPotential E P
                (clockFreezeOrdinaryBits ring x s.bits e))).sum := by
        apply FiniteUniformStoppingTree.ofFn_sum_le
        intro e
        exact stoppedClockFreezePotential_step_le_ordinary
          hn2 ring x E P hmono s e
      have hsum := clockFreezeOrdinaryChild_sum hn2 ring x E P s.bits
      simpa [stoppedClockFreezePotential, hs] using
        Nat.le_trans hdom (Nat.le_of_eq hsum)

private theorem sum_map_flatMap_freeze
    {A B : Type} (xs : List A) (ys : A → List B) (f : B → Nat) :
    ((xs.flatMap ys).map f).sum =
      (xs.map (fun x => ((ys x).map f).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem sum_map_mul_left_freeze
    {A : Type} (xs : List A) (c : Nat) (f : A → Nat) :
    (xs.map (fun x => c * f x)).sum = c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.mul_add]

private def stoppedClockFreezePotentialSum
    {n psi kappa : Nat} (ring : DirectedRing n) (x : Fin n)
    (C : PPLConfig n psi kappa) (E T : Nat) (P : List Bool → Bool) : Nat :=
  ((allSchedules n T).map (fun word =>
    stoppedClockFreezePotential E P
      (stoppedClockFreezeRun ring x (stoppedClockFreezeStart C) word))).sum

private theorem stoppedClockFreezePotentialSum_le
    {n psi kappa : Nat} (hn2 : 2 ≤ n) (ring : DirectedRing n)
    (x : Fin n) (C : PPLConfig n psi kappa) (E T : Nat)
    (P : List Bool → Bool) (hmono : ExtensionMonotone P) :
    stoppedClockFreezePotentialSum ring x C E T P ≤
      n ^ T * (allHTWords E).countP P := by
  induction T with
  | zero =>
      simp [stoppedClockFreezePotentialSum, allSchedules,
        stoppedClockFreezeRun, stoppedClockFreezeStart,
        stoppedClockFreezePotential, completionPotential,
        binaryCompletionCount]
  | succ T ih =>
      unfold stoppedClockFreezePotentialSum at ih ⊢
      rw [allSchedules, sum_map_flatMap_freeze]
      have hinner : ∀ pre : DetSchedule n,
          ((List.ofFn (fun e : Fin n =>
            pre ++ [e])).map (fun word =>
              stoppedClockFreezePotential E P
                (stoppedClockFreezeRun ring x
                  (stoppedClockFreezeStart C) word))).sum ≤
          n * stoppedClockFreezePotential E P
            (stoppedClockFreezeRun ring x
              (stoppedClockFreezeStart C) pre) := by
        intro pre
        rw [List.map_ofFn]
        calc
          (List.ofFn (fun e : Fin n =>
            stoppedClockFreezePotential E P
              (stoppedClockFreezeRun ring x
                (stoppedClockFreezeStart C) (pre ++ [e])))).sum ≤
              (List.ofFn (fun e : Fin n =>
                stoppedClockFreezePotential E P
                  (stoppedClockFreezeStep ring x
                    (stoppedClockFreezeRun ring x
                      (stoppedClockFreezeStart C) pre) e))).sum := by
                apply FiniteUniformStoppingTree.ofFn_sum_le
                intro e
                rw [stoppedClockFreezeRun_append]
                simp [stoppedClockFreezeRun]
          _ ≤ n * stoppedClockFreezePotential E P
                (stoppedClockFreezeRun ring x
                  (stoppedClockFreezeStart C) pre) :=
            stoppedClockFreezePotential_child_sum_le
              hn2 ring x E P hmono _
      calc
        ((allSchedules n T).map (fun pre =>
          ((List.ofFn (fun e : Fin n => pre ++ [e])).map (fun word =>
            stoppedClockFreezePotential E P
              (stoppedClockFreezeRun ring x
                (stoppedClockFreezeStart C) word))).sum)).sum ≤
            ((allSchedules n T).map (fun pre =>
              n * stoppedClockFreezePotential E P
                (stoppedClockFreezeRun ring x
                  (stoppedClockFreezeStart C) pre))).sum := by
          apply ofFn_sum_le_ofFn_sum_freeze
          intro pre _
          exact hinner pre
        _ = n * ((allSchedules n T).map (fun pre =>
              stoppedClockFreezePotential E P
                (stoppedClockFreezeRun ring x
                  (stoppedClockFreezeStart C) pre))).sum :=
          sum_map_mul_left_freeze _ n _
        _ ≤ n * (n ^ T * (allHTWords E).countP P) :=
          Nat.mul_le_mul_left n ih
        _ = n ^ (T + 1) * (allHTWords E).countP P := by
          rw [Nat.pow_succ]
          ac_rfl

private theorem countP_mul_le_sum_freeze
    {A : Type} (xs : List A) (p : A → Bool) (c : Nat) (f : A → Nat)
    (h : ∀ x, x ∈ xs → p x = true → c ≤ f x) :
    xs.countP p * c ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have ht := ih (fun y hy hpy => h y (by simp [hy]) hpy)
      rw [List.countP_cons, List.map_cons, List.sum_cons]
      cases hp : p x with
      | false => simp [hp] at *; omega
      | true =>
          have hx := h x (by simp) hp
          simp [hp, Nat.succ_mul] at *
          omega

private theorem stoppedClockFreezePotential_eq_twoPow_of_event
    {n psi kappa : Nat} (E : Nat) (P : List Bool → Bool)
    (hmono : ExtensionMonotone P)
    (s : StoppedClockFreezeState n psi kappa)
    (hlen : s.bits.length ≤ E) (hp : P s.bits = true) :
    stoppedClockFreezePotential E P s = 2 ^ E := by
  cases hs : s.frozen with
  | true => simp [stoppedClockFreezePotential, hs, hlen, hp]
  | false =>
      simpa [stoppedClockFreezePotential, hs] using
        (completionPotential_eq_twoPow_of_padded_freeze
          E P hmono s.bits hlen hp)

private theorem stoppedClockSuffixFreezeTransfer_generic
    {n psi kappa : Nat} (hn2 : 2 ≤ n) (ring : DirectedRing n)
    (C : PPLConfig n psi kappa) (x : Fin n) (T E : Nat)
    (P : List Bool → Bool) (hmono : ExtensionMonotone P) :
    (allSchedules n T).countP (fun word =>
      let bits := clockSuffixBits ring C x word
      decide (bits.length ≤ E ∧ P bits = true)) * 2 ^ E ≤
      n ^ T * (allHTWords E).countP P := by
  have hdom :
      (allSchedules n T).countP (fun word =>
        let bits := clockSuffixBits ring C x word
        decide (bits.length ≤ E ∧ P bits = true)) * 2 ^ E ≤
      stoppedClockFreezePotentialSum ring x C E T P := by
    unfold stoppedClockFreezePotentialSum
    apply countP_mul_le_sum_freeze
    intro word _ hgood
    dsimp only at hgood
    have hg := of_decide_eq_true hgood
    have hbits := stoppedClockFreezeRun_start_bits ring C x word
    have hp : P (stoppedClockFreezeRun ring x
        (stoppedClockFreezeStart C) word).bits = true := by
      simpa [hbits] using hg.2
    have hlen : (stoppedClockFreezeRun ring x
        (stoppedClockFreezeStart C) word).bits.length ≤ E := by
      simpa [hbits] using hg.1
    have hpot := stoppedClockFreezePotential_eq_twoPow_of_event
      E P hmono _ hlen hp
    change 2 ^ E ≤ stoppedClockFreezePotential E P
      (stoppedClockFreezeRun ring x (stoppedClockFreezeStart C) word)
    rw [hpot]
    exact Nat.le_refl _
  exact Nat.le_trans hdom
    (stoppedClockFreezePotentialSum_le hn2 ring x C E T P hmono)

theorem stoppedClockSuffixLetterDependentFreezeTransfer :
    StoppedClockSuffixLetterDependentFreezeTransfer := by
  intro n psi kappa T E M hn2 hpsi ring C x
  let P : List Bool → Bool := fun bits =>
    decide (M ≤ (lotteryRun psi (lotteryOffset (C x).hits.val) bits).wins)
  have hmono : ExtensionMonotone P := by
    dsimp [P]
    exact lotteryAtLeast_extensionMonotone_freeze
      psi (C x).hits.val M
  have h := stoppedClockSuffixFreezeTransfer_generic
    hn2 ring C x T E P hmono
  simpa [stoppedClockSuffixFrozenLotteryCount, P,
    lotteryAtLeastWordCount, lotteryPredWordCount] using h

private def clockArmedSignalVal_freeze
    {psi kappa : Nat} (q : PPL.State psi kappa) : Nat :=
  if q.leader = true then kappa else q.signalR.val

private def clockBumpedHitsVal_freeze
    {psi kappa : Nat} (q : PPL.State psi kappa) : Nat :=
  Nat.min (q.hits.val + 1) psi

private theorem rightNeighbor_ne_self_freeze
    {n : Nat} (ring : DirectedRing n) (hn2 : 2 ≤ n) (i : Fin n) :
    ring.rightNeighbor i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  by_cases hlt : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : i.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega

private theorem fin2_edge_incident_freeze
    (ring : DirectedRing 2) (x e : Fin 2) :
    e = ring.leftNeighbor x ∨ e = x := by
  by_cases hself : e = x
  · exact Or.inr hself
  · have hx : x.val = 0 ∨ x.val = 1 := by omega
    have he : e.val = 0 ∨ e.val = 1 := by omega
    rcases hx with hx | hx <;> rcases he with he | he
    · exact False.elim (hself (Fin.ext (he.trans hx.symm)))
    · left
      apply Fin.ext
      simp [DirectedRing.leftNeighbor, hx, he]
    · left
      apply Fin.ext
      simp [DirectedRing.leftNeighbor, hx, he]
    · exact False.elim (hself (Fin.ext (he.trans hx.symm)))

private theorem pplStep_endpoint_clock_hits_two
    {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing 2)
    (C : PPLConfig 2 psi kappa) (e : Fin 2) :
    let j := ring.rightNeighbor e
    let d := PPL.determineMode (C e) (C j)
    ((pplStep ring C e e).clock = d.1.clock ∧
      (pplStep ring C e e).hits = d.1.hits) ∧
    ((pplStep ring C e j).clock = d.2.clock ∧
      (pplStep ring C e j).hits = d.2.hits) := by
  dsimp only
  have hp := clockSuffixPairProjection hpsi
    (C e) (C (ring.rightNeighbor e))
  dsimp only at hp
  have hne : ring.rightNeighbor e ≠ e :=
    rightNeighbor_ne_self_freeze ring (by omega) e
  constructor
  · constructor
    · simpa [pplStep, PopulationProtocol.step,
        PPL.protocol, PPL.transition, hpsi] using hp.1
    · simpa [pplStep, PopulationProtocol.step,
        PPL.protocol, PPL.transition, hpsi] using hp.2.1
  · constructor
    · simpa [pplStep, PopulationProtocol.step,
        PPL.protocol, PPL.transition, hpsi, hne] using hp.2.2.1
    · simpa [pplStep, PopulationProtocol.step,
        PPL.protocol, PPL.transition, hpsi, hne] using hp.2.2.2

private theorem noReset_signal_zero_freeze
    {n psi kappa : Nat} (ring : DirectedRing n)
    (C : PPLConfig n psi kappa) (x e : Fin n)
    (hinc : x = e ∨ x = ring.rightNeighbor e)
    (hreset : clockResetAt ring C x e = false) :
    clockArmedSignalVal_freeze (C e) = 0 ∧
      (C (ring.rightNeighbor e)).signalR.val = 0 := by
  have hf := hreset
  unfold clockResetAt at hf
  change
    decide
      ((x = e ∨ x = ring.rightNeighbor e) ∧
        (0 < clockArmedSignalVal_freeze (C e) ∨
          0 < (C (ring.rightNeighbor e)).signalR.val)) = false at hf
  simp only [decide_eq_false_iff_not] at hf
  have hz :
      ¬ (0 < clockArmedSignalVal_freeze (C e) ∨
        0 < (C (ring.rightNeighbor e)).signalR.val) := by
    intro hs
    exact hf ⟨hinc, hs⟩
  constructor <;> omega

private theorem bumpedHits_eq_psi_iff_freeze
    {psi kappa : Nat} (q : PPL.State psi kappa) :
    clockBumpedHitsVal_freeze q = psi ↔ psi ≤ q.hits.val + 1 := by
  unfold clockBumpedHitsVal_freeze
  constructor
  · intro h
    calc
      psi = clockBumpedHitsVal_freeze q := h.symm
      _ ≤ q.hits.val + 1 := Nat.min_le_left _ _
  · intro h
    exact Nat.min_eq_right h

private theorem determineMode_noSignal_fields_freeze
    {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa)
    (hl : clockArmedSignalVal_freeze l = 0)
    (hr : r.signalR.val = 0) :
    let q := PPL.determineMode l r
    q.1.clock = l.clock ∧
      q.1.hits.val = 0 ∧
      q.2.hits.val =
        (if clockBumpedHitsVal_freeze r = psi then 0
          else clockBumpedHitsVal_freeze r) ∧
      (r.clock.val < q.2.clock.val →
        clockBumpedHitsVal_freeze r = psi) := by
  cases hlead : l.leader with
  | false =>
      have hls : l.signalR.val = 0 := by
        simpa [clockArmedSignalVal_freeze, hlead] using hl
      by_cases hhit : clockBumpedHitsVal_freeze r = psi
      · simp [PPL.determineMode, hlead, hls, hr,
          clockBumpedHitsVal_freeze, hhit] <;>
          unfoldFinishModes <;> simp_all [clockBumpedHitsVal_freeze] <;> omega
      · simp [PPL.determineMode, hlead, hls, hr,
          clockBumpedHitsVal_freeze, hhit] <;>
          unfoldFinishModes <;> simp_all [clockBumpedHitsVal_freeze] <;> omega
  | true =>
      have hk : kappa = 0 := by
        simpa [clockArmedSignalVal_freeze, hlead] using hl
      by_cases hhit : clockBumpedHitsVal_freeze r = psi
      · simp [PPL.determineMode, hlead, hk, hr,
          clockBumpedHitsVal_freeze, hhit] <;>
          unfoldFinishModes <;> simp_all [clockBumpedHitsVal_freeze] <;> omega
      · simp [PPL.determineMode, hlead, hk, hr,
          clockBumpedHitsVal_freeze, hhit] <;>
          unfoldFinishModes <;> simp_all [clockBumpedHitsVal_freeze] <;> omega

private theorem clockSuffixAux_bridge_two
    {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing 2) (x : Fin 2) :
    ∀ (C : PPLConfig 2 psi kappa)
      (word : DetSchedule 2) (s : LotteryState),
      ClockLotteryInvariant C x s →
      s.wins + clockSuffixTicksAux ring x C word ≤
        (lotteryRun psi s (clockSuffixBitsAux ring x C word)).wins := by
  intro C word s hsync
  induction word generalizing C s with
  | nil => simp [clockSuffixTicksAux, clockSuffixBitsAux, lotteryRun]
  | cons e rest ih =>
      change s.headRun = (C x).hits.val at hsync
      cases hreset : clockResetAt ring C x e with
      | true =>
          simp [clockSuffixTicksAux, clockSuffixBitsAux, hreset, lotteryRun]
      | false =>
          let C' := pplStep ring C e
          by_cases hH : e = ring.leftNeighbor x
          · subst e
            have hrx : ring.rightNeighbor (ring.leftNeighbor x) = x :=
              rightNeighbor_leftNeighbor_freeze ring x
            have hinc : x = ring.leftNeighbor x ∨
                x = ring.rightNeighbor (ring.leftNeighbor x) := Or.inr hrx.symm
            have hzeros := noReset_signal_zero_freeze ring C x
              (ring.leftNeighbor x) hinc hreset
            have hright0 : (C x).signalR.val = 0 := by
              simpa [hrx] using hzeros.2
            have hdet := determineMode_noSignal_fields_freeze hpsi
              (C (ring.leftNeighbor x)) (C x) hzeros.1 hright0
            dsimp only at hdet
            have hfull0 := pplStep_endpoint_clock_hits_two hpsi
              ring C (ring.leftNeighbor x)
            have hfull :
                (C' x).clock =
                    (PPL.determineMode (C (ring.leftNeighbor x)) (C x)).2.clock ∧
                  (C' x).hits =
                    (PPL.determineMode (C (ring.leftNeighbor x)) (C x)).2.hits := by
              simpa [C', hrx] using hfull0.2
            have hhits : (C' x).hits.val =
                (if clockBumpedHitsVal_freeze (C x) = psi then 0
                  else clockBumpedHitsVal_freeze (C x)) := by
              exact (congrArg Fin.val hfull.2).trans hdet.2.2.1
            have htick : (C x).clock.val < (C' x).clock.val →
                clockBumpedHitsVal_freeze (C x) = psi := by
              intro ht
              have hc := congrArg Fin.val hfull.1
              rw [hc] at ht
              exact hdet.2.2.2 ht
            by_cases hwin : psi ≤ s.headRun + 1
            · have hphysWin : clockBumpedHitsVal_freeze (C x) = psi := by
                apply (bumpedHits_eq_psi_iff_freeze (C x)).2
                simpa [hsync] using hwin
              let s' := lotteryStep psi s true
              have hsync' : ClockLotteryInvariant C' x s' := by
                unfold ClockLotteryInvariant
                simp [s', lotteryStep, hwin, hhits, hphysWin]
              have htail := ih C' s' hsync'
              have hsWin : s'.wins = s.wins + 1 := by
                simp [s', lotteryStep, hwin]
              have htickOne :
                  (if (C x).clock.val < (C' x).clock.val then 1 else 0) ≤ 1 := by
                split <;> omega
              have htotal :
                  s.wins +
                      (if (C x).clock.val < (C' x).clock.val then 1 else 0) +
                      clockSuffixTicksAux ring x C' rest ≤
                    (lotteryRun psi s' (clockSuffixBitsAux ring x C' rest)).wins := by
                rw [hsWin] at htail
                omega
              simpa [clockSuffixTicksAux, clockSuffixBitsAux,
                hreset, incidentBit, lotteryRun, C', s', Nat.add_assoc]
                using htotal
            · have hphysNo : clockBumpedHitsVal_freeze (C x) ≠ psi := by
                intro hb
                have hle := (bumpedHits_eq_psi_iff_freeze (C x)).1 hb
                apply hwin
                simpa [hsync] using hle
              have hmin : clockBumpedHitsVal_freeze (C x) =
                  (C x).hits.val + 1 := by
                unfold clockBumpedHitsVal_freeze
                apply Nat.min_eq_left
                have hlt : (C x).hits.val + 1 < psi := by omega
                exact Nat.le_of_lt hlt
              have hclockNo : ¬ (C x).clock.val < (C' x).clock.val := by
                intro ht
                exact hphysNo (htick ht)
              have hneq : (C x).hits.val + 1 ≠ psi := by omega
              have hnwin : ¬ psi ≤ (C x).hits.val + 1 := by omega
              let s' := lotteryStep psi s true
              have hsync' : ClockLotteryInvariant C' x s' := by
                unfold ClockLotteryInvariant
                simp [s', lotteryStep, hhits, hmin, hneq, hnwin, hsync]
              have htail := ih C' s' hsync'
              have hsWin : s'.wins = s.wins := by
                simp [s', lotteryStep, hwin]
              have htotal :
                  s.wins + clockSuffixTicksAux ring x C' rest ≤
                    (lotteryRun psi s' (clockSuffixBitsAux ring x C' rest)).wins := by
                rw [hsWin] at htail
                exact htail
              simpa [clockSuffixTicksAux, clockSuffixBitsAux,
                hreset, incidentBit, lotteryRun, C', s', hclockNo] using htotal
          · have hclass := fin2_edge_incident_freeze ring x e
            have hT : e = x := by
              rcases hclass with hleft | hself
              · exact (hH hleft).elim
              · exact hself
            subst e
            have hinc : x = x ∨ x = ring.rightNeighbor x := Or.inl rfl
            have hzeros := noReset_signal_zero_freeze ring C x x hinc hreset
            have hdet := determineMode_noSignal_fields_freeze hpsi
              (C x) (C (ring.rightNeighbor x)) hzeros.1 hzeros.2
            dsimp only at hdet
            have hfull := (pplStep_endpoint_clock_hits_two hpsi ring C x).1
            have hclock : (C' x).clock = (C x).clock := hfull.1.trans hdet.1
            have hhits : (C' x).hits.val = 0 :=
              (congrArg Fin.val hfull.2).trans hdet.2.1
            let s' := lotteryStep psi s false
            have hsync' : ClockLotteryInvariant C' x s' := by
              unfold ClockLotteryInvariant
              simp [s', lotteryStep, hhits]
            have htail := ih C' s' hsync'
            have hsWin : s'.wins = s.wins := by simp [s', lotteryStep]
            have htotal :
                s.wins + clockSuffixTicksAux ring x C' rest ≤
                  (lotteryRun psi s' (clockSuffixBitsAux ring x C' rest)).wins := by
              rw [hsWin] at htail
              exact htail
            simpa [clockSuffixTicksAux, clockSuffixBitsAux,
              hreset, incidentBit, hH, lotteryRun, C', s', hclock] using htotal

theorem stoppedClockSuffixTickLotteryBridgeAtTwo :
    StoppedClockSuffixTickLotteryBridgeAtTwo := by
  intro psi kappa hpsi ring C x word
  have hsync : ClockLotteryInvariant C x
      (lotteryOffset (C x).hits.val) := rfl
  have h := clockSuffixAux_bridge_two hpsi ring x C word
    (lotteryOffset (C x).hits.val) hsync
  simpa [clockSuffixTicks, clockSuffixBits, lotteryOffset] using h

theorem stoppedClockSuffixBoundsCorrected :
    StoppedClockSuffixBoundsCorrected :=
  stoppedClockSuffixBoundsCorrected_of_letterDependentFreezeTransfer
    ⟨stoppedClockSuffixLetterDependentFreezeTransfer,
      stoppedClockSuffixTickLotteryBridgeAtTwo⟩

#print axioms PPL.Probability.stoppedClockSuffixLetterDependentFreezeTransfer
#print axioms PPL.Probability.stoppedClockSuffixTickLotteryBridgeAtTwo
#print axioms PPL.Probability.stoppedClockSuffixBoundsCorrected

end PPL.Probability
