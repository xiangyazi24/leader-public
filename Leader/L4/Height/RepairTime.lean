import Leader.L4.Height.Throughput
import Leader.L4.Height.Physical

namespace L4.Height

open Classical

set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

/-- Abstract coverage of one recovery stage by a finite family of service
waiting-time functions.  The exponential moments live in the accepted
`Thru.wordSum` counting model.  Coverage itself is stated using the
`Window.lean` execution function consumed by `iidHitCost`. -/
def StageCover {α : Type} {n : Nat}
    (next : α → Fin n → α) (Src Tgt : α → Prop)
    (L Nq Mq : Nat) : Prop :=
  ∀ x, Src x →
    ∃ Ws : List (Thru.Word n → Nat),
      Ws.length = Nq ∧
      (∀ W, W ∈ Ws → ∀ t,
        Thru.wordSum
            (fun u => 2 ^ (Nat.min (W u) t / L)) t ≤
          Mq * n ^ t) ∧
      (∀ u : Thru.Word n, ∀ k,
        Thru.maxWait Ws u ≤ k →
        k ≤ u.length →
        Tgt (runWord next x (u.take k)))

/-- The numerical mean bound supplied by one stage. -/
def stageBound (L Nq Mq : Nat) : Nat :=
  L * (Nat.log2 Nq + Nat.log2 Mq + 4)

/-- Sum of the quiet, frozen, and clearance stage bounds. -/
def repairBound
    (L NqQuiet MqQuiet NqFrozen MqFrozen NqClear MqClear : Nat) : Nat :=
  stageBound L NqQuiet MqQuiet +
    stageBound L NqFrozen MqFrozen +
    stageBound L NqClear MqClear

/-- The concrete three-stage service-family budget from the paper. -/
def repairTimeBudget (L m D : Nat) : Nat :=
  repairBound L
    m 4
    (m * m) (4 ^ D)
    (m * 3 ^ (D + 1)) (4 ^ (D + 1))

/-- `Window.wordSum` and `Thru.wordSum` are definitionally parallel
recursions, but they are distinct declarations in the accepted files. -/
theorem repair_wordSum_eq_thru {n : Nat}
    (f : List (Fin n) → Nat) :
    ∀ k, wordSum f k = Thru.wordSum f k := by
  intro k
  induction k generalizing f with
  | zero =>
      rfl
  | succ k ih =>
      simp only [wordSum, Thru.wordSum]
      apply sum_ofFn_eq
      intro e
      exact ih (fun v => f (e :: v))

/-- Monotonicity of `Window.wordSum` when the comparison is known only on
words of the indexed length. -/
theorem repair_wordSum_mono_length {n : Nat}
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
      apply h (e :: w)
      simp only [List.length_cons]
      omega

/-- If the target holds after the first `k` letters, then the stopped time
on the whole word is at most `k`. -/
theorem repair_stoppedTime_le_prefix {α : Type} {n : Nat}
    (next : α → Fin n → α) (Tgt : α → Prop) :
    ∀ (x : α) (u : List (Fin n)) (k : Nat),
      k ≤ u.length →
      Tgt (runWord next x (u.take k)) →
      stoppedTime next Tgt x u ≤ k := by
  intro x u
  induction u generalizing x with
  | nil =>
      intro k hk hhit
      simp [stoppedTime]
  | cons e u ih =>
      intro k hk hhit
      cases k with
      | zero =>
          have hx : Tgt x := by
            simpa [runWord] using hhit
          simp [stoppedTime, hx]
      | succ k =>
          have hkTail : k ≤ u.length := by
            simp only [List.length_cons] at hk
            omega
          have hhitTail :
              Tgt (runWord next (next x e) (u.take k)) := by
            simpa [runWord] using hhit
          by_cases hx : Tgt x
          · simp [stoppedTime, hx]
          · simp only [stoppedTime, hx, if_false]
            exact Nat.succ_le_succ
              (ih (next x e) k hkTail hhitTail)

/-- A service-family cover gives the advertised one-stage truncated mean. -/
theorem stage_mean {α : Type} {n L Nq Mq : Nat}
    (next : α → Fin n → α) (Src Tgt : α → Prop)
    (hCover : StageCover next Src Tgt L Nq Mq)
    (hNq : 1 ≤ Nq) (hMq : 1 ≤ Mq) (hL : 1 ≤ L)
    (x : α) (hx : Src x) :
    IIDExpectedHittingTimeAtMost next Tgt x
      (L * (Nat.log2 Nq + Nat.log2 Mq + 4)) := by
  rcases hCover x hx with
    ⟨Ws, hLength, hEach, hReach⟩
  unfold IIDExpectedHittingTimeAtMost
  intro t
  have hmax :
      Thru.wordSum
          (fun u => Nat.min (Thru.maxWait Ws u) t) t ≤
        L * (Nat.log2 Nq + Nat.log2 Mq + 4) * n ^ t := by
    exact Thru.mean_max Ws Nq Mq L t
      hLength hNq hMq hL
      (fun W hW => hEach W hW t)
  have hpoint :
      ∀ u, u.length = t →
        stoppedTime next Tgt x u ≤
          Nat.min (Thru.maxWait Ws u) t := by
    intro u hu
    by_cases hw : Thru.maxWait Ws u ≤ t
    · have hwlen : Thru.maxWait Ws u ≤ u.length := by
        omega
      have hhit :
          Tgt (runWord next x
            (u.take (Thru.maxWait Ws u))) :=
        hReach u (Thru.maxWait Ws u)
          (Nat.le_refl _) hwlen
      have hstop := repair_stoppedTime_le_prefix
        next Tgt x u (Thru.maxWait Ws u) hwlen hhit
      simpa only [Nat.min_eq_left hw] using hstop
    · have htmax : t ≤ Thru.maxWait Ws u := by
        omega
      have hstop := stoppedTime_le_length next Tgt x u
      have hstop' : stoppedTime next Tgt x u ≤ t := by
        rw [hu] at hstop
        exact hstop
      simpa only [Nat.min_eq_right htmax] using hstop'
  calc
    iidHitCost next Tgt t x =
        wordSum (stoppedTime next Tgt x) t :=
      iidHitCost_eq_wordSum next Tgt t x
    _ ≤ wordSum
          (fun u => Nat.min (Thru.maxWait Ws u) t) t :=
      repair_wordSum_mono_length
        (stoppedTime next Tgt x)
        (fun u => Nat.min (Thru.maxWait Ws u) t)
        t hpoint
    _ = Thru.wordSum
          (fun u => Nat.min (Thru.maxWait Ws u) t) t :=
      repair_wordSum_eq_thru
        (fun u => Nat.min (Thru.maxWait Ws u) t) t
    _ ≤ L * (Nat.log2 Nq + Nat.log2 Mq + 4) * n ^ t :=
      hmax

/-- Compose the quiet, frozen, and clearance stages through the accepted
forward-closed-set interface. -/
theorem repair_mean {α : Type} {n : Nat}
    (next : α → Fin n → α)
    (Cust Qu Fr Lg : α → Prop)
    (L NqQuiet MqQuiet NqFrozen MqFrozen NqClear MqClear : Nat)
    (hL : 1 ≤ L)
    (hNqQuiet : 1 ≤ NqQuiet) (hMqQuiet : 1 ≤ MqQuiet)
    (hNqFrozen : 1 ≤ NqFrozen) (hMqFrozen : 1 ≤ MqFrozen)
    (hNqClear : 1 ≤ NqClear) (hMqClear : 1 ≤ MqClear)
    (hQuClosed : ∀ x e, Qu x → Qu (next x e))
    (hFrClosed : ∀ x e, Fr x → Fr (next x e))
    (_hLgClosed : ∀ x e, Lg x → Lg (next x e))
    (hQuietCover :
      StageCover next Cust Qu L NqQuiet MqQuiet)
    (hFrozenCover :
      StageCover next Qu Fr L NqFrozen MqFrozen)
    (hClearCover :
      StageCover next Fr Lg L NqClear MqClear)
    (x : α) (hxCust : Cust x) :
    IIDExpectedHittingTimeAtMost next Lg x
      (repairBound L
        NqQuiet MqQuiet NqFrozen MqFrozen NqClear MqClear) := by
  have hCQ : ∀ y, Cust y →
      IIDExpectedHittingTimeAtMost next Qu y
        (stageBound L NqQuiet MqQuiet) := by
    intro y hy
    exact stage_mean
      (next := next) (Src := Cust) (Tgt := Qu)
      (L := L) (Nq := NqQuiet) (Mq := MqQuiet)
      hQuietCover hNqQuiet hMqQuiet hL y hy
  have hQF : ∀ y, Qu y →
      IIDExpectedHittingTimeAtMost next Fr y
        (stageBound L NqFrozen MqFrozen) := by
    intro y hy
    exact stage_mean
      (next := next) (Src := Qu) (Tgt := Fr)
      (L := L) (Nq := NqFrozen) (Mq := MqFrozen)
      hFrozenCover hNqFrozen hMqFrozen hL y hy
  have hFL : ∀ y, Fr y →
      IIDExpectedHittingTimeAtMost next Lg y
        (stageBound L NqClear MqClear) := by
    intro y hy
    exact stage_mean
      (next := next) (Src := Fr) (Tgt := Lg)
      (L := L) (Nq := NqClear) (Mq := MqClear)
      hClearCover hNqClear hMqClear hL y hy
  have hCF : ∀ y, Cust y →
      IIDExpectedHittingTimeAtMost next Fr y
        (stageBound L NqQuiet MqQuiet +
          stageBound L NqFrozen MqFrozen) := by
    intro y hy
    exact expected_then_closed
      (next := next) (A := Cust) (B := Qu) (C := Fr)
      (a := stageBound L NqQuiet MqQuiet)
      (b := stageBound L NqFrozen MqFrozen)
      hCQ hQuClosed hQF y hy
  have hCL := expected_then_closed
    (next := next) (A := Cust) (B := Fr) (C := Lg)
    (a := stageBound L NqQuiet MqQuiet +
      stageBound L NqFrozen MqFrozen)
    (b := stageBound L NqClear MqClear)
    hCF hFrClosed hFL x hxCust
  simpa only [repairBound] using hCL

/-- Product logarithms cost at most one extra bit. -/
theorem repair_log2_mul_le (a b : Nat)
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Nat.log2 (a * b) ≤ Nat.log2 a + Nat.log2 b + 1 := by
  have haPos : 0 < a := by omega
  have hbPos : 0 < b := by omega
  have habPos : 0 < a * b := Nat.mul_pos haPos hbPos
  have haPow : a < 2 ^ (Nat.log2 a + 1) :=
    (Nat.log2_lt (Nat.ne_of_gt haPos)).1 (by omega)
  have hbPow : b < 2 ^ (Nat.log2 b + 1) :=
    (Nat.log2_lt (Nat.ne_of_gt hbPos)).1 (by omega)
  have hprod :
      a * b < 2 ^ (Nat.log2 a + Nat.log2 b + 2) := by
    calc
      a * b < 2 ^ (Nat.log2 a + 1) * b :=
        Nat.mul_lt_mul_of_pos_right haPow hbPos
      _ < 2 ^ (Nat.log2 a + 1) *
            2 ^ (Nat.log2 b + 1) :=
        Nat.mul_lt_mul_of_pos_left hbPow
          (Nat.pow_pos (by omega))
      _ = 2 ^ ((Nat.log2 a + 1) +
            (Nat.log2 b + 1)) :=
        (Nat.pow_add 2 (Nat.log2 a + 1)
          (Nat.log2 b + 1)).symm
      _ = 2 ^ (Nat.log2 a + Nat.log2 b + 2) :=
        congrArg (fun q : Nat => 2 ^ q) (by omega)
  have hlog :
      Nat.log2 (a * b) < Nat.log2 a + Nat.log2 b + 2 :=
    (Nat.log2_lt (Nat.ne_of_gt habPos)).2 hprod
  omega

/-- `3^h` is bounded by `2^(2h)`. -/
theorem repair_three_pow_le_two_pow (h : Nat) :
    3 ^ h ≤ 2 ^ (2 * h) := by
  induction h with
  | zero =>
      decide
  | succ h ih =>
      calc
        3 ^ (h + 1) = 3 ^ h * 3 :=
          Nat.pow_succ 3 h
        _ ≤ 2 ^ (2 * h) * 4 :=
          Nat.mul_le_mul ih (by decide)
        _ = 2 ^ (2 * h) * 2 ^ 2 := by
          exact congrArg
            (fun q : Nat => 2 ^ (2 * h) * q)
            (by decide)
        _ = 2 ^ (2 * h + 2) :=
          (Nat.pow_add 2 (2 * h) 2).symm
        _ = 2 ^ (2 * (h + 1)) :=
          congrArg (fun q : Nat => 2 ^ q) (by omega)

/-- Consequently `log2 (3^h) ≤ 2h`. -/
theorem repair_log2_three_pow_le (h : Nat) :
    Nat.log2 (3 ^ h) ≤ 2 * h := by
  have hbase := repair_three_pow_le_two_pow h
  have hpos : 0 < 3 ^ h := Nat.pow_pos (by omega)
  have htwoPos : 0 < 2 ^ (2 * h) := Nat.pow_pos (by omega)
  have hlt : 3 ^ h < 2 ^ (2 * h + 1) := by
    calc
      3 ^ h ≤ 2 ^ (2 * h) := hbase
      _ < 2 ^ (2 * h) * 2 := by omega
      _ = 2 ^ (2 * h + 1) :=
        (Nat.pow_succ 2 (2 * h)).symm
  have hlog : Nat.log2 (3 ^ h) < 2 * h + 1 :=
    (Nat.log2_lt (Nat.ne_of_gt hpos)).2 hlt
  omega

/-- Rewrite powers of four as even powers of two. -/
theorem repair_four_pow_eq_two_pow (h : Nat) :
    4 ^ h = 2 ^ (2 * h) := by
  induction h with
  | zero =>
      decide
  | succ h ih =>
      calc
        4 ^ (h + 1) = 4 ^ h * 4 :=
          Nat.pow_succ 4 h
        _ = 2 ^ (2 * h) * 4 := by
          rw [ih]
        _ = 2 ^ (2 * h) * 2 ^ 2 := by
          exact congrArg
            (fun q : Nat => 2 ^ (2 * h) * q)
            (by decide)
        _ = 2 ^ (2 * h + 2) :=
          (Nat.pow_add 2 (2 * h) 2).symm
        _ = 2 ^ (2 * (h + 1)) :=
          congrArg (fun q : Nat => 2 ^ q) (by omega)

/-- The logarithm of `4^h` is at most `2h`. -/
theorem repair_log2_four_pow_le (h : Nat) :
    Nat.log2 (4 ^ h) ≤ 2 * h := by
  have hpos : 0 < 4 ^ h := Nat.pow_pos (by omega)
  have htwoPos : 0 < 2 ^ (2 * h) := Nat.pow_pos (by omega)
  have hlt : 4 ^ h < 2 ^ (2 * h + 1) := by
    calc
      4 ^ h = 2 ^ (2 * h) :=
        repair_four_pow_eq_two_pow h
      _ < 2 ^ (2 * h) * 2 := by omega
      _ = 2 ^ (2 * h + 1) :=
        (Nat.pow_succ 2 (2 * h)).symm
  have hlog : Nat.log2 (4 ^ h) < 2 * h + 1 :=
    (Nat.log2_lt (Nat.ne_of_gt hpos)).2 hlt
  omega

/-- For `m ≥ 2`, the elementary strict bound `m < 2^m`. -/
theorem repair_nat_lt_two_pow (m : Nat) (hm : 2 ≤ m) :
    m < 2 ^ m := by
  let k := m - 2
  have hmEq : m = 2 + k := by
    dsimp [k]
    omega
  rw [hmEq]
  induction k with
  | zero =>
      decide
  | succ k ih =>
      have hp : 0 < 2 ^ (2 + k) := Nat.pow_pos (by omega)
      calc
        2 + (k + 1) < 2 ^ (2 + k) * 2 := by
          omega
        _ = 2 ^ ((2 + k) + 1) :=
          (Nat.pow_succ 2 (2 + k)).symm
        _ = 2 ^ (2 + (k + 1)) :=
          congrArg (fun q : Nat => 2 ^ q) (by omega)

/-- For `m ≥ 2`, `log2 m ≤ m-1`. -/
theorem repair_log2_le_pred (m : Nat) (hm : 2 ≤ m) :
    Nat.log2 m ≤ m - 1 := by
  have hne : m ≠ 0 := by omega
  have hp := repair_nat_lt_two_pow m hm
  have hlog : Nat.log2 m < m :=
    (Nat.log2_lt hne).2 hp
  omega

/-- For `m ≥ 8`, the stronger strict bound `m < 2^(m-4)`. -/
theorem repair_nat_lt_two_pow_sub_four (m : Nat) (hm : 8 ≤ m) :
    m < 2 ^ (m - 4) := by
  let k := m - 8
  have hmEq : m = 8 + k := by
    dsimp [k]
    omega
  rw [hmEq]
  induction k with
  | zero =>
      decide
  | succ k ih =>
      have hp : 0 < 2 ^ ((8 + k) - 4) :=
        Nat.pow_pos (by omega)
      calc
        8 + (k + 1) < 2 ^ ((8 + k) - 4) * 2 := by
          omega
        _ = 2 ^ (((8 + k) - 4) + 1) :=
          (Nat.pow_succ 2 ((8 + k) - 4)).symm
        _ = 2 ^ ((8 + (k + 1)) - 4) :=
          congrArg (fun q : Nat => 2 ^ q) (by omega)

/-- For `m ≥ 8`, `log2 m ≤ m-5`. -/
theorem repair_log2_le_sub_five (m : Nat) (hm : 8 ≤ m) :
    Nat.log2 m ≤ m - 5 := by
  have hne : m ≠ 0 := by omega
  have hp := repair_nat_lt_two_pow_sub_four m hm
  have hlog : Nat.log2 m < m - 4 :=
    (Nat.log2_lt hne).2 hp
  omega

/-- Closed form for the three concrete service-family stage bounds.  The
`D ≤ m` premise is retained for the paper interface, although the displayed
closed-form inequality itself is stronger and does not need it. -/
theorem repair_budget (L m D : Nat)
    (hm : 1 ≤ m) (_hDm : D ≤ m) :
    repairTimeBudget L m D ≤
      L * (4 * Nat.log2 m + 6 * D + 20) := by
  have hlogFour : Nat.log2 4 = 2 := by decide
  have hmm := repair_log2_mul_le m m hm hm
  have hfourD := repair_log2_four_pow_le D
  have hthreePos : 1 ≤ 3 ^ (D + 1) := by
    have hp : 0 < 3 ^ (D + 1) := Nat.pow_pos (by omega)
    omega
  have hmthree := repair_log2_mul_le
    m (3 ^ (D + 1)) hm hthreePos
  have hthree := repair_log2_three_pow_le (D + 1)
  have hfourSucc := repair_log2_four_pow_le (D + 1)
  have hOne :
      stageBound L m 4 ≤
        L * (Nat.log2 m + 6) := by
    unfold stageBound
    exact Nat.mul_le_mul_left L (by omega)
  have hTwo :
      stageBound L (m * m) (4 ^ D) ≤
        L * (2 * Nat.log2 m + 2 * D + 5) := by
    unfold stageBound
    exact Nat.mul_le_mul_left L (by omega)
  have hThree :
      stageBound L (m * 3 ^ (D + 1)) (4 ^ (D + 1)) ≤
        L * (Nat.log2 m + 4 * D + 9) := by
    unfold stageBound
    exact Nat.mul_le_mul_left L (by omega)
  unfold repairTimeBudget repairBound
  calc
    stageBound L m 4 +
          stageBound L (m * m) (4 ^ D) +
          stageBound L (m * 3 ^ (D + 1)) (4 ^ (D + 1)) ≤
        L * (Nat.log2 m + 6) +
          L * (2 * Nat.log2 m + 2 * D + 5) +
          L * (Nat.log2 m + 4 * D + 9) :=
      Nat.add_le_add (Nat.add_le_add hOne hTwo) hThree
    _ = L *
        ((Nat.log2 m + 6) +
          (2 * Nat.log2 m + 2 * D + 5) +
          (Nat.log2 m + 4 * D + 9)) := by
      calc
        L * (Nat.log2 m + 6) +
              L * (2 * Nat.log2 m + 2 * D + 5) +
              L * (Nat.log2 m + 4 * D + 9) =
            L * ((Nat.log2 m + 6) +
              (2 * Nat.log2 m + 2 * D + 5)) +
              L * (Nat.log2 m + 4 * D + 9) := by
          exact congrArg
            (fun z : Nat =>
              z + L * (Nat.log2 m + 4 * D + 9))
            (Nat.mul_add L
              (Nat.log2 m + 6)
              (2 * Nat.log2 m + 2 * D + 5)).symm
        _ = L *
            (((Nat.log2 m + 6) +
              (2 * Nat.log2 m + 2 * D + 5)) +
              (Nat.log2 m + 4 * D + 9)) :=
          (Nat.mul_add L
            ((Nat.log2 m + 6) +
              (2 * Nat.log2 m + 2 * D + 5))
            (Nat.log2 m + 4 * D + 9)).symm
    _ = L * (4 * Nat.log2 m + 6 * D + 20) := by
      exact congrArg (fun q : Nat => L * q) (by omega)

/-- Under `2D ≤ m`, the requested `8Lm` bound is valid from `m ≥ 8`. -/
theorem repair_budget_eight (L m D : Nat)
    (hm : 8 ≤ m) (hhalf : 2 * D ≤ m) :
    repairTimeBudget L m D ≤ 8 * L * m := by
  have hmOne : 1 ≤ m := by omega
  have hDm : D ≤ m := by omega
  have hbase := repair_budget L m D hmOne hDm
  have hlog := repair_log2_le_sub_five m hm
  have hinner :
      4 * Nat.log2 m + 6 * D + 20 ≤ 8 * m := by
    omega
  calc
    repairTimeBudget L m D ≤
        L * (4 * Nat.log2 m + 6 * D + 20) := hbase
    _ ≤ L * (8 * m) := Nat.mul_le_mul_left L hinner
    _ = 8 * L * m := by ac_rfl

/-- Corrected `16Lm` statement: it holds for every `m ≥ 2` under
`2D ≤ m`. -/
theorem repair_budget_sixteen (L m D : Nat)
    (hm : 2 ≤ m) (hhalf : 2 * D ≤ m) :
    repairTimeBudget L m D ≤ 16 * L * m := by
  have hmOne : 1 ≤ m := by omega
  have hDm : D ≤ m := by omega
  have hbase := repair_budget L m D hmOne hDm
  have hlog := repair_log2_le_pred m hm
  have hinner :
      4 * Nat.log2 m + 6 * D + 20 ≤ 16 * m := by
    omega
  calc
    repairTimeBudget L m D ≤
        L * (4 * Nat.log2 m + 6 * D + 20) := hbase
    _ ≤ L * (16 * m) := Nat.mul_le_mul_left L hinner
    _ = 16 * L * m := by ac_rfl

/-- Literal counterexample to the proposed all-`m ≥ 1` `16Lm` clause. -/
theorem repair_budget_sixteen_counterexample :
    repairTimeBudget 1 1 0 = 17 := by
  decide

/-- A uniform corrected small-size statement: `17Lm` holds for every
`m ≥ 1` under `2D ≤ m`. -/
theorem repair_budget_seventeen (L m D : Nat)
    (hm : 1 ≤ m) (hhalf : 2 * D ≤ m) :
    repairTimeBudget L m D ≤ 17 * L * m := by
  by_cases hmOne : m = 1
  · subst m
    have hDzero : D = 0 := by omega
    subst D
    have hlogOne : Nat.log2 1 = 0 := by decide
    have hlogThree : Nat.log2 3 = 1 := by decide
    have hlogFour : Nat.log2 4 = 2 := by decide
    simp [repairTimeBudget, repairBound, stageBound,
      hlogOne, hlogThree, hlogFour] <;> omega
  · have hmTwo : 2 ≤ m := by omega
    have hsixteen := repair_budget_sixteen L m D hmTwo hhalf
    calc
      repairTimeBudget L m D ≤ 16 * L * m := hsixteen
      _ ≤ 17 * L * m := by
        have hcoef : 16 ≤ 17 := by omega
        have hmul := Nat.mul_le_mul_right (L * m) hcoef
        simpa [Nat.mul_assoc] using hmul

end L4.Height
