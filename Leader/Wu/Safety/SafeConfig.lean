import Leader.Wu.Protocol.SubProtocol
import Leader.Core.ModArith

/-!
# Safe Configuration and Closedness

Definition 2 (p.41): A configuration is safe if it satisfies five conditions.
Lemma 4.1.1: The safe configuration is closed.

The five conditions:
1. Exactly one leader
2. No non-peaceful bullet
3. No free barrier
4. No free overwriting signal
5. Stable ID sequence from the leader
-/

/-! ## Leader counting -/

/-- Exactly one leader: there exists a unique agent with leader = true. -/
def hasUniqueLeader {ψ : Nat} (n : Nat) (C : Fin n → AgentState ψ) : Prop :=
  ∃ i : Fin n, (C i).isLeader ∧ ∀ j : Fin n, (C j).isLeader → j = i

/-- At least one leader. -/
def hasLeader {ψ : Nat} (n : Nat) (C : Fin n → AgentState ψ) : Prop :=
  ∃ i : Fin n, (C i).isLeader

/-! ## Peaceful bullet -/

/-- Literal transcription of Wu's peaceful-live-bullet conditions on p.42.
Distance `d = 0` is permitted when the bullet is colocated with its right
leader. For every offset `k = 0..d`, the bullet-absence signal is zero and the
next label is consecutive, matching the printed inclusive range. -/
def isPeacefulBullet {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (i : Fin n) : Prop :=
  (C i).bullet = ⟨2, by omega⟩ ∧
  ∃ d : Nat, d < n ∧
    let j : Fin n := ⟨(i.val + d) % n, Nat.mod_lt _ ring.hn⟩
    (C j).isLeader ∧
    (C j).shield ∧
    (∀ k : Nat, k ≤ d →
      let m : Fin n := ⟨(i.val + k) % n, Nat.mod_lt _ ring.hn⟩
      (C m).signal_B = ⟨0, by omega⟩) ∧
    (∀ k : Nat, k ≤ d →
      let m : Fin n := ⟨(i.val + k) % n, Nat.mod_lt _ ring.hn⟩
      let m' : Fin n := ⟨(i.val + k + 1) % n, Nat.mod_lt _ ring.hn⟩
      (C m').label = ⟨((C m).label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)

/-- No non-peaceful bullet: every live bullet is peaceful. -/
def noNonPeacefulBullet {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) : Prop :=
  ∀ i : Fin n, (C i).bullet = ⟨2, by omega⟩ → isPeacefulBullet hψ ring C i

/-! ## Free barrier -/

/-- No free barrier: every barrier edge has its right agent as a leader. -/
def noFreeBarrier {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) : Prop :=
  ∀ i : Fin n,
    let j := ring.rightNeighbor i
    isBarrier hψ (C i) (C j) → (C j).isLeader

/-- On a no-free-barrier configuration, every edge whose responder is a
follower has the successor label.  This is the local non-wrap geometry used by
the corrected retry scheduler; it does not impose cyclic alignment at the
edge entering the designated leader. -/
theorem successor_label_of_noFreeBarrier_of_right_not_leader
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ)
    (hfree : noFreeBarrier hψ ring C)
    (i : Fin n)
    (hr : ¬ (C (ring.rightNeighbor i)).isLeader) :
    (C (ring.rightNeighbor i)).label =
      ⟨((C i).label.val + 1) % ψ, Nat.mod_lt _ hψ⟩ := by
  apply Classical.byContradiction
  intro hbarrier
  exact hr (hfree i hbarrier)

/-- Cyclic successor labels around a finite directed ring force the label
modulus to divide the ring size.  This exposes the precise arithmetic scope of
any retry boundary that assumes successor labels on every edge. -/
theorem dvd_of_all_successor_labels
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ)
    (hall : ∀ i,
      (C (ring.rightNeighbor i)).label =
        ⟨((C i).label.val + 1) % ψ, Nat.mod_lt _ hψ⟩) :
    ψ ∣ n := by
  apply Classical.byContradiction
  intro hndvd
  obtain ⟨i, hi⟩ :=
    barrier_exists_of_not_dvd ring.hn hψ hndvd C ring
  exact hi (hall i)

/-! ## Overwriting-action approximation used by historical scaffolding -/

/-- No agent currently has both a non-`none` write state and write action.
This was formerly (and incorrectly) named `noFreeOverwritingSignal`; Wu's
actual free-signal definition depends on signal payload, group index, and group
ID. It remains useful only for the historical quiescent proof scaffolding. -/
def noActiveWriteAction {ψ n : Nat} (_ring : DirectedRing n)
    (C : Fin n → AgentState ψ) : Prop :=
  ∀ i : Fin n, (C i).write_state = .none ∨ (C i).write = .none

/-! ## Quiescence -/

/-- Quiescence: the comparison protocol is resting and no overwriting
signal generation is in progress. -/
def isQuiescent {ψ n : Nat} (_ring : DirectedRing n)
    (C : Fin n → AgentState ψ) : Prop :=
  (∀ i : Fin n, (C i).state = .none) ∧
  (∀ i : Fin n, (C i).gen_ws = false)

/-! ## Stable ID sequence -/

/-- The ID of a group of ψ consecutive agents starting at position `start`.
ID(G) = Σ_{i=0}^{ψ-1} bᵢ · 2^{ψ-1-i} where bᵢ = agent_{start+i}.bit. -/
def groupID {ψ n : Nat} (hn : n > 0) (C : Fin n → AgentState ψ) (start : Fin n) : Nat :=
  (List.range ψ).foldl (fun acc i =>
    let agentIdx : Fin n := ⟨(start.val + i) % n, Nat.mod_lt _ hn⟩
    acc + (if (C agentIdx).bit then 1 else 0) * 2 ^ (ψ - 1 - i)) 0

/-- The number of trailing zeros of a positive natural number in binary. -/
def trailingZeros : Nat → Nat
  | 0 => 0
  | n + 1 =>
    if (n + 1) % 2 = 0 then 1 + trailingZeros ((n + 1) / 2)
    else 0

/-- An odd number has 0 trailing zeros. -/
theorem trailingZeros_of_odd (k : Nat) (hk : k ≥ 1) (hodd : k % 2 = 1) :
    trailingZeros k = 0 := by
  cases k with
  | zero => omega
  | succ m =>
    simp only [trailingZeros]
    split <;> omega

/-- A positive even number has at least 1 trailing zero. -/
theorem trailingZeros_of_even_pos (k : Nat) (hk : k ≥ 1) (heven : k % 2 = 0) :
    trailingZeros k ≥ 1 := by
  cases k with
  | zero => omega
  | succ m =>
    simp only [trailingZeros]
    split <;> omega

/-- Exact recursive equation for a positive even integer. -/
theorem trailingZeros_of_even (k : Nat) (hk : k ≥ 1) (heven : k % 2 = 0) :
    trailingZeros k = 1 + trailingZeros (k / 2) := by
  cases k with
  | zero => omega
  | succ m =>
    simp only [trailingZeros]
    rw [if_pos heven]

/-- **Global ruler-sequence peak property.** If two positive positions in the
stable trailing-zero sequence have the same value, a strictly larger value lies
between them. This is the number-theoretic core of Wu's `perfect` condition:
a correctly sourced signal returning to an equal-ID group must have crossed a
larger-ID group first.

The proof repeatedly halves equal positive even endpoints. At odd endpoints,
the immediately following even position is the required peak. -/
theorem trailingZeros_repeat_has_higher_between (j : Nat) : ∀ i : Nat,
    0 < i → i < j → trailingZeros i = trailingZeros j →
      ∃ k : Nat, i < k ∧ k < j ∧ trailingZeros i < trailingZeros k := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro i hi hij heq
    rcases Nat.mod_two_eq_zero_or_one i with hieven | hiodd
    · have htzi := trailingZeros_of_even i hi hieven
      have hjpos : 0 < j := by omega
      have hjeven : j % 2 = 0 := by
        rcases Nat.mod_two_eq_zero_or_one j with h | h
        · exact h
        · have htzj := trailingZeros_of_odd j hjpos h
          omega
      have htzj := trailingZeros_of_even j hjpos hjeven
      have hi_repr := Nat.mod_add_div i 2
      have hj_repr := Nat.mod_add_div j 2
      have hi2pos : 0 < i / 2 := by omega
      have hij2 : i / 2 < j / 2 := by omega
      have hj2lt : j / 2 < j := Nat.div_lt_self hjpos (by omega)
      have heq2 : trailingZeros (i / 2) = trailingZeros (j / 2) := by omega
      obtain ⟨k, hik, hkj, hpeak⟩ :=
        ih (j / 2) hj2lt (i / 2) hi2pos hij2 heq2
      refine ⟨2 * k, ?_, ?_, ?_⟩
      · omega
      · omega
      · have hkpos : 0 < 2 * k := by omega
        have hkeven : (2 * k) % 2 = 0 := by omega
        have htzk := trailingZeros_of_even (2 * k) hkpos hkeven
        have hkdiv : (2 * k) / 2 = k :=
          Nat.mul_div_cancel_left k (by omega)
        rw [hkdiv] at htzk
        omega
    · have htzi := trailingZeros_of_odd i hi hiodd
      have hjpos : 0 < j := by omega
      have hjodd : j % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one j with h | h
        · have htzj := trailingZeros_of_even_pos j hjpos h
          omega
        · exact h
      have hik : i < i + 1 := by omega
      have hkj : i + 1 < j := by omega
      have hkeven : (i + 1) % 2 = 0 := by omega
      have htzk := trailingZeros_of_even_pos (i + 1) (by omega) hkeven
      exact ⟨i + 1, hik, hkj, by omega⟩

/-- Operational corollary for the future signal invariant. A signal carrying
the source ruler value cannot both (i) survive only groups whose IDs are at
most its payload and (ii) arrive at a later equal-ID group. -/
theorem trailingZeros_survivor_cannot_match
    (i j : Nat) (hi : 0 < i) (hij : i < j)
    (hSurvives : ∀ k, i < k → k < j → trailingZeros k ≤ trailingZeros i) :
    trailingZeros i ≠ trailingZeros j := by
  intro heq
  obtain ⟨k, hik, hkj, hhigh⟩ :=
    trailingZeros_repeat_has_higher_between j i hi hij heq
  have := hSurvives k hik hkj
  omega

/-! ## Writer-flag arithmetic on the ruler sequence -/

/-- A strict ruler-value lower bound forces the corresponding power of two to
divide the group index. -/
theorem two_pow_succ_dvd_of_lt_trailingZeros
    (i x : Nat) (hi : 0 < i) (hix : x < trailingZeros i) :
    2 ^ (x + 1) ∣ i := by
  induction x generalizing i with
  | zero =>
      rcases Nat.mod_two_eq_zero_or_one i with heven | hodd
      · simpa using (Nat.dvd_iff_mod_eq_zero.mpr heven : 2 ∣ i)
      · have htz := trailingZeros_of_odd i hi hodd
        omega
  | succ x ih =>
      rcases Nat.mod_two_eq_zero_or_one i with heven | hodd
      · have htz := trailingZeros_of_even i hi heven
        have htwo : 2 ∣ i := Nat.dvd_iff_mod_eq_zero.mpr heven
        have hi2 : 0 < i / 2 :=
          Nat.div_pos (by omega) (by omega)
        have hlt : x < trailingZeros (i / 2) := by omega
        obtain ⟨m, hm⟩ := ih (i / 2) hi2 hlt
        have hdvd : 2 ^ (x + 2) ∣ i := by
          refine ⟨m, ?_⟩
          calc
            i = (i / 2) * 2 := (Nat.div_mul_cancel htwo).symm
            _ = (2 ^ (x + 1) * m) * 2 := by rw [hm]
            _ = 2 ^ (x + 2) * m := by
              have hp : 2 ^ (x + 2) = 2 ^ (x + 1) * 2 := by
                rw [show x + 2 = (x + 1).succ by omega, Nat.pow_succ]
              rw [hp]
              ac_rfl
        simpa only [Nat.succ_eq_add_one] using hdvd
      · have htz : trailingZeros i = 0 :=
          trailingZeros_of_odd i hi hodd
        omega

/-- Ruler values characterize divisibility by powers of two. -/
theorem two_pow_dvd_iff_le_trailingZeros
    (i x : Nat) (hi : 0 < i) :
    2 ^ x ∣ i ↔ x ≤ trailingZeros i := by
  constructor
  · intro hdvd
    induction x generalizing i with
    | zero => omega
    | succ x ih =>
        obtain ⟨m, hm⟩ := hdvd
        have hp : 2 ^ (x + 1) = 2 ^ x * 2 := by
          rw [show x + 1 = x.succ by omega, Nat.pow_succ]
        have heven : i % 2 = 0 := by
          apply Nat.dvd_iff_mod_eq_zero.mp
          refine ⟨2 ^ x * m, ?_⟩
          rw [hm, hp]
          ac_rfl
        have htwo : 2 ∣ i := Nat.dvd_iff_mod_eq_zero.mpr heven
        have hi2 : 0 < i / 2 := Nat.div_pos (by omega) (by omega)
        have hdvdHalf : 2 ^ x ∣ i / 2 := by
          refine ⟨m, ?_⟩
          apply Nat.div_eq_of_eq_mul_left (by omega)
          rw [hm, hp]
          ac_rfl
        have hhalf := ih (i / 2) hi2 hdvdHalf
        have htz := trailingZeros_of_even i hi heven
        omega
  · intro hle
    cases x with
    | zero => simp
    | succ x =>
        exact two_pow_succ_dvd_of_lt_trailingZeros i x hi (by omega)

/-- Closed form of the write bit immediately before visiting positive group
`i`: it starts true and flips once for each earlier group whose ruler value is
at least `payload`. -/
def rulerWriterFlagBefore (payload i : Nat) : Bool :=
  decide ((((i - 1) / (2 ^ payload)) % 2) = 0)

private theorem quotient_pred_of_dvd
    (i d : Nat) (hi : 0 < i) (hd : 0 < d) (hdiv : d ∣ i) :
    (i - 1) / d = i / d - 1 := by
  obtain ⟨m, hm⟩ := hdiv
  have hmne : m ≠ 0 := by
    intro hmzero
    subst m
    simp at hm
    omega
  have hmpos : 0 < m := Nat.pos_iff_ne_zero.mpr hmne
  have hlt : 0 < d * m := Nat.mul_pos hd hmpos
  have hpred := Nat.mul_sub_div 0 d m hlt
  simp only [Nat.zero_div, Nat.zero_add] at hpred
  rw [hm, hpred, Nat.mul_div_cancel_left m hd]

private theorem quotient_pred_eq_of_not_dvd
    (i d : Nat) (hi : 0 < i) (hd : 0 < d) (hnot : ¬d ∣ i) :
    (i - 1) / d = i / d := by
  have hmodne : i % d ≠ 0 := by
    intro hzero
    exact hnot (Nat.dvd_iff_mod_eq_zero.mpr hzero)
  have hmodpos : 0 < i % d := Nat.pos_iff_ne_zero.mpr hmodne
  have hmodlt : i % d < d := Nat.mod_lt i hd
  have hdecomp := Nat.mod_add_div i d
  apply Nat.div_eq_of_lt_le
  · have hlower : d * (i / d) ≤ i - 1 := by omega
    simpa [Nat.mul_comm] using hlower
  · have hupper : i - 1 < d * (i / d) + d := by omega
    simpa [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hupper

private theorem decide_even_pred_toggle (q : Nat) (hq : 0 < q) :
    decide (q % 2 = 0) = !decide ((q - 1) % 2 = 0) := by
  rcases Nat.mod_two_eq_zero_or_one q with heven | hodd
  · have hpred : (q - 1) % 2 = 1 := by omega
    simp [heven, hpred]
  · have hpred : (q - 1) % 2 = 0 := by omega
    simp [hodd, hpred]

/-- Exact Algorithm-16/19 flag recurrence on the stable ruler sequence. The
flag flips at group `i` exactly when its ID is at least the payload. -/
theorem rulerWriterFlagBefore_succ
    (payload i : Nat) (hi : 0 < i) :
    rulerWriterFlagBefore payload (i + 1) =
      if payload ≤ trailingZeros i then
        !rulerWriterFlagBefore payload i
      else rulerWriterFlagBefore payload i := by
  have hpow : 0 < 2 ^ payload := Nat.pow_pos (by omega)
  by_cases hle : payload ≤ trailingZeros i
  · have hdvd : 2 ^ payload ∣ i :=
      (two_pow_dvd_iff_le_trailingZeros i payload hi).2 hle
    have hq := quotient_pred_of_dvd i (2 ^ payload) hi hpow hdvd
    have hqpos : 0 < i / 2 ^ payload :=
      Nat.div_pos (Nat.le_of_dvd hi hdvd) hpow
    rw [if_pos hle]
    unfold rulerWriterFlagBefore
    simp only [Nat.add_sub_cancel]
    rw [hq]
    exact decide_even_pred_toggle (i / 2 ^ payload) hqpos
  · have hnot : ¬2 ^ payload ∣ i := by
      intro hdvd
      exact hle ((two_pow_dvd_iff_le_trailingZeros i payload hi).1 hdvd)
    have hq := quotient_pred_eq_of_not_dvd
      i (2 ^ payload) hi hpow hnot
    rw [if_neg hle]
    unfold rulerWriterFlagBefore
    simp only [Nat.add_sub_cancel]
    rw [hq]

private theorem quotient_before_even_power_multiple
    (i x : Nat) (hi : 0 < i) (hdiv : 2 ^ (x + 1) ∣ i) :
    ((i - 1) / (2 ^ x)) % 2 = 1 := by
  obtain ⟨m, hm⟩ := hdiv
  have hpow : 0 < 2 ^ x := Nat.pow_pos (by omega)
  have hmne : m ≠ 0 := by
    intro hmzero
    subst m
    simp at hm
    omega
  have hmpos : 0 < m := Nat.pos_iff_ne_zero.mpr hmne
  have hshape : i = (2 ^ x) * (2 * m) := by
    have hp : 2 ^ (x + 1) = 2 ^ x * 2 := by
      rw [show x + 1 = x.succ by omega, Nat.pow_succ]
    calc
      i = 2 ^ (x + 1) * m := hm
      _ = (2 ^ x) * (2 * m) := by
        rw [hp]
        ac_rfl
  have hlt : 0 < (2 ^ x) * (2 * m) := by
    exact Nat.mul_pos hpow (Nat.mul_pos (by omega) hmpos)
  have hq := Nat.mul_sub_div 0 (2 ^ x) (2 * m) hlt
  simp only [Nat.zero_div, Nat.zero_add] at hq
  rw [hshape]
  rw [hq]
  omega

/-- At every group whose ruler value is strictly larger than the writer
payload, the writer arrives with skip flag zero. -/
theorem rulerWriterFlagBefore_false_of_payload_lt_target
    (i payload : Nat) (hi : 0 < i)
    (hgreater : payload < trailingZeros i) :
    rulerWriterFlagBefore payload i = false := by
  have hdiv := two_pow_succ_dvd_of_lt_trailingZeros i payload hi hgreater
  have hq := quotient_before_even_power_multiple i payload hi hdiv
  simp [rulerWriterFlagBefore, hq]

/-! ## Wu-style free overwriting signals -/

/-- Agent position at offset `k` from a group start. -/
def groupOffset {n : Nat} (ring : DirectedRing n)
    (start : Fin n) (k : Nat) : Fin n :=
  ⟨(start.val + k) % n, Nat.mod_lt _ ring.hn⟩

/-- ID carried by path3 sub-signals aligned over one group. The separate
`isAlignedOverwritingSignalAt` predicate ensures each selected path3 entry has
the expected label and a Boolean-valued bit. -/
def overwritingSignalIDAt {ψ n : Nat} (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (start : Fin n) : Nat :=
  (List.range ψ).foldl (fun acc k =>
    match (C (groupOffset ring start k)).path3 with
    | some p => acc + p.bit * 2 ^ (ψ - 1 - k)
    | none => acc) 0

/-- A complete overwriting signal whose sub-signals are aligned with a group
and share the same write-bit flag. `flag = 1` is Wu's `wb = write`. -/
def isAlignedOverwritingSignalAt {ψ n : Nat} (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (start : Fin n) (flag : Nat) : Prop :=
  flag ≤ 1 ∧ ∀ k : Nat, k < ψ →
    ∃ p : Path3Info,
      (C (groupOffset ring start k)).path3 = some p ∧
      p.label = k ∧ p.bit ≤ 1 ∧ p.flag = flag

/-- Interpreted version of Wu's free-overwriting-signal definition on p.53.
The printed condition 2 says `i ≠ x`, where `x` is trailingZeros(i). Both are
natural numbers, but the test is disconnected from the signal ID used by the
surrounding conditions. We use the signal-ID-connected likely intent
`ID(WS) ≠ trailingZeros(i)`. This interpretation is explicitly tracked as a
thesis ambiguity in `ERRATA.md`. -/
def isFreeOverwritingSignalAt {ψ n : Nat} (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (leaderPos : Fin n) (i : Nat) : Prop :=
  let start : Fin n :=
    ⟨(leaderPos.val + i * ψ) % n, Nat.mod_lt _ ring.hn⟩
  isAlignedOverwritingSignalAt ring C start 1 ∧
  overwritingSignalIDAt ring C start ≠ trailingZeros i ∧
  groupID ring.hn C start > overwritingSignalIDAt ring C start

/-- No free overwriting signal, using the group sequence rooted at the unique
label-zero leader. This replaces the former per-agent write-action shortcut. -/
def noFreeOverwritingSignal {ψ n : Nat} (hψ : ψ > 0)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ) : Prop :=
  ∃ leaderPos : Fin n,
    (C leaderPos).isLeader ∧ (C leaderPos).label = ⟨0, hψ⟩ ∧
    ∀ i : Nat, i > 0 → i < n / ψ →
      ¬isFreeOverwritingSignalAt ring C leaderPos i

/-- Adjacent positive integers have different trailing zero counts.
One of k, k+1 is odd (tz=0) and the other is even (tz≥1). -/
theorem trailingZeros_succ_ne (k : Nat) (hk : k ≥ 1) :
    trailingZeros k ≠ trailingZeros (k + 1) := by
  by_cases h : k % 2 = 0
  · have h1 := trailingZeros_of_even_pos k hk h
    have h2 := trailingZeros_of_odd (k + 1) (by omega) (by omega)
    omega
  · have h1 := trailingZeros_of_odd k hk (by omega)
    have h2 := trailingZeros_of_even_pos (k + 1) (by omega) (by omega)
    omega

/-- A configuration has a perfect/stable ID sequence starting from the leader.
The leader is at the start of group g₀. The groups g₀, g₁, ..., g_{m-1} (where
m = ⌊n/ψ⌋) have IDs forming a specific sequence: for i ≠ 0,
ID(gᵢ) = trailingZeros(i).  This is the integer represented by the group's
ψ bits, not a power of two.

Additionally, all agents have consecutive labels within their groups. -/
def isStableIDSequence {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) : Prop :=
  ∃ leaderPos : Fin n, (C leaderPos).isLeader ∧
    (C leaderPos).label = ⟨0, hψ⟩ ∧
    (∀ k : Nat, k < n →
      let pos : Fin n := ⟨(leaderPos.val + k) % n, Nat.mod_lt _ ring.hn⟩
      (C pos).label = ⟨k % ψ, Nat.mod_lt _ hψ⟩) ∧
    (∀ i : Nat, i > 0 → i < n / ψ →
      let groupStart : Fin n := ⟨(leaderPos.val + i * ψ) % n, Nat.mod_lt _ ring.hn⟩
      groupID ring.hn C groupStart = trailingZeros i)

/-- Consecutive non-leader groups in a stable sequence have distinct IDs.
This is the exact number-theoretic fact available from stability. It does not,
by itself, say that an arbitrary in-flight comparison signal faithfully carries
either group's ID; that requires a separate signal-coherence invariant. -/
theorem stable_adjacent_groupID_ne
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ)
    (hStable : isStableIDSequence hψ ring C)
    (i : Nat) (hi : i ≥ 1) (hnext : i + 1 < n / ψ) :
    ∃ leaderPos : Fin n, (C leaderPos).isLeader ∧
      let gi : Fin n :=
        ⟨(leaderPos.val + i * ψ) % n, Nat.mod_lt _ ring.hn⟩
      let gj : Fin n :=
        ⟨(leaderPos.val + (i + 1) * ψ) % n, Nat.mod_lt _ ring.hn⟩
      groupID ring.hn C gi ≠ groupID ring.hn C gj := by
  obtain ⟨leaderPos, hleader, _, _, hgroups⟩ := hStable
  refine ⟨leaderPos, hleader, ?_⟩
  dsimp only
  have hgi := hgroups i hi (by omega)
  have hgj := hgroups (i + 1) (by omega) hnext
  dsimp only at hgi hgj
  rw [hgi, hgj]
  exact trailingZeros_succ_ne i hi

/-! ## Condition 3 derived from Condition 5 -/

private theorem offset_covers {n : Nat} (hn : n > 0) (lp i : Fin n) :
    ∃ k : Nat, k < n ∧ (lp.val + k) % n = i.val := by
  refine ⟨(i.val + n - lp.val) % n, Nat.mod_lt _ hn, ?_⟩
  by_cases h : lp.val ≤ i.val
  · have h1 : i.val + n - lp.val = n + (i.val - lp.val) := by omega
    rw [h1, add_self_mod, Nat.mod_eq_of_lt (show i.val - lp.val < n by omega)]
    have : lp.val + (i.val - lp.val) = i.val := by omega
    rw [this, Nat.mod_eq_of_lt i.isLt]
  · have h1 : i.val + n - lp.val < n := by omega
    rw [Nat.mod_eq_of_lt h1]
    have h2 : lp.val + (i.val + n - lp.val) = n + i.val := by omega
    rw [h2, add_self_mod, Nat.mod_eq_of_lt i.isLt]

/-- Condition 3 (noFreeBarrier) follows from Condition 5 (isStableIDSequence).
The stable ID sequence forces consecutive labels at all edges except the one
leading back to the leader position. -/
theorem noFreeBarrier_of_stableID
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ)
    (hStable : isStableIDSequence hψ ring C) :
    noFreeBarrier hψ ring C := by
  obtain ⟨lp, hlp_leader, _, hlabels, _⟩ := hStable
  intro i _ hBarrier
  obtain ⟨k, hk, hoff⟩ := offset_covers ring.hn lp i
  have hfin_i : (⟨(lp.val + k) % n, Nat.mod_lt _ ring.hn⟩ : Fin n) = i :=
    Fin.ext hoff
  have hlbl_i := hlabels k hk
  rw [hfin_i] at hlbl_i
  by_cases hkn : k + 1 < n
  · have hlbl_j := hlabels (k + 1) hkn
    have hpos_j : (lp.val + (k + 1)) % n = (i.val + 1) % n := by
      have : lp.val + (k + 1) = lp.val + k + 1 := by omega
      rw [this, ← mod_succ_eq, hoff]
    have hfin_j : (⟨(lp.val + (k + 1)) % n, Nat.mod_lt _ ring.hn⟩ : Fin n) =
        ⟨(i.val + 1) % n, Nat.mod_lt _ ring.hn⟩ := Fin.ext hpos_j
    rw [hfin_j] at hlbl_j
    exfalso; apply hBarrier
    show (C (ring.rightNeighbor i)).label = ⟨((C i).label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
    have h_rn : (C (ring.rightNeighbor i)).label = ⟨(k + 1) % ψ, Nat.mod_lt _ hψ⟩ := hlbl_j
    rw [h_rn, hlbl_i]
    exact Fin.ext (mod_succ_eq k ψ).symm
  · have hk_eq : k = n - 1 := by omega
    show (C (ring.rightNeighbor i)).isLeader
    have h_eq : ring.rightNeighbor i = lp := by
      ext
      show (i.val + 1) % n = lp.val
      calc (i.val + 1) % n
          = ((lp.val + k) % n + 1) % n := by rw [hoff]
        _ = (lp.val + k + 1) % n := mod_succ_eq (lp.val + k) n
        _ = (n + lp.val) % n := by
            have : lp.val + k + 1 = n + lp.val := by omega
            rw [this]
        _ = lp.val % n := add_self_mod lp.val n
        _ = lp.val := Nat.mod_eq_of_lt lp.isLt
    rw [h_eq]
    exact hlp_leader

/-! ## Safe configuration -/

/-- The output-relevant safety kernel for the repaired protocol.  These are
exactly the four facts consumed by the machine-checked conditions 1--3: one
leader, that leader at label zero, peaceful bullets, and no free barrier.  It
intentionally omits Wu's write-signal and group-bit conditions, which are not
preserved by the current repair and are unnecessary for Definition-1 output
safety. -/
structure OutputSafeConfig {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) : Prop where
  unique_leader : hasUniqueLeader n C
  leader_label_zero : ∀ i : Fin n, (C i).isLeader →
    (C i).label = ⟨0, hψ⟩
  no_nonpeaceful_bullet : noNonPeacefulBullet hψ ring C
  no_free_barrier : noFreeBarrier hψ ring C

/-- Wu's five-field safe-configuration schema (Definition 2, p.41),
without additional auxiliary-field coherence. Condition 4 uses the documented
T6 interpretation for complete aligned path3 signals; T8 shows that moving,
partial, and orphan write carriers still need a provenance semantics. The
counterexamples in `Leader.Wu.Safety.Counterexamples` show that this schema is not closed
on arbitrary encoded states. -/
structure PaperSafeConfig {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) : Prop where
  unique_leader : hasUniqueLeader n C
  no_nonpeaceful_bullet : noNonPeacefulBullet hψ ring C
  no_free_barrier : noFreeBarrier hψ ring C
  no_free_overwriting_signal : noFreeOverwritingSignal hψ ring C
  stable_id_sequence : isStableIDSequence hψ ring C

/-- Wu's five-field predicate implies the output-relevant kernel.  The
label-zero fact follows because its stable-sequence root is the unique leader. -/
theorem PaperSafeConfig.toOutputSafe
    {ψ n : Nat} {hψ : ψ > 0} {ring : DirectedRing n}
    {C : Fin n → AgentState ψ} (hSafe : PaperSafeConfig hψ ring C) :
    OutputSafeConfig hψ ring C := by
  refine
    { unique_leader := hSafe.unique_leader
      no_nonpeaceful_bullet := hSafe.no_nonpeaceful_bullet
      no_free_barrier := hSafe.no_free_barrier
      leader_label_zero := ?_ }
  intro i hi
  obtain ⟨uniquePos, _, honly⟩ := hSafe.unique_leader
  obtain ⟨stablePos, hstableLeader, hstableZero, _, _⟩ :=
    hSafe.stable_id_sequence
  have hiUnique : i = uniquePos := honly i hi
  have hstableUnique : stablePos = uniquePos :=
    honly stablePos hstableLeader
  rw [hiUnique, ← hstableUnique]
  exact hstableZero

instance {ψ n : Nat} {hψ : ψ > 0} {ring : DirectedRing n}
    {C : Fin n → AgentState ψ} :
    Coe (PaperSafeConfig hψ ring C) (OutputSafeConfig hψ ring C) where
  coe := PaperSafeConfig.toOutputSafe

/-- Predicate used by the historical conditional closedness proof. It uses
the old per-agent `noActiveWriteAction` approximation and adds quiescence, so it
is neither Wu's condition 4 nor Definition 2. Concrete `ppll` also does not
preserve quiescence. -/
structure QuiescentSafeConfig {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) : Prop where
  unique_leader : hasUniqueLeader n C
  no_nonpeaceful_bullet : noNonPeacefulBullet hψ ring C
  no_free_barrier : noFreeBarrier hψ ring C
  no_active_write_action : noActiveWriteAction ring C
  stable_id_sequence : isStableIDSequence hψ ring C
  quiescent : isQuiescent ring C

/-! ## Closedness status

`Leader.Wu.Safety.ConditionalClosedness` proves an abstract theorem for `QuiescentSafeConfig` under
`ProtocolProperties`. It is not Wu's Lemma 4.1.1 for concrete P_PLL: no concrete
instance exists, quiescence is not preserved, and `PaperSafeConfig` has a
machine-checked one-step counterexample. -/
