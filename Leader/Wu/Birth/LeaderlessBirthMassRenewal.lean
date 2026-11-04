import Leader.Wu.Birth.ReacquireReentryMass

set_option autoImplicit false

/-! # Uniform birth mass implies a geometric first-leader tail

Candidate route for B4/B7 (not adopted; recorded as a checked reduction).  Instead of the two-phase
Carrier/Reacquire rank contract, assume one uniform leaf over *all* leaderless configurations:

  every leaderless configuration makes a leader appear within `L` literal scheduler letters on at least
  a `1/Q` fraction of the words of length `L`.

The class of leaderless configurations is closed under words along which no leader appears, so no
closure, rank or monotonicity clause is needed.  `alive_tail` is the resulting geometric tail on the
exact number of length `k * L` words that keep every prefix endpoint leaderless, and
`leaderless_tail_one_over_n` is its `1/n` corollary at `Q = 8` with `k = 6 * (log2 n + 1)`.

The generic part (`AliveAlong`, `aliveBit`, `alive_tail`) holds for any step function and any predicate
`Good`; the instance is the literal physical step `currentStep2` with `Good = Leaderless`. -/

namespace BirthLeaderlessBirthMassRenewal

open PPLL PPLLRepair PPLLResearchFormulation PPLLExpiringComparisonRepair
open FiniteUniformStoppingTree BirthWaitPassive

section Generic

variable {S : Type} {n : Nat}

/-- Every prefix endpoint of `u` from `x` satisfies `Good`. -/
def AliveAlong (step : S → Fin n → S) (Good : S → Prop) (x : S) : List (Fin n) → Prop
  | [] => Good x
  | e :: u => Good x ∧ AliveAlong step Good (step x e) u

noncomputable def aliveBit (step : S → Fin n → S) (Good : S → Prop) (x : S) (u : List (Fin n)) : Nat := by
  classical
  exact if AliveAlong step Good x u then 1 else 0

theorem aliveAlong_good {step : S → Fin n → S} {Good : S → Prop} {x : S} :
    ∀ {u : List (Fin n)}, AliveAlong step Good x u → Good x
  | [], h => h
  | _ :: _, h => h.1

theorem aliveAlong_append (step : S → Fin n → S) (Good : S → Prop) :
    ∀ (x : S) (u v : List (Fin n)),
      AliveAlong step Good x (u ++ v) ↔
        AliveAlong step Good x u ∧ AliveAlong step Good (u.foldl step x) v
  | x, [], v => by
      simp only [List.nil_append, List.foldl_nil]
      constructor
      · intro h
        exact ⟨aliveAlong_good (step := step) (Good := Good) (x := x) (u := v) h, h⟩
      · intro h
        exact h.2
  | x, e :: u, v => by
      simp only [List.cons_append, AliveAlong, List.foldl_cons]
      rw [aliveAlong_append step Good (step x e) u v]
      constructor
      · rintro ⟨hx, hu, hv⟩
        exact ⟨⟨hx, hu⟩, hv⟩
      · rintro ⟨⟨hx, hu⟩, hv⟩
        exact ⟨hx, hu, hv⟩

theorem aliveBit_append (step : S → Fin n → S) (Good : S → Prop) (x : S) (u v : List (Fin n)) :
    aliveBit step Good x (u ++ v) =
      aliveBit step Good x u * aliveBit step Good (u.foldl step x) v := by
  classical
  unfold aliveBit
  by_cases hu : AliveAlong step Good x u
  · by_cases hv : AliveAlong step Good (u.foldl step x) v
    · have h := (aliveAlong_append step Good x u v).2 ⟨hu, hv⟩
      simp [h, hu, hv]
    · have h : ¬ AliveAlong step Good x (u ++ v) := fun h =>
        hv ((aliveAlong_append step Good x u v).1 h).2
      simp [h, hu, hv]
  · have h : ¬ AliveAlong step Good x (u ++ v) := fun h =>
      hu ((aliveAlong_append step Good x u v).1 h).1
    simp [h, hu]

theorem aliveBit_le_one (step : S → Fin n → S) (Good : S → Prop) (x : S) (u : List (Fin n)) :
    aliveBit step Good x u ≤ 1 := by
  classical
  unfold aliveBit
  split <;> omega

theorem good_of_aliveBit_pos (step : S → Fin n → S) (Good : S → Prop) (x : S) (u : List (Fin n))
    (h : 0 < aliveBit step Good x u) : Good (u.foldl step x) := by
  classical
  unfold aliveBit at h
  split at h
  · rename_i hu
    have := (aliveAlong_append step Good x u []).1 (by simpa using hu)
    exact this.2
  · omega

end Generic

section WordSums

private theorem wordSum_congr_length
    {n T : Nat} (f g : List (Fin n) -> Nat)
    (h : forall u : List (Fin n), u.length = T -> f u = g u) :
    FixedSpanRenewalPayload.wordSum n T f =
      FixedSpanRenewalPayload.wordSum n T g := by
  rw [<- FixedSpanRenewalPayload.rawWord_sum n T f,
    <- FixedSpanRenewalPayload.rawWord_sum n T g]
  apply FiniteUniformStoppingTree.ofFn_sum_eq
  intro i
  exact h _ (FixedSpanRenewalPayload.rawWord_length n T i)

private theorem wordSum_mono_length
    {n T : Nat} (f g : List (Fin n) -> Nat)
    (h : forall u : List (Fin n), u.length = T -> f u <= g u) :
    FixedSpanRenewalPayload.wordSum n T f <=
      FixedSpanRenewalPayload.wordSum n T g := by
  rw [<- FixedSpanRenewalPayload.rawWord_sum n T f,
    <- FixedSpanRenewalPayload.rawWord_sum n T g]
  apply FiniteUniformStoppingTree.ofFn_sum_le
  intro i
  exact h _ (FixedSpanRenewalPayload.rawWord_length n T i)

private theorem wordSum_mul_left
    (n T c : Nat) (f : List (Fin n) -> Nat) :
    FixedSpanRenewalPayload.wordSum n T (fun u => c * f u) =
      c * FixedSpanRenewalPayload.wordSum n T f := by
  rw [<- FixedSpanRenewalPayload.rawWord_sum n T (fun u => c * f u),
    <- FixedSpanRenewalPayload.rawWord_sum n T f]
  exact FiniteUniformStoppingTree.ofFn_sum_mul_left c _

private theorem wordSum_horizon_add
    (n T U : Nat) (f : List (Fin n) -> Nat) :
    FixedSpanRenewalPayload.wordSum n (T + U) f =
      FixedSpanRenewalPayload.wordSum n T
        (fun u => FixedSpanRenewalPayload.wordSum n U
          (fun v => f (u ++ v))) := by
  induction T generalizing f with
  | zero =>
      simp [FixedSpanRenewalPayload.wordSum, allSchedules]
  | succ T ih =>
      rw [Nat.succ_add]
      change
        FixedSpanRenewalPayload.wordSum n (T + U + 1) f =
          FixedSpanRenewalPayload.wordSum n (T + 1)
            (fun u => FixedSpanRenewalPayload.wordSum n U
              (fun v => f (u ++ v)))
      rw [FixedSpanRenewalPayload.wordSum_succ,
        FixedSpanRenewalPayload.wordSum_succ]
      apply FiniteUniformStoppingTree.ofFn_sum_eq
      intro e
      simpa only [List.cons_append] using
        ih (f := fun w => f (e :: w))

private theorem wordSum_const (n T c : Nat) :
    FixedSpanRenewalPayload.wordSum n T (fun _ => c) = c * n ^ T := by
  rw [<- FixedSpanRenewalPayload.rawWord_sum n T (fun _ => c)]
  simp only [FiniteUniformStoppingTree.ofFn_sum_const]
  exact Nat.mul_comm _ _

end WordSums

section Tail

variable {S : Type} {n : Nat}

/-- Exact number of length-`T` words along which every prefix endpoint stays `Good`. -/
noncomputable def aliveCount (step : S → Fin n → S) (Good : S → Prop) (x : S) (T : Nat) : Nat :=
  FixedSpanRenewalPayload.wordSum n T (aliveBit step Good x)

/-- The uniform escape-mass leaf: from every `Good` state, at most a `(Q-1)/Q` fraction of the words of
length `L` stay `Good` along every prefix. -/
def UniformEscapeMass (step : S → Fin n → S) (Good : S → Prop) (L Q : Nat) : Prop :=
  ∀ x, Good x → Q * aliveCount step Good x L ≤ (Q - 1) * n ^ L

/-- Geometric tail over `k` consecutive blocks of `L` letters. -/
theorem alive_tail (step : S → Fin n → S) (Good : S → Prop) (L Q : Nat)
    (hmass : UniformEscapeMass step Good L Q) :
    ∀ (k : Nat) (x : S), Good x →
      Q ^ k * aliveCount step Good x (k * L) ≤ (Q - 1) ^ k * n ^ (k * L) := by
  intro k
  induction k with
  | zero =>
      intro x hx
      simp only [Nat.pow_zero, Nat.one_mul, Nat.zero_mul]
      unfold aliveCount
      calc FixedSpanRenewalPayload.wordSum n 0 (aliveBit step Good x)
          ≤ FixedSpanRenewalPayload.wordSum n 0 (fun _ => 1) :=
            wordSum_mono_length _ _ (fun u _ => aliveBit_le_one step Good x u)
        _ = 1 := by rw [wordSum_const]; simp
  | succ k ih =>
      intro x hx
      have hsplit : aliveCount step Good x ((k + 1) * L) =
          FixedSpanRenewalPayload.wordSum n L
            (fun u => aliveBit step Good x u * aliveCount step Good (u.foldl step x) (k * L)) := by
        unfold aliveCount
        rw [show (k + 1) * L = L + k * L by rw [Nat.succ_mul]; omega, wordSum_horizon_add]
        apply wordSum_congr_length
        intro u _
        rw [← wordSum_mul_left]
        apply wordSum_congr_length
        intro v _
        exact aliveBit_append step Good x u v
      have hpoint : ∀ u : List (Fin n), u.length = L →
          Q ^ k * (aliveBit step Good x u * aliveCount step Good (u.foldl step x) (k * L)) ≤
            ((Q - 1) ^ k * n ^ (k * L)) * aliveBit step Good x u := by
        intro u _
        by_cases hpos : 0 < aliveBit step Good x u
        · have hgood := good_of_aliveBit_pos step Good x u hpos
          have h1 : aliveBit step Good x u = 1 := by
            have := aliveBit_le_one step Good x u
            omega
          rw [h1, Nat.one_mul, Nat.mul_one]
          exact ih _ hgood
        · have h0 : aliveBit step Good x u = 0 := by omega
          simp [h0]
      have hsum :
          Q ^ k * aliveCount step Good x ((k + 1) * L) ≤
            ((Q - 1) ^ k * n ^ (k * L)) * aliveCount step Good x L := by
        rw [hsplit, ← wordSum_mul_left]
        unfold aliveCount
        rw [← wordSum_mul_left]
        exact wordSum_mono_length _ _ hpoint
      have hm := hmass x hx
      calc Q ^ (k + 1) * aliveCount step Good x ((k + 1) * L)
          = Q * (Q ^ k * aliveCount step Good x ((k + 1) * L)) := by
            rw [Nat.pow_succ]; ac_rfl
        _ ≤ Q * (((Q - 1) ^ k * n ^ (k * L)) * aliveCount step Good x L) :=
            Nat.mul_le_mul_left Q hsum
        _ = ((Q - 1) ^ k * n ^ (k * L)) * (Q * aliveCount step Good x L) := by ac_rfl
        _ ≤ ((Q - 1) ^ k * n ^ (k * L)) * ((Q - 1) * n ^ L) :=
            Nat.mul_le_mul_left _ hm
        _ = (Q - 1) ^ (k + 1) * n ^ ((k + 1) * L) := by
            rw [Nat.pow_succ, show (k + 1) * L = k * L + L by rw [Nat.succ_mul], Nat.pow_add]
            ac_rfl

/-- `1/n` corollary at `Q = 8`: `k = 6 * (log2 n + 1)` blocks suffice. -/
theorem tail_one_over_n (step : S → Fin n → S) (Good : S → Prop) (L : Nat)
    (hmass : UniformEscapeMass step Good L 8) (hn : 2 ≤ n) (x : S) (hx : Good x) :
    n * aliveCount step Good x (6 * (Nat.log2 n + 1) * L) ≤ n ^ (6 * (Nat.log2 n + 1) * L) := by
  let s := Nat.log2 n + 1
  have ht := alive_tail step Good L 8 hmass (6 * s) x hx
  have hpow : n ≤ 2 ^ s := by
    simpa [s] using (LeaderCountDyadicTail.log_parameters n hn).2.2.2
  -- 2 * 7^6 ≤ 8^6, hence 2^s * 7^(6s) ≤ 8^(6s)
  have hbase : 2 * 7 ^ 6 ≤ 8 ^ 6 := by decide
  have hratio : 2 ^ s * 7 ^ (6 * s) ≤ 8 ^ (6 * s) := by
    have h1 : (2 * 7 ^ 6) ^ s ≤ (8 ^ 6) ^ s := Nat.pow_le_pow_left hbase s
    rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at h1
    exact h1
  calc n * aliveCount step Good x (6 * s * L)
      ≤ 2 ^ s * aliveCount step Good x (6 * s * L) := Nat.mul_le_mul_right _ hpow
    _ ≤ n ^ (6 * s * L) := by
        -- multiply by 7^(6s) and compare with the tail bound
        have hpos : 0 < 7 ^ (6 * s) := Nat.pow_pos (by decide)
        refine Nat.le_of_mul_le_mul_left ?_ hpos
        calc 7 ^ (6 * s) * (2 ^ s * aliveCount step Good x (6 * s * L))
            = (2 ^ s * 7 ^ (6 * s)) * aliveCount step Good x (6 * s * L) := by ac_rfl
          _ ≤ 8 ^ (6 * s) * aliveCount step Good x (6 * s * L) := Nat.mul_le_mul_right _ hratio
          _ ≤ (8 - 1) ^ (6 * s) * n ^ (6 * s * L) := ht
          _ = 7 ^ (6 * s) * n ^ (6 * s * L) := rfl

/-- Restricted-class version: the mass is only required on a class `R` that is closed under single
steps (for example the configurations reachable from a Carrier start). -/
def UniformEscapeMassOn (step : S → Fin n → S) (Good R : S → Prop) (L Q : Nat) : Prop :=
  ∀ x, R x → Good x → Q * aliveCount step Good x L ≤ (Q - 1) * n ^ L

theorem closed_foldl (step : S → Fin n → S) (R : S → Prop) (hR : ∀ x e, R x → R (step x e)) :
    ∀ (u : List (Fin n)) (x : S), R x → R (u.foldl step x)
  | [], _, hx => hx
  | e :: u, x, hx => closed_foldl step R hR u (step x e) (hR x e hx)

theorem alive_tail_on (step : S → Fin n → S) (Good R : S → Prop) (L Q : Nat)
    (hR : ∀ x e, R x → R (step x e))
    (hmass : UniformEscapeMassOn step Good R L Q) :
    ∀ (k : Nat) (x : S), R x → Good x →
      Q ^ k * aliveCount step Good x (k * L) ≤ (Q - 1) ^ k * n ^ (k * L) := by
  intro k
  induction k with
  | zero =>
      intro x _ hx
      simp only [Nat.pow_zero, Nat.one_mul, Nat.zero_mul]
      unfold aliveCount
      calc FixedSpanRenewalPayload.wordSum n 0 (aliveBit step Good x)
          ≤ FixedSpanRenewalPayload.wordSum n 0 (fun _ => 1) :=
            wordSum_mono_length _ _ (fun u _ => aliveBit_le_one step Good x u)
        _ = 1 := by rw [wordSum_const]; simp
  | succ k ih =>
      intro x hxR hx
      have hsplit : aliveCount step Good x ((k + 1) * L) =
          FixedSpanRenewalPayload.wordSum n L
            (fun u => aliveBit step Good x u * aliveCount step Good (u.foldl step x) (k * L)) := by
        unfold aliveCount
        rw [show (k + 1) * L = L + k * L by rw [Nat.succ_mul]; omega, wordSum_horizon_add]
        apply wordSum_congr_length
        intro u _
        rw [← wordSum_mul_left]
        apply wordSum_congr_length
        intro v _
        exact aliveBit_append step Good x u v
      have hpoint : ∀ u : List (Fin n), u.length = L →
          Q ^ k * (aliveBit step Good x u * aliveCount step Good (u.foldl step x) (k * L)) ≤
            ((Q - 1) ^ k * n ^ (k * L)) * aliveBit step Good x u := by
        intro u _
        by_cases hpos : 0 < aliveBit step Good x u
        · have hgood := good_of_aliveBit_pos step Good x u hpos
          have h1 : aliveBit step Good x u = 1 := by
            have := aliveBit_le_one step Good x u
            omega
          rw [h1, Nat.one_mul, Nat.mul_one]
          exact ih _ (closed_foldl step R hR u x hxR) hgood
        · have h0 : aliveBit step Good x u = 0 := by omega
          simp [h0]
      have hsum :
          Q ^ k * aliveCount step Good x ((k + 1) * L) ≤
            ((Q - 1) ^ k * n ^ (k * L)) * aliveCount step Good x L := by
        rw [hsplit, ← wordSum_mul_left]
        unfold aliveCount
        rw [← wordSum_mul_left]
        exact wordSum_mono_length _ _ hpoint
      have hm := hmass x hxR hx
      calc Q ^ (k + 1) * aliveCount step Good x ((k + 1) * L)
          = Q * (Q ^ k * aliveCount step Good x ((k + 1) * L)) := by
            rw [Nat.pow_succ]; ac_rfl
        _ ≤ Q * (((Q - 1) ^ k * n ^ (k * L)) * aliveCount step Good x L) :=
            Nat.mul_le_mul_left Q hsum
        _ = ((Q - 1) ^ k * n ^ (k * L)) * (Q * aliveCount step Good x L) := by ac_rfl
        _ ≤ ((Q - 1) ^ k * n ^ (k * L)) * ((Q - 1) * n ^ L) :=
            Nat.mul_le_mul_left _ hm
        _ = (Q - 1) ^ (k + 1) * n ^ ((k + 1) * L) := by
            rw [Nat.pow_succ, show (k + 1) * L = k * L + L by rw [Nat.succ_mul], Nat.pow_add]
            ac_rfl

/-- `1/n` corollary of the restricted-class tail at `Q = 8`. -/
theorem tail_one_over_n_on (step : S → Fin n → S) (Good R : S → Prop) (L : Nat)
    (hR : ∀ x e, R x → R (step x e))
    (hmass : UniformEscapeMassOn step Good R L 8) (hn : 2 ≤ n) (x : S) (hxR : R x) (hx : Good x) :
    n * aliveCount step Good x (6 * (Nat.log2 n + 1) * L) ≤ n ^ (6 * (Nat.log2 n + 1) * L) := by
  let s := Nat.log2 n + 1
  have ht := alive_tail_on step Good R L 8 hR hmass (6 * s) x hxR hx
  have hpow : n ≤ 2 ^ s := by
    simpa [s] using (LeaderCountDyadicTail.log_parameters n hn).2.2.2
  have hbase : 2 * 7 ^ 6 ≤ 8 ^ 6 := by decide
  have hratio : 2 ^ s * 7 ^ (6 * s) ≤ 8 ^ (6 * s) := by
    have h1 : (2 * 7 ^ 6) ^ s ≤ (8 ^ 6) ^ s := Nat.pow_le_pow_left hbase s
    rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at h1
    exact h1
  calc n * aliveCount step Good x (6 * s * L)
      ≤ 2 ^ s * aliveCount step Good x (6 * s * L) := Nat.mul_le_mul_right _ hpow
    _ ≤ n ^ (6 * s * L) := by
        have hpos : 0 < 7 ^ (6 * s) := Nat.pow_pos (by decide)
        refine Nat.le_of_mul_le_mul_left ?_ hpos
        calc 7 ^ (6 * s) * (2 ^ s * aliveCount step Good x (6 * s * L))
            = (2 ^ s * 7 ^ (6 * s)) * aliveCount step Good x (6 * s * L) := by ac_rfl
          _ ≤ 8 ^ (6 * s) * aliveCount step Good x (6 * s * L) := Nat.mul_le_mul_right _ hratio
          _ ≤ (8 - 1) ^ (6 * s) * n ^ (6 * s * L) := ht
          _ = 7 ^ (6 * s) * n ^ (6 * s * L) := rfl

end Tail

section Instance

variable {n psi kappa tau : Nat}

abbrev FC (n psi kappa tau : Nat) := BirthPhaseWait2BlockProgress.FC n psi kappa tau

/-- No raw cell is a leader. -/
def Leaderless (C : FC n psi kappa tau) : Prop := ∀ i, (raw (C i)).leader = false

/-- The candidate uniform leaf on the literal physical step: every leaderless configuration makes a
leader appear within `L` letters on at least one eighth of the words. -/
def UniformLeaderlessBirthMass (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) (L : Nat) : Prop :=
  UniformEscapeMass (S := FC n psi kappa tau)
    (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring) Leaderless L 8

/-- Checked reduction: the uniform leaf gives the `1/n` no-leader tail over `6 (log2 n + 1)` blocks. -/
theorem leaderless_tail_one_over_n (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) (L : Nat)
    (hmass : UniformLeaderlessBirthMass (kappa := kappa) (tau := tau) hpsi h2 ring L)
    (hn : 2 ≤ n) (C : FC n psi kappa tau) (hC : Leaderless C) :
    n * aliveCount (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring) Leaderless C
        (6 * (Nat.log2 n + 1) * L) ≤
      n ^ (6 * (Nat.log2 n + 1) * L) :=
  tail_one_over_n _ _ L hmass hn C hC

end Instance

end BirthLeaderlessBirthMassRenewal
