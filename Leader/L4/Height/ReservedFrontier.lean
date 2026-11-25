import Leader.L4.Height.ClockHead

namespace L4.Height

open Classical

/-- The first aligned phase-zero frontier strictly beyond the warmup
margin and the whole recovered ring. -/
def publicationFrontier (base m : Nat) : Nat :=
  32 * ((base + m + 200) / 32 + 1)

/-- The next multiple is strictly above its argument and within one
multiple. This form also covers an empty index alphabet. -/
private theorem publication_frontier_rounding (base m : Nat) :
    base + m + 200 < publicationFrontier base m ∧
      publicationFrontier base m ≤ base + m + 232 := by
  have hrem : (base + m + 200) % 32 < 32 :=
    Nat.mod_lt _ (by decide)
  have hdiv := Nat.mod_add_div (base + m + 200) 32
  unfold publicationFrontier
  constructor <;> omega

/-- The smallest member of a finite list, allowing an explicit seed. -/
private theorem frontier_list_minimum (a : Nat) (xs : List Nat) :
    ∃ v, (v = a ∨ v ∈ xs) ∧
      v ≤ a ∧ ∀ b, b ∈ xs → v ≤ b := by
  induction xs generalizing a with
  | nil =>
      exact ⟨a, Or.inl rfl, Nat.le_refl _, by simp⟩
  | cons b xs ih =>
      obtain ⟨v, hv, hvb, hvs⟩ := ih b
      by_cases ha : a ≤ v
      · refine ⟨a, Or.inl rfl, Nat.le_refl _, ?_⟩
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact Nat.le_trans ha hvb
        · exact Nat.le_trans ha (hvs c hc)
      · refine ⟨v, Or.inr ?_, by omega, ?_⟩
        · rcases hv with hv | hv
          · exact List.mem_cons.mpr (Or.inl hv)
          · exact List.mem_cons.mpr (Or.inr hv)
        · intro c hc
          rcases List.mem_cons.mp hc with rfl | hc
          · exact hvb
          · exact hvs c hc

/-- A nonempty finite ring has an attained minimum of its chosen lifts. -/
private theorem frontier_minimum_exists {m : Nat} (hm : 0 < m)
    (lift : Fin m → Nat) :
    ∃ base, (∃ i, lift i = base) ∧ ∀ j, base ≤ lift j := by
  obtain ⟨base, hmem, _, hfloor⟩ :=
    frontier_list_minimum (lift ⟨0, hm⟩) (List.ofFn lift)
  refine ⟨base, ?_, ?_⟩
  · rcases hmem with he | he
    · exact ⟨⟨0, hm⟩, he.symm⟩
    · obtain ⟨i, hi⟩ := List.mem_ofFn.mp he
      exact ⟨i, hi⟩
  · intro j
    exact hfloor _ (List.mem_ofFn.mpr ⟨j, rfl⟩)

/-- Recovery has a coherent coset even at the small one-site modulus
allowed by the weaker StageTwo parameter predicate. For two or more
sites the usual recovered coset theorem applies without changing its
hypotheses. -/
private theorem recovered_coset_exists
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : Recover.Chain.ClockChain α n m B M hm)
    (hM : Recover.StageTwo.ClockParams M) (hmP : m < M / 2)
    (x : α) (hx : Recover.Chain.LgSet C x) :
    ∃ lift : Fin m → Nat, LegitCoset M hm ⟨C.cfg x, lift⟩ := by
  by_cases hsingle : m = 1
  · let lift : Fin m → Nat :=
      fun i => (C.cfg x i).tick % (M / 2)
    refine ⟨lift, ?_⟩
    refine ⟨hx.1, ?_, ?_, ?_, hx.2.1⟩
    · intro i
      dsimp [lift]
      simp only [Nat.mod_mod]
    · intro i j _
      have hij : i = j := by
        apply Fin.ext
        have hi := i.isLt
        have hj := j.isLt
        omega
      subst j
      exact ⟨Nat.le_succ _, Nat.le_succ _⟩
    · intro i
      exact (hx.2.2 i).1
  · have hmTwo : 2 ≤ m := by omega
    have hClock : ClockParams M := by
      refine ⟨?_, hM.2⟩
      omega
    obtain ⟨lift, _, hc⟩ :=
      lgSet_coset C x hx hmP hClock 0
    exact ⟨lift, hc⟩

/-- An attained minimum of a recovered coherent relift is the true
floor. The next phase-zero frontier is above every current lift and
its reserved successor, and the trial ends at the specified cap+1. -/
theorem recovered_publication_frontier
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : Recover.Chain.ClockChain α n m B M hm)
    (hM : Recover.StageTwo.ClockParams M) (hmP : m < M / 2)
    (x : α) (hx : Recover.Chain.LgSet C x) :
    ∃ (lift : Fin m → Nat) (base : Nat),
      (∃ i, lift i = base) ∧
      (∀ i, base ≤ lift i) ∧
      LegitCoset M hm ⟨C.cfg x, lift⟩ ∧
      (publicationFrontier base m) % 32 = 0 ∧
      (∀ i, lift i + 200 < publicationFrontier base m) ∧
      publicationFrontier base m + 32 * (2 ^ 19 * m) + 1 - base ≤
        m + 233 + 32 * (2 ^ 19 * m) := by
  obtain ⟨lift, hc⟩ :=
    recovered_coset_exists C hM hmP x hx
  obtain ⟨base, hmin, hfloor⟩ :=
    frontier_minimum_exists hm lift
  have hfront := clock_aligned_frontier hm base
  have hzero : publicationFrontier base m % 32 = 0 := by
    simpa only [publicationFrontier] using hfront.1
  have habove :
      base + m + 200 < publicationFrontier base m := by
    simpa only [publicationFrontier] using hfront.2.1
  have hupper :
      publicationFrontier base m ≤ base + m + 232 :=
    (publication_frontier_rounding base m).2
  refine ⟨lift, base, hmin, hfloor, hc, hzero, ?_, ?_⟩
  · intro i
    have hspread :=
      clock_lift_le_floor hm lift hc.near base hmin i
    omega
  · omega

/-- A reservation from the current or immediately succeeding level
cannot belong to a fresh aligned trial after the warmup margin. -/
theorem reserved_keys_below_frontier {m base : Nat}
    (lift : Fin m → Nat)
    (hSpread : ∀ i, lift i ≤ base + m)
    (reserved : Fin m → Option Nat)
    (hReserved : ∀ i k, reserved i = some k → k ≤ lift i + 1) :
    ∀ i k, reserved i = some k →
      k + 2 < publicationFrontier base m := by
  intro i k hk
  have hsite := hSpread i
  have hkey := hReserved i k hk
  have habove := (publication_frontier_rounding base m).1
  omega

end L4.Height

