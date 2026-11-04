import Leader.L3.Headline.Statement

/-!
The separate four-color protocol of Proposition prop:four, equation (F.27).
Consumer: L3 board, row H1b. Times count real uniform ring-edge services.
-/

namespace L3

open FiniteUniformStoppingTree
open LeaderCountDyadicTail
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false

/-- The four-state F.27 table. Consumer: L3 board H1b. -/
@[reducible] def fourAgentProtocol : PopulationProtocol where
  Q := Fin 4
  Y := Bool
  transition := fun x _ => (x, x + 1)
  output := fun c => c == (0 : Fin 4)

/-- All four physical ring edges are satisfied. Consumer: L3 board H1b. -/
def fourAgentTarget (ring : DirectedRing 4) :
    fourAgentProtocol.Configuration 4 → Prop :=
  fun C => ∀ i : Fin 4, C (ring.rightNeighbor i) = C i + 1

/-- The actual F.27 edge for finite-word counting.
Consumer: L3 board H1b, fourAgentWordHits and fourAgentExpected. -/
private def fourAgentNext (ring : DirectedRing 4) :
    fourAgentProtocol.Configuration 4 → Fin 4 →
      fourAgentProtocol.Configuration 4 :=
  fun C e => fourAgentProtocol.step ring C e

/-- A satisfied edge frames its full configuration.
Consumer: L3 board H1b, fourAgentClosed and fourAgentSafe. -/
theorem fourAgentFixed (ring : DirectedRing 4)
    (C : fourAgentProtocol.Configuration 4)
    (hC : fourAgentTarget ring C) (e : Fin 4) :
    fourAgentProtocol.step ring C e = C := by
  funext i
  by_cases hie : i = e
  · subst hie
    simp [PopulationProtocol.step, fourAgentProtocol]
  · by_cases hij : i = ring.rightNeighbor e
    · subst hij
      have h := hC e
      simp [PopulationProtocol.step, fourAgentProtocol, hie, h]
    · simp [PopulationProtocol.step, fourAgentProtocol, hie, hij]

/-- Closed under every physical edge. Consumer: L3 board H1b. -/
theorem fourAgentClosed (ring : DirectedRing 4) :
    PopulationProtocol.ClosedPred fourAgentProtocol ring
      (fourAgentTarget ring) := by
  intro C hC C' hstep
  obtain ⟨e, he⟩ := hstep
  rw [he, fourAgentFixed ring C hC e]
  exact hC

/-- Four physical indices, from the Fin bound.
Consumer: L3 board H1b, fourAgentTargetColors and fourAgentWordHits. -/
private theorem fourAgentPositionCases (i : Fin 4) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  have hi : i.val < 4 := i.isLt
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  rcases h with h | h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))

/-- Each physical color is the first color plus its offset.
Consumer: L3 board H1b, fourAgentSafe. -/
private theorem fourAgentTargetColors (ring : DirectedRing 4)
    (C : fourAgentProtocol.Configuration 4)
    (hC : fourAgentTarget ring C) :
    ∀ i : Fin 4, C i = C 0 + i := by
  have hfirst : C 1 = C 0 + 1 := hC 0
  have hsecond : C 2 = C 1 + 1 := hC 1
  have hthird : C 3 = C 2 + 1 := hC 2
  have hadd2 : ∀ a : Fin 4, a + 1 + 1 = a + 2 := by decide
  have hadd3 : ∀ a : Fin 4, a + 2 + 1 = a + 3 := by decide
  have hadd0 : ∀ a : Fin 4, a = a + 0 := by decide
  have htwo : C 2 = C 0 + 2 := by
    rw [hsecond, hfirst]
    exact hadd2 (C 0)
  have hthree : C 3 = C 0 + 3 := by
    rw [hthird, htwo]
    exact hadd3 (C 0)
  intro i
  rcases fourAgentPositionCases i with hi | hi | hi | hi
  · rw [hi]
    exact hadd0 (C 0)
  · rw [hi]
    exact hfirst
  · rw [hi]
    exact htwo
  · rw [hi]
    exact hthree

/-- A translate of the four residues has exactly one zero.
Consumer: L3 board H1b, fourAgentSafe. -/
private theorem fourAgentUniqueZero :
    ∀ a : Fin 4, ∃ i : Fin 4,
      (a + i == (0 : Fin 4)) = true ∧
      ∀ j : Fin 4, (a + j == (0 : Fin 4)) = true → j = i := by
  decide

/-- Exactly one permanent physical leader, for every future word.
Consumer: L3 board H1b, IsSafe headline conjunct. -/
theorem fourAgentSafe (ring : DirectedRing 4) :
    ∀ C, fourAgentTarget ring C →
      PopulationProtocol.IsSafe fourAgentProtocol ring C (fun b => b) := by
  intro C hC
  have hcolors := fourAgentTargetColors ring C hC
  obtain ⟨i, hzero, hunique⟩ := fourAgentUniqueZero (C 0)
  refine ⟨⟨i, ?_, ?_⟩, ?_⟩
  · change (C i == (0 : Fin 4)) = true
    rw [hcolors i]
    exact hzero
  · intro j hj
    change (C j == (0 : Fin 4)) = true at hj
    rw [hcolors j] at hj
    exact hunique j hj
  · intro D hreach j
    have hcl : PopulationProtocol.ClosedPred fourAgentProtocol ring
        (fun D => D = C) := by
      intro D hD D' hstep
      obtain ⟨e, he⟩ := hstep
      rw [he, hD]
      exact fourAgentFixed ring C hC e
    have hD : D = C := PopulationProtocol.ClosedPred.reachable hcl rfl hreach
    rw [hD]

/-- The value of a ring edge update at one site. Consumer: L3 board H1b. -/
private theorem fourAgentStepApply (ring : DirectedRing 4)
    (C : fourAgentProtocol.Configuration 4) (e k : Fin 4) :
    fourAgentProtocol.step ring C e k =
      if k = e then C e else
        if k = ring.rightNeighbor e then C e + 1 else C k := rfl

/-- Any three consecutive edges create the whole satisfied cycle.
Consumer: L3 board H1b, fourAgentThreeMiss. -/
theorem fourAgentWordHits (ring : DirectedRing 4)
    (C : fourAgentProtocol.Configuration 4) (start : Fin 4) :
    fourAgentTarget ring
      (fourAgentNext ring
        (fourAgentNext ring
          (fourAgentNext ring C start)
          (ring.rightNeighbor start))
        (ring.rightNeighbor (ring.rightNeighbor start))) := by
  have h0 : ring.rightNeighbor (0 : Fin 4) = 1 := rfl
  have h1 : ring.rightNeighbor (1 : Fin 4) = 2 := rfl
  have h2 : ring.rightNeighbor (2 : Fin 4) = 3 := rfl
  have h3 : ring.rightNeighbor (3 : Fin 4) = 0 := rfl
  intro i
  rcases fourAgentPositionCases start with hs | hs | hs | hs <;> subst hs
  all_goals
    rcases fourAgentPositionCases i with hi | hi | hi | hi <;> subst hi
  all_goals
    simp only [fourAgentNext, fourAgentStepApply, h0, h1, h2, h3]
    simp <;>
      exact (by decide : ∀ a : Fin 4, a = a + 1 + 1 + 1 + 1) _

/-- Four-way scheduler sum under a pointwise bound.
Consumer: L3 board H1b, fourAgentThreeMiss. -/
private theorem fourAgentSumAll (f : Fin 4 → Nat) (a : Nat)
    (h : ∀ i, f i ≤ a) :
    (List.ofFn f).sum ≤ 4 * a := by
  calc
    (List.ofFn f).sum ≤ (List.ofFn (fun _ : Fin 4 => a)).sum :=
      ofFn_sum_le f (fun _ => a) h
    _ = 4 * a := ofFn_sum_const 4 a

/-- One nominated scheduler edge has a smaller contribution.
Consumer: L3 board H1b, fourAgentThreeMiss. -/
private theorem fourAgentSumExcept (f : Fin 4 → Nat) (special : Fin 4)
    (a b : Nat) (hall : ∀ i, f i ≤ a) (hspecial : f special ≤ b) :
    (List.ofFn f).sum ≤ 3 * a + b := by
  have hpoint : ∀ i, f i ≤ if i = special then b else a := by
    intro i
    by_cases hi : i = special
    · subst i
      simpa using hspecial
    · simpa [hi] using hall i
  have hsum := ofFn_sum_le f
    (fun i : Fin 4 => if i = special then b else a) hpoint
  have hvalue :
      (List.ofFn (fun i : Fin 4 => if i = special then b else a)).sum =
        3 * a + b := by
    rcases fourAgentPositionCases special with hs | hs | hs | hs
    all_goals
      subst special
      simp [List.ofFn_succ] <;> omega
  rw [hvalue] at hsum
  exact hsum

/-- At most 63 of the 64 length-three words miss the target.
Consumer: L3 board H1b, fourAgentCostBound. -/
private theorem fourAgentThreeMiss (ring : DirectedRing 4)
    (C : fourAgentProtocol.Configuration 4) :
    wordSum (fourAgentNext ring)
      (miss (fourAgentTarget ring)) C 3 ≤ 63 := by
  classical
  have hgood :
      fourAgentTarget ring
        (fourAgentNext ring
          (fourAgentNext ring (fourAgentNext ring C 0) 1) 2) := by
    change fourAgentTarget ring
      (fourAgentNext ring
        (fourAgentNext ring (fourAgentNext ring C 0)
          (ring.rightNeighbor 0))
        (ring.rightNeighbor (ring.rightNeighbor 0)))
    exact fourAgentWordHits ring C 0
  have hgoodzero :
      miss (fourAgentTarget ring)
        (fourAgentNext ring
          (fourAgentNext ring (fourAgentNext ring C 0) 1) 2) = 0 := by
    simp [miss, hgood]
  have hinner (D : fourAgentProtocol.Configuration 4) :
      (List.ofFn (fun g : Fin 4 =>
        miss (fourAgentTarget ring) (fourAgentNext ring D g))).sum ≤ 4 := by
    have h := fourAgentSumAll
      (fun g : Fin 4 =>
        miss (fourAgentTarget ring) (fourAgentNext ring D g)) 1
      (fun g => miss_le_one (fourAgentTarget ring) _)
    simpa using h
  have hspecial :
      (List.ofFn (fun g : Fin 4 =>
        miss (fourAgentTarget ring)
          (fourAgentNext ring
            (fourAgentNext ring (fourAgentNext ring C 0) 1) g))).sum ≤ 3 := by
    have h := fourAgentSumExcept
      (fun g : Fin 4 =>
        miss (fourAgentTarget ring)
          (fourAgentNext ring
            (fourAgentNext ring (fourAgentNext ring C 0) 1) g))
      (2 : Fin 4) 1 0
      (fun g => miss_le_one (fourAgentTarget ring) _)
      (by simp [hgoodzero])
    simpa using h
  have hmiddle (D : fourAgentProtocol.Configuration 4) :
      (List.ofFn (fun f : Fin 4 =>
        (List.ofFn (fun g : Fin 4 =>
          miss (fourAgentTarget ring)
            (fourAgentNext ring (fourAgentNext ring D f) g))).sum)).sum ≤ 16 := by
    have h := fourAgentSumAll
      (fun f : Fin 4 =>
        (List.ofFn (fun g : Fin 4 =>
          miss (fourAgentTarget ring)
            (fourAgentNext ring (fourAgentNext ring D f) g))).sum)
      4 (fun f => hinner (fourAgentNext ring D f))
    simpa using h
  have hmiddleSpecial :
      (List.ofFn (fun f : Fin 4 =>
        (List.ofFn (fun g : Fin 4 =>
          miss (fourAgentTarget ring)
            (fourAgentNext ring
              (fourAgentNext ring (fourAgentNext ring C 0) f) g))).sum)).sum ≤ 15 := by
    have h := fourAgentSumExcept
      (fun f : Fin 4 =>
        (List.ofFn (fun g : Fin 4 =>
          miss (fourAgentTarget ring)
            (fourAgentNext ring
              (fourAgentNext ring (fourAgentNext ring C 0) f) g))).sum)
      (1 : Fin 4) 4 3
      (fun f => hinner (fourAgentNext ring (fourAgentNext ring C 0) f))
      hspecial
    simpa using h
  have houter :
      (List.ofFn (fun e : Fin 4 =>
        (List.ofFn (fun f : Fin 4 =>
          (List.ofFn (fun g : Fin 4 =>
            miss (fourAgentTarget ring)
              (fourAgentNext ring
                (fourAgentNext ring (fourAgentNext ring C e) f) g))).sum)).sum)).sum ≤ 63 := by
    have h := fourAgentSumExcept
      (fun e : Fin 4 =>
        (List.ofFn (fun f : Fin 4 =>
          (List.ofFn (fun g : Fin 4 =>
            miss (fourAgentTarget ring)
              (fourAgentNext ring
                (fourAgentNext ring (fourAgentNext ring C e) f) g))).sum)).sum)
      (0 : Fin 4) 16 15
      (fun e => hmiddle (fourAgentNext ring C e))
      hmiddleSpecial
    simpa using h
  change
    (List.ofFn (fun e : Fin 4 =>
      (List.ofFn (fun f : Fin 4 =>
        (List.ofFn (fun g : Fin 4 =>
          miss (fourAgentTarget ring)
            (fourAgentNext ring
              (fourAgentNext ring (fourAgentNext ring C e) f) g))).sum)).sum)).sum ≤ 63
  exact houter

/-- The 192-interaction first-hit cost bound at every finite horizon.
Consumer: L3 board H1b, fourAgentExpected. -/
private theorem fourAgentCostBound (ring : DirectedRing 4) :
    ∀ T C, costNumerator (fourAgentNext ring)
      (fourAgentTarget ring) C T ≤ 4 ^ T * 192 := by
  classical
  have hclosed : ∀ C e, fourAgentTarget ring C →
      fourAgentTarget ring (fourAgentNext ring C e) := by
    intro C e hC
    change fourAgentTarget ring (fourAgentProtocol.step ring C e)
    rw [fourAgentFixed ring C hC e]
    exact hC
  intro T
  induction T using Nat.strongRecOn with
  | ind T ih =>
      intro C
      by_cases hsmall : T ≤ 3
      · have hsmallBound : T ≤ 192 := by omega
        exact Nat.le_trans
          (costNumerator_le_horizon
            (fourAgentNext ring) (fourAgentTarget ring) C T)
          (Nat.mul_le_mul_left (4 ^ T) hsmallBound)
      · have hbefore : T - 3 < T := by omega
        have hsplit : T = 3 + (T - 3) := by omega
        have hpoint :
            ∀ D : fourAgentProtocol.Configuration 4,
              costNumerator (fourAgentNext ring)
                (fourAgentTarget ring) D (T - 3) ≤
                (4 ^ (T - 3) * 192) * miss (fourAgentTarget ring) D := by
          intro D
          by_cases hD : fourAgentTarget ring D
          · rw [costNumerator_terminal (fourAgentNext ring)
                (fourAgentTarget ring) D hD]
            exact Nat.zero_le _
          · simpa [miss, hD] using ih (T - 3) hbefore D
        have htail := wordSum_mono (fourAgentNext ring)
          (fun D => costNumerator (fourAgentNext ring)
            (fourAgentTarget ring) D (T - 3))
          (fun D => (4 ^ (T - 3) * 192) * miss (fourAgentTarget ring) D)
          hpoint C 3
        rw [wordSum_mul] at htail
        have hmass := fourAgentThreeMiss ring C
        have hsplitEq := costNumerator_split (fourAgentNext ring)
          (fourAgentTarget ring) hclosed C 3 (T - 3)
        rw [← hsplit] at hsplitEq
        calc
          costNumerator (fourAgentNext ring) (fourAgentTarget ring) C T =
              4 ^ (T - 3) *
                costNumerator (fourAgentNext ring) (fourAgentTarget ring) C 3 +
              wordSum (fourAgentNext ring)
                (fun D => costNumerator (fourAgentNext ring)
                  (fourAgentTarget ring) D (T - 3)) C 3 :=
            hsplitEq
          _ ≤ 4 ^ (T - 3) * (4 ^ 3 * 3) +
                (4 ^ (T - 3) * 192) * 63 := by
            apply Nat.add_le_add
            · exact Nat.mul_le_mul_left _
                (costNumerator_le_horizon
                  (fourAgentNext ring) (fourAgentTarget ring) C 3)
            · exact Nat.le_trans htail
                (Nat.mul_le_mul_left _ hmass)
          _ = 4 ^ T * 192 := by
            calc
              4 ^ (T - 3) * (4 ^ 3 * 3) +
                  (4 ^ (T - 3) * 192) * 63 =
                  4 ^ (T - 3) * (64 * 3 + 192 * 63) := by
                rw [show (4 : Nat) ^ 3 = 64 by decide]
                simp only [Nat.mul_add, Nat.mul_assoc]
              _ = 4 ^ (T - 3) * (64 * 192) := by
                rw [show 64 * 3 + 192 * 63 = 64 * 192 by decide]
              _ = 4 ^ T * 192 := by
                calc
                  4 ^ (T - 3) * (64 * 192) =
                      (4 ^ 3 * 4 ^ (T - 3)) * 192 := by
                    rw [show (4 : Nat) ^ 3 = 64 by decide]
                    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
                  _ = 4 ^ T * 192 := by
                    rw [← Nat.pow_add, ← hsplit]

/-- Almost-sure first entrance and expectation at most 192, using
the existing finite-word cost equivalence. Consumer: L3 board H1b. -/
theorem fourAgentExpected (ring : DirectedRing 4) :
    ∀ C0 : fourAgentProtocol.Configuration 4,
      UniformFirstHit.ExpectedHittingTimeAtMost
        (fun D e => fourAgentProtocol.step ring D e)
        (fourAgentTarget ring) C0 192 := by
  intro C0
  change UniformFirstHit.ExpectedHittingTimeAtMost
    (fourAgentNext ring) (fourAgentTarget ring) C0 (192 : Rat)
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (fourAgentNext ring) (fourAgentTarget ring)
    (by decide : 0 < (4 : Nat)) C0 192).2
  intro T
  exact fourAgentCostBound ring T C0

/-- The n = 4 clause of thm:main: four states, permanent unique leader and
192-interaction bound. Consumer: L3 board H1b. -/
def L3FourAgentHeadline (ring : DirectedRing 4) : Prop :=
  (∃ N : Nat, N ≤ 4 ∧
    ∃ decode : Fin N → Fin 4,
      (∀ i j, decode i = decode j → i = j) ∧
      ∀ a, ∃ i, decode i = a) ∧
  ∃ G : fourAgentProtocol.Configuration 4 → Prop,
    PopulationProtocol.ClosedPred fourAgentProtocol ring G ∧
    (∀ C, G C →
      PopulationProtocol.IsSafe fourAgentProtocol ring C (fun b => b)) ∧
    ∀ C0,
      UniformFirstHit.ExpectedHittingTimeAtMost
        (fun D e => fourAgentProtocol.step ring D e) G C0 192

/-- Four states, permanent unique leader and 192-interaction bound.
Consumer: L3 board H1b, exceptional n=4 clause of thm:main. -/
theorem l3FourAgentHeadline (ring : DirectedRing 4) :
    L3FourAgentHeadline ring := by
  constructor
  · refine ⟨4, by decide, (fun i : Fin 4 => i), ?_, ?_⟩
    · intro i j h
      exact h
    · intro a
      exact ⟨a, rfl⟩
  · exact ⟨fourAgentTarget ring, fourAgentClosed ring,
      fourAgentSafe ring, fourAgentExpected ring⟩

end L3

#print axioms L3.fourAgentFixed
#print axioms L3.fourAgentClosed
#print axioms L3.fourAgentSafe
#print axioms L3.fourAgentExpected
#print axioms L3.l3FourAgentHeadline
