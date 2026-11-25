import Leader.L4.WindowA0ClosedEntry
import Leader.L4.WindowA0Restart
import Leader.L4.WindowFiveStages
import Leader.L4.FastRestart

/-! L1: keep pre-drain states on raw words. Choose the physical
restart seed and its door only at the first drained prefix. No scheduler
labels are changed, skipped, or conditioned upon. -/
namespace L4.WindowA0Bridge
open TripleRenewal WindowFiveStages WindowClock RootedAssembly
open Classical TaggedTail

private theorem edge_sum_le {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i ≤ g i) :
    sumEdge f ≤ sumEdge g := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons]
    exact Nat.add_le_add (h _) (ih (fun i => h i.succ))

/-- A pathwise implication into the word target suffices: the word
transaction may have additional legitimate reasons to stop. -/
theorem word_cost_le {n : Nat} {α : Type} (step : α → Fin n → α)
    (goal : α → Prop) (hit : Word n → Prop) (read : Word n → α)
    (commute : ∀ u e, read (wordNext u e) = step (read u) e)
    (stop : ∀ u, goal (read u) → hit u) (t : Nat) (u : Word n) :
    iidHitCost wordNext hit t u ≤ iidHitCost step goal t (read u) := by
  induction t generalizing u with
  | zero => exact Nat.le_refl _
  | succ t ih =>
    by_cases hu : hit u
    · rw [iidHitCost_of_target _ _ _ hu]
      exact Nat.zero_le _
    · have hv : ¬goal (read u) := fun h => hu (stop u h)
      rw [iidHitCost, if_neg hu, iidHitCost, if_neg hv]
      apply Nat.add_le_add_left
      apply edge_sum_le
      intro i
      rw [← commute]
      exact ih (wordNext u i)

/-- Use the same raw-edge word with a restart seed chosen at prefix `u`.
The continuation is defined on every suffix, including padding after
the first stop. -/
theorem mean_at_prefix {n : Nat} {α : Type} (step : α → Fin n → α)
    (goal : α → Prop) (hit : Word n → Prop) (u : Word n) (seed : α)
    (accept : ∀ v, goal (GGTiming.runMarks step seed v) → hit (u++v))
    {B : Nat} (clock : IIDExpectedHittingTimeAtMost step goal seed B) :
    IIDExpectedHittingTimeAtMost wordNext hit u B := by
  intro t
  suffices h : ∀ v, iidHitCost wordNext hit t (u++v) ≤
      iidHitCost step goal t (GGTiming.runMarks step seed v) by
    simpa only [List.append_nil,GGTiming.runMarks] using
      Nat.le_trans (h []) (clock t)
  induction t with
  | zero => intro v; exact Nat.le_refl _
  | succ t ih =>
    intro v
    by_cases hv : hit (u++v)
    · rw [iidHitCost_of_target _ _ _ hv]
      exact Nat.zero_le _
    · have hn : ¬goal (GGTiming.runMarks step seed v) := fun h => hv (accept v h)
      rw [iidHitCost,if_neg hv,iidHitCost,if_neg hn]
      apply Nat.add_le_add_left
      apply edge_sum_le
      intro i
      simpa only [wordNext, List.append_assoc, GGTiming.runMarks_append,
        GGTiming.runMarks] using ih (v++[i])

/-- The state-side half-block restart, on the closed drained set.
No premise of closure of the terminal word predicate is needed. -/
theorem state_block_mean {p c n : Nat} (hn : 4≤n) (initial : Config p c n)
    (scope : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat)
    (trials : ∀ z, WindowA0ClosedEntry.Admitted initial scope J H z →
      ¬WindowA0Ledger.done z.tag →
      Nonempty (UniformAttempt (WindowA0ClosedEntry.next scope)
        (fun x => WindowA0Ledger.done x.tag) (WindowA0ClosedEntry.Admitted initial scope J H)
        (WindowA0Restart.attemptCost c n H) (WindowA0Restart.attempts c) z))
    (z : WindowA0ClosedEntry.State p c n)
    (hz : WindowA0ClosedEntry.Admitted initial scope J H z) :
    IIDExpectedHittingTimeAtMost (WindowA0ClosedEntry.next scope)
      (fun x => WindowA0Ledger.done x.tag) z
      (2*(4*(3*WindowA0Restart.attempts c)*WindowA0Restart.attemptCost c n H)) := by
  have hn' : 0<n := by omega
  apply FastRestart.mean_of_half_block _ _ _
    (WindowA0ClosedEntry.close hn scope J H)
  · apply Nat.mul_pos (Nat.mul_pos (by decide) (Nat.mul_pos (by decide)
      (Nat.pow_pos (by decide))))
    unfold WindowA0Restart.attemptCost
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) hn') (by omega)
  · exact WindowA0Restart.half_block_of_attempts _ _ _ hn' c H trials
  · exact hz

/-- Timing part of slot 4. The preparation and final hit are on words;
the drained state and its physical door are produced separately at
each reachable terminal cut. The result does not assert the physical
drain, the construction of that cut, or the uniform-attempt premise. -/
theorem entry_mean_of_cut {p c n s : Nat}
    (initial : Config p c n) (scope : WindowA0Ledger.Scope n)
    (prepHit hit : Word n → Prop)
    (prepMean : IIDExpectedHittingTimeAtMost wordNext prepHit [] (17*n*(s+1)))
    (cut : ∀ u, FirstExit prepHit u → ¬hit u →
      ∃ (J : Fin n) (H : Nat) (seed : WindowA0ClosedEntry.State p c n),
        H ≤ 2*s ∧ WindowA0ClosedEntry.Admitted initial scope J H seed ∧
        ∀ v, WindowA0Ledger.done
          (GGTiming.runMarks (WindowA0ClosedEntry.next scope) seed v).tag → hit (u++v))
    (trials : ∀ J H, H≤2*s →
      ∀ z, WindowA0ClosedEntry.Admitted initial scope J H z →
      ¬WindowA0Ledger.done z.tag →
      Nonempty (UniformAttempt (WindowA0ClosedEntry.next scope)
        (fun x => WindowA0Ledger.done x.tag) (WindowA0ClosedEntry.Admitted initial scope J H)
        (WindowA0Restart.attemptCost c n H) (WindowA0Restart.attempts c) z)) :
    IIDExpectedHittingTimeAtMost wordNext hit []
      (WindowA0Restart.entryKSharp c*n*(s+1)) := by
  let prep := suffixStage ([] : Word n) prepHit
  let B := WindowA0Restart.attempts c*(16*(2*c+3)*n*(2*(s+1)))
  have P : IIDExpectedHittingTimeAtMost prep.next prep.ready prep.start (17*n*(s+1)) := by
    intro t
    change iidHitCost wordNext (FirstExit prepHit) t [] ≤ _
    rw [cost_firstExit prepHit t [] (clean_nil _)]
    exact prepMean t
  have h := expected_with_preparation prep hit _ B P (fun u _ hu hn => by
    change FirstExit prepHit u at hu
    change ¬hit u at hn
    change IIDExpectedHittingTimeAtMost wordNext hit u B
    obtain ⟨J,H,z,hH,hz,accept⟩ := cut u hu hn
    apply mean_at_prefix _ (fun x => WindowA0Ledger.done x.tag) hit u z accept
    apply expected_mono (WindowA0Restart.drained_mean _ _ _ c H (trials J H hH) z hz)
    unfold B WindowA0Restart.attemptCost
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega)))
  apply expected_mono h
  calc
    _ ≤ 64*n*(s+1)+B := Nat.add_le_add_right
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right n (by decide))) _
    _ = WindowA0Restart.entryKSharp c*n*(s+1) := by
      unfold WindowA0Restart.entryKSharp B
      rw [Nat.add_mul,Nat.add_mul]
      congr 1
      rw [show (32 : Nat) = 16*2 by decide]
      ac_rfl

/-- Printed half-block constants, keyed to the same cut witness as
the sharp form. The choice of door at the prep cut is not made at time zero. -/
theorem entry_block_mean_of_cut {p c n s : Nat} (hn : 4≤n)
    (initial : Config p c n) (scope : WindowA0Ledger.Scope n)
    (prepHit hit : Word n → Prop)
    (prepMean : IIDExpectedHittingTimeAtMost wordNext prepHit [] (17*n*(s+1)))
    (cut : ∀ u, FirstExit prepHit u → ¬hit u →
      ∃ (J : Fin n) (H : Nat) (seed : WindowA0ClosedEntry.State p c n),
        H ≤ 2*s ∧ WindowA0ClosedEntry.Admitted initial scope J H seed ∧
        ∀ v, WindowA0Ledger.done
          (GGTiming.runMarks (WindowA0ClosedEntry.next scope) seed v).tag → hit (u++v))
    (trials : ∀ J H, H≤2*s →
      ∀ z, WindowA0ClosedEntry.Admitted initial scope J H z →
      ¬WindowA0Ledger.done z.tag →
      Nonempty (UniformAttempt (WindowA0ClosedEntry.next scope)
        (fun x => WindowA0Ledger.done x.tag) (WindowA0ClosedEntry.Admitted initial scope J H)
        (WindowA0Restart.attemptCost c n H) (WindowA0Restart.attempts c) z)) :
    IIDExpectedHittingTimeAtMost wordNext hit []
      (WindowA0Restart.entryK c*n*(s+1)) := by
  let prep := suffixStage ([] : Word n) prepHit
  let B := 2*(4*(3*WindowA0Restart.attempts c)*(16*(2*c+3)*n*(2*(s+1))))
  have P : IIDExpectedHittingTimeAtMost prep.next prep.ready prep.start (17*n*(s+1)) := by
    intro t
    change iidHitCost wordNext (FirstExit prepHit) t [] ≤ _
    rw [cost_firstExit prepHit t [] (clean_nil _)]
    exact prepMean t
  have h := expected_with_preparation prep hit _ B P (fun u _ hu hnHit => by
    change FirstExit prepHit u at hu
    change ¬hit u at hnHit
    change IIDExpectedHittingTimeAtMost wordNext hit u B
    obtain ⟨J,H,z,hH,hz,accept⟩ := cut u hu hnHit
    apply mean_at_prefix _ (fun x => WindowA0Ledger.done x.tag) hit u z accept
    apply expected_mono (state_block_mean hn initial scope J H (trials J H hH) z hz)
    unfold B WindowA0Restart.attemptCost
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))))
  apply expected_mono h
  calc
    _ ≤ 64*n*(s+1)+B := Nat.add_le_add_right
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right n (by decide))) _
    _ = WindowA0Restart.entryK c*n*(s+1) := by
      unfold WindowA0Restart.entryK B
      rw [Nat.add_mul,Nat.add_mul]
      congr 1
      rw [show (768 : Nat) = 2*4*3*16*2 by decide]
      ac_rfl

#print axioms state_block_mean
#print axioms entry_block_mean_of_cut
#print axioms word_cost_le
#print axioms mean_at_prefix
#print axioms entry_mean_of_cut
end L4.WindowA0Bridge
