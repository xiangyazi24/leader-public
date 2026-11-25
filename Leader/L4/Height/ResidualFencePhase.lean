import Leader.L4.Height.ResidualEscrow

namespace L4.Height.ResidualFencePhase
open Classical

/-- Escrow is prepaid once for this residual attempt. These are history
phases of the chosen attempt, not decoded physical opcodes. -/
inductive Phase where
  | reserve | active | spent
  deriving DecidableEq

/-- Instantiate the escrow fields of the residual Bellman argument,
without using publication as a substitute for attempt termination.
The concrete caller still owes FENCE exit cost on the actual steered
chain, plus this phase transition contract and the serial rank laws. -/
theorem exists_fence_fields {S : Type} {n : Nat}
    (hn : 0<n) (next : S→Fin n→S) (Q attemptEnded : S→Prop)
    (phase : S→Phase) (F : Nat)
    (closed : ∀ y e,Q y→Q (next y e))
    (noRefund : ∀ y e,Q y→¬attemptEnded y→¬attemptEnded (next y e)→
      phase y=.active → phase (next y e)≠.reserve)
    (noRearm : ∀ y e,Q y→¬attemptEnded y→¬attemptEnded (next y e)→
      phase y=.spent → phase (next y e)=.spent)
    (bound : ∀ y,Q y→IIDExpectedHittingTimeAtMost next
      (fun z=>phase z≠.active ∨ attemptEnded z) y F) :
    ∃ E : S→Nat,
      (∀ y,E y≤2*F) ∧ (∀ y,attemptEnded y→E y=0) ∧
      (∀ y,Q y→¬attemptEnded y→phase y=.active →
        n+(List.ofFn (fun e : Fin n=>E (next y e))).sum≤n*E y) ∧
      (∀ y e,Q y→¬attemptEnded y→phase y≠.active→E (next y e)≤E y) ∧
      (∀ y e,Q y→¬attemptEnded y→phase y=.active→phase (next y e)≠.active→E (next y e)=0) := by
  let hit := fun z=>phase z≠.active ∨ attemptEnded z
  obtain ⟨U,cap,zero,drift⟩ := ResidualEscrow.exists_escrow hn next Q hit F closed bound
  let E := fun y=>if attemptEnded y then 0 else
    match phase y with
    | .reserve => 2*F
    | .active => U y
    | .spent => 0
  have B (y : S) : E y≤2*F := by
    unfold E
    split
    · exact Nat.zero_le _
    · cases phase y
      · exact Nat.le_refl _
      · exact cap y
      · exact Nat.zero_le _
  have Z (y : S) (done : attemptEnded y) : E y=0 := by simp only [E,if_pos done]
  have agree (y : S) (e : Fin n) (hq : Q y) (h : ¬attemptEnded y)
      (active : phase y=.active) : E (next y e)=U (next y e) := by
    by_cases endNext : attemptEnded (next y e)
    · exact (Z _ endNext).trans (zero _ (.inr endNext)).symm
    cases p : phase (next y e)
    · exact False.elim (noRefund y e hq h endNext active p)
    · simp only [E,if_neg endNext,p]
    · have zeroNext := zero (next y e) (.inl (by rw [p]; decide))
      simp only [E,if_neg endNext,p,zeroNext]
  refine ⟨E,B,Z,?_,?_,?_⟩
  · intro y hq h hf
    have T := drift y hq (show ¬hit y from fun D=>D.elim (fun A=>A hf) h)
    have Eq := sum_ofFn_eq (fun e=>E (next y e)) (fun e=>U (next y e))
      (fun e=>agree y e hq h hf)
    rw [Eq]
    simpa only [E,if_neg h,hf] using T
  · intro y e hq h Hf
    cases p : phase y
    · simpa only [E,if_neg h,p] using B (next y e)
    · exact False.elim (Hf p)
    · by_cases endNext : attemptEnded (next y e)
      · rw [Z _ endNext]
        exact Nat.zero_le _
      · have P := noRearm y e hq h endNext p
        simp only [E,if_neg h,if_neg endNext,P,p,Nat.le_refl]
  · intro y e hq h hf off
    rw [agree y e hq h hf]
    exact zero _ (.inl off)

/-- Doubling the 128-unit clearance allowance for Nat rounding
still fits the published per-cycle coefficient. -/
theorem doubled_reserve_budget {W chart H : Nat} (pos : 0<W)
    (hc : chart≤11*W) (hh : H≤2*W) :
    420*(4*chart+10)+256*H≤23192*W ∧
    420*(4*chart+10)+256*H<2^15*W := by omega

#print axioms exists_fence_fields
#print axioms doubled_reserve_budget
end L4.Height.ResidualFencePhase
