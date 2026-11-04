import Leader.PPL.MainTheorem.Whp
import Leader.PPL.MainTheorem.Skeleton
import Leader.PPL.ReachCPB.Assembly
import Leader.PPL.Modes.MidEntryRetimedSplit
import Leader.PPL.Elim.OneLeaderBoundLeaves
import Leader.PPL.Convergence.QuietWindow
import Leader.PPL.Elim.LiteralBridges
import Leader.PPL.Safety.PeacefulScan
import Leader.Wu.Scheduler.RepeatedBlocks

/-!
# Superseded (log-window route): dead declarations of `Leader/PPL/MainTheorem/Whp.lean`

Moved out of `Leader/PPL/MainTheorem/Whp.lean` by the P_PL Theorem 1 cleanup, phase 2.
These declarations served only the original psi <= log2 n + 1 route to
`PPL.theorem1Statement_proved`, which now goes through
`PPL.theorem1Statement_proved_via_slack` (`Leader/PPL/MainTheorem/PsiWindowSlack.lean`).
Nothing in the live Theorem 1 closure uses them; they are kept, and still build,
as the record of that route.  Every name `PPL.X` became `PPL.Superseded.LogWindow.X`;
see `research-map/RENAME_MAP_PPL.md` (phase 2).
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
namespace PPL.Superseded.LogWindow

theorem theorem1_countP_four_union_le
    {A : Type}
    (xs : List A)
    (bad b1 b2 b3 b4 : A → Bool)
    (hcover :
      ∀ x, x ∈ xs →
        bad x = true →
          b1 x = true ∨
          b2 x = true ∨
          b3 x = true ∨
          b4 x = true) :
    xs.countP bad ≤
      xs.countP b1 +
        xs.countP b2 +
        xs.countP b3 +
        xs.countP b4 := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have htail :
          ∀ y, y ∈ xs →
            bad y = true →
              b1 y = true ∨
              b2 y = true ∨
              b3 y = true ∨
              b4 y = true := by
        intro y hy hbad
        exact hcover y (by simp [hy]) hbad
      have hi := ih htail
      cases hbad : bad x with
      | false =>
          cases h1 : b1 x <;>
            cases h2 : b2 x <;>
              cases h3 : b3 x <;>
                cases h4 : b4 x <;>
                  simp
                    [List.countP_cons,
                      hbad, h1, h2, h3, h4]
                    at hi ⊢ <;>
                  omega
      | true =>
          have hx :=
            hcover x (by simp) hbad
          cases h1 : b1 x <;>
            cases h2 : b2 x <;>
              cases h3 : b3 x <;>
                cases h4 : b4 x <;>
                  simp
                    [List.countP_cons,
                      hbad, h1, h2, h3, h4]
                    at hx hi ⊢ <;>
                  omega

/--
A denominator-cleared phase estimate at horizon T pads to a larger horizon H:
each bad T-prefix has exactly n^(H-T) possible scheduler suffixes.
-/
theorem theorem1_pad_phase_bound
    {n T H c F : Nat}
    (hTH : T ≤ H)
    (hbound :
      n * F ≤ c * n ^ T) :
    n * (F * n ^ (H - T)) ≤
      c * n ^ H := by
  calc
    n * (F * n ^ (H - T)) =
        (n * F) * n ^ (H - T) :=
      (Nat.mul_assoc n F (n ^ (H - T))).symm
    _ ≤
        (c * n ^ T) * n ^ (H - T) :=
      Nat.mul_le_mul_right
        (n ^ (H - T)) hbound
    _ =
        c * (n ^ T * n ^ (H - T)) := by
      rw [Nat.mul_assoc]
    _ =
        c * n ^ (T + (H - T)) := by
      rw [Nat.pow_add]
    _ = c * n ^ H := by
      rw [Nat.add_sub_of_le hTH]

/--
For the source-faithful route that also counts the omitted Lemma-5(ii) quiet
event, the coefficient is still only 26.
-/
theorem theorem1_five_event_constants
    (n H : Nat) :
    12 * n ^ H +
        8 * n ^ H +
        4 * n ^ H +
        n ^ H +
        n ^ H ≤
      64 * n ^ H := by
  omega

end PPL.Superseded.LogWindow
end
