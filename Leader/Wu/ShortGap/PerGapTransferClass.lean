import Leader.Wu.ShortGap.PerGapOffPay

set_option autoImplicit false

namespace PerGapOffPay

/-!
TWELVE-ROW OWNERSHIP TABLE — evidence-only.

The labels below concern PER-GAP OWNERSHIP migration, not merely whether a
scheduled pair changes local fields.  No physical ownership projection or
proof locating each guarded pair relative to a gap boundary has been supplied,
so lifecycle names alone are not used as geometry facts.

1. freshFlush      — UNDETERMINED
   Shown effect changes flush/raw staging on the pair; owner relevance and
   boundary geometry are not established.

2. freshLaunch     — UNDETERMINED
   Starts fresh control state; the tag does not establish whether the pair is
   interior to one ownership domain or is a boundary pair.

3. freshForward    — UNDETERMINED
   Advances fresh control across the scheduled pair; missing guard geometry
   prevents deciding interior motion versus ownership-boundary crossing.

4. retireFused     — UNDETERMINED
   Combines retirement/drain updates; no shown ownership projection says
   whether those role changes reassign a gap.

5. retireLaunch    — UNDETERMINED
   Creates retirement-witness/drain state; pair geometry is not established.

6. retireBackward  — UNDETERMINED
   Moves witness/control backward across the pair; whether that edge is inside
   one gap or at an ownership boundary is not established.

7. retireDeposit   — UNDETERMINED
   Completes retirement bookkeeping and clears witness state; ownership effect
   is not determined by the shown update alone.

8. adoptDeposit    — CROSSES-A-BOUNDARY at the control/payload level
   The shown effect consumes right-side payload into left-side adoption state
   and clears the right-side payload/carrier.  Identifying this pair with a
   particular formal gap boundary still requires a geometry lemma.

9. directAdopt     — UNDETERMINED
   Consumes already-local left payload and commits left adoption while the
   right endpoint is unchanged; provenance/ownership semantics are missing.

10. handoffArm     — UNDETERMINED
    Arms a future send on the left endpoint while the right endpoint is
    unchanged; whether ownership changes at arming or only later is missing.

11. demotion       — UNDETERMINED
    A distinct role-changing tag is known, but its concrete row update and the
    ownership projection needed for this classification have not been shown.

12. core           — UNDETERMINED
    Wraps an arbitrary core Rule; a uniform classification requires the core
    rule cases, their row effects, and the ownership projection.
-/

/-- A scheduler edge is exceptional for gap `g` exactly when it raises that
component's potential. -/
def transferAt {State Gap : Type} {n : Nat}
    (next : State → Fin n → State)
    (Phi : Gap → State → Nat)
    (g : Gap) (s : State) (e : Fin n) : Prop :=
  Phi g (next s e) > Phi g s

/--
Derived no-transfer makes the `quiet` half of `OrdinaryLocality` automatic.
The `frame` half remains a genuine spatial-locality fact, supplied here as
`frameOutside`.
-/
theorem ordinaryLocality_of_derived
    {State Gap : Type} {n : Nat}
    (next : State → Fin n → State)
    (Phi : Gap → State → Nat)
    (enabled : Gap → State → Prop)
    (touches : Gap → State → Fin n → Prop)
    (frameOutside :
      ∀ g s e, ¬ touches g s e →
        Phi g (next s e) = Phi g s) :
    OrdinaryLocality next Phi
      (fun s => ∀ g e, ¬ transferAt next Phi g s e)
      enabled touches := by
  refine ⟨?_, ?_⟩
  · intro g s e _ hnotTouches
    exact frameOutside g s e hnotTouches
  · intro g s e hNoTransfer _ _
    rcases Nat.lt_or_ge (Phi g s) (Phi g (next s e)) with hlt | hle
    · exact (hNoTransfer g e hlt).elim
    · exact hle

end PerGapOffPay

#print axioms PerGapOffPay.ordinaryLocality_of_derived
