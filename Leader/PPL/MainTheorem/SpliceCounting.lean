import Leader.PPL.MainTheorem.Skeleton
import Leader.PPL.Modes.MidEntryRetimedSplit
import Leader.PPL.Elim.OneLeaderBoundLeaves
import Leader.PPL.Convergence.QuietWindow
import Leader.PPL.Elim.LiteralBridges
import Leader.PPL.Safety.PeacefulScan
import Leader.Wu.Scheduler.RepeatedBlocks
import Init.Omega

namespace PPL

instance theorem1LiteralL1Decidable {n : Nat} (C : LiteralElimConfig n) :
    Decidable (PPL.LiteralL1 C) := by
  unfold PPL.LiteralL1
  infer_instance

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-
Canonical first-hit offset for a Boolean state predicate along the literal
full P_PL run. Offset 0 means the start state itself is good.
-/
def theorem1FirstHitCut
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (good : Config n psi kappa → Bool) :
    Config n psi kappa →
      DetSchedule n →
      Option Nat
  | C, [] =>
      if good C then some 0 else none
  | C, e :: rest =>
      if good C then
        some 0
      else
        match theorem1FirstHitCut
            ring good
            (PPL.Probability.pplStep ring C e)
            rest with
        | none => none
        | some t => some (t + 1)

/-
This is the padding arithmetic. Theorem1Whp.lean is not on
current main, so the helper is restated here verbatim at the Nat level.
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

theorem theorem1_countP_mono_mem
    {A : Type}
    (xs : List A)
    (p q : A → Bool)
    (hpq :
      ∀ x, x ∈ xs →
        p x = true →
        q x = true) :
    xs.countP p ≤ xs.countP q := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx :
          p x = true →
            q x = true := by
        intro hp
        exact hpq x (by simp) hp
      have htail :
          ∀ y, y ∈ xs →
            p y = true →
            q y = true := by
        intro y hy hp
        exact hpq y (by simp [hy]) hp
      have hi := ih htail
      cases hp : p x <;>
        cases hq : q x <;>
          simp [List.countP_cons, hp, hq]
            at hx hi ⊢ <;>
          omega

theorem theorem1_countP_or_le_add
    {A : Type}
    (xs : List A)
    (p q : A → Bool) :
    xs.countP (fun x => p x || q x) ≤
      xs.countP p + xs.countP q := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.countP_cons,
        List.countP_cons,
        List.countP_cons]
      cases hp : p x <;>
        cases hq : q x <;>
          simp [hp, hq] <;>
          omega

theorem theorem1_countP_five_union_le
    {A : Type}
    (xs : List A)
    (bad b1 b2 b3 b4 b5 : A → Bool)
    (hcover :
      ∀ x, x ∈ xs →
        bad x = true →
          b1 x = true ∨
          b2 x = true ∨
          b3 x = true ∨
          b4 x = true ∨
          b5 x = true) :
    xs.countP bad ≤
      xs.countP b1 +
        xs.countP b2 +
        xs.countP b3 +
        xs.countP b4 +
        xs.countP b5 := by
  let q : A → Bool :=
    fun x =>
      b1 x ||
        (b2 x ||
          (b3 x ||
            (b4 x || b5 x)))
  have hmono :
      xs.countP bad ≤ xs.countP q := by
    apply theorem1_countP_mono_mem
    intro x hx hbad
    have hc := hcover x hx hbad
    rcases hc with h1 | h2 | h3 | h4 | h5
    · simp [q, h1]
    · simp [q, h2]
    · simp [q, h3]
    · simp [q, h4]
    · simp [q, h5]
  have h1 :
      xs.countP q ≤
        xs.countP b1 +
          xs.countP
            (fun x =>
              b2 x ||
                (b3 x ||
                  (b4 x || b5 x))) := by
    simpa [q] using
      theorem1_countP_or_le_add
        xs b1
        (fun x =>
          b2 x ||
            (b3 x ||
              (b4 x || b5 x)))
  have h2 :=
    theorem1_countP_or_le_add
      xs b2
      (fun x =>
        b3 x || (b4 x || b5 x))
  have h3 :=
    theorem1_countP_or_le_add
      xs b3
      (fun x => b4 x || b5 x)
  have h4 :=
    theorem1_countP_or_le_add
      xs b4 b5
  omega

theorem theorem1_five_event_constants
    (n H : Nat) :
    12 * n ^ H +
        8 * n ^ H +
        4 * n ^ H +
        n ^ H +
        n ^ H ≤
      64 * n ^ H := by
  omega

end PPL

#print axioms PPL.theorem1_pad_phase_bound
#print axioms PPL.theorem1_countP_mono_mem
#print axioms PPL.theorem1_countP_or_le_add
#print axioms PPL.theorem1_countP_five_union_le
#print axioms PPL.theorem1_five_event_constants
