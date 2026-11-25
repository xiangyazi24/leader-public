import Leader.L4.PhysicalShortSheet
import Leader.L4.AllSizeComposition
import Leader.L4.PhysicalCustodyH2Ready
import Leader.L4.ShortResetMIS1Ring

namespace L4.ShortLayerStage
open AllSizeProtocol PhysicalCustody PhysicalShortSheet

abbrev Slice (n : Nat) := Fin n → BitVec 96

def project {s n : Nat} (j : Sheet) (x : Raw s n) : Slice n :=
  fun i => bytes j (x i)

/-- A stage must prove its own frozen lower mask and certified target.
Neither closure of the preceding stage nor seeing selected bits at
one cut alone supplies these fields. -/
structure Transfer {s n : Nat} (j : Sheet) (Lower Upper : Raw s n → Prop)
    (T : (Fin n → Bool) → Slice n → Prop) : Prop where
  lowerClosed : AllSizeComposition.Closed (rawNext s) Lower
  nested : ∀ x, Upper x → Lower x
  maskFrozen : ∀ x e, Lower x → mask j (rawNext s x e)=mask j x
  exactTarget : ∀ x, Lower x → (Upper x ↔ T (mask j x) (project j x))

private theorem hit_congr_closed {α : Type} {n : Nat} (step : α → Fin n → α)
    (P Q R : α → Prop) (closed : AllSizeComposition.Closed step R)
    (agree : ∀ x, R x → (P x ↔ Q x)) (t : Nat) (x : α) (rx : R x) :
    iidHitCost step P t x=iidHitCost step Q t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    by_cases H : P x
    · simp [iidHitCost,H,(agree x rx).mp H]
    · have H' : ¬ Q x := fun g=>H ((agree x rx).mpr g)
      simp only [iidHitCost,if_neg H,if_neg H']
      congr 2
      apply congrArg List.ofFn
      funext e
      exact ih _ (closed x e rx)

/-- The lower mask is chosen at the real stage cut. The lifted horizon
cost is equal, not just bounded, on the very same n-mark alphabet. -/
theorem exact_stage_cost {s n : Nat} (j : Sheet) {Lower Upper : Raw s n → Prop}
    {T : (Fin n → Bool) → Slice n → Prop} (B : Transfer j Lower Upper T)
    (t : Nat) (x : Raw s n) (X : Lower x) :
    iidHitCost (rawNext s) Upper t x =
      iidHitCost (sliceStep (rows s) (mask j x)) (T (mask j x)) t (project j x) := by
  let Q : Raw s n → Prop := fun z => Lower z ∧ mask j z=mask j x
  have init : Q x := ⟨X,rfl⟩
  have stay : AllSizeComposition.Closed (rawNext s) Q :=
    fun y e hy => ⟨B.lowerClosed y e hy.1,(B.maskFrozen y e hy.1).trans hy.2⟩
  have eqv (y : Raw s n) (Y : Q y) :
      Upper y ↔ T (mask j x) (project j y) := by
    rw [←Y.2]
    exact B.exactTarget y Y.1
  exact (hit_congr_closed (rawNext s) Upper
      (fun y => T (mask j x) (project j y)) Q stay eqv t x init).trans
    (exact_fixed_cost j (mask j x) Q (fun _ H=>H.2) stay (T (mask j x)) t x init)

theorem stage_closed {s n : Nat} (j : Sheet) {Lower Upper : Raw s n → Prop}
    {T : (Fin n → Bool) → Slice n → Prop} (B : Transfer j Lower Upper T)
    (closed : ∀ h, AllSizeComposition.Closed (sliceStep (rows s) h) (T h)) :
    AllSizeComposition.Closed (rawNext s) Upper := by
  intro x e A
  have L := B.nested x A
  apply (B.exactTarget _ (B.lowerClosed x e L)).mpr
  rw [B.maskFrozen x e L]
  unfold project
  rw [exact_raw_step]
  exact closed _ _ _ ((B.exactTarget x L).mp A)

theorem stage_mean {s n K : Nat} (j : Sheet) {Lower Upper : Raw s n → Prop}
    {T : (Fin n → Bool) → Slice n → Prop} (B : Transfer j Lower Upper T)
    (mean : ∀ x, Lower x → IIDExpectedHittingTimeAtMost
      (sliceStep (rows s) (mask j x)) (T (mask j x)) (project j x) K) :
    ∀ x, Lower x → IIDExpectedHittingTimeAtMost (rawNext s) Upper x K := by
  intro x X t
  rw [exact_stage_cost j B t x X]
  exact mean x X t

/-- This is the additive entrance adapter for one concrete sheet
following any already established entrance mean on the joined raw row. -/
theorem add_sheet_stage {s n a b : Nat} (j : Sheet) {Lower Upper : Raw s n → Prop}
    {T : (Fin n → Bool) → Slice n → Prop} (B : Transfer j Lower Upper T)
    (mean : ∀ x, Lower x → IIDExpectedHittingTimeAtMost
      (sliceStep (rows s) (mask j x)) (T (mask j x)) (project j x) b)
    (x : Raw s n) (prep : IIDExpectedHittingTimeAtMost (rawNext s) Lower x a) :
    IIDExpectedHittingTimeAtMost (rawNext s) Upper x (a+b) :=
  AllSizeComposition.additive_stage (rawNext s) Lower Upper a b x prep (stage_mean j B mean)

/-- The next short mask comes from the prior mask and that prior
sheet's selected bank, read in the same old configuration. -/
theorem next_short_masks {s n : Nat} (x : Raw s n) (i : Fin n) :
    mask .mis2 x i=(mask .mis1 x i && (rows s).misSelected (bytes .mis1 (x i))) ∧
    mask .mis3 x i=(mask .mis2 x i && (rows s).misSelected (bytes .mis2 (x i))) :=
  ⟨rfl,rfl⟩

/-- The MIS1 instance of the common tape equation. This proves no
selected-mask stability for MIS2 or MIS3. -/
theorem mis1_ready_run {s n : Nat} (N : 5≤n) (x : Raw s n)
    (X : H2Ready x) (w : List (Fin n)) :
    project .mis1 (rawRun x w) =
      BStarResetSchedule.run (sliceStep (rows s) (mask .mis1 x)) (project .mis1 x) w := by
  let Q : Raw s n → Prop := fun y => H2Ready y ∧ mask .mis1 y=mask .mis1 x
  apply exact_fixed_run .mis1 (mask .mis1 x) Q (fun _ Y=>Y.2) _ w x ⟨X,rfl⟩
  intro y e Y
  refine ⟨h2_ready_closed N y e Y.1,?_⟩
  refine (funext fun i => ?_).trans Y.2
  exact H1.raw_h1_selected_frozen N y e i Y.1.1

end L4.ShortLayerStage
