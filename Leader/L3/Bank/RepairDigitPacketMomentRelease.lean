import Leader.L3.Bank.RepairDigitPacketMoment
import Leader.L3.Bank.RepairDigitPacketTransport

/-!
# Lemma e-packet in moment form: transport of moments, and the release phase

* `momentNumeratorSimLe`, `momentSimQ`: the moment numerator moves along a simulation exactly as
  the cost numerator does (`L3.CohortTransfer.costNumeratorSimLe`); hence moment bounds of the
  T22 lane transfer to the coupled BANK x audit chain.
* `momentQCross`: compare two rational moment bounds.
* `releaseMoment` (lane), `releaseMomentCoupled` (coupled chain): the release phase of Lemma
  e-packet (repair.tex 1223-1250) has `E[z^{T_B}] ≤ w^{R (2R+2)} ≤ w^{3R²+4R+2}`,
  `w = N/(N-n)`, from every layout state: the release weight is a potential with a nominated
  drop (`edgeMono`, `edgeDrop`), so `L3.PacketMoment.momentOfPotential` applies.

This is the first obligation phase of the per-pair moment in the form Lemma e-max consumes.
-/

namespace L3.PacketMomentRelease

set_option autoImplicit false

open K2ArbitraryElimination.FiniteAccounting
open L3.PairMoment
open L3.PacketMoment
open L3
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.WidthDigit
open L3.DigitPacketRelease
open L3.DigitPacketTransport

/-- **Moment transfer along a simulation.** Consumer: `momentSimQ`. -/
theorem momentNumeratorSimLe {X Y : Type} {n : Nat} (next' : X → Fin n → X)
    (next : Y → Fin n → Y) (Sim : X → Y → Prop) (Good' : X → Prop) (Good : Y → Prop) (N : Nat)
    (hstep : ∀ x y e, Sim x y → ¬ Good' x → Sim (next' x e) (next y e))
    (hgood : ∀ x y, Sim x y → Good y → Good' x) :
    ∀ T x y, Sim x y → momentNumerator next' Good' N x T ≤ momentNumerator next Good N y T := by
  intro T
  induction T with
  | zero => intro x y _; rw [momentNumeratorZero, momentNumeratorZero]; exact Nat.le_refl _
  | succ T ih =>
    intro x y hxy
    by_cases hx : Good' x
    · rw [momentNumeratorTerminal next' Good' N x hx]
      exact momentNumeratorGe next Good N (T + 1) y
    · have hy : ¬ Good y := fun hy => hx (hgood x y hxy hy)
      rw [momentNumeratorSucc next' Good' N x hx, momentNumeratorSucc next Good N y hy]
      exact Nat.mul_le_mul_left N (sumLe _ _ (fun e => ih _ _ (hstep x y e hxy hx)))

/-- Moment bounds transfer along a simulation. Consumer: `releaseMomentCoupled`. -/
theorem momentSimQ {X Y : Type} {n : Nat} (next' : X → Fin n → X)
    (next : Y → Fin n → Y) (Sim : X → Y → Prop) (Good' : X → Prop) (Good : Y → Prop)
    (N a b : Nat) (hstep : ∀ x y e, Sim x y → ¬ Good' x → Sim (next' x e) (next y e))
    (hgood : ∀ x y, Sim x y → Good y → Good' x) (x : X) (y : Y) (hxy : Sim x y)
    (h : MomentBoundQ next Good N a b y) : MomentBoundQ next' Good' N a b x := fun T =>
  Nat.le_trans (Nat.mul_le_mul_left b
    (momentNumeratorSimLe next' next Sim Good' Good N hstep hgood T x y hxy)) (h T)

/-- Cross-multiplied comparison of rational bounds. Consumer: `releaseMomentCoupled`. -/
theorem momentQCross {S : Type} {n : Nat} (next : S → Fin n → S) (P : S → Prop)
    (N a b a' b' : Nat) (x : S) (hb : 0 < b) (h1 : a * b' ≤ a' * b)
    (h : MomentBoundQ next P N a b x) : MomentBoundQ next P N a' b' x := by
  intro T
  have h2 := h T
  refine Nat.le_of_mul_le_mul_left ?_ hb
  calc b * (b' * momentNumerator next P N x T) = b' * (b * momentNumerator next P N x T) :=
        Nat.mul_left_comm _ _ _
    _ ≤ b' * (a * (n ^ T * (N - 1) ^ T)) := Nat.mul_le_mul_left _ h2
    _ = (a * b') * (n ^ T * (N - 1) ^ T) := by
        rw [← Nat.mul_assoc, Nat.mul_comm b' a]
    _ ≤ (a' * b) * (n ^ T * (N - 1) ^ T) := Nat.mul_le_mul_right _ h1
    _ = b * (a' * (n ^ T * (N - 1) ^ T)) := by
        rw [Nat.mul_comm a' b, Nat.mul_assoc]

/-- `w^k ≤ w^B` for `k ≤ B`, cleared of denominators. Consumer: `releaseMomentCoupled`. -/
theorem powCross (N m k B : Nat) (h : k ≤ B) :
    N ^ k * (N - m) ^ B ≤ N ^ B * (N - m) ^ k := by
  obtain ⟨d, rfl⟩ : ∃ d, B = k + d := ⟨B - k, by omega⟩
  rw [Nat.pow_add, Nat.pow_add]
  have hp : (N - m) ^ d ≤ N ^ d := Nat.pow_le_pow_left (Nat.sub_le N m) d
  calc N ^ k * ((N - m) ^ k * (N - m) ^ d) = (N ^ k * (N - m) ^ k) * (N - m) ^ d := by
        rw [Nat.mul_assoc]
    _ ≤ (N ^ k * (N - m) ^ k) * N ^ d := Nat.mul_le_mul_left _ hp
    _ = N ^ k * N ^ d * (N - m) ^ k := by
        rw [Nat.mul_assoc, Nat.mul_comm ((N - m) ^ k) (N ^ d), ← Nat.mul_assoc]

/-- **The release phase in moment form, on the lane.** From every lane state the border is free
with `E[z^{T}] ≤ w^{releaseWeight}`. Consumer: `releaseMomentCoupled`. -/
theorem releaseMoment {n R : Nat} (hR : 2 ≤ R) (hn : 1 ≤ n) (N : Nat) (hN : n ≤ N)
    (site : Nat → Fin n) (edgeOf : Fin n → Option Nat)
    (hedge : ∀ k, k < 2 * R → edgeOf (site k) = some k) (s : CohortLane) :
    MomentBoundQ (releaseNext R edgeOf) (BorderFree R) N (N ^ releaseWeight R s)
      ((N - n) ^ releaseWeight R s) s := by
  have hex : ∀ s : CohortLane, ∃ e : Fin n, ¬ BorderFree R s →
      releaseWeight R (releaseNext R edgeOf s e) + 1 ≤ releaseWeight R s := by
    intro s
    by_cases hb : BorderFree R s
    · exact ⟨site 0, fun h => absurd hb h⟩
    · obtain ⟨k, hk, hd⟩ := edgeDrop R s hR hb
      refine ⟨site k, fun _ => ?_⟩
      show releaseWeight R (cohortLaneStep R s (edgeOf (site k))) + 1 ≤ releaseWeight R s
      rw [hedge k hk]
      exact hd
  exact momentOfPotential (releaseNext R edgeOf) (BorderFree R) N (releaseWeight R)
    (fun s => Classical.choose (hex s)) hn hN
    (fun s hs => Classical.choose_spec (hex s) hs)
    (fun s hs e => by
      show releaseWeight R (cohortLaneStep R s (edgeOf e)) ≤ releaseWeight R s
      cases edgeOf e with
      | none => exact Nat.le_refl _
      | some k => exact edgeMono R k s hR hs) s

/-- **The release phase in moment form, on the coupled chain.** From every layout state of the
coupled BANK x audit chain the border of the pair's target is free with
`E[z^{T_B}] ≤ w^{R(2R+2)}`, `w = N/(N-n)`, uniformly over source registers and audit. With the
paper's `B = 3R²+4R+2 ≥ R(2R+2)` this is the factor `w^B` of the release obligations.
Consumer: the per-pair moment (`E[z^{T_pair}] < 40`, Lemma e-max). -/
theorem releaseMomentCoupled {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun y => BorderFree R (laneOfState ring hbank root lane src R y)) N
      (N ^ (R * (2 * R + 2))) ((N - n) ^ (R * (2 * R + 2))) x := by
  have hlane := releaseMoment hR (by omega) N (Nat.le_of_lt hN) (fun k => digitSite ring root (src + k))
    (cohortEdgeOf root src R) (fun k hk => cohortEdgeOfSite ring root src R hend k hk)
    (laneOfState ring hbank root lane src R x)
  have hco := momentSimQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
    (releaseNext R (cohortEdgeOf root src R))
    (fun y s => CohortLayout ring hbank root src R y.1 ∧ laneOfState ring hbank root lane src R y = s)
    (fun y => BorderFree R (laneOfState ring hbank root lane src R y)) (BorderFree R) N _ _
    (fun y s e hys _ => by
      obtain ⟨hl, hs⟩ := hys
      obtain ⟨h1, h2⟩ := laneStep ring hn hbank root lane src R hR hsrc hend y hl e
      refine ⟨h1, ?_⟩
      rw [h2, hs]
      rfl)
    (fun y s hys hg => by rw [hys.2]; exact hg) x _ ⟨hx, rfl⟩ hlane
  refine momentQCross _ _ N _ _ _ _ x (Nat.pow_pos (by omega)) ?_ hco
  exact powCross N n _ _ (releaseWeightLe R _)

end L3.PacketMomentRelease

#print axioms L3.PacketMomentRelease.momentNumeratorSimLe
#print axioms L3.PacketMomentRelease.momentSimQ
#print axioms L3.PacketMomentRelease.momentQCross
#print axioms L3.PacketMomentRelease.powCross
#print axioms L3.PacketMomentRelease.releaseMoment
#print axioms L3.PacketMomentRelease.releaseMomentCoupled
