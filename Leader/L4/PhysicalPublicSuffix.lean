import Leader.L4.PhysicalPublicObserver
import Leader.L4.BoundedPublicCodec
import Leader.L4.RootedAssembly
import Leader.L4.Height.Window

namespace L4.PhysicalPublic
open PhysicalCustody

export BoundedPublicCodec (boundedN boundedP BoundedCode BoundedRaw boundedEncode
  boundedDecode boundedDecode_encode boundedDecode_spare boundedPair boundedNext
  boundedProject boundedLeader BoundedElected)

def PackedElected {s n : Nat} (x : Raw s n) : Prop :=
  RootedProduct.ProductSafe (rawNext s) packedLeader x

theorem bounded_projects {n : Nat} (_hn : 4 ≤ n) (x : BoundedRaw n) (e : Fin n) :
    (fun i => boundedDecode (boundedNext x e i)) =
      L4.step (fun i => boundedDecode (x i)) e :=
  BoundedPublicCodec.bounded_projects x e

/-- Calibrated rooted L4 bound, uniform in the modulus and ring size. -/
def RootedPublicMean (coefficient : Nat) : Prop :=
  ∀ {p n : Nat} (x : Config p 12 n), 2 ≤ p → 4 ≤ n →
    RootedEntrance.RootNonempty x →
      L4.IIDExpectedHittingTimeAtMost step SafeOneLeader x (coefficient*n^2)

private theorem same_numerator {X : Type} {n : Nat}
    (next : X → Fin n → X) (target : X → Prop) (t : Nat) (x : X) :
    L4.iidHitCost next target t x = L4.Height.iidHitCost next target t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    by_cases h : target x
    · simp only [L4.iidHitCost, L4.Height.iidHitCost, if_pos h]
    · simp only [L4.iidHitCost, L4.Height.iidHitCost, if_neg h, ih]

/-- Preserve the exact first-hit estimate through a leader-bit projection
on a forward-closed domain. -/
theorem projected_mean {coefficient : Nat} (rooted : RootedPublicMean coefficient)
    {X : Type} {p n : Nat}
    (next : X → Fin n → X) (project : X → Config p 12 n)
    (leader : X → Fin n → Bool) (ready : X → Prop)
    (closed : ∀ x e, ready x → ready (next x e))
    (projects : ∀ x e, ready x → project (next x e) = step (project x) e)
    (reads : ∀ x i, ready x → leader x i = (project x i).leader)
    (hp : 2 ≤ p) (hn : 4 ≤ n) (x : X) (hx : ready x)
    (hroot : RootedEntrance.RootNonempty (project x)) :
    Height.IIDExpectedHittingTimeAtMost next (RootedProduct.ProductSafe next leader) x
      (coefficient * n^2) := by
  have h := RootedProduct.public_mean_to_product next project leader ready
    closed projects reads x hx _ (rooted (project x) hp hn hroot)
  intro t
  rw [← same_numerator]
  exact h t


theorem packed_suffix {coefficient : Nat} (rooted : RootedPublicMean coefficient) {s n : Nat} (hn : 4 ≤ n) (x : Raw s n) (hx : Marked x) :
    Height.IIDExpectedHittingTimeAtMost (rawNext s) PackedElected x (coefficient * n^2) :=
  projected_mean rooted (rawNext s) pubConfig packedLeader Marked
    (fun _ e h => marked_closed hn e h)
    (fun _ e h => marked_projects hn e h)
    (fun _ _ _ => rfl) (by decide) hn x hx
    (RootedEntrance.rootNonempty_of_mark hx.2.2.1)

/-- Below the bounded cutoff every decoded state starts in the rooted
domain because the residue modulus exceeds the ring size. -/
theorem bounded_suffix {coefficient : Nat} (rooted : RootedPublicMean coefficient) {n : Nat} (hn : 4 ≤ n) (hBound : n ≤ boundedN)
    (x : BoundedRaw n) :
    Height.IIDExpectedHittingTimeAtMost boundedNext BoundedElected x (coefficient * n^2) := by
  have hp : 2 ≤ boundedP := by decide
  have hnPos : 0 < n := by omega
  have hs : n < boundedP := Nat.lt_succ_of_le hBound
  have hnd : ¬ boundedP ∣ n :=
    fun hd => Nat.not_le_of_lt hs (Nat.le_of_dvd hnPos hd)
  exact projected_mean rooted boundedNext boundedProject boundedLeader (fun _ => True)
    (fun _ _ _ => trivial) (fun y e _ => BoundedPublicCodec.bounded_projects y e) (fun _ _ _ => rfl)
    hp hn x trivial (RootedAssembly.rootNonempty_of_not_dvd (boundedProject x) hn hnd)


theorem public_suffixes_of_mean {coefficient : Nat} (rooted : RootedPublicMean coefficient) :
    ∃ cpub : Nat,
      (∀ {s n : Nat}, 4 ≤ n → ∀ x : Raw s n, Marked x →
        Height.IIDExpectedHittingTimeAtMost (rawNext s) PackedElected x (cpub*n^2)) ∧
      (∀ {n : Nat}, 4 ≤ n → n ≤ boundedN → ∀ x : BoundedRaw n,
        Height.IIDExpectedHittingTimeAtMost boundedNext BoundedElected x (cpub*n^2)) :=
  ⟨coefficient, packed_suffix rooted, bounded_suffix rooted⟩

#print axioms bounded_projects
#print axioms projected_mean
#print axioms packed_suffix
#print axioms bounded_suffix
#print axioms public_suffixes_of_mean

end L4.PhysicalPublic
