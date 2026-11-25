import Leader.L4.Height.G9WirePart13
set_option Elab.async false

namespace L4.Height.G9Wire
open G9Spine L4.Compiler.Native Classical

section PublicBudget

open PhysicalCustody ClockDisplaySpec PublicSpec
open Classical

/-- The public and clock developments count the same truncated first hit
on the same raw edge alphabet. -/
theorem public_iidHitCost_eq {X : Type} {n : Nat}
    (next : X → Fin n → X) (A : X → Prop) (t : Nat) (x : X) :
    L4.iidHitCost next A t x = L4.Height.iidHitCost next A t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    by_cases hx : A x
    · simp only [L4.iidHitCost, L4.Height.iidHitCost, if_pos hx]
    · simp only [L4.iidHitCost, L4.Height.iidHitCost, if_neg hx, ih]

theorem ordinary_safe_permanent {p c n : Nat} {x : L4.Config p c n}
    (hx : L4.SafeOneLeader x) :
    permanentSiteOutput L4.step (fun y i => (y i).leader) x := by
  have hProduct : RootedProduct.ProductSafe L4.step (fun y i => (y i).leader) x :=
    (RootedProduct.safe_of_proj L4.step (fun z : L4.Config p c n => z)
      (fun y i => (y i).leader) (fun _ => True) (fun _ _ _ => trivial)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) x trivial).2 hx
  exact (productSafe_iff_permanent _ _ _).1 hProduct

/-- A section for the public byte decoder gives same-label projection on
every raw byte configuration, including arbitrary spare codes. -/
theorem bounded_projects_of_section
    (encode : L4.Site boundedP 12 → BoundedCode)
    (decode : BoundedCode → L4.Site boundedP 12)
    (hSection : ∀ a, decode (encode a) = a) {n : Nat} (x : BoundedRaw n) (e : Fin n) :
    (fun i => decode (boundedNextWith encode decode x e i)) =
      L4.step (fun i => decode (x i)) e := by
  funext i
  by_cases he : i = e
  · simp [boundedNextWith, boundedPairWith, L4.step, he, hSection]
  · by_cases hr : i = rightNeighbor e
    · have hne : rightNeighbor e ≠ e := hr ▸ he
      subst i
      simp only [boundedNextWith, boundedPairWith, L4.step, if_neg hne, eq_self, if_true, hSection]
    · simp [boundedNextWith, L4.step, he, hr]

/-- Bounded sizes inherit the rooted public estimate through their total
decoder, using one patrol coefficient for every size and initial code. -/
theorem bounded_field_of_projects
    (encode : L4.Site boundedP 12 → BoundedCode)
    (decode : BoundedCode → L4.Site boundedP 12)
    (hProject : ∀ {n : Nat}, 4 ≤ n → ∀ (x : BoundedRaw n) (e : Fin n),
      (fun i => decode (boundedNextWith encode decode x e i)) =
        L4.step (fun i => decode (x i)) e) :
    ∃ patrol : Nat, ∀ {n : Nat}, 4 ≤ n → n ≤ boundedN → ∀ x : BoundedRaw n,
      IIDExpectedHittingTimeAtMost (boundedNextWith encode decode)
        (Permanent (boundedNextWith encode decode) (boundedLeaderWith decode)) x
        ((2049 + patrol) * n^2) := by
  obtain ⟨C, hC⟩ := L4.row175_rooted_complete 12 (by decide)
  refine ⟨C, ?_⟩
  intro n hn hUpper x
  have hNotDvd : ¬ boundedP ∣ n := by
    intro hDvd
    have hLe := Nat.le_of_dvd (show 0 < n by omega) hDvd
    change boundedN + 1 ≤ n at hLe
    omega
  have hMean (y : L4.Config boundedP 12 n) :
      IIDExpectedHittingTimeAtMost L4.step L4.SafeOneLeader y (C * n^2) := by
    have hRoot := RootedAssembly.rootNonempty_of_not_dvd y hn hNotDvd
    have hOrdinary := hC y (by decide) hn hRoot
    intro t
    rw [← public_iidHitCost_eq]
    exact hOrdinary t
  have hResult := bounded_decoder_permanent_cost
    (boundedNextWith encode decode) L4.step
    (fun x : BoundedRaw n => fun i => decode (x i))
    (boundedLeaderWith decode) (fun y i => (y i).leader)
    (hProject hn) (fun _ _ => rfl) L4.SafeOneLeader
    (fun _ => ordinary_safe_permanent) C hMean x
  exact expected_bound_mono _ _ _ hResult
    (Nat.mul_le_mul_right (n^2) (Nat.le_add_left C 2049))

/-- A proved encode/decode section supplies the bounded field directly. -/
theorem bounded_field_of_section
    (encode : L4.Site boundedP 12 → BoundedCode)
    (decode : BoundedCode → L4.Site boundedP 12)
    (hSection : ∀ a, decode (encode a) = a) :
    ∃ patrol : Nat, ∀ {n : Nat}, 4 ≤ n → n ≤ boundedN → ∀ x : BoundedRaw n,
      IIDExpectedHittingTimeAtMost (boundedNextWith encode decode)
        (Permanent (boundedNextWith encode decode) (boundedLeaderWith decode)) x
        ((2049 + patrol) * n^2) :=
  bounded_field_of_projects encode decode
    (fun _ x e => bounded_projects_of_section encode decode hSection x e)

/-- The observer's nominated raw marks witnessed on an enriched replay
whose projection follows the joined physical row. -/
structure ObserverNomination {s n : Nat} (x : Raw s n) where
  State : Type
  initial : State
  project : State → Raw s n
  next : State → Fin n → State
  initial_raw : project initial = x
  raw_step : ∀ y e, project (next y e) = rawNext s (project y) e
  remaining : State → Nat
  nonincrease : ∀ y e, ¬ Marked (project y) → remaining (next y e) ≤ remaining y
  nominate : ∀ y, ¬ Marked (project y) → Fin n
  progress : ∀ y (hy : ¬ Marked (project y)),
    remaining (next y (nominate y hy)) < remaining y
  budget : remaining initial ≤ 5 * n + 7

/-- A nomination witness at every permanent-reference state is sufficient
for the raw observer mean supplied by the public handoff. -/
def PackedObserverNominations : Prop :=
  ∀ {s n : Nat}, 4 ≤ n → ∀ x : Raw s n, PermanentReference x →
    Nonempty (ObserverNomination x)

/-- Each nomination names one literal scheduler edge. The accepted
nominated-edge estimate charges its service on the original raw clock. -/
theorem packed_observer_of_nominations (hDebt : PackedObserverNominations) :
    PackedObserverMean := by
  intro s n hn x hx
  obtain ⟨d⟩ := hDebt hn x hx
  have hCost := observer_nominated_cost (rawNext s) d.next d.project d.raw_step
    Marked d.remaining d.nonincrease (fun y hy => ⟨d.nominate y hy, d.progress y hy⟩)
    d.initial d.budget
  rw [d.initial_raw] at hCost
  exact hCost

/-- The nomination route supplies the packed chart's observer field. -/
theorem packed_observer_field_of_nominations {s n : Nat} (hn : 4 ≤ n) (hs : 6 ≤ s)
    (hDebt : PackedObserverNominations) :
    let D := packedData s n hn hs
    2^32 < n → ∀ x, D.display (by omega) x →
      IIDExpectedHittingTimeAtMost (D.next (by omega)) D.marked x (5*n^2+7*n) := by
  dsimp only
  intro _ x hx
  change Permanent ((packedData s n hn hs).next (by omega))
    (fun y i => packedRead s (y i)) x at hx
  change IIDExpectedHittingTimeAtMost ((packedData s n hn hs).next (by omega))
    (Marked (s := s)) x (5*n^2+7*n)
  rw [packed_next hn hs] at hx ⊢
  exact packed_observer_of_nominations hDebt hn x
    ((reference_iff_permanent x).2 hx)

end PublicBudget

end L4.Height.G9Wire
