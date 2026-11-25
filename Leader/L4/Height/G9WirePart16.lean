import Leader.L4.Height.G9WirePart15
set_option Elab.async false

namespace L4.Height.G9Wire
open G9Spine L4.Compiler.Native Classical

section PublicSuffix

open PhysicalCustody PublicSpec

/-- The production bounded decoder gives its quadratic field from every
Cartesian byte configuration. -/
theorem bounded_field :
    ∃ patrol : Nat, ∀ {n : Nat}, 4 ≤ n → n ≤ boundedN → ∀ x : BoundedRaw n,
      IIDExpectedHittingTimeAtMost (boundedNextWith boundedEncode boundedDecode)
        (Permanent (boundedNextWith boundedEncode boundedDecode) (boundedLeaderWith boundedDecode)) x
        ((2049 + patrol) * n^2) :=
  bounded_field_of_section boundedEncode boundedDecode boundedDecode_encode

/-- A completed handoff supplies an actual explicit marker and the
ordinary rooted estimate on the closed packed domain. -/
theorem packed_suffix_of_marked (hClosed : MarkedClosed) (hProjects : MarkedProjects) :
    ∃ C : Nat, ∀ {s n : Nat}, 4 ≤ n → ∀ x : Raw s n, Marked x →
      IIDExpectedHittingTimeAtMost (rawNext s) PackedElected x (C * n^2) := by
  obtain ⟨C, hC⟩ := L4.row175_rooted_complete 12 (by decide)
  refine ⟨C, ?_⟩
  intro s n hn x hx
  have hRoot : RootedEntrance.RootNonempty (pubConfig x) :=
    RootedEntrance.rootNonempty_of_mark hx.2.2.1
  have hOrdinary := hC (pubConfig x) (by decide) hn hRoot
  have hProduct := RootedProduct.public_mean_to_product (rawNext s) pubConfig packedLeader Marked
    (fun _ e hy => hClosed hn e hy) (fun _ e hy => hProjects hn e hy)
    (fun _ _ _ => rfl) x hx (C * n^2) hOrdinary
  intro t
  rw [← public_iidHitCost_eq]
  exact hProduct t

/-- Both production branches use the same uniform public coefficient
after installing their literal step projections. -/
theorem public_suffixes_of_packed
    (hPack : ∃ C : Nat, ∀ {s n : Nat}, 4 ≤ n → ∀ x : Raw s n, Marked x →
      IIDExpectedHittingTimeAtMost (rawNext s) PackedElected x (C * n^2)) :
    PublicSuffixes := by
  obtain ⟨packed, hPacked⟩ := hPack
  obtain ⟨patrol, hBounded⟩ := bounded_field
  let C := max packed (2049 + patrol)
  refine ⟨C, ?_, ?_⟩
  · intro s n hn x hx
    exact expected_bound_mono _ _ _ (hPacked hn x hx)
      (Nat.mul_le_mul_right _ (Nat.le_max_left packed (2049 + patrol)))
  · intro n hn hb x
    have hTarget : (BoundedElected : BoundedRaw n → Prop) =
        Permanent (boundedNextWith boundedEncode boundedDecode) (boundedLeaderWith boundedDecode) :=
      funext fun y => propext (productSafe_iff_permanent _ _ y)
    rw [hTarget]
    exact expected_bound_mono _ _ _ (hBounded hn hb x)
      (Nat.mul_le_mul_right _ (Nat.le_max_right packed (2049 + patrol)))

/-- The two literal marked-domain exports also suffice at the public handoff. -/
theorem public_suffixes_of_marked (hClosed : MarkedClosed) (hProjects : MarkedProjects) :
    PublicSuffixes :=
  public_suffixes_of_packed (packed_suffix_of_marked hClosed hProjects)

end PublicSuffix

end L4.Height.G9Wire
