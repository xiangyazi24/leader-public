import Leader.L4.Height.G9WirePart16
set_option Elab.async false

namespace L4.Height.G9Wire
open G9Spine L4.Compiler.Native Classical

section PublicProjection

open PhysicalCustody PublicSpec AllSizeProtocol

/-- After the final seed, every continuation stays on the ordinary
public row. This predicate is defined on the original raw tape. -/
def PublicSeedsStopped {s n : Nat} (x : Raw s n) : Prop :=
  ∀ (w : List (Fin n)) (e : Fin n), seed (rawRun x w) e = false

theorem publicSeedsStopped_closed {s n : Nat} (x : Raw s n) (e : Fin n)
    (hx : PublicSeedsStopped x) : PublicSeedsStopped (rawNext s x e) :=
  fun w j => hx (e :: w) j

theorem clear_seed_preserves_site {p c : Nat} (u : L4.Site p c)
    (bit : Bool) (hb : bit = false) : {u with mark := u.mark || bit} = u := by
  subst bit
  cases u
  simp only [Bool.or_false]

/-- The literal joined row decodes to the ordinary public step whenever
the initiator seed is false. The responder seed is always false. -/
theorem packed_public_step_of_no_seed {s n : Nat} (hn : 4 ≤ n)
    (x : Raw s n) (e : Fin n) (hNoSeed : seed x e = false) :
    pubConfig (rawNext s x e) = L4.step (pubConfig x) e := by
  let j := rightNeighbor e
  let pair := largePair (rows s) (x e, x j)
  let ordinary := L4.pairStep (pubConfig x e) (pubConfig x j)
  let guard := ((x e).guard, (x j).guard)
  let oldRef := (reference (rows s) (x e), reference (rows s) (x j))
  let newRef := (reference (rows s) pair.1, reference (rows s) pair.2)
  let marks := ((pubConfig x e).mark, (pubConfig x j).mark)
  let ordinaryMarks := (ordinary.1.mark, ordinary.2.mark)
  let H := H5.row guard oldRef newRef marks ordinaryMarks
  have hPhysical (i : Fin n) : rawNext s x e i =
      if i = e then pair.1 else if i = j then pair.2 else x i := rfl
  have hLeft : rawNext s x e e = pair.1 := by
    rw [hPhysical, if_pos rfl]
  have hRight : rawNext s x e j = pair.2 := by
    rw [hPhysical, if_neg (pair_distinct hn e).symm, if_pos rfl]
  have hLeftSeed : H.seed.1 = false := by
    dsimp only [PublicSpec.seed] at hNoSeed
    rw [hLeft, hRight] at hNoSeed
    exact hNoSeed
  have hRightSeed : H.seed.2 = false :=
    congrArg Prod.snd (H5.seed_exact guard oldRef newRef marks ordinaryMarks)
  let hp : 0 < 2 := by decide
  have hPair := BStarJoinedPublic.joined_public (rows s) hp rfl (x e, x j)
  change
    (BStarPublicCodec.readPub (p := 2) (c := 12) hp pair.1.publicRow, BStarPublicCodec.readPub (p := 2) (c := 12) hp pair.2.publicRow) =
      ({ordinary.1 with mark := ordinary.1.mark || H.seed.1},
       {ordinary.2 with mark := ordinary.2.mark || H.seed.2}) at hPair
  have hDecodedLeft : BStarPublicCodec.readPub (p := 2) (c := 12) hp pair.1.publicRow = ordinary.1 := by
    exact (congrArg Prod.fst hPair).trans (clear_seed_preserves_site ordinary.1 H.seed.1 hLeftSeed)
  have hDecodedRight : BStarPublicCodec.readPub (p := 2) (c := 12) hp pair.2.publicRow = ordinary.2 := by
    exact (congrArg Prod.snd hPair).trans (clear_seed_preserves_site ordinary.2 H.seed.2 hRightSeed)
  funext i
  change BStarPublicCodec.readPub (p := 2) (c := 12) hp (rawNext s x e i).publicRow =
    (if i = e then ordinary.1 else if i = j then ordinary.2 else pubConfig x i)
  rw [hPhysical]
  by_cases he : i = e
  · simpa only [if_pos he] using hDecodedLeft
  · by_cases hj : i = j
    · simpa only [if_neg he, if_pos hj] using hDecodedRight
    · simp only [if_neg he, if_neg hj] <;> rfl

/-- One explicit mark at handoff supplies rootedness. Only the future-zero
seed invariant is used to transfer the rooted bound along raw words. -/
theorem packed_suffix_of_stopped_seeds :
    ∃ C : Nat, ∀ {s n : Nat}, 4 ≤ n → ∀ x : Raw s n,
      RootedEntrance.MarkNonempty (pubConfig x) → PublicSeedsStopped x →
      IIDExpectedHittingTimeAtMost (rawNext s) PackedElected x (C * n^2) := by
  obtain ⟨C, hC⟩ := L4.row175_rooted_complete 12 (by decide)
  refine ⟨C, ?_⟩
  intro s n hn x hMark hStop
  have hRoot := RootedEntrance.rootNonempty_of_mark hMark
  have hOrdinary := hC (pubConfig x) (by decide) hn hRoot
  have hProduct := RootedProduct.public_mean_to_product (rawNext s) pubConfig packedLeader
    PublicSeedsStopped publicSeedsStopped_closed
    (fun y e hy => packed_public_step_of_no_seed hn y e (hy [] e))
    (fun _ _ _ => rfl) x hStop (C * n^2) hOrdinary
  intro t
  rw [← public_iidHitCost_eq]
  exact hProduct t

/-- The production public suffixes follow from the verified rooted row
and the literal public projection on the handoff domain. -/
theorem production_public_suffixes : PublicSpec.PublicSuffixes := by
  apply public_suffixes_of_packed
  obtain ⟨C, hC⟩ := packed_suffix_of_stopped_seeds
  refine ⟨C, ?_⟩
  intro s n hn x hx
  exact hC hn x hx.2.2.1 hx.2.1

end PublicProjection

end L4.Height.G9Wire
