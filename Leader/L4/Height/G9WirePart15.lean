import Leader.L4.Height.G9WirePart14
set_option Elab.async false

namespace L4.Height.G9Wire.PublicSpec

theorem bounded_rank_pos : 0 < L4.stateCount boundedP 12 := by decide

theorem bounded_rank_fits : L4.stateCount boundedP 12 < 2^48 := by decide

/-- The mixed-radix public-state rank padded to the bounded branch's
48-bit alphabet. -/
def boundedEncode (x : L4.Site boundedP 12) : BoundedCode :=
  let rank := (L4.stateCoding boundedP 12).encode x
  ⟨rank.val, Nat.lt_trans rank.isLt bounded_rank_fits⟩

/-- Decode any bounded byte; spare ranks decode to the rank-zero state. -/
def boundedDecode (a : BoundedCode) : L4.Site boundedP 12 :=
  let coding := L4.stateCoding boundedP 12
  if h : a.val < L4.stateCount boundedP 12 then
    coding.decode ⟨a.val, h⟩
  else
    coding.decode ⟨0, bounded_rank_pos⟩

/-- The concrete 48-bit pair map and physical readout shared with `BoundedPublicCodec`. -/
def boundedPair (a b : BoundedCode) := boundedPairWith boundedEncode boundedDecode a b
def boundedNext {n : Nat} (x : BoundedRaw n) (e : Fin n) :=
  boundedNextWith boundedEncode boundedDecode x e
def boundedLeader {n : Nat} (x : BoundedRaw n) (i : Fin n) :=
  boundedLeaderWith boundedDecode x i
def BoundedElected {n : Nat} (x : BoundedRaw n) : Prop :=
  RootedProduct.ProductSafe boundedNext boundedLeader x

/-- The existential export over the two concrete production rows. -/
def PublicSuffixes : Prop :=
  ∃ C : Nat,
    (∀ {s n : Nat}, 4 ≤ n → ∀ x : PhysicalCustody.Raw s n, Marked x →
      Height.IIDExpectedHittingTimeAtMost (PhysicalCustody.rawNext s) PackedElected x (C*n^2)) ∧
    (∀ {n : Nat}, 4 ≤ n → n ≤ boundedN → ∀ x : BoundedRaw n,
      Height.IIDExpectedHittingTimeAtMost boundedNext BoundedElected x (C*n^2))

/-- Every typed public state round-trips through the bounded byte. -/
theorem boundedDecode_encode (x : L4.Site boundedP 12) :
    boundedDecode (boundedEncode x) = x := by
  let coding := L4.stateCoding boundedP 12
  let rank := coding.encode x
  change (if h : rank.val < L4.stateCount boundedP 12 then
    coding.decode ⟨rank.val, h⟩ else coding.decode ⟨0, bounded_rank_pos⟩) = x
  rw [dif_pos rank.isLt]
  exact coding.left_inv x

/-- The first spare rank decodes to the rank-zero tuple. -/
theorem boundedDecode_first_spare :
    boundedDecode ⟨L4.stateCount boundedP 12, bounded_rank_fits⟩ =
      (L4.stateCoding boundedP 12).decode ⟨0, bounded_rank_pos⟩ := by
  unfold boundedDecode
  rw [dif_neg (Nat.lt_irrefl _)]

/-- The decoded bounded pair rule is the ordinary public step on every
raw configuration, including spare bytes. -/
theorem bounded_projects {n : Nat} (_hn : 4 ≤ n) (x : BoundedRaw n) (e : Fin n) :
    (fun i => boundedDecode (boundedNextWith boundedEncode boundedDecode x e i)) =
      L4.step (fun i => boundedDecode (x i)) e :=
  L4.Height.G9Wire.bounded_projects_of_section
    boundedEncode boundedDecode boundedDecode_encode x e

/-- Literal preservation of the completed public handoff. -/
def MarkedClosed : Prop :=
  ∀ {s n : Nat}, 4 ≤ n → ∀ {x : PhysicalCustody.Raw s n} (e : Fin n),
    Marked x → Marked (PhysicalCustody.rawNext s x e)

/-- After the handoff the packed raw step projects to the ordinary
public pair rule on the very same scheduler edge. -/
def MarkedProjects : Prop :=
  ∀ {s n : Nat}, 4 ≤ n → ∀ {x : PhysicalCustody.Raw s n} (e : Fin n),
    Marked x → pubConfig (PhysicalCustody.rawNext s x e) = L4.step (pubConfig x) e

end L4.Height.G9Wire.PublicSpec
