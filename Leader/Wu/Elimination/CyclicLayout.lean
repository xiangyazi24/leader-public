import Leader.Wu.Elimination.GapClosure
import Init.Data.List.Nat.Pairwise

/-!
Construct cyclic gap layouts from the actual K2 leader bits.  The source
list is the existing ring indices in increasing order, filtered by the
physical leader flag.  Its length is proved equal to the physical count;
no leader enumeration, gap validity, or mass identity is an input promise.
All enumerations and selected frames are ghost data, with no protocol change.
-/

namespace K2CyclicLayout

open LDSinkGapCleanup LDTwoGapFrame LDSinkTwoGapReachInvariant
  K2GlobalGapClosure K2OutputSafety

set_option autoImplicit false
set_option pp.structureInstances false

variable {n ψ k : Nat}

/-! ## The sorted list of actual leaders -/

/-- Existing ring positions, filtered by their actual physical leader bit.
Filtering preserves their increasing numerical order. -/
def leaderSites (C : Fin n → AgentState ψ) : List (Fin n) :=
  (List.ofFn (fun i : Fin n => i)).filter (fun i => (C i).leader)

private theorem filter_length_sum {α : Type} (xs : List α) (p : α → Bool) :
    (xs.filter p).length = (xs.map (fun x => if p x then 1 else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases hp : p a <;> simp [hp, ih, Nat.add_comm]

/-- The enumerated length is derived from the same physical sum used by
`GlobalClass`, rather than asserted as a representation field. -/
theorem leaderSites_length (C : Fin n → AgentState ψ) :
    (leaderSites C).length = physicalLeaderCount C := by
  unfold leaderSites physicalLeaderCount
  rw [filter_length_sum, List.map_ofFn]
  rfl

/-- Membership is exactly the actual leader flag, with every physical site
covered by the original finite enumeration. -/
theorem mem_leaderSites (C : Fin n → AgentState ψ) (v : Fin n) :
    v ∈ leaderSites C ↔ (C v).leader = true := by
  simp [leaderSites, List.mem_filter, List.mem_ofFn]

private theorem leaderSites_sorted (C : Fin n → AgentState ψ) :
    (leaderSites C).Pairwise (fun a b => a.val < b.val) := by
  apply List.Pairwise.filter
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  simpa only [List.getElem_ofFn] using hij

/-- Index the actual filtered list with the supplied physical count equality.
That equality is furnished directly by `GlobalClass`. -/
def leaderAt (C : Fin n → AgentState ψ) (hc : physicalLeaderCount C = k)
    (i : Fin k) : Fin n :=
  (leaderSites C)[i.val]'(by rw [leaderSites_length, hc]; exact i.isLt)

theorem leaderAt_leader (C : Fin n → AgentState ψ)
    (hc : physicalLeaderCount C = k) (i : Fin k) :
    (C (leaderAt C hc i)).leader = true := by
  apply (mem_leaderSites C _).mp
  exact List.getElem_mem _

/-- Strict numerical ordering follows from filtering the original ring
enumeration, so distinct list indices name distinct physical leaders. -/
theorem leaderAt_strict (C : Fin n → AgentState ψ)
    (hc : physicalLeaderCount C = k) (i j : Fin k) (hij : i.val < j.val) :
    (leaderAt C hc i).val < (leaderAt C hc j).val := by
  exact List.pairwise_iff_getElem.mp (leaderSites_sorted C)
    i.val j.val (by rw [leaderSites_length, hc]; exact i.isLt)
    (by rw [leaderSites_length, hc]; exact j.isLt) hij

/-- Every actual leader is in the sorted enumeration. -/
theorem leaderAt_complete (C : Fin n → AgentState ψ)
    (hc : physicalLeaderCount C = k) (v : Fin n) (hv : (C v).leader = true) :
    ∃ i : Fin k, leaderAt C hc i = v := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp ((mem_leaderSites C v).mpr hv)
  exact ⟨⟨i, by simpa only [leaderSites_length, hc] using hi⟩, he⟩

/-! ## Cyclic geometry of an increasing finite enumeration -/

/-- Clockwise position with the exact modular formula of `GapFrame.pos`,
available before the distance-two bound needed to construct a frame. -/
def arcPos (ring : DirectedRing n) (a : Fin n) (t : Nat) : Fin n :=
  ⟨(a.val + t) % n, Nat.mod_lt _ ring.hn⟩

@[simp] theorem arcPos_zero (ring : DirectedRing n) (a : Fin n) :
    arcPos ring a 0 = a := by
  apply Fin.ext
  simp [arcPos, Nat.mod_eq_of_lt a.isLt]

private theorem enum_le (p : Fin k → Fin n)
    (hs : ∀ i j, i.val < j.val → (p i).val < (p j).val)
    (i j : Fin k) (hij : i.val ≤ j.val) : (p i).val ≤ (p j).val := by
  by_cases he : i = j
  · subst i; exact Nat.le_refl _
  · have hne : i.val ≠ j.val := fun hh => he (Fin.ext hh)
    exact Nat.le_of_lt (hs i j (by omega))

private theorem next_val (i : Fin k) (hi : i.val + 1 < k) :
    (MinimalTripleChoice.cyclicSucc i).val = i.val + 1 :=
  Nat.mod_eq_of_lt hi

private theorem next_wrap (i : Fin k) (hi : ¬ i.val + 1 < k) :
    (MinimalTripleChoice.cyclicSucc i).val = 0 := by
  have he : i.val + 1 = k := by have := i.isLt; omega
  change (i.val + 1) % k = 0
  rw [he, Nat.mod_self]

/-- Distance to the next enumerated leader.  Only the last sorted index
wraps around the ring. -/
def gapDistance (p : Fin k → Fin n) (i : Fin k) : Nat :=
  if i.val + 1 < k then
    (p (MinimalTripleChoice.cyclicSucc i)).val - (p i).val
  else
    n + (p (MinimalTripleChoice.cyclicSucc i)).val - (p i).val

/-- Every distance is positive and strictly below the ring size as soon as
the increasing enumeration contains two distinct leaders. -/
theorem gapDistance_bounds (p : Fin k → Fin n) (hk : 2 ≤ k)
    (hs : ∀ i j, i.val < j.val → (p i).val < (p j).val) (i : Fin k) :
    0 < gapDistance p i ∧ gapDistance p i < n := by
  have ha := (p i).isLt
  have hb := (p (MinimalTripleChoice.cyclicSucc i)).isLt
  unfold gapDistance
  split
  · rename_i hi
    have hv := next_val i hi
    have hh := hs i (MinimalTripleChoice.cyclicSucc i) (by omega)
    omega
  · rename_i hi
    have hv := next_wrap i hi
    have hil := i.isLt
    have hh := hs (MinimalTripleChoice.cyclicSucc i) i (by omega)
    omega

/-- The modular endpoint is the next actual position in the enumeration. -/
theorem arcPos_distance (ring : DirectedRing n) (p : Fin k → Fin n)
    (hs : ∀ i j, i.val < j.val → (p i).val < (p j).val) (i : Fin k) :
    arcPos ring (p i) (gapDistance p i) = p (MinimalTripleChoice.cyclicSucc i) := by
  apply Fin.ext
  have ha := (p i).isLt
  have hb := (p (MinimalTripleChoice.cyclicSucc i)).isLt
  change ((p i).val + gapDistance p i) % n = (p (MinimalTripleChoice.cyclicSucc i)).val
  unfold gapDistance
  split
  · rename_i hi
    have hv := next_val i hi
    have hh := hs i (MinimalTripleChoice.cyclicSucc i) (by omega)
    have he : (p i).val + ((p (MinimalTripleChoice.cyclicSucc i)).val - (p i).val) =
        (p (MinimalTripleChoice.cyclicSucc i)).val := by omega
    rw [he, Nat.mod_eq_of_lt hb]
  · have he : (p i).val + (n + (p (MinimalTripleChoice.cyclicSucc i)).val - (p i).val) =
        n + (p (MinimalTripleChoice.cyclicSucc i)).val := by omega
    rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt hb]

/-- A strictly intermediate point of an enumerated gap cannot be any
enumerated leader.  The wraparound branch is proved on its two actual
modular coordinate pieces, without assuming a follower interior. -/
theorem arcPos_interior_ne (ring : DirectedRing n) (p : Fin k → Fin n)
    (hs : ∀ i j, i.val < j.val → (p i).val < (p j).val)
    (i j : Fin k) (t : Nat) (ht : 0 < t) (htd : t < gapDistance p i) :
    arcPos ring (p i) t ≠ p j := by
  intro he
  have heval := congrArg Fin.val he
  change ((p i).val + t) % n = (p j).val at heval
  have ha := (p i).isLt
  have hb := (p (MinimalTripleChoice.cyclicSucc i)).isLt
  unfold gapDistance at htd
  split at htd
  · rename_i hi
    have hv := next_val i hi
    have hab := hs i (MinimalTripleChoice.cyclicSucc i) (by omega)
    have hu : (p i).val + t < n := by omega
    rw [Nat.mod_eq_of_lt hu] at heval
    by_cases hj : j.val ≤ i.val
    · have hh := enum_le p hs j i hj
      omega
    · have hh := enum_le p hs (MinimalTripleChoice.cyclicSucc i) j (by omega)
      omega
  · rename_i hi
    have hv := next_wrap i hi
    have hii := i.isLt
    have hjj := j.isLt
    have hjleft := enum_le p hs (MinimalTripleChoice.cyclicSucc i) j (by omega)
    have hjright := enum_le p hs j i (by omega)
    by_cases hu : (p i).val + t < n
    · rw [Nat.mod_eq_of_lt hu] at heval
      omega
    · have hsub : (p i).val + t - n < n := by omega
      rw [Nat.mod_eq_sub_mod (by omega : n ≤ (p i).val + t),
        Nat.mod_eq_of_lt hsub] at heval
      omega

/-- The distance-one case contradicts physical leader separation, so the
existing lower bound of `GapFrame` is a derived fact. -/
theorem gapDistance_two (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (p : Fin k → Fin n) (hk : 2 ≤ k)
    (hs : ∀ i j, i.val < j.val → (p i).val < (p j).val)
    (hl : ∀ i, (C (p i)).leader = true) (hsep : Separated ring C) (i : Fin k) :
    2 ≤ gapDistance p i := by
  have hpos := (gapDistance_bounds p hk hs i).1
  by_cases hd : gapDistance p i = 1
  · have he := arcPos_distance ring p hs i
    rw [hd] at he
    have hnext : ring.rightNeighbor (p i) = p (MinimalTripleChoice.cyclicSucc i) := he
    have hf := hsep (p i) (hl i)
    rw [hnext] at hf
    exact Bool.noConfusion (hf.symm.trans (hl _))
  · omega

private theorem gapDistance_balance (p : Fin k → Fin n)
    (hs : ∀ i j, i.val < j.val → (p i).val < (p j).val) (i : Fin k) :
    (p i).val + gapDistance p i =
      (p (MinimalTripleChoice.cyclicSucc i)).val +
        (if i.val + 1 < k then 0 else n) := by
  have ha := (p i).isLt
  unfold gapDistance
  split
  · rename_i hi
    have hv := next_val i hi
    have hh := hs i (MinimalTripleChoice.cyclicSucc i) (by omega)
    omega
  · rename_i hi
    omega

private theorem wrap_mass (n k : Nat) (hk : 0 < k) :
    (List.ofFn (fun i : Fin k => if i.val + 1 < k then 0 else n)).sum = n := by
  cases k with
  | zero => omega
  | succ m =>
    rw [List.ofFn_succ_last, List.sum_append, List.sum_cons, List.sum_nil]
    simp only [Nat.add_zero]
    change (List.ofFn (fun i : Fin m => if i.val + 1 < m + 1 then 0 else n)).sum +
      (if m + 1 < m + 1 then 0 else n) = n
    have hi : ∀ i : Fin m, i.val + 1 < m + 1 := by intro i; have := i.isLt; omega
    simp [hi, FiniteUniformStoppingTree.ofFn_sum_const]

/-- The gap lengths sum to the ring size: adjacent position terms cancel,
and exactly the last sorted gap contributes the one wrap around the ring. -/
theorem gapDistance_sum (p : Fin k → Fin n) (hk : 0 < k)
    (hs : ∀ i j, i.val < j.val → (p i).val < (p j).val) :
    (List.ofFn (gapDistance p)).sum = n := by
  have hbalance := FiniteUniformStoppingTree.ofFn_sum_eq
    (fun i => (p i).val + gapDistance p i)
    (fun i => (p (MinimalTripleChoice.cyclicSucc i)).val +
      (if i.val + 1 < k then 0 else n)) (gapDistance_balance p hs)
  rw [FiniteUniformStoppingTree.ofFn_sum_add, FiniteUniformStoppingTree.ofFn_sum_add] at hbalance
  have hreindex : (List.ofFn (fun i => (p (MinimalTripleChoice.cyclicSucc i)).val)).sum =
      (List.ofFn (fun i => (p i).val)).sum := by
    have hh := MinimalTripleChoice.cyclicPairSpan_sum hk (fun i => (p i).val)
    change (List.ofFn (fun i => (p i).val + (p (MinimalTripleChoice.cyclicSucc i)).val)).sum =
      2 * (List.ofFn (fun i => (p i).val)).sum at hh
    rw [FiniteUniformStoppingTree.ofFn_sum_add] at hh
    omega
  rw [hreindex, wrap_mass n k hk] at hbalance
  omega

/-! ## Constructing the real frames -/

/-- Existing `GapFrame` built from an increasing enumeration of actual
separated leaders.  Its distance bounds are the preceding geometry lemmas. -/
def enumeratedGap (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (p : Fin k → Fin n) (hk : 2 ≤ k)
    (hs : ∀ i j, i.val < j.val → (p i).val < (p j).val)
    (hl : ∀ i, (C (p i)).leader = true) (hsep : Separated ring C)
    (i : Fin k) : GapFrame n where
  ring := ring
  low := p i
  d := gapDistance p i
  hd := gapDistance_two ring C p hk hs hl hsep i
  hdn := (gapDistance_bounds p hk hs i).2

private theorem enumeratedGap_pos (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (p : Fin k → Fin n) (hk : 2 ≤ k)
    (hs : ∀ i j, i.val < j.val → (p i).val < (p j).val)
    (hl : ∀ i, (C (p i)).leader = true) (hsep : Separated ring C)
    (i : Fin k) (t : Nat) :
    (enumeratedGap ring C p hk hs hl hsep i).pos t = arcPos ring (p i) t := rfl

private theorem enumeratedGap_endpoints (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (p : Fin k → Fin n) (hk : 2 ≤ k)
    (hs : ∀ i j, i.val < j.val → (p i).val < (p j).val)
    (hl : ∀ i, (C (p i)).leader = true) (hsep : Separated ring C) (i : Fin k) :
    GapEndpointsPresent (enumeratedGap ring C p hk hs hl hsep i) C := by
  change (C (arcPos ring (p i) 0)).leader = true ∧
    (C (arcPos ring (p i) (gapDistance p i))).leader = true
  rw [arcPos_zero, arcPos_distance ring p hs i]
  exact ⟨hl i, hl _⟩

private theorem enumeratedGap_followers (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (p : Fin k → Fin n) (hk : 2 ≤ k)
    (hs : ∀ i j, i.val < j.val → (p i).val < (p j).val)
    (hl : ∀ i, (C (p i)).leader = true) (hsep : Separated ring C)
    (hcover : ∀ v, (C v).leader = true → ∃ j, p j = v) (i : Fin k) :
    GapInteriorFollowers (enumeratedGap ring C p hk hs hl hsep i) C := by
  intro t ht htd
  change (C (arcPos ring (p i) t)).leader = false
  cases hc : (C (arcPos ring (p i) t)).leader
  · rfl
  · obtain ⟨j, hj⟩ := hcover _ hc
    exact (arcPos_interior_ne ring p hs i j t (by omega) htd hj.symm).elim

/-- Package the proved cyclic geometry in the frozen `CyclicLayout` type.
Neither its shared-endpoint field nor its mass field is an input premise. -/
def enumerationLayout (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (p : Fin k → Fin n) (hk : 2 ≤ k)
    (hs : ∀ i j, i.val < j.val → (p i).val < (p j).val)
    (hl : ∀ i, (C (p i)).leader = true) (hsep : Separated ring C) : CyclicLayout n k where
  gap := enumeratedGap ring C p hk hs hl hsep
  shared := by
    intro i
    change arcPos ring (p i) (gapDistance p i) =
      arcPos ring (p (MinimalTripleChoice.cyclicSucc i)) 0
    rw [arcPos_zero, arcPos_distance ring p hs i]
  mass := gapDistance_sum p (by omega) hs

/-! ## The constructor from the actual configuration -/

/-- Canonical ghost layout of the actual configuration.  All data come from
its physical leader bits; the count equality and separation are taken from
the original `GlobalClass`, with no enumeration or gap-validity promise. -/
def canonicalLayout (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : GlobalClass hψ ring k C) : CyclicLayout n k :=
  enumerationLayout ring C (leaderAt C hC.2.1) hC.1
    (leaderAt_strict C hC.2.1) (leaderAt_leader C hC.2.1) hC.2.2.separated

/-- The canonical gaps have real leader endpoints and leader-free interiors.
These facts are derived from exact enumeration membership and order. -/
theorem canonicalLayout_real (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : GlobalClass hψ ring k C) :
    (∀ i, GapEndpointsPresent ((canonicalLayout hψ ring C hC).gap i) C) ∧
    (∀ i, GapInteriorFollowers ((canonicalLayout hψ ring C hC).gap i) C) := by
  constructor
  · exact enumeratedGap_endpoints ring C (leaderAt C hC.2.1) hC.1
      (leaderAt_strict C hC.2.1) (leaderAt_leader C hC.2.1) hC.2.2.separated
  · exact enumeratedGap_followers ring C (leaderAt C hC.2.1) hC.1
      (leaderAt_strict C hC.2.1) (leaderAt_leader C hC.2.1) hC.2.2.separated
      (leaderAt_complete C hC.2.1)

/-- The `k` left endpoints are exactly the actual leaders. -/
theorem canonicalLayout_covers (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : GlobalClass hψ ring k C) (v : Fin n) :
    (C v).leader = true ↔ ∃ i : Fin k, ((canonicalLayout hψ ring C hC).gap i).low = v := by
  constructor
  · exact leaderAt_complete C hC.2.1 v
  · rintro ⟨i, hi⟩
    have hh := leaderAt_leader C hC.2.1 i
    change leaderAt C hC.2.1 i = v at hi
    rw [hi] at hh
    exact hh

/-- No actual leader is duplicated in the cyclic enumeration.  Together
with coverage and the derived physical count, this establishes exactly `k`
consecutive gaps rather than a repeated or truncated circuit. -/
theorem canonicalLayout_injective (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : GlobalClass hψ ring k C) :
    ∀ i j : Fin k, ((canonicalLayout hψ ring C hC).gap i).low =
      ((canonicalLayout hψ ring C hC).gap j).low → i = j := by
  intro i j he
  change leaderAt C hC.2.1 i = leaderAt C hC.2.1 j at he
  have hv := congrArg Fin.val he
  apply Fin.ext
  by_cases hij : i.val < j.val
  · have hh := leaderAt_strict C hC.2.1 i j hij
    omega
  · by_cases hji : j.val < i.val
    · have hh := leaderAt_strict C hC.2.1 j i hji
      omega
    · omega

/-- The missing realizing-layout producer.  The only state premise is the
actual `GlobalClass`; every represented endpoint, follower interior, and
exactly-once coverage fact is a proved output.  The layout's cyclic sharing
and total mass were derived by `canonicalLayout`. -/
theorem exists_realizing_layout (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : GlobalClass hψ ring k C) :
    ∃ L : CyclicLayout n k,
      (∀ i, GapEndpointsPresent (L.gap i) C) ∧
      (∀ i, GapInteriorFollowers (L.gap i) C) ∧
      (∀ v, (C v).leader = true ↔ ∃ i : Fin k, (L.gap i).low = v) ∧
      (∀ i j : Fin k, (L.gap i).low = (L.gap j).low → i = j) := by
  have hr := canonicalLayout_real hψ ring C hC
  exact ⟨canonicalLayout hψ ring C hC, hr.1, hr.2,
    canonicalLayout_covers hψ ring C hC, canonicalLayout_injective hψ ring C hC⟩

/-- Every canonical gap has the original physical signal-order invariant,
not a weaker enumerated surrogate. -/
theorem canonicalLayout_invariants (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : GlobalClass hψ ring k C) :
    ∀ i, GapInvariant hψ ((canonicalLayout hψ ring C hC).gap i) C := by
  intro i
  have hr := canonicalLayout_real hψ ring C hC
  exact global_gap hψ ring C hC.2.2 _ (hr.1 i) (hr.2 i)

/-! ## Direct physical short-pair choice and reselection -/

/-- Choose a genuine adjacent pair of span at most `floor(2*n/k)` directly
from the actual global class.  There is no supplied layout, gap-validity,
or mass hypothesis.  The configuration and every existing ghost phase are
retained.  The original class still requires fully cyclic labels, hence
`psi | n`; this is not an all-ring normalization theorem. -/
theorem short_pair_of_globalClass (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hk : 3 ≤ k) (hC : GlobalClass hψ ring k C) :
    ∃ F : TwoGapFrame n,
      F.recovery.d + F.attack.d ≤ (2 * n) / k ∧
      ∀ phase : LDSinkTwoGapNoResetKernel.APhase, GapPair hψ F ⟨C, phase⟩ := by
  obtain ⟨L, hE, hI, _, _⟩ := exists_realizing_layout hψ ring C hC
  obtain ⟨F, hspan, hp⟩ := select_short_pair hψ ring k hk C hC.2.2 L hE hI
  refine ⟨F, ?_, hp⟩
  apply (Nat.le_div_iff_mul_le (by omega : 0 < k)).mpr
  simpa only [Nat.mul_comm] using hspan

/-- The arithmetic domain and the physical choice in one explicit result.
All enumeration nonemptiness and count facts are derived from `GlobalClass`. -/
theorem short_pair_with_domain (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hk : 3 ≤ k) (hC : GlobalClass hψ ring k C) :
    ψ ∣ n ∧ ∃ F : TwoGapFrame n,
      F.recovery.d + F.attack.d ≤ (2 * n) / k ∧
      ∀ phase : LDSinkTwoGapNoResetKernel.APhase, GapPair hψ F ⟨C, phase⟩ :=
  ⟨global_requires_dvd hψ ring C hC.2.2,
    short_pair_of_globalClass hψ ring C hk hC⟩

/-- After any actual K2 row at at least three leaders, either the physical
count has reached two or a fresh pair is available at the bound for the
actual new count.  Physical row closure is reused from the frozen module;
this theorem adds only the now-derived enumeration and choice. -/
theorem step_two_or_short_pair (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hk : 3 ≤ k) (hC : GlobalClass hψ ring k C)
    (e : Fin n) :
    physicalLeaderCount (rawStep hψ ring C e) = 2 ∨
      ∃ F : TwoGapFrame n,
        F.recovery.d + F.attack.d ≤ (2 * n) / physicalLeaderCount (rawStep hψ ring C e) ∧
        ∀ phase : LDSinkTwoGapNoResetKernel.APhase, GapPair hψ F ⟨rawStep hψ ring C e, phase⟩ := by
  rcases global_class_step hψ ring k C hk hC e with ⟨hs, _⟩ | ⟨hs, _, _⟩
  · right
    obtain ⟨F, hb, hp⟩ := short_pair_of_globalClass hψ ring _ hk hs
    refine ⟨F, ?_, hp⟩
    rw [hs.2.1]
    exact hb
  · by_cases htwo : k - 1 = 2
    · exact Or.inl (hs.2.1.trans htwo)
    · right
      obtain ⟨F, hb, hp⟩ := short_pair_of_globalClass hψ ring _ (by omega : 3 ≤ k - 1) hs
      refine ⟨F, ?_, hp⟩
      rw [hs.2.1]
      exact hb

/-! ## Concrete consumers of the constructor -/

/-- The constructor computes the true post-deletion cycle `2,2,4`, without
using the manually supplied layout in the frozen module. -/
theorem seed8_three_lengths :
    (List.ofFn (fun i => ((canonicalLayout (by decide) ⟨by decide⟩
      (rawStep (by decide) ⟨by decide⟩ seed8 6) seed8_three).gap i).d)) = [2, 2, 4] := by
  decide

/-- The same constructor handles the two-leader terminal slice; the two
actual cyclic gap lengths are two and six, both strictly below eight. -/
theorem seed8_two_lengths :
    (List.ofFn (fun i => ((canonicalLayout (by decide) ⟨by decide⟩
      (rawStep (by decide) ⟨by decide⟩ (rawStep (by decide) ⟨by decide⟩ seed8 6) 4)
        seed8_two).gap i).d)) = [2, 6] := by
  decide

/-- Fresh physical short-pair selection after a witnessed real deletion,
with no representation premise and no restriction on the ghost phase. -/
theorem seed8_short_pair :
    ∃ F : TwoGapFrame 8,
      F.recovery.d + F.attack.d ≤ 5 ∧
      ∀ phase : LDSinkTwoGapNoResetKernel.APhase,
        GapPair (by decide) F ⟨rawStep (by decide) ⟨by decide⟩ seed8 6, phase⟩ := by
  exact short_pair_of_globalClass (by decide) ⟨by decide⟩ _ (by decide) seed8_three

end K2CyclicLayout
