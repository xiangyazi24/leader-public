import Leader.Wu.Epoch.VoterBellman

/-!
# Two-domain quotient of the directed epoch voter process

A canonical voter configuration has color zero on positions `0,...,x-1` and
color one on the rest of the ring.  For `0<x<n`, exactly two directed edges can
change it: the right boundary grows the zero domain, the wrap boundary shrinks
it and rotates the result, and every other edge is a self-loop.

Rotation commutes with the voter update.  Consequently all rotated contiguous
two-domain configurations have the same lazy domain-length quotient used by
`EpochVoterBellman`; this is the concrete process bridge behind its first-step
equations.
-/

namespace PPLLEpochVoterTwoDomain

open PPLLEpochVoterReduction

/-! ## Canonical contiguous domains -/

/-- Zero voter color on a nonempty ring. -/
def zeroColor (hn : n > 0) : Fin n := ⟨0, hn⟩

/-- A distinct second color, available on every nontrivial ring. -/
def oneColor (hn2 : 1 < n) : Fin n := ⟨1, hn2⟩

/-- Canonical contiguous domain: zero on the first `x` positions and one on the
remaining positions. -/
def canonicalTwoDomain (hn2 : 1 < n) (x : Nat) (_hx : x ≤ n) :
    Fin n → Fin n :=
  fun i => if i.val < x then zeroColor (by omega) else oneColor hn2

/-- Shape obtained when the wrap boundary shrinks a canonical zero domain:
position zero becomes one and positions `1,...,x-1` remain zero. -/
def leftShrunkDomain (hn2 : 1 < n) (x : Nat) (_hx : x ≤ n) :
    Fin n → Fin n :=
  fun i => if i.val = 0 then oneColor hn2
    else if i.val < x then zeroColor (by omega) else oneColor hn2

/-- The right boundary edge of a nonempty canonical domain. -/
def rightBoundary (x : Nat) (hx : 0 < x) (hxn : x < n) : Fin n :=
  ⟨x - 1, by omega⟩

/-- The wrap edge is the left boundary of the canonical domain. -/
def leftBoundary (hn2 : 1 < n) : Fin n :=
  ⟨n - 1, by omega⟩

/-- Selecting the right boundary grows the zero domain by one position. -/
theorem rightBoundary_grows
    (hn2 : 1 < n) (x : Nat) (hx : 0 < x) (hxn : x < n)
    (ring : DirectedRing n) :
    directedVoterStep ring (canonicalTwoDomain hn2 x (by omega))
        (rightBoundary x hx hxn) =
      canonicalTwoDomain hn2 (x + 1) (by omega) := by
  funext i
  let e : Fin n := rightBoundary x hx hxn
  let j : Fin n := ⟨x, hxn⟩
  have hneighbor : ring.rightNeighbor e = j := by
    apply Fin.ext
    change (x - 1 + 1) % n = x
    have heq : x - 1 + 1 = x := by omega
    rw [heq, Nat.mod_eq_of_lt hxn]
  unfold directedVoterStep
  change (if i = e then canonicalTwoDomain hn2 x _ e
    else if i = ring.rightNeighbor e then canonicalTwoDomain hn2 x _ e
    else canonicalTwoDomain hn2 x _ i) =
      canonicalTwoDomain hn2 (x + 1) _ i
  rw [hneighbor]
  unfold canonicalTwoDomain
  by_cases hie : i = e
  · subst i
    have he1 : x - 1 < x := by omega
    have he2 : x - 1 < x + 1 := by omega
    simp [e, rightBoundary, he1, he2]
  by_cases hij : i = j
  · subst i
    have he1 : x - 1 < x := by omega
    have hj2 : x < x + 1 := by omega
    simp [e, j, rightBoundary, he1, hj2]
  rw [if_neg hie, if_neg hij]
  have hiff : i.val < x ↔ i.val < x + 1 := by
    constructor
    · intro hi
      omega
    · intro hi
      by_cases hlt : i.val < x
      · exact hlt
      · have heq : i.val = x := by omega
        exact absurd (Fin.ext heq) hij
  by_cases hi : i.val < x
  · have hi2 : i.val < x + 1 := hiff.mp hi
    simp [hi, hi2]
  · have hi2 : ¬i.val < x + 1 := by
      intro hbad
      exact hi (hiff.mpr hbad)
    simp [hi, hi2]

/-- Selecting the wrap boundary shrinks the canonical zero domain by one and
moves its start one position clockwise. -/
theorem leftBoundary_shrinks
    (hn2 : 1 < n) (x : Nat) (_hx : 0 < x) (hxn : x < n)
    (ring : DirectedRing n) :
    directedVoterStep ring (canonicalTwoDomain hn2 x (by omega))
        (leftBoundary hn2) = leftShrunkDomain hn2 x (by omega) := by
  funext i
  let e : Fin n := leftBoundary hn2
  let j : Fin n := ⟨0, by omega⟩
  have hneighbor : ring.rightNeighbor e = j := by
    apply Fin.ext
    change (n - 1 + 1) % n = 0
    have heq : n - 1 + 1 = n := by omega
    rw [heq, Nat.mod_self]
  unfold directedVoterStep
  change (if i = e then canonicalTwoDomain hn2 x _ e
    else if i = ring.rightNeighbor e then canonicalTwoDomain hn2 x _ e
    else canonicalTwoDomain hn2 x _ i) = leftShrunkDomain hn2 x _ i
  rw [hneighbor]
  unfold canonicalTwoDomain leftShrunkDomain
  have henx : ¬e.val < x := by
    dsimp [e, leftBoundary]
    omega
  by_cases hie : i = e
  · subst i
    have hn10 : n - 1 ≠ 0 := by omega
    have hnlt : ¬n - 1 < x := by omega
    simp [e, leftBoundary, hn10, hnlt]
  by_cases hij : i = j
  · subst i
    simp [hie, henx, j]
  have hi0 : i.val ≠ 0 := by
    intro hz
    exact hij (Fin.ext hz)
  simp [hie, hij, hi0]

/-- If an edge's endpoint colors already agree, its voter update is identity. -/
theorem directedVoterStep_eq_of_edge_eq
    (ring : DirectedRing n) (D : Fin n → Fin n) (e : Fin n)
    (h : D e = D (ring.rightNeighbor e)) :
    directedVoterStep ring D e = D := by
  funext i
  unfold directedVoterStep
  by_cases hie : i = e
  · subst i
    simp
  by_cases hij : i = ring.rightNeighbor e
  · subst i
    simp [hie, h]
  · simp [hie, hij]

/-- Every non-boundary edge of a canonical two-domain state is a self-loop. -/
theorem nonboundary_stutters
    (hn2 : 1 < n) (x : Nat) (hx : 0 < x) (hxn : x < n)
    (ring : DirectedRing n) (e : Fin n)
    (hright : e ≠ rightBoundary x hx hxn)
    (hleft : e ≠ leftBoundary hn2) :
    directedVoterStep ring (canonicalTwoDomain hn2 x (by omega)) e =
      canonicalTwoDomain hn2 x (by omega) := by
  apply directedVoterStep_eq_of_edge_eq
  unfold canonicalTwoDomain
  by_cases hwrap : e.val + 1 < n
  · have hj : (ring.rightNeighbor e).val = e.val + 1 := by
      simp [DirectedRing.rightNeighbor, Nat.mod_eq_of_lt hwrap]
    rw [hj]
    by_cases he : e.val < x
    · have hej : e.val + 1 < x := by
        by_cases heq : e.val + 1 = x
        · have hev : e.val = x - 1 := by omega
          exact absurd (Fin.ext hev) hright
        · omega
      simp [he, hej]
    · have hej : ¬e.val + 1 < x := by omega
      simp [he, hej]
  · have heq : e.val + 1 = n := by omega
    have hev : e.val = n - 1 := by omega
    exact absurd (Fin.ext hev) hleft

/-! ## Rotation symmetry -/

/-- Rotate a color configuration one physical position clockwise. -/
def rotateRight (ring : DirectedRing n) (D : Fin n → Fin n) :
    Fin n → Fin n :=
  fun i => D (ring.leftNeighbor i)

/-- Left and right neighbor maps are inverse on a nonempty directed ring. -/
theorem leftNeighbor_rightNeighbor (ring : DirectedRing n) (i : Fin n) :
    ring.leftNeighbor (ring.rightNeighbor i) = i := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hi : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hi]
    have heq : i.val + 1 + n - 1 = n + i.val := by omega
    rw [heq, add_self_mod, Nat.mod_eq_of_lt i.isLt]
  · have hie : i.val + 1 = n := by omega
    rw [hie, Nat.mod_self]
    have hlt : n - 1 < n := by omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    omega

/-- Right and left neighbor maps are inverse on a nonempty directed ring. -/
theorem rightNeighbor_leftNeighbor (ring : DirectedRing n) (i : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor i) = i := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hi : i.val = 0
  · rw [hi]
    have hlt : n - 1 < n := by omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    have hs : n - 1 + 1 = n := by omega
    rw [hs, Nat.mod_self]
  · have heq : i.val + n - 1 = n + (i.val - 1) := by omega
    rw [heq, add_self_mod, Nat.mod_eq_of_lt (by omega : i.val - 1 < n)]
    have hs : i.val - 1 + 1 = i.val := by omega
    rw [hs, Nat.mod_eq_of_lt i.isLt]

/-- The shrunk canonical domain is exactly the `(x-1)` canonical domain rotated
one position clockwise. -/
theorem leftShrunkDomain_eq_rotateRight
    (hn2 : 1 < n) (x : Nat) (hx : 0 < x) (hxn : x < n)
    (ring : DirectedRing n) :
    leftShrunkDomain hn2 x (by omega) =
      rotateRight ring (canonicalTwoDomain hn2 (x - 1) (by omega)) := by
  funext i
  unfold leftShrunkDomain rotateRight canonicalTwoDomain
  by_cases hi0 : i.val = 0
  · have hie : i = (⟨0, by omega⟩ : Fin n) := Fin.ext hi0
    rw [hie]
    have hl : (ring.leftNeighbor (⟨0, by omega⟩ : Fin n)).val =
        n - 1 := by
      simp [DirectedRing.leftNeighbor]
    rw [hl]
    simp
    omega
  · have hl : (ring.leftNeighbor i).val = i.val - 1 := by
      simp [DirectedRing.leftNeighbor]
      have heq : i.val + n - 1 = n + (i.val - 1) := by omega
      rw [heq, add_self_mod,
        Nat.mod_eq_of_lt (by omega : i.val - 1 < n)]
    rw [hl]
    simp [hi0]
    have hiff : i.val - 1 < x - 1 ↔ i.val < x := by omega
    by_cases hi : i.val < x
    · have hprev := hiff.mpr hi
      rw [if_pos hi, if_pos hprev]
    · have hprev : ¬i.val - 1 < x - 1 := by omega
      rw [if_neg hi, if_neg hprev]

/-- Rotation commutes with one voter interaction when the scheduled edge is
rotated with the configuration. -/
theorem directedVoterStep_rotateRight
    (ring : DirectedRing n) (D : Fin n → Fin n) (e : Fin n) :
    directedVoterStep ring (rotateRight ring D) (ring.rightNeighbor e) =
      rotateRight ring (directedVoterStep ring D e) := by
  funext i
  by_cases h0 : ring.leftNeighbor i = e
  · have hi : i = ring.rightNeighbor e := by
      rw [← rightNeighbor_leftNeighbor ring i, h0]
    rw [hi]
    simp [directedVoterStep, rotateRight, leftNeighbor_rightNeighbor]
  by_cases h1 : ring.leftNeighbor i = ring.rightNeighbor e
  · have hi : i = ring.rightNeighbor (ring.rightNeighbor e) := by
      rw [← rightNeighbor_leftNeighbor ring i, h1]
    have hne : ring.rightNeighbor (ring.rightNeighbor e) ≠
        ring.rightNeighbor e := by
      intro h
      have hl := congrArg (fun z => ring.leftNeighbor z) h
      rw [leftNeighbor_rightNeighbor, leftNeighbor_rightNeighbor] at hl
      exact h0 (h1.trans hl)
    rw [hi]
    simp [directedVoterStep, rotateRight, hne,
      leftNeighbor_rightNeighbor]
  · have hi0 : i ≠ ring.rightNeighbor e := by
      intro hi
      apply h0
      rw [hi, leftNeighbor_rightNeighbor]
    have hi1 : i ≠ ring.rightNeighbor (ring.rightNeighbor e) := by
      intro hi
      apply h1
      rw [hi, leftNeighbor_rightNeighbor]
    simp [directedVoterStep, rotateRight, hi0, hi1, h0, h1]

/-- Exact one-step quotient certificate: a canonical interior two-domain state
has one `x+1` edge, one rotated `x-1` edge, and every other edge is identity.
Together with rotation equivariance, this is the lazy length process used by the
cubic Bellman equations. -/
theorem canonicalTwoDomain_lazy_quotient
    (hn2 : 1 < n) (x : Nat) (hx : 0 < x) (hxn : x < n)
    (ring : DirectedRing n) :
    directedVoterStep ring (canonicalTwoDomain hn2 x (by omega))
        (rightBoundary x hx hxn) =
        canonicalTwoDomain hn2 (x + 1) (by omega) ∧
      directedVoterStep ring (canonicalTwoDomain hn2 x (by omega))
        (leftBoundary hn2) =
        rotateRight ring (canonicalTwoDomain hn2 (x - 1) (by omega)) ∧
      ∀ e, e ≠ rightBoundary x hx hxn → e ≠ leftBoundary hn2 →
        directedVoterStep ring (canonicalTwoDomain hn2 x (by omega)) e =
          canonicalTwoDomain hn2 x (by omega) := by
  exact ⟨rightBoundary_grows hn2 x hx hxn ring,
    (leftBoundary_shrinks hn2 x hx hxn ring).trans
      (leftShrunkDomain_eq_rotateRight hn2 x hx hxn ring),
    nonboundary_stutters hn2 x hx hxn ring⟩

end PPLLEpochVoterTwoDomain
