import Leader.Wu.ShortGap.TwoDenialRearm
import Leader.Wu.ShortGap.DenialTransport

/-!
# Joining the two-receipt view and the token-walk transport

This file joins the two intermediate quotients built for the short-gap rearm
service:

* `Leader/Wu/ShortGap/TwoDenialRearm.lean` — every root carries two receipt bits
  (clockwise-gap denial arrived at its outgoing port, counterclockwise-gap
  denial arrived at its incoming port) and rearms only when both are present;
* `Leader/Wu/ShortGap/DenialTransport.lean` — every gap carries one message token
  that walks from the left root to the right root as a declaration
  (`declareRight k`), is compared there, and walks back as a denial
  (`denyLeft k`) until it is discharged at `denyLeft 0`.

With a root ring `ring : DirectedRing m`, gap `g` runs from root `g` to root
`ring.rightNeighbor g`.  The two receipt bits of the first file are read off
the token phases of the second:

* `rightReceiptOf gap i` — gap `i`'s denial token has returned to its left
  endpoint (`gap i = denyLeft 0`): root `i`'s clockwise receipt;
* `leftReceiptOf ring gap j` — the gap `ring.leftNeighbor j` (the one ending
  at `j`) has reached its compare/deny phase (`denyLeft k` for some `k`): the
  declaration reached root `j`, which compared and holds its own denial
  receipt for its counterclockwise gap.

The file proves that these projections are monotone along the token walk,
that "every gap discharged" is exactly "every root rearmed", that the
two-receipt missing count is bounded by the remaining token hops (so the
two-receipt potential is bounded by the transport potential), and that the
fresh all-declare start projects to all receipts false.  Hence the
two-receipt state is a monotone projection of the multi-gap token transport
whose potential the transport potential dominates.  No step-level simulation
between `multiGapStep` and `twoDenialStep` is proved here; the two quotients
are related through the projection and the potential inequality only.

**Honest cost remark.**  For `h = 1` the token needs two firings of the single
gap edge (`declareRight 0 → denyLeft 1 → denyLeft 0`), one hop more than the
atomic two-sided delivery of `shortGap_edge_delivers_both`, where one firing
of the shared edge sets both incident receipts.  Stop-and-wait costs two edge
firings even at physical length one; this file does not hide that.

**Abstraction boundary.**  `participating` is all-true (the uniform
all-denial word).  There is still no modelling of receipt staleness or
currentness authentication, forged declarations or receipts, or
serializer/abort obligations, and the gap edge sets are given abstractly by
the `GapLayout`.  Nothing here claims complete leader stabilization or a final
complexity bound.
-/

namespace ShortGapTwoDenialJoin

open FiniteUniformStoppingTree
open PeriodHIncidenceChoice
open ShortGapChoiceStopping
open ShortGapTwoDenialRearm
open ShortGapDenialTransport

set_option autoImplicit false

/-! ## Ring re-indexing helpers -/

private theorem leftNeighbor_rightNeighbor
    {n : Nat} (ring : DirectedRing n) (i : Fin n) :
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

private theorem sum_ofFn_rightNeighbor
    {n : Nat} (ring : DirectedRing n) (f : Fin n → Nat) :
    (List.ofFn (fun e => f (ring.rightNeighbor e))).sum =
      (List.ofFn f).sum := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt ring.hn)
  subst n
  rw [show List.ofFn (fun e : Fin (k + 1) => f (ring.rightNeighbor e)) =
    (List.ofFn (fun i : Fin k =>
      f (ring.rightNeighbor i.castSucc))) ++
      [f (ring.rightNeighbor (Fin.last k))] from List.ofFn_succ_last]
  rw [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero,
    List.ofFn_succ, List.sum_cons]
  have hlast : ring.rightNeighbor (Fin.last k) = 0 := by
    apply Fin.ext
    simp [DirectedRing.rightNeighbor]
  have hsucc : ∀ i : Fin k,
      ring.rightNeighbor i.castSucc = i.succ := by
    intro i
    apply Fin.ext
    simp [DirectedRing.rightNeighbor,
      Nat.mod_eq_of_lt (by omega : i.val + 1 < k + 1)]
  rw [hlast]
  have hfun :
      (fun i : Fin k => f (ring.rightNeighbor i.castSucc)) =
        (fun i : Fin k => f i.succ) := by
    funext i
    rw [hsucc]
  rw [hfun]
  omega

private theorem sum_ofFn_leftNeighbor
    {n : Nat} (ring : DirectedRing n) (f : Fin n → Nat) :
    (List.ofFn (fun e => f (ring.leftNeighbor e))).sum =
      (List.ofFn f).sum := by
  have h := sum_ofFn_rightNeighbor ring
    (fun e => f (ring.leftNeighbor e))
  simp only [leftNeighbor_rightNeighbor] at h
  exact h.symm

private theorem ofFn_sum_add_split {m : Nat} (f g : Fin m → Nat) :
    (List.ofFn (fun i => f i + g i)).sum =
      (List.ofFn f).sum + (List.ofFn g).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [List.ofFn_succ, List.sum_cons]
      rw [ih (fun i => f i.succ) (fun i => g i.succ)]
      omega

/-! ## Receipt phases of one gap token -/

/-- The gap is discharged: its denial token is back at the left root. -/
def isDischarged {h : Nat} : GapDenialState h → Bool
  | .denyLeft 0 _ => true
  | _ => false

/-- The gap has reached its compare/deny phase: the declaration arrived at
the right root, which compared it and now holds its receipt. -/
def isDenying {h : Nat} : GapDenialState h → Bool
  | .denyLeft _ _ => true
  | .declareRight _ _ => false

theorem isDischarged_iff_hops {h : Nat} (s : GapDenialState h) :
    isDischarged s = true ↔ s.hops = 0 := by
  cases s with
  | declareRight k hk =>
      simp only [isDischarged, GapDenialState.hops]
      constructor
      · intro hfalse
        exact absurd hfalse (by simp)
      · intro hzero
        omega
  | denyLeft k hk =>
      cases k with
      | zero => simp [isDischarged, GapDenialState.hops]
      | succ k => simp [isDischarged, GapDenialState.hops]

theorem isDenying_of_isDischarged {h : Nat} (s : GapDenialState h)
    (hs : isDischarged s = true) : isDenying s = true := by
  cases s with
  | declareRight k hk => simp [isDischarged] at hs
  | denyLeft k hk => rfl

/-- Missing receipts attributable to one gap (its left root's clockwise
receipt and its right root's counterclockwise receipt) never exceed its
remaining hops: a declaring gap still owes both and has at least two hops, a
returning denial owes exactly one, a discharged gap owes none. -/
theorem gapMissing_le_hops {h : Nat} (s : GapDenialState h) :
    (if isDischarged s then 0 else 1) + (if isDenying s then 0 else 1) ≤
      s.hops := by
  cases s with
  | declareRight k hk =>
      simp only [isDischarged, isDenying, GapDenialState.hops]
      simp
      omega
  | denyLeft k hk =>
      cases k with
      | zero => simp [isDischarged, isDenying, GapDenialState.hops]
      | succ k => simp [isDischarged, isDenying, GapDenialState.hops]

/-! ## Monotonicity along the token walk -/

theorem isDischarged_localStep {n h : Nat} (edgeAt : Fin h → Fin n)
    (s : GapDenialState h) (e : Fin n) (hs : isDischarged s = true) :
    isDischarged (GapDenialState.localStep edgeAt s e) = true := by
  cases s with
  | declareRight k hk => simp [isDischarged] at hs
  | denyLeft k hk =>
      cases k with
      | zero =>
          simp [GapDenialState.localStep, GapDenialState.advanceEdge,
            isDischarged]
      | succ k => simp [isDischarged] at hs

theorem isDenying_localStep {n h : Nat} (edgeAt : Fin h → Fin n)
    (s : GapDenialState h) (e : Fin n) (hs : isDenying s = true) :
    isDenying (GapDenialState.localStep edgeAt s e) = true := by
  cases s with
  | declareRight k hk => simp [isDenying] at hs
  | denyLeft k hk =>
      cases k with
      | zero =>
          simp [GapDenialState.localStep, GapDenialState.advanceEdge,
            isDenying]
      | succ k =>
          simp only [GapDenialState.localStep, GapDenialState.advanceEdge]
          split <;> simp [GapDenialState.advance, isDenying]

/-! ## Receipt projection of the multi-gap state -/

/-- Root `i`'s clockwise receipt: gap `i` (from `i` to its right neighbour)
has been discharged. -/
def rightReceiptOf {h m : Nat} (gap : Fin m → GapDenialState h) (i : Fin m) :
    Bool :=
  isDischarged (gap i)

/-- Root `j`'s counterclockwise receipt: the gap ending at `j`, namely gap
`ring.leftNeighbor j`, has reached its compare/deny phase. -/
def leftReceiptOf {h m : Nat} (ring : DirectedRing m)
    (gap : Fin m → GapDenialState h) (j : Fin m) : Bool :=
  isDenying (gap (ring.leftNeighbor j))

/-- Root `i` may rearm: both receipts present. -/
def rearmedOf {h m : Nat} (ring : DirectedRing m)
    (gap : Fin m → GapDenialState h) (i : Fin m) : Bool :=
  rightReceiptOf gap i && leftReceiptOf ring gap i

theorem rightReceiptOf_multiLocalStep {n h m : Nat} (L : GapLayout n h m)
    (gap : Fin m → GapDenialState h) (e : Fin n) (i : Fin m)
    (hi : rightReceiptOf gap i = true) :
    rightReceiptOf (multiLocalStep L gap e) i = true :=
  isDischarged_localStep (L.edgeAt i) (gap i) e hi

theorem leftReceiptOf_multiLocalStep {n h m : Nat} (ring : DirectedRing m)
    (L : GapLayout n h m) (gap : Fin m → GapDenialState h) (e : Fin n)
    (j : Fin m) (hj : leftReceiptOf ring gap j = true) :
    leftReceiptOf ring (multiLocalStep L gap e) j = true :=
  isDenying_localStep (L.edgeAt (ring.leftNeighbor j))
    (gap (ring.leftNeighbor j)) e hj

/-- Receipts, hence rearm permissions, are never withdrawn by a scheduler
edge of the token transport. -/
theorem rearmedOf_multiLocalStep {n h m : Nat} (ring : DirectedRing m)
    (L : GapLayout n h m) (gap : Fin m → GapDenialState h) (e : Fin n)
    (i : Fin m) (hi : rearmedOf ring gap i = true) :
    rearmedOf ring (multiLocalStep L gap e) i = true := by
  simp only [rearmedOf, Bool.and_eq_true] at hi ⊢
  exact ⟨rightReceiptOf_multiLocalStep L gap e i hi.1,
    leftReceiptOf_multiLocalStep ring L gap e i hi.2⟩

/-! ## Discharge of all gaps is rearm of all roots -/

/-- Every gap has been discharged iff every root holds both receipts. -/
theorem allDone_iff {h m : Nat} (ring : DirectedRing m)
    (gap : Fin m → GapDenialState h) :
    (∀ g, (gap g).hops = 0) ↔ (∀ i, rearmedOf ring gap i = true) := by
  constructor
  · intro hall i
    simp only [rearmedOf, rightReceiptOf, leftReceiptOf, Bool.and_eq_true]
    exact ⟨(isDischarged_iff_hops _).2 (hall i),
      isDenying_of_isDischarged _ ((isDischarged_iff_hops _).2 (hall _))⟩
  · intro hall g
    have hg := hall g
    simp only [rearmedOf, rightReceiptOf, Bool.and_eq_true] at hg
    exact (isDischarged_iff_hops _).1 hg.1

/-- Some gap still in transit means some root still misses a receipt (in
fact its clockwise receipt). -/
theorem rightReceiptOf_eq_false_of_hops_pos {h m : Nat}
    (gap : Fin m → GapDenialState h) (g : Fin m) (hg : 0 < (gap g).hops) :
    rightReceiptOf gap g = false := by
  have hnot : ¬ isDischarged (gap g) = true := by
    intro hd
    have := (isDischarged_iff_hops _).1 hd
    omega
  simpa [rightReceiptOf] using hnot

/-! ## Missing receipts are bounded by remaining hops -/

/-- The two-receipt missing count (all roots participating) is at most the
total remaining token hops.  Each gap accounts for its left root's clockwise
receipt and its right root's counterclockwise receipt; the left-receipt sum
over roots is re-indexed to a sum over gaps through `ring.leftNeighbor`. -/
theorem missingCount_le_totalHops {h m : Nat} (ring : DirectedRing m)
    (gap : Fin m → GapDenialState h) :
    missingCount (fun _ => true) (rightReceiptOf gap)
        (leftReceiptOf ring gap) ≤
      totalHops gap := by
  have hweight : missingWeight (fun _ : Fin m => true) (rightReceiptOf gap)
      (leftReceiptOf ring gap) =
        fun i => (if isDischarged (gap i) then 0 else 1) +
          (if isDenying (gap (ring.leftNeighbor i)) then 0 else 1) := by
    funext i
    simp only [missingWeight, rightReceiptOf, leftReceiptOf]
    by_cases hd : isDischarged (gap i) = true <;>
      by_cases hn : isDenying (gap (ring.leftNeighbor i)) = true <;>
      simp [hd, hn]
  have hleft : (List.ofFn (fun i : Fin m =>
      if isDenying (gap (ring.leftNeighbor i)) then 0 else 1)).sum =
        (List.ofFn (fun g : Fin m => if isDenying (gap g) then 0 else 1)).sum :=
    sum_ofFn_leftNeighbor ring (fun g => if isDenying (gap g) then 0 else 1)
  rw [missingCount, hweight, ofFn_sum_add_split, hleft, ← ofFn_sum_add_split]
  exact ofFn_sum_le _ _ (fun g => gapMissing_le_hops (gap g))

/-- The two-receipt state read off a multi-gap transport state. -/
def toTwoDenialState {h m : Nat} (ring : DirectedRing m)
    (state : MultiGapState h m) : TwoDenialState m :=
  ⟨fun _ => true, rightReceiptOf state.gap, leftReceiptOf ring state.gap, by
    obtain ⟨g, hg⟩ := state.hasActive
    exact ⟨g, rfl, Or.inl (rightReceiptOf_eq_false_of_hops_pos state.gap g hg)⟩⟩

/-- The two-receipt potential of the projected state never exceeds the
token-transport potential. -/
theorem twoDenialPotential_toTwoDenialState_le {n h m : Nat}
    (ring : DirectedRing m) (state : MultiGapState h m) :
    twoDenialPotential (n := n) (.active (toTwoDenialState ring state)) ≤
      multiGapPotential (n := n) (.active state) := by
  simp only [twoDenialPotential, multiGapPotential, toTwoDenialState]
  exact Nat.mul_le_mul_left n (missingCount_le_totalHops ring state.gap)

/-! ## Fresh start -/

@[simp] theorem rightReceiptOf_allDeclare {h m : Nat} (hpos : 0 < h)
    (i : Fin m) :
    rightReceiptOf (fun _ : Fin m => GapDenialState.declareRight 0 hpos) i =
      false := rfl

@[simp] theorem leftReceiptOf_allDeclare {h m : Nat} (ring : DirectedRing m)
    (hpos : 0 < h) (j : Fin m) :
    leftReceiptOf ring (fun _ : Fin m => GapDenialState.declareRight 0 hpos)
      j = false := rfl

@[simp] theorem rearmedOf_allDeclare {h m : Nat} (ring : DirectedRing m)
    (hpos : 0 < h) (i : Fin m) :
    rearmedOf ring (fun _ : Fin m => GapDenialState.declareRight 0 hpos) i =
      false := rfl

/-- The fresh all-declare start of the transport projects to the all-pending
two-receipt start: no root holds any receipt. -/
theorem toTwoDenialState_allDeclareStart {n h m : Nat}
    (ring : DirectedRing m) (L : GapLayout n h m) (hm : 0 < m) :
    toTwoDenialState ring (allDeclareStart L hm) =
      allPendingTwoDenialState hm := rfl

/-! ## Length-one gap: two firings, not one -/

/-- For `h = 1` the single gap edge must fire twice: first the declaration
crosses to the right root (`declareRight 0 → denyLeft 1`), then the denial
returns (`denyLeft 1 → denyLeft 0`).  Compare `shortGap_edge_delivers_both`,
where one firing of the shared edge sets both incident receipts atomically:
the stop-and-wait transport costs one hop more even at physical length one. -/
theorem shortGap_h1_atomic {n : Nat} (edgeAt : Fin 1 → Fin n) :
    GapDenialState.localStep edgeAt
        (GapDenialState.declareRight (h := 1) 0 Nat.one_pos) (edgeAt 0) =
      GapDenialState.denyLeft 1 (Nat.le_refl 1) ∧
    GapDenialState.localStep edgeAt
        (GapDenialState.denyLeft (h := 1) 1 (Nat.le_refl 1)) (edgeAt 0) =
      GapDenialState.denyLeft 0 (Nat.zero_le 1) := by
  constructor
  · simp [GapDenialState.localStep, GapDenialState.advanceEdge,
      GapDenialState.advance]
  · simp [GapDenialState.localStep, GapDenialState.advanceEdge,
      GapDenialState.advance]

theorem hops_declareRight_h1 :
    (GapDenialState.declareRight (h := 1) 0 Nat.one_pos).hops = 2 := rfl

#print axioms allDone_iff
#print axioms missingCount_le_totalHops
#print axioms rearmedOf_multiLocalStep
#print axioms twoDenialPotential_toTwoDenialState_le
#print axioms toTwoDenialState_allDeclareStart
#print axioms shortGap_h1_atomic

end ShortGapTwoDenialJoin
