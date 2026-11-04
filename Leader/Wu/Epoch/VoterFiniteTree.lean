import Leader.Wu.Epoch.VoterTwoDomain

/-!
# Exact finite scheduler tree for the two-domain voter quotient

This file counts length-`t` uniform edge words that have not yet reached voter
consensus.  Rotation invariance and the concrete two-boundary classification
reduce the actual directed-voter tree exactly to a lazy walk on the domain
length: one grow action, one shrink action, and `n-2` stutters.

The result is finite combinatorics.  It introduces no measure, expectation, or
independence assumption and preserves every scheduler multiplicity.
-/

namespace PPLLEpochVoterFiniteTree

open PPLLEpochVoterReduction PPLLEpochVoterTwoDomain

/-! ## Consensus and rotation-invariant miss trees -/

/-- All positions carry one common voter color. -/
def VoterConsensus (D : Fin n → Fin n) : Prop :=
  ∃ color : Fin n, ∀ i, D i = color

/-- Consensus is invariant under a one-position physical rotation. -/
theorem voterConsensus_rotateRight_iff
    (ring : DirectedRing n) (D : Fin n → Fin n) :
    VoterConsensus (rotateRight ring D) ↔ VoterConsensus D := by
  constructor
  · rintro ⟨color, hcolor⟩
    refine ⟨color, ?_⟩
    intro i
    have h := hcolor (ring.rightNeighbor i)
    simpa [rotateRight, leftNeighbor_rightNeighbor] using h
  · rintro ⟨color, hcolor⟩
    exact ⟨color, fun i => hcolor (ring.leftNeighbor i)⟩

/-- Number of exact length-`t` scheduler words that have not visited consensus.
Consensus states contribute zero at every later horizon. -/
noncomputable def voterMissTree (ring : DirectedRing n) :
    (Fin n → Fin n) → Nat → Nat
  | D, 0 => @ite Nat (VoterConsensus D) (Classical.propDecidable _) 0 1
  | D, t + 1 =>
      @ite Nat (VoterConsensus D) (Classical.propDecidable _) 0
        ((List.ofFn (fun e : Fin n =>
          voterMissTree ring (directedVoterStep ring D e) t)).sum)

private theorem sum_ofFn_rightNeighbor
    (ring : DirectedRing n) (f : Fin n → Nat) :
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
    (ring : DirectedRing n) (f : Fin n → Nat) :
    (List.ofFn (fun e => f (ring.leftNeighbor e))).sum =
      (List.ofFn f).sum := by
  have h := sum_ofFn_rightNeighbor ring
    (fun e => f (ring.leftNeighbor e))
  simp only [leftNeighbor_rightNeighbor] at h
  exact h.symm

/-- Rotating a voter configuration does not change its exact miss count. -/
theorem voterMissTree_rotateRight
    (ring : DirectedRing n) (D : Fin n → Fin n) (t : Nat) :
    voterMissTree ring (rotateRight ring D) t = voterMissTree ring D t := by
  induction t generalizing D with
  | zero =>
      simp only [voterMissTree]
      rw [show VoterConsensus (rotateRight ring D) = VoterConsensus D from
        propext (voterConsensus_rotateRight_iff ring D)]
  | succ t ih =>
      simp only [voterMissTree]
      have hcons := voterConsensus_rotateRight_iff ring D
      by_cases hD : VoterConsensus D
      · rw [if_pos hD, if_pos (hcons.2 hD)]
      · have hrot : ¬VoterConsensus (rotateRight ring D) := by
          intro h
          exact hD (hcons.1 h)
        rw [if_neg hD, if_neg hrot]
        have hpoint : ∀ e : Fin n,
            voterMissTree ring
                (directedVoterStep ring (rotateRight ring D) e) t =
              voterMissTree ring
                (directedVoterStep ring D (ring.leftNeighbor e)) t := by
          intro e
          have hstep := directedVoterStep_rotateRight ring D
            (ring.leftNeighbor e)
          rw [rightNeighbor_leftNeighbor] at hstep
          rw [hstep, ih]
        have hfun :
            (fun e : Fin n => voterMissTree ring
              (directedVoterStep ring (rotateRight ring D) e) t) =
            (fun e : Fin n => voterMissTree ring
              (directedVoterStep ring D (ring.leftNeighbor e)) t) := by
          funext e
          exact hpoint e
        rw [hfun]
        simpa [Function.comp_def] using sum_ofFn_leftNeighbor ring
          (fun e => voterMissTree ring (directedVoterStep ring D e) t)

/-! ## Two exceptional outcomes in a finite sum -/

private theorem sum_map_const (xs : List α) (c : Nat) :
    (xs.map fun _ => c).sum = xs.length * c := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.succ_mul, Nat.add_comm]

private theorem pred_mul (L c : Nat) (hL : 0 < L) :
    c + (L - 1) * c = L * c := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
  subst L
  simp [Nat.succ_mul, Nat.add_comm]

private theorem sum_one_exception
    [BEq α] [LawfulBEq α]
    (xs : List α) (a : α) (f : α → Nat) (c : Nat)
    (hnodup : xs.Nodup) (ha : a ∈ xs)
    (hother : ∀ z, z ∈ xs → z ≠ a → f z = c) :
    (xs.map f).sum = f a + (xs.length - 1) * c := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
      rw [List.nodup_cons] at hnodup
      by_cases hxa : x = a
      · subst x
        have hall : xs.map f = xs.map (fun _ => c) := by
          apply List.map_congr_left
          intro z hz
          exact hother z (by simp [hz])
            (by intro q; subst z; exact hnodup.1 hz)
        rw [List.map_cons, List.sum_cons, hall, sum_map_const]
        simp
      · have hat : a ∈ xs := by
          rcases List.mem_cons.mp ha with hax | hat
          · exact absurd hax.symm hxa
          · exact hat
        have hot : ∀ z, z ∈ xs → z ≠ a → f z = c := by
          intro z hz
          exact hother z (by simp [hz])
        have hi := ih hnodup.2 hat hot
        have hx : f x = c := hother x (by simp) hxa
        rw [List.map_cons, List.sum_cons, hx, hi, List.length_cons]
        have hpos : 0 < xs.length :=
          List.length_pos_iff.mpr (List.ne_nil_of_mem hat)
        have hc := pred_mul xs.length c hpos
        have hsub : xs.length + 1 - 1 = xs.length := by omega
        rw [hsub]
        omega

private theorem sum_two_exceptions
    [BEq α] [LawfulBEq α]
    (xs : List α) (a b : α) (f : α → Nat) (c : Nat)
    (hnodup : xs.Nodup) (ha : a ∈ xs) (hb : b ∈ xs) (hab : a ≠ b)
    (hother : ∀ z, z ∈ xs → z ≠ a → z ≠ b → f z = c) :
    (xs.map f).sum = f a + f b + (xs.length - 2) * c := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
      rw [List.nodup_cons] at hnodup
      by_cases hxa : x = a
      · subst x
        have hbt : b ∈ xs := by
          rcases List.mem_cons.mp hb with hbx | hbt
          · exact absurd hbx.symm hab
          · exact hbt
        have hone := sum_one_exception xs b f c hnodup.2 hbt (by
          intro z hz hzb
          exact hother z (by simp [hz])
            (by intro hza; subst z; exact hnodup.1 hz) hzb)
        rw [List.map_cons, List.sum_cons, hone, List.length_cons]
        have hlen : 0 < xs.length :=
          List.length_pos_iff.mpr (List.ne_nil_of_mem hbt)
        have hsub : xs.length + 1 - 2 = xs.length - 1 := by omega
        rw [hsub]
        omega
      by_cases hxb : x = b
      · subst x
        have hat : a ∈ xs := by
          rcases List.mem_cons.mp ha with hax | hat
          · exact absurd hax hab
          · exact hat
        have hone := sum_one_exception xs a f c hnodup.2 hat (by
          intro z hz hza
          exact hother z (by simp [hz]) hza
            (by intro hzb; subst z; exact hnodup.1 hz))
        rw [List.map_cons, List.sum_cons, hone, List.length_cons]
        have hlen : 0 < xs.length :=
          List.length_pos_iff.mpr (List.ne_nil_of_mem hat)
        have hsub : xs.length + 1 - 2 = xs.length - 1 := by omega
        rw [hsub]
        omega
      · have hat : a ∈ xs := by
          rcases List.mem_cons.mp ha with hax | hat
          · exact absurd hax.symm hxa
          · exact hat
        have hbt : b ∈ xs := by
          rcases List.mem_cons.mp hb with hbx | hbt
          · exact absurd hbx.symm hxb
          · exact hbt
        have hot : ∀ z, z ∈ xs → z ≠ a → z ≠ b → f z = c := by
          intro z hz
          exact hother z (by simp [hz])
        have hi := ih hnodup.2 hat hbt hot
        have hx : f x = c := hother x (by simp) hxa hxb
        rw [List.map_cons, List.sum_cons, hx, hi, List.length_cons]
        have hlen : 2 ≤ xs.length := by
          have h1 : 0 < xs.length :=
            List.length_pos_iff.mpr (List.ne_nil_of_mem hat)
          by_cases hlen1 : xs.length = 1
          · rw [List.length_eq_one_iff] at hlen1
            obtain ⟨z, hz⟩ := hlen1
            subst xs
            simp at hat hbt
            exact absurd (hat.trans hbt.symm) hab
          · omega
        have hLp : 0 < xs.length - 1 := by omega
        have hc := pred_mul (xs.length - 1) c hLp
        have hidx : xs.length + 1 - 2 = xs.length - 1 := by omega
        have hidx2 : xs.length - 1 - 1 = xs.length - 2 := by omega
        rw [hidx2] at hc
        rw [hidx]
        omega

/-! ## Exact lazy length recurrence -/

/-- Exact miss count of the quotient lazy domain-length action tree. -/
def lazyDomainMissCount (n x : Nat) : Nat → Nat
  | 0 => if x = 0 ∨ x = n then 0 else 1
  | t + 1 => if x = 0 ∨ x = n then 0
    else (n - 2) * lazyDomainMissCount n x t +
      lazyDomainMissCount n (x - 1) t +
      lazyDomainMissCount n (x + 1) t

/-- A canonical two-domain state is consensus exactly at lengths zero and `n`. -/
theorem canonicalTwoDomain_consensus_iff
    (hn2 : 1 < n) (x : Nat) (hx : x ≤ n) :
    VoterConsensus (canonicalTwoDomain hn2 x hx) ↔ x = 0 ∨ x = n := by
  constructor
  · intro hcons
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    by_cases hxn : x = n
    · exact Or.inr hxn
    have hxpos : 0 < x := by omega
    have hxlt : x < n := by omega
    obtain ⟨color, hcolor⟩ := hcons
    have hzero := hcolor (⟨0, by omega⟩ : Fin n)
    have hone := hcolor (⟨x, hxlt⟩ : Fin n)
    have heq := hzero.trans hone.symm
    simp [canonicalTwoDomain, hxpos] at heq
    have hv := congrArg Fin.val heq
    contradiction
  · intro hboundary
    rcases hboundary with rfl | rfl
    · exact ⟨oneColor hn2, by
        intro i
        simp [canonicalTwoDomain]⟩
    · exact ⟨zeroColor (by omega), by
        intro i
        simp [canonicalTwoDomain, Nat.lt_of_lt_of_le i.isLt (Nat.le_refl n)]⟩

/-- The actual finite voter miss tree on every canonical contiguous domain is
exactly the lazy domain-length recurrence, including all scheduler
multiplicities. -/
theorem voterMissTree_canonicalTwoDomain
    (hn2 : 1 < n) (ring : DirectedRing n) :
    ∀ t x (hx : x ≤ n),
      voterMissTree ring (canonicalTwoDomain hn2 x hx) t =
        lazyDomainMissCount n x t := by
  intro t
  induction t with
  | zero =>
      intro x hx
      simp only [voterMissTree, lazyDomainMissCount]
      rw [show VoterConsensus (canonicalTwoDomain hn2 x hx) =
        (x = 0 ∨ x = n) from
          propext (canonicalTwoDomain_consensus_iff hn2 x hx)]
      by_cases hboundary : x = 0 ∨ x = n
      · rw [if_pos hboundary, if_pos hboundary]
      · rw [if_neg hboundary, if_neg hboundary]
  | succ t ih =>
      intro x hxle
      simp only [voterMissTree, lazyDomainMissCount]
      rw [show VoterConsensus (canonicalTwoDomain hn2 x hxle) =
        (x = 0 ∨ x = n) from
          propext (canonicalTwoDomain_consensus_iff hn2 x hxle)]
      by_cases hboundary : x = 0 ∨ x = n
      · rw [if_pos hboundary, if_pos hboundary]
      · rw [if_neg hboundary, if_neg hboundary]
        have hx : 0 < x := by omega
        have hxn : x < n := by omega
        let a := rightBoundary x hx hxn
        let b := leftBoundary hn2
        let D := canonicalTwoDomain hn2 x hxle
        let f := fun e : Fin n =>
          voterMissTree ring (directedVoterStep ring D e) t
        let xs := List.ofFn (fun i : Fin n => i)
        have hnodup : xs.Nodup := by
          exact ExhaustiveList.values_nodup_fin n
        have ha : a ∈ xs := by
          exact List.mem_ofFn.mpr ⟨a, rfl⟩
        have hb : b ∈ xs := by
          exact List.mem_ofFn.mpr ⟨b, rfl⟩
        have hab : a ≠ b := by
          intro h
          have hv := congrArg Fin.val h
          dsimp [a, b, rightBoundary, leftBoundary] at hv
          omega
        have hother : ∀ z, z ∈ xs → z ≠ a → z ≠ b →
            f z = voterMissTree ring D t := by
          intro z hz hza hzb
          dsimp [f, D]
          rw [nonboundary_stutters hn2 x hx hxn ring z hza hzb]
        have hsum := sum_two_exceptions xs a b f
          (voterMissTree ring D t) hnodup ha hb hab hother
        have hfa : f a = lazyDomainMissCount n (x + 1) t := by
          dsimp [f, a, D]
          rw [rightBoundary_grows hn2 x hx hxn ring]
          exact ih (x + 1) (by omega)
        have hfb : f b = lazyDomainMissCount n (x - 1) t := by
          dsimp [f, b, D]
          rw [leftBoundary_shrinks hn2 x hx hxn ring,
            leftShrunkDomain_eq_rotateRight hn2 x hx hxn ring,
            voterMissTree_rotateRight]
          exact ih (x - 1) (by omega)
        have hfc : voterMissTree ring D t =
            lazyDomainMissCount n x t := by
          exact ih x hxle
        have hlen : xs.length = n := by
          simp [xs]
        have hmap : xs.map f = List.ofFn f := by
          simp [xs, List.map_ofFn, Function.comp_def]
        rw [← hmap]
        rw [hsum, hfa, hfb, hfc, hlen]
        omega

end PPLLEpochVoterFiniteTree
