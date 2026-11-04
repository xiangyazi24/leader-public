import Leader.L3.Top.FreshTailTicketBarrier

/-!
Q7c P.3 J4 source half (I.prepaid):
the prepaid potential Phi_* (the model check's (c*) budget) on the
actual reached trace of a leaderless fixed-public entrance.

Site credits, by OLD-free token at source offset j of the nominated
block: E 0; U r-j+1 (0 at the border, whose U is covered by the
border reserve); D(false) r-j; D(true) b(j) = (r-j) + sum over
k = max(j,1) .. r-1 of (r-k+1), prepaying the parent's remaining
travel and one future oldVisit child per offset. The frontier F1 is
the rightmost live fresh-border D(true). Without F1 the potential is
the border reserve (r+2 for E/D(false) at offset zero, r+1 for U/D(true))
plus all site credits; with F1 at f it is (r-f) plus the credits of
the sites ahead of f.
-/

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- childSum d = 2 + 3 + ... + (d+1): the prepaid services of the
oldVisit children an inherited tail can still mint at d offsets. -/
def topFreshTailPrepaidChildSum : Nat → Nat
  | 0 => 0
  | d + 1 => (d + 2) + topFreshTailPrepaidChildSum d

/-- b(j) = (r-j) + sum_{k=max(j,1)}^{r-1} (r-k+1). -/
def topFreshTailPrepaidTailCredit (r j : Nat) : Nat :=
  (r - j) + topFreshTailPrepaidChildSum (r - max j 1)

/-- Credit of one source output token at offset j. -/
def topFreshTailPrepaidTokenCredit {A : Nat} (r j : Nat) : OutTok A → Nat
  | .E => 0
  | .U => if j = 0 then 0 else r - j + 1
  | .D _ false => r - j
  | .D _ true => topFreshTailPrepaidTailCredit r j

/-- Border reserve for producing the first genuine border sample. -/
def topFreshTailPrepaidReserve {A : Nat} (r : Nat) : OutTok A → Nat
  | .U => r + 1
  | .D _ true => r + 1
  | _ => r + 2

/-- Largest m' < m with P m' (a frontier search). -/
noncomputable def topFreshTailPrepaidSearch (P : Nat → Prop) : Nat → Option Nat
  | 0 => none
  | m + 1 => if P m then some m else topFreshTailPrepaidSearch P m

/-- A live fresh-border D(true) at source offset k. -/
def TopFreshTailPrepaidFreshTail
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) (k : Nat) : Prop :=
  ∃ (h : k < topClockSpan n) (a : TopFreshTailCarrier (topClockSpan n))
    (v : Fin (compileAdvice (ceilLogTwo n)).topA),
    (topFreshTailGenealogy ring C s Z).slots ⟨k, h⟩ = some a ∧
    topFreshTailTicketIsFresh a.origin = true ∧
    (Z.1.1 (certSite s k)).qOut = .D v true

/-- F1: the rightmost live fresh-border D(true). -/
noncomputable def topFreshTailPrepaidFrontier
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) : Option Nat :=
  topFreshTailPrepaidSearch (TopFreshTailPrepaidFreshTail ring C s Z) (topClockSpan n)

/-- Sum of the site credits at offsets lo .. r-1. -/
def topFreshTailPrepaidSumFrom
    {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) (lo : Nat) : Nat :=
  ((List.range (topClockSpan n)).map (fun j =>
    if lo ≤ j then
      topFreshTailPrepaidTokenCredit (topClockSpan n) j (Z.1.1 (certSite s j)).qOut
    else 0)).sum

/-- The prepaid potential Phi_*. -/
noncomputable def topFreshTailPrepaidPotential
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) : Nat :=
  match topFreshTailPrepaidFrontier ring C s Z with
  | none =>
      topFreshTailPrepaidReserve (topClockSpan n) (Z.1.1 (certSite s 0)).qOut +
        topFreshTailPrepaidSumFrom s Z 0
  | some f => (topClockSpan n - f) + topFreshTailPrepaidSumFrom s Z (f + 1)

/-- Prepayment transfer at an interior inherited-tail hop:
b(j) = 1 + (r-j+1) + b(j+1) for 1 <= j < r (b(r) = 0).
Consumer: topFreshTailPrepaidSourceContactStep. -/
theorem topFreshTailPrepaidTailTransfer (r j : Nat) (h1 : 1 ≤ j) (hj : j < r) :
    topFreshTailPrepaidTailCredit r j =
      1 + (r - j + 1) + topFreshTailPrepaidTailCredit r (j + 1) := by
  unfold topFreshTailPrepaidTailCredit
  have hm1 : max j 1 = j := by omega
  have hm2 : max (j + 1) 1 = j + 1 := by omega
  rw [hm1, hm2, show r - j = (r - (j + 1)) + 1 by omega, topFreshTailPrepaidChildSum]
  omega

/-- Border transfer: b(0) = 1 + b(1). Consumer:
topFreshTailPrepaidSourceContactStep. -/
theorem topFreshTailPrepaidTailBorder (r : Nat) (hr : 1 ≤ r) :
    topFreshTailPrepaidTailCredit r 0 = 1 + topFreshTailPrepaidTailCredit r 1 := by
  unfold topFreshTailPrepaidTailCredit
  have hm1 : max 0 1 = 1 := rfl
  have hm2 : max 1 1 = 1 := rfl
  rw [hm1, hm2]
  omega

/-- A found frontier is a fresh tail with none to its right.
Consumer: topFreshTailPrepaidSourceContactStep. -/
theorem topFreshTailPrepaidSearchSome (P : Nat → Prop) :
    ∀ (m f : Nat), topFreshTailPrepaidSearch P m = some f →
      P f ∧ f < m ∧ ∀ k, f < k → k < m → ¬ P k := by
  intro m
  induction m with
  | zero => intro f h; cases h
  | succ m ih =>
      intro f h
      unfold topFreshTailPrepaidSearch at h
      by_cases hp : P m
      · rw [if_pos hp] at h
        cases h
        exact ⟨hp, by omega, fun k h1 h2 => by omega⟩
      · rw [if_neg hp] at h
        obtain ⟨h1, h2, h3⟩ := ih f h
        refine ⟨h1, by omega, ?_⟩
        intro k hk1 hk2
        by_cases hkm : k = m
        · subst hkm; exact hp
        · exact h3 k hk1 (by omega)

/-- No frontier means no fresh tail below the bound.
Consumer: topFreshTailPrepaidSourceContactStep. -/
theorem topFreshTailPrepaidSearchNone (P : Nat → Prop) :
    ∀ m, topFreshTailPrepaidSearch P m = none → ∀ k, k < m → ¬ P k := by
  intro m
  induction m with
  | zero => intro _ k hk; omega
  | succ m ih =>
      intro h k hk
      unfold topFreshTailPrepaidSearch at h
      by_cases hp : P m
      · rw [if_pos hp] at h; cases h
      · rw [if_neg hp] at h
        by_cases hkm : k = m
        · subst hkm; exact hp
        · exact ih h k (by omega)

/-- The frontier search only reads P below its bound.
Consumer: frontier preservation in topFreshTailPrepaidSourceContactStep. -/
theorem topFreshTailPrepaidSearchCongr (P Q : Nat → Prop) :
    ∀ m, (∀ k, k < m → (P k ↔ Q k)) →
      topFreshTailPrepaidSearch P m = topFreshTailPrepaidSearch Q m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
      intro h
      unfold topFreshTailPrepaidSearch
      have hm := h m (by omega)
      have hrest := ih (fun k hk => h k (by omega))
      by_cases hp : P m
      · rw [if_pos hp, if_pos (hm.1 hp)]
      · rw [if_neg hp, if_neg (fun hq => hp (hm.2 hq)), hrest]

/-- Characterises the frontier as the rightmost fresh tail.
Consumer: topFreshTailPrepaidSourceContactStep (frontier moves). -/
theorem topFreshTailPrepaidSearchEqSome (P : Nat → Prop) :
    ∀ (m f : Nat), P f → f < m → (∀ k, f < k → k < m → ¬ P k) →
      topFreshTailPrepaidSearch P m = some f := by
  intro m
  induction m with
  | zero => intro f _ hf; omega
  | succ m ih =>
      intro f hp hf hmax
      unfold topFreshTailPrepaidSearch
      by_cases hfm : f = m
      · subst hfm; rw [if_pos hp]
      · have hnm : ¬ P m := hmax m (by omega) (by omega)
        rw [if_neg hnm]
        exact ih f hp (by omega) (fun k h1 h2 => hmax k h1 (by omega))

/-- No fresh tail gives no frontier.
Consumer: topFreshTailPrepaidSourceContactStep. -/
theorem topFreshTailPrepaidSearchEqNone (P : Nat → Prop) :
    ∀ m, (∀ k, k < m → ¬ P k) → topFreshTailPrepaidSearch P m = none := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
      intro h
      unfold topFreshTailPrepaidSearch
      rw [if_neg (h m (by omega))]
      exact ih (fun k hk => h k (by omega))

/-- Sums over a duplicate-free list that agree off one point.
Consumer: topFreshTailPrepaidSumTwo. -/
theorem topFreshTailPrepaidSumOne (f g : Nat → Nat) (a : Nat) :
    ∀ L : List Nat, L.Nodup → a ∈ L → (∀ x ∈ L, x ≠ a → f x = g x) →
      (L.map g).sum + f a = (L.map f).sum + g a := by
  intro L
  induction L with
  | nil => intro _ h; cases h
  | cons x L ih =>
      intro hL ha hagree
      rw [List.nodup_cons] at hL
      simp only [List.map_cons, List.sum_cons]
      by_cases hxa : x = a
      · subst hxa
        have hrest : (L.map g).sum = (L.map f).sum := by
          have : ∀ y ∈ L, f y = g y := fun y hy =>
            hagree y (List.mem_cons_of_mem _ hy) (fun h => hL.1 (h ▸ hy))
          rw [List.map_congr_left this]
        omega
      · have ha' : a ∈ L := by
          rcases List.mem_cons.1 ha with h | h
          · exact absurd h.symm hxa
          · exact h
        have := ih hL.2 ha' (fun y hy hya => hagree y (List.mem_cons_of_mem _ hy) hya)
        have hx := hagree x List.mem_cons_self hxa
        omega

/-- Sums over a duplicate-free list that agree off two points.
Consumer: topFreshTailPrepaidSourceContactStep. -/
theorem topFreshTailPrepaidSumTwo (f g : Nat → Nat) (a b : Nat) (hab : a ≠ b)
    (L : List Nat) (hL : L.Nodup) (ha : a ∈ L) (hb : b ∈ L)
    (hagree : ∀ x ∈ L, x ≠ a → x ≠ b → f x = g x) :
    (L.map g).sum + f a + f b = (L.map f).sum + g a + g b := by
  let h : Nat → Nat := fun x => if x = a then g a else f x
  have h1 := topFreshTailPrepaidSumOne f h a L hL ha (by
    intro x _ hxa; simp [h, hxa])
  have h2 := topFreshTailPrepaidSumOne h g b L hL hb (by
    intro x hx hxb
    by_cases hxa : x = a
    · subst hxa; simp [h]
    · simp [h, hxa]; exact hagree x hx hxa hxb)
  have hha : h a = g a := by simp [h]
  have hhb : h b = f b := by simp [h, Ne.symm hab]
  rw [hha] at h1
  rw [hhb] at h2
  omega

/-- Sums of pointwise equal maps agree.
Consumer: topFreshTailPrepaidSumFromCongr. -/
theorem topFreshTailPrepaidSumZero (f g : Nat → Nat) :
    ∀ L : List Nat, (∀ x ∈ L, f x = g x) → (L.map g).sum = (L.map f).sum := by
  intro L h
  rw [List.map_congr_left h]

/-- Credit of the token at source offset k of a cut. -/
def topFreshTailPrepaidCredit {n : Nat} (s : Fin n) (Z : TopFixedTraceState n)
    (k : Nat) : Nat :=
  topFreshTailPrepaidTokenCredit (topClockSpan n) k (Z.1.1 (certSite s k)).qOut

/-- Credit sums agree when the credits agree from lo on.
Consumer: topFreshTailPrepaidSourceContactStep. -/
theorem topFreshTailPrepaidSumFromCongr {n : Nat} (s : Fin n)
    (Z Y : TopFixedTraceState n) (lo : Nat)
    (h : ∀ k, k < topClockSpan n → lo ≤ k →
      topFreshTailPrepaidCredit s Y k = topFreshTailPrepaidCredit s Z k) :
    topFreshTailPrepaidSumFrom s Y lo = topFreshTailPrepaidSumFrom s Z lo := by
  unfold topFreshTailPrepaidSumFrom
  apply topFreshTailPrepaidSumZero
  intro k hk
  have hk' := List.mem_range.1 hk
  by_cases hlo : lo ≤ k
  · simp only [hlo, if_true]
    exact (h k hk' hlo).symm
  · simp [hlo]

/-- Credit sums from lo when only offset a changes.
Consumer: topFreshTailPrepaidCloseOne. -/
theorem topFreshTailPrepaidSumFromOne {n : Nat} (s : Fin n)
    (Z Y : TopFixedTraceState n) (lo a : Nat)
    (ha : a < topClockSpan n) (hla : lo ≤ a)
    (h : ∀ k, k < topClockSpan n → lo ≤ k → k ≠ a →
      topFreshTailPrepaidCredit s Y k = topFreshTailPrepaidCredit s Z k) :
    topFreshTailPrepaidSumFrom s Y lo + topFreshTailPrepaidCredit s Z a =
      topFreshTailPrepaidSumFrom s Z lo + topFreshTailPrepaidCredit s Y a := by
  unfold topFreshTailPrepaidSumFrom
  have := topFreshTailPrepaidSumOne
    (fun j => if lo ≤ j then topFreshTailPrepaidTokenCredit (topClockSpan n) j
      (Z.1.1 (certSite s j)).qOut else 0)
    (fun j => if lo ≤ j then topFreshTailPrepaidTokenCredit (topClockSpan n) j
      (Y.1.1 (certSite s j)).qOut else 0)
    a (List.range (topClockSpan n)) List.nodup_range (List.mem_range.2 ha) (by
      intro k hk hka
      have hk' := List.mem_range.1 hk
      by_cases hlo : lo ≤ k
      · simp only [hlo, if_true]
        exact (h k hk' hlo hka).symm
      · simp [hlo])
  simp only [hla, if_true] at this
  exact this

/-- Credit sums from lo when only offsets a and b change.
Consumer: topFreshTailPrepaidCloseTwo. -/
theorem topFreshTailPrepaidSumFromTwo {n : Nat} (s : Fin n)
    (Z Y : TopFixedTraceState n) (lo a b : Nat) (hab : a ≠ b)
    (ha : a < topClockSpan n) (hb : b < topClockSpan n)
    (hla : lo ≤ a) (hlb : lo ≤ b)
    (h : ∀ k, k < topClockSpan n → lo ≤ k → k ≠ a → k ≠ b →
      topFreshTailPrepaidCredit s Y k = topFreshTailPrepaidCredit s Z k) :
    topFreshTailPrepaidSumFrom s Y lo + topFreshTailPrepaidCredit s Z a +
        topFreshTailPrepaidCredit s Z b =
      topFreshTailPrepaidSumFrom s Z lo + topFreshTailPrepaidCredit s Y a +
        topFreshTailPrepaidCredit s Y b := by
  unfold topFreshTailPrepaidSumFrom
  have := topFreshTailPrepaidSumTwo
    (fun j => if lo ≤ j then topFreshTailPrepaidTokenCredit (topClockSpan n) j
      (Z.1.1 (certSite s j)).qOut else 0)
    (fun j => if lo ≤ j then topFreshTailPrepaidTokenCredit (topClockSpan n) j
      (Y.1.1 (certSite s j)).qOut else 0)
    a b hab (List.range (topClockSpan n)) List.nodup_range (List.mem_range.2 ha)
    (List.mem_range.2 hb) (by
      intro k hk hka hkb
      have hk' := List.mem_range.1 hk
      by_cases hlo : lo ≤ k
      · simp only [hlo, if_true]
        exact (h k hk' hlo hka hkb).symm
      · simp [hlo])
  simp only [hla, hlb, if_true] at this
  exact this

/-- Peeling the lowest offset off a credit sum.
Consumer: topFreshTailPrepaidSourceContactStep (frontier moves). -/
theorem topFreshTailPrepaidSumFromSucc {n : Nat} (s : Fin n)
    (Z : TopFixedTraceState n) (lo : Nat) (hlo : lo < topClockSpan n) :
    topFreshTailPrepaidSumFrom s Z lo =
      topFreshTailPrepaidCredit s Z lo + topFreshTailPrepaidSumFrom s Z (lo + 1) := by
  unfold topFreshTailPrepaidSumFrom
  have := topFreshTailPrepaidSumOne
    (fun j => if lo + 1 ≤ j then topFreshTailPrepaidTokenCredit (topClockSpan n) j
      (Z.1.1 (certSite s j)).qOut else 0)
    (fun j => if lo ≤ j then topFreshTailPrepaidTokenCredit (topClockSpan n) j
      (Z.1.1 (certSite s j)).qOut else 0)
    lo (List.range (topClockSpan n)) List.nodup_range (List.mem_range.2 hlo) (by
      intro k _ hk
      by_cases h1 : lo + 1 ≤ k
      · have h2 : lo ≤ k := by omega
        simp [h1, h2]
      · have h2 : ¬ lo ≤ k := by omega
        simp [h1, h2])
  simp only [show ¬ (lo + 1 ≤ lo) by omega, if_false, Nat.le_refl, if_true] at this
  unfold topFreshTailPrepaidCredit
  omega

/-- With no leader, a service into source offset zero (beta true)
never changes its output token. Consumer: topFreshTailPrepaidTokenFrame. -/
theorem topFreshTailPrepaidResponderZeroFrame
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hleader : ∀ i : Fin n, (C i).l = false)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n) (hresp : ring.rightNeighbor e = certSite s 0) :
    ((topFixedTraceNext ring C Z e).1.1 (certSite s 0)).qOut =
      (Z.1.1 (certSite s 0)).qOut := by
  have hr := cert_rho_ge_three n hn
  change 3 ≤ topClockSpan n at hr
  have hformula := topFreshTailCausalResponderPhysicalOutput ring (by omega) C Z e
  rw [hresp] at hformula
  have hgeo := topFreshTailCausalSourcePublicGeometry ring C s hn hbad Z hreach
    ⟨0, by omega⟩
  have hel : (Z.1.1 e).l = false := by
    rw [(topFreshTailCausalReachedPublicMask ring C Z hreach e).1]; exact hleader e
  have hjl : (Z.1.1 (certSite s 0)).l = false := hgeo.1
  have hbeta : (Z.1.1 (certSite s 0)).beta = true := by
    have h := hgeo.2.2.1; simp only [if_true] at h; exact h
  rw [hel, hjl, hbeta] at hformula
  simpa using hformula

/-- Off the selected source and its successor, a source output token
is unchanged (leaderless entrance). Consumer:
topFreshTailPrepaidSourceContactStep. -/
theorem topFreshTailPrepaidTokenFrame
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hleader : ∀ i : Fin n, (C i).l = false)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n) (k : Nat) (hk : k < topClockSpan n)
    (hnot : ∀ j, j < topClockSpan n → e = certSite s j → k ≠ j ∧ k ≠ j + 1) :
    ((topFixedTraceNext ring C Z e).1.1 (certSite s k)).qOut =
      (Z.1.1 (certSite s k)).qOut := by
  by_cases hsrc : e = certSite s k
  · exact absurd rfl (hnot k hk hsrc).1
  · by_cases hresp : ring.rightNeighbor e = certSite s k
    · by_cases hk0 : k = 0
      · subst hk0
        exact topFreshTailPrepaidResponderZeroFrame ring C s hn hbad hleader Z
          hreach e hresp
      · have hpred := topFreshTailCausalIncomingPredecessor ring hn s ⟨k, hk⟩
          (by simp only; omega) e hresp
        exact absurd (show k = (k - 1) + 1 by omega) (hnot (k - 1) (by omega) hpred).2
    · exact (topPortLiteralAwayFields ring C Z.1.1 e (certSite s k)
        (fun h => hsrc h.symm) (fun h => hresp h.symm)).2.2

/-- An unchanged source token keeps its genealogy slot.
Consumer: topFreshTailPrepaidSourceContactStep. -/
theorem topFreshTailPrepaidSlotFrame
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n) (k : Fin (topClockSpan n))
    (hsame : ((topFixedTraceNext ring C Z e).1.1 (certSite s k.val)).qOut =
      (Z.1.1 (certSite s k.val)).qOut) :
    (topFreshTailGenealogy ring C s (topFixedTraceNext ring C Z e)).slots k =
      (topFreshTailGenealogy ring C s Z).slots k := by
  have hqueue := topFreshTailCloseReachedQueue ring C s hn hbad Z hreach
  have htrace := topFreshTailGenealogyTraceReached ring C s Z hreach
  have hslotEq :
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots k =
      topFreshTailGenealogyNextSlot ring C s
        (topFreshTailGenealogy ring C s Z) e k := by
    rw [topFreshTailCausalReplayNext]
    rfl
  rw [hslotEq]
  unfold topFreshTailGenealogyNextSlot
  rw [htrace, hsame]
  cases ho : (Z.1.1 (certSite s k.val)).qOut with
  | E =>
      simp only
      exact ((hqueue.slot k).1 ho).symm
  | U => rfl
  | D v t => rfl

/-- The fresh-tail predicate at an offset with unchanged token.
Consumer: topFreshTailPrepaidSourceContactStep. -/
theorem topFreshTailPrepaidFreshTailFrame
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n) (k : Nat) (hk : k < topClockSpan n)
    (hsame : ((topFixedTraceNext ring C Z e).1.1 (certSite s k)).qOut =
      (Z.1.1 (certSite s k)).qOut) :
    TopFreshTailPrepaidFreshTail ring C s (topFixedTraceNext ring C Z e) k ↔
      TopFreshTailPrepaidFreshTail ring C s Z k := by
  have hslot := topFreshTailPrepaidSlotFrame ring C s hn hbad Z hreach e ⟨k, hk⟩ hsame
  constructor
  · rintro ⟨h, a, v, ha, hf, hD⟩
    exact ⟨h, a, v, hslot ▸ ha, hf, hsame ▸ hD⟩
  · rintro ⟨h, a, v, ha, hf, hD⟩
    exact ⟨h, a, v, hslot.symm ▸ ha, hf, hsame.symm ▸ hD⟩

/-- If no source token changes, Phi_* is unchanged.
Consumer: topFreshTailPrepaidSourceContactStep. -/
theorem topFreshTailPrepaidNoChange
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n)
    (hsame : ∀ k, k < topClockSpan n →
      ((topFixedTraceNext ring C Z e).1.1 (certSite s k)).qOut =
        (Z.1.1 (certSite s k)).qOut) :
    topFreshTailPrepaidPotential ring C s (topFixedTraceNext ring C Z e) =
      topFreshTailPrepaidPotential ring C s Z := by
  have hr := cert_rho_ge_three n hn
  change 3 ≤ topClockSpan n at hr
  have hfront : topFreshTailPrepaidFrontier ring C s (topFixedTraceNext ring C Z e) =
      topFreshTailPrepaidFrontier ring C s Z := by
    unfold topFreshTailPrepaidFrontier
    apply topFreshTailPrepaidSearchCongr
    intro k hk
    exact topFreshTailPrepaidFreshTailFrame ring C s hn hbad Z hreach e k hk (hsame k hk)
  have hsum : ∀ lo, topFreshTailPrepaidSumFrom s (topFixedTraceNext ring C Z e) lo =
      topFreshTailPrepaidSumFrom s Z lo := by
    intro lo
    apply topFreshTailPrepaidSumFromCongr
    intro k hk _
    unfold topFreshTailPrepaidCredit
    rw [hsame k hk]
  unfold topFreshTailPrepaidPotential
  rw [hfront, hsame 0 (by omega)]
  cases topFreshTailPrepaidFrontier ring C s Z with
  | none => simp only; rw [hsum]
  | some f => simp only; rw [hsum]

/-- A useful source contact charged to Phi_*: the selected source
offset j changes its output token and lies at or ahead of F1 (or F1
does not exist yet). Blocked services and contacts behind F1 are not
charged. -/
noncomputable def TopFreshTailPrepaidCharged
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) (e : Fin n) : Prop :=
  ∃ j, j < topClockSpan n ∧ e = certSite s j ∧
    ((topFixedTraceNext ring C Z e).1.1 (certSite s j)).qOut ≠
      (Z.1.1 (certSite s j)).qOut ∧
    ∀ f, topFreshTailPrepaidFrontier ring C s Z = some f → f ≤ j

/-- A selected source names at most one source offset.
Consumer: topFreshTailPrepaidChargedIff. -/
theorem topFreshTailPrepaidSiteInj {n : Nat} (s : Fin n) (hn : 5 ≤ n)
    (e : Fin n) (j j' : Nat) (hj : j < topClockSpan n) (hj' : j' < topClockSpan n)
    (h1 : e = certSite s j) (h2 : e = certSite s j') : j' = j := by
  have := topFreshTailCausalSourceSiteInjective s hn ⟨j', hj'⟩ ⟨j, hj⟩
    (by simp only; rw [← h1, ← h2])
  exact congrArg Fin.val this

/-- The charge condition at the selected source offset.
Consumer: topFreshTailPrepaidSourceContactStep. -/
theorem topFreshTailPrepaidChargedIff
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n) (hn : 5 ≤ n)
    (Z : TopFixedTraceState n) (e : Fin n) (j : Nat) (hj : j < topClockSpan n)
    (hsite : e = certSite s j) :
    TopFreshTailPrepaidCharged ring C s Z e ↔
      (((topFixedTraceNext ring C Z e).1.1 (certSite s j)).qOut ≠
          (Z.1.1 (certSite s j)).qOut ∧
        ∀ f, topFreshTailPrepaidFrontier ring C s Z = some f → f ≤ j) := by
  constructor
  · rintro ⟨j', hj', hsite', hch, hf⟩
    have := topFreshTailPrepaidSiteInj s hn e j j' hj hj' hsite hsite'
    subst this
    exact ⟨hch, hf⟩
  · rintro ⟨hch, hf⟩
    exact ⟨j, hj, hsite, hch, hf⟩

/-- Offsets other than the selected source and its successor keep
their token. Consumer: topFreshTailPrepaidSourceContactStep. -/
theorem topFreshTailPrepaidOthersFrame
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hleader : ∀ i : Fin n, (C i).l = false)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n) (j : Nat) (hj : j < topClockSpan n) (hsite : e = certSite s j) :
    ∀ k, k < topClockSpan n → k ≠ j → k ≠ j + 1 →
      ((topFixedTraceNext ring C Z e).1.1 (certSite s k)).qOut =
        (Z.1.1 (certSite s k)).qOut := by
  intro k hk h1 h2
  apply topFreshTailPrepaidTokenFrame ring C s hn hbad hleader Z hreach e k hk
  intro j' hj' hsite'
  have := topFreshTailPrepaidSiteInj s hn e j j' hj hj' hsite hsite'
  subst this
  exact ⟨h1, h2⟩

/-- The successor slot of a selected source keeps its token unless the
source's own D moved into it. Consumer: the step cases below. -/
theorem topFreshTailPrepaidSuccFrame
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n) (j : Nat) (hj1 : j + 1 < topClockSpan n) (hsite : e = certSite s j)
    (hkeep : ∀ (v : Fin (compileAdvice (ceilLogTwo n)).topA) (t : Bool),
      (Z.1.1 (certSite s j)).qOut = .D v t →
      ((topFixedTraceNext ring C Z e).1.1 (certSite s j)).qOut = .D v t) :
    ((topFixedTraceNext ring C Z e).1.1 (certSite s (j + 1))).qOut =
      (Z.1.1 (certSite s (j + 1))).qOut := by
  rcases topFreshTailTicketSlotPhysical ring C s hn hbad Z hreach e ⟨j + 1, hj1⟩ with
    hsame | ⟨hsrc, _⟩ | ⟨hsrc, _⟩ | ⟨hsrc, _⟩ | ⟨_, _, hoE, v, t, hpD, _⟩ | ⟨h0, _⟩
  · exact hsame
  · exact absurd (topFreshTailPrepaidSiteInj s hn e j (j + 1) (by omega) hj1 hsite hsrc)
      (by omega)
  · exact absurd (topFreshTailPrepaidSiteInj s hn e j (j + 1) (by omega) hj1 hsite hsrc)
      (by omega)
  · exact absurd (topFreshTailPrepaidSiteInj s hn e j (j + 1) (by omega) hj1 hsite hsrc)
      (by omega)
  · simp only [Nat.add_sub_cancel] at hpD
    have hgeo := topFreshTailCausalSourcePublicGeometry ring C s hn hbad Z hreach
      ⟨j, by omega⟩
    have hxl : (Z.1.1 e).l = false := by rw [hsite]; exact hgeo.1
    have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := by rw [hsite]; exact hgeo.2.1
    have hyb : (Z.1.1 (ring.rightNeighbor e)).beta = false := by
      rw [hsite]
      have h := hgeo.2.2.2
      simp only [show ¬ (j + 1 = topClockSpan n) by omega, if_false] at h
      exact h
    have hnb : ring.rightNeighbor e = certSite s (j + 1) := by
      rw [hsite, topFreshTailTicketNeighborSite]
    have hxo : (Z.1.1 e).qOut = .D v t := by rw [hsite]; exact hpD
    have hyo : (Z.1.1 (ring.rightNeighbor e)).qOut = .E := by rw [hnb]; exact hoE
    have hmove := (topFreshTailFifoDataMove ring (by omega) C Z e v t hxl hyl hxo hyo hyb).1
    have hstay := hkeep v t hpD
    rw [← hsite, hmove] at hstay
    cases t <;> simp at hstay
  · simp only at h0
    omega

/-- The frontier depends only on the fresh-tail predicate below r.
Consumer: topFreshTailPrepaidSourceContactStep. -/
theorem topFreshTailPrepaidFrontierFrame
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z Y : TopFixedTraceState n)
    (h : ∀ k, k < topClockSpan n →
      (TopFreshTailPrepaidFreshTail ring C s Y k ↔ TopFreshTailPrepaidFreshTail ring C s Z k)) :
    topFreshTailPrepaidFrontier ring C s Y = topFreshTailPrepaidFrontier ring C s Z := by
  unfold topFreshTailPrepaidFrontier
  exact topFreshTailPrepaidSearchCongr _ _ _ h

/-- A non-D(true) token is not a fresh tail.
Consumer: topFreshTailPrepaidSourceContactStep. -/
theorem topFreshTailPrepaidNotFreshTailOfToken
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) (k : Nat)
    (h : ∀ v : Fin (compileAdvice (ceilLogTwo n)).topA,
      (Z.1.1 (certSite s k)).qOut ≠ .D v true) :
    ¬ TopFreshTailPrepaidFreshTail ring C s Z k := by
  rintro ⟨_, _, v, _, _, hD⟩
  exact h v hD

/-- Potential bookkeeping when only offset a changes, the frontier is
unchanged and the credit at a drops by one. Consumer:
topFreshTailPrepaidSourceContactStep. -/
theorem topFreshTailPrepaidCloseOne
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z Y : TopFixedTraceState n) (a : Nat) (ha : a < topClockSpan n)
    (hsame : ∀ k, k < topClockSpan n → k ≠ a →
      (Y.1.1 (certSite s k)).qOut = (Z.1.1 (certSite s k)).qOut)
    (hfront : topFreshTailPrepaidFrontier ring C s Y = topFreshTailPrepaidFrontier ring C s Z)
    (hres : topFreshTailPrepaidReserve (topClockSpan n) (Y.1.1 (certSite s 0)).qOut =
      topFreshTailPrepaidReserve (topClockSpan n) (Z.1.1 (certSite s 0)).qOut)
    (hcred : topFreshTailPrepaidCredit s Z a = topFreshTailPrepaidCredit s Y a + 1) :
    (topFreshTailPrepaidFrontier ring C s Z = none →
      topFreshTailPrepaidPotential ring C s Y + 1 = topFreshTailPrepaidPotential ring C s Z) ∧
    (∀ f, topFreshTailPrepaidFrontier ring C s Z = some f → f < a →
      topFreshTailPrepaidPotential ring C s Y + 1 = topFreshTailPrepaidPotential ring C s Z) ∧
    (∀ f, topFreshTailPrepaidFrontier ring C s Z = some f → a < f →
      topFreshTailPrepaidPotential ring C s Y = topFreshTailPrepaidPotential ring C s Z) := by
  have hc : ∀ k, k < topClockSpan n → k ≠ a →
      topFreshTailPrepaidCredit s Y k = topFreshTailPrepaidCredit s Z k := by
    intro k hk hka; unfold topFreshTailPrepaidCredit; rw [hsame k hk hka]
  refine ⟨?_, ?_, ?_⟩
  · intro hF
    unfold topFreshTailPrepaidPotential
    rw [hfront, hF]
    simp only
    have := topFreshTailPrepaidSumFromOne s Z Y 0 a ha (Nat.zero_le _)
      (fun k hk _ hka => hc k hk hka)
    omega
  · intro f hF hfa
    unfold topFreshTailPrepaidPotential
    rw [hfront, hF]
    simp only
    have := topFreshTailPrepaidSumFromOne s Z Y (f + 1) a ha (by omega)
      (fun k hk _ hka => hc k hk hka)
    omega
  · intro f hF haf
    unfold topFreshTailPrepaidPotential
    rw [hfront, hF]
    simp only
    rw [topFreshTailPrepaidSumFromCongr s Z Y (f + 1)
      (fun k hk hlo => hc k hk (by omega))]

/-- Potential bookkeeping when only offsets a and a+1 change, the
frontier is unchanged and their joint credit drops by one.
Consumer: topFreshTailPrepaidSourceContactStep. -/
theorem topFreshTailPrepaidCloseTwo
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z Y : TopFixedTraceState n) (a : Nat) (ha : a + 1 < topClockSpan n)
    (hsame : ∀ k, k < topClockSpan n → k ≠ a → k ≠ a + 1 →
      (Y.1.1 (certSite s k)).qOut = (Z.1.1 (certSite s k)).qOut)
    (hfront : topFreshTailPrepaidFrontier ring C s Y = topFreshTailPrepaidFrontier ring C s Z)
    (hres : topFreshTailPrepaidReserve (topClockSpan n) (Y.1.1 (certSite s 0)).qOut =
      topFreshTailPrepaidReserve (topClockSpan n) (Z.1.1 (certSite s 0)).qOut)
    (hcred : topFreshTailPrepaidCredit s Z a + topFreshTailPrepaidCredit s Z (a + 1) =
      topFreshTailPrepaidCredit s Y a + topFreshTailPrepaidCredit s Y (a + 1) + 1) :
    (topFreshTailPrepaidFrontier ring C s Z = none →
      topFreshTailPrepaidPotential ring C s Y + 1 = topFreshTailPrepaidPotential ring C s Z) ∧
    (∀ f, topFreshTailPrepaidFrontier ring C s Z = some f → f < a →
      topFreshTailPrepaidPotential ring C s Y + 1 = topFreshTailPrepaidPotential ring C s Z) ∧
    (∀ f, topFreshTailPrepaidFrontier ring C s Z = some f → a + 1 < f →
      topFreshTailPrepaidPotential ring C s Y = topFreshTailPrepaidPotential ring C s Z) := by
  have hc : ∀ k, k < topClockSpan n → k ≠ a → k ≠ a + 1 →
      topFreshTailPrepaidCredit s Y k = topFreshTailPrepaidCredit s Z k := by
    intro k hk h1 h2; unfold topFreshTailPrepaidCredit; rw [hsame k hk h1 h2]
  refine ⟨?_, ?_, ?_⟩
  · intro hF
    unfold topFreshTailPrepaidPotential
    rw [hfront, hF]
    simp only
    have := topFreshTailPrepaidSumFromTwo s Z Y 0 a (a + 1) (by omega) (by omega) ha
      (Nat.zero_le _) (Nat.zero_le _) (fun k hk _ h1 h2 => hc k hk h1 h2)
    omega
  · intro f hF hfa
    unfold topFreshTailPrepaidPotential
    rw [hfront, hF]
    simp only
    have := topFreshTailPrepaidSumFromTwo s Z Y (f + 1) a (a + 1) (by omega) (by omega) ha
      (by omega) (by omega) (fun k hk _ h1 h2 => hc k hk h1 h2)
    omega
  · intro f hF haf
    unfold topFreshTailPrepaidPotential
    rw [hfront, hF]
    simp only
    rw [topFreshTailPrepaidSumFromCongr s Z Y (f + 1)
      (fun k hk hlo => hc k hk (by omega) (by omega))]

/-- Item 6: the (c*) potential never rises on any actual edge of
a leaderless entrance before the first genuine border tail, and it
falls by exactly one on every charged useful source contact (a source
token change at or ahead of F1, or any source token change before F1
exists); blocked services, target-only edges and contacts behind F1
leave it unchanged.
Consumer: P.3 J4 (topFreshTailPrepaidContactBound). -/
theorem topFreshTailPrepaidSourceContactStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hleader : ∀ i : Fin n, (C i).l = false)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n)
    (hng : ¬ topClockGenuineTailAccepted C s (topFixedTraceNext ring C Z e)) :
    topFreshTailPrepaidPotential ring C s (topFixedTraceNext ring C Z e) +
        (if TopFreshTailPrepaidCharged ring C s Z e then 1 else 0) =
      topFreshTailPrepaidPotential ring C s Z := by
  have hr := cert_rho_ge_three n hn
  change 3 ≤ topClockSpan n at hr
  have hqueue := topFreshTailCloseReachedQueue ring C s hn hbad Z hreach
  by_cases hnin : ¬ ∃ j, j < topClockSpan n ∧ e = certSite s j
  · have hin := hnin
    have hsame : ∀ k, k < topClockSpan n →
        ((topFixedTraceNext ring C Z e).1.1 (certSite s k)).qOut =
          (Z.1.1 (certSite s k)).qOut := fun k hk =>
      topFreshTailPrepaidTokenFrame ring C s hn hbad hleader Z hreach e k hk
        (fun j hj hs => absurd ⟨j, hj, hs⟩ hin)
    have hnc : ¬ TopFreshTailPrepaidCharged ring C s Z e :=
      fun ⟨j, hj, hs, _, _⟩ => hin ⟨j, hj, hs⟩
    rw [if_neg hnc, topFreshTailPrepaidNoChange ring C s hn hbad Z hreach e hsame]
    rfl
  have hin : ∃ j, j < topClockSpan n ∧ e = certSite s j :=
    Classical.byContradiction (fun h => hnin h)
  obtain ⟨j, hj, hsite⟩ := hin
  have hiff := topFreshTailPrepaidChargedIff ring C s hn Z e j hj hsite
  have hothers := topFreshTailPrepaidOthersFrame ring C s hn hbad hleader Z hreach e j hj hsite
  have hgeo := topFreshTailCausalSourcePublicGeometry ring C s hn hbad Z hreach ⟨j, hj⟩
  have hxl : (Z.1.1 e).l = false := by rw [hsite]; exact hgeo.1
  have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := by rw [hsite]; exact hgeo.2.1
  -- generic closers
  have hPframe : ∀ k, k < topClockSpan n →
      ((topFixedTraceNext ring C Z e).1.1 (certSite s k)).qOut =
        (Z.1.1 (certSite s k)).qOut →
      (TopFreshTailPrepaidFreshTail ring C s (topFixedTraceNext ring C Z e) k ↔
        TopFreshTailPrepaidFreshTail ring C s Z k) := fun k hk h =>
    topFreshTailPrepaidFreshTailFrame ring C s hn hbad Z hreach e k hk h
  have hcredFrame : ∀ k, k < topClockSpan n → k ≠ j → k ≠ j + 1 →
      topFreshTailPrepaidCredit s (topFixedTraceNext ring C Z e) k =
        topFreshTailPrepaidCredit s Z k := by
    intro k hk h1 h2
    unfold topFreshTailPrepaidCredit
    rw [hothers k hk h1 h2]
  cases htok : (Z.1.1 (certSite s j)).qOut with
  | E =>
      by_cases hj0 : j = 0
      · -- border marker bootstrap E -> U
        subst hj0
        have hU : ((topFixedTraceNext ring C Z e).1.1 (certSite s 0)).qOut = .U := by
          have h := (topFreshTailCausalBadBorderBirthStep ring C s hn hbad Z e hqueue
            ⟨0, hj⟩ rfl hsite (by rw [hsite]; exact htok)).1
          rw [← hsite]; exact h
        have hsucc := topFreshTailPrepaidSuccFrame ring C s hn hbad Z hreach e 0
          (by omega) hsite (fun v t h => by rw [htok] at h; cases h)
        have hsame : ∀ k, k < topClockSpan n → k ≠ 0 →
            ((topFixedTraceNext ring C Z e).1.1 (certSite s k)).qOut =
              (Z.1.1 (certSite s k)).qOut := by
          intro k hk hk0
          by_cases hk1 : k = 1
          · subst hk1; exact hsucc
          · exact hothers k hk hk0 hk1
        have hfront := topFreshTailPrepaidFrontierFrame ring C s Z
          (topFixedTraceNext ring C Z e) (by
            intro k hk
            by_cases hk0 : k = 0
            · subst hk0
              constructor
              · intro h
                exact absurd h (topFreshTailPrepaidNotFreshTailOfToken ring C s _ 0
                  (by intro v hv; rw [hU] at hv; cases hv))
              · intro h
                exact absurd h (topFreshTailPrepaidNotFreshTailOfToken ring C s _ 0
                  (by intro v hv; rw [htok] at hv; cases hv))
            · exact hPframe k hk (hsame k hk hk0))
        unfold topFreshTailPrepaidPotential
        rw [hfront]
        cases hF : topFreshTailPrepaidFrontier ring C s Z with
        | none =>
            have hc : TopFreshTailPrepaidCharged ring C s Z e :=
              hiff.2 ⟨(by rw [hU, htok]; intro h; cases h),
                (fun f hf => by rw [hF] at hf; cases hf)⟩
            rw [if_pos hc]
            simp only
            have hsum := topFreshTailPrepaidSumFromOne s Z (topFixedTraceNext ring C Z e)
              0 0 hj (Nat.le_refl _) (by
                intro k hk _ hk0
                unfold topFreshTailPrepaidCredit
                rw [hsame k hk hk0])
            unfold topFreshTailPrepaidCredit at hsum
            rw [hU, htok] at hsum
            rw [hU, htok]
            simp [topFreshTailPrepaidTokenCredit, topFreshTailPrepaidReserve] at hsum ⊢
            omega
        | some f =>
            have hPf := (topFreshTailPrepaidSearchSome _ _ f hF).1
            have hf0 : f ≠ 0 := by
              intro h; subst h
              exact topFreshTailPrepaidNotFreshTailOfToken ring C s Z 0
                (by intro v hv; rw [htok] at hv; cases hv) hPf
            have hnc : ¬ TopFreshTailPrepaidCharged ring C s Z e := by
              intro hc
              have := (hiff.1 hc).2 f hF
              omega
            rw [if_neg hnc]
            simp only
            rw [topFreshTailPrepaidSumFromCongr s Z (topFixedTraceNext ring C Z e) (f + 1)
              (by
                intro k hk hlo
                unfold topFreshTailPrepaidCredit
                rw [hsame k hk (by omega)])]
            rfl
      · -- interior empty source stays empty
        have hE : ((topFixedTraceNext ring C Z e).1.1 (certSite s j)).qOut = .E := by
          have h := (topFreshTailCausalBadInteriorEmptyStep ring C s hn hbad Z e hqueue
            ⟨j, hj⟩ (by simp only; omega) hsite (by rw [hsite]; exact htok)).1
          rw [← hsite]; exact h
        have hsame : ∀ k, k < topClockSpan n →
            ((topFixedTraceNext ring C Z e).1.1 (certSite s k)).qOut =
              (Z.1.1 (certSite s k)).qOut := by
          intro k hk
          by_cases hkj : k = j
          · subst hkj; rw [hE, htok]
          · by_cases hk1 : k = j + 1
            · subst hk1
              exact topFreshTailPrepaidSuccFrame ring C s hn hbad Z hreach e j hk hsite
                (fun v t h => by rw [htok] at h; cases h)
            · exact hothers k hk hkj hk1
        have hnc : ¬ TopFreshTailPrepaidCharged ring C s Z e := by
          intro hc
          exact (hiff.1 hc).1 (hsame j hj)
        rw [if_neg hnc, topFreshTailPrepaidNoChange ring C s hn hbad Z hreach e hsame]
        rfl
  | U =>
      have hu : (Z.1.1 e).qOut = .U := by rw [hsite]; exact htok
      have hbeta : (Z.1.1 e).beta = (if j = 0 then true else false) := by
        rw [hsite]; exact hgeo.2.2.1
      have hnewj : ((topFixedTraceNext ring C Z e).1.1 (certSite s j)).qOut =
          .D (Z.1.1 e).d (if j = 0 then true else false) := by
        have h := topFreshTailFifoUnreadSamples ring C Z e hxl hyl hu
        rw [hbeta] at h
        rw [← hsite]; exact h
      have hsame : ∀ k, k < topClockSpan n → k ≠ j →
          ((topFixedTraceNext ring C Z e).1.1 (certSite s k)).qOut =
            (Z.1.1 (certSite s k)).qOut := by
        intro k hk hkj
        by_cases hk1 : k = j + 1
        · subst hk1
          exact topFreshTailPrepaidSuccFrame ring C s hn hbad Z hreach e j hk hsite
            (fun v t h => by rw [htok] at h; cases h)
        · exact hothers k hk hkj hk1
      have hPj : ¬ TopFreshTailPrepaidFreshTail ring C s Z j :=
        topFreshTailPrepaidNotFreshTailOfToken ring C s Z j
          (by intro v hv; rw [htok] at hv; cases hv)
      have hch : ((topFixedTraceNext ring C Z e).1.1 (certSite s j)).qOut ≠
          (Z.1.1 (certSite s j)).qOut := by
        rw [hnewj, htok]; intro h; cases h
      by_cases hj0 : j = 0
      · subst hj0
        have hq' := topFreshTailCloseReachedQueue ring C s hn hbad
          (topFixedTraceNext ring C Z e) (topClockReachedNext ring C Z e hreach)
        obtain ⟨a, ha⟩ := topFreshTailCausalOccupiedHasCarrier ring C s
          (topFixedTraceNext ring C Z e) hq' ⟨0, hj⟩
          (by simp only; rw [hnewj]; intro h; cases h)
        have hafresh : topFreshTailTicketIsFresh a.origin = true := by
          rcases topFreshTailTicketSlotCases ring C s hn hbad Z hreach e ⟨0, hj⟩ a ha with
            ⟨_, _, hphys⟩ | ⟨hpos, _⟩ | ⟨_, _, _, _, _, hoD, _⟩ | ⟨_, _, ha', _⟩
          · rcases hphys with heq | ⟨hpos, _⟩
            · simp only at heq; rw [hnewj, htok] at heq; cases heq
            · simp only at hpos; omega
          · simp only at hpos; omega
          · simp only at hoD; rw [htok] at hoD; cases hoD
          · rw [ha']; rfl
        have hP'0 : TopFreshTailPrepaidFreshTail ring C s (topFixedTraceNext ring C Z e) 0 :=
          ⟨hj, a, (Z.1.1 e).d, ha, hafresh, by rw [hnewj]; rfl⟩
        have hPeq : ∀ k, k < topClockSpan n → k ≠ 0 →
            (TopFreshTailPrepaidFreshTail ring C s (topFixedTraceNext ring C Z e) k ↔
              TopFreshTailPrepaidFreshTail ring C s Z k) :=
          fun k hk hk0 => hPframe k hk (hsame k hk hk0)
        have hS1 : topFreshTailPrepaidSumFrom s (topFixedTraceNext ring C Z e) 1 =
            topFreshTailPrepaidSumFrom s Z 1 :=
          topFreshTailPrepaidSumFromCongr s Z _ 1 (by
            intro k hk hlo
            unfold topFreshTailPrepaidCredit
            rw [hsame k hk (by omega)])
        cases hF : topFreshTailPrepaidFrontier ring C s Z with
        | none =>
            have hnone := topFreshTailPrepaidSearchNone _ _ hF
            have hF' : topFreshTailPrepaidFrontier ring C s (topFixedTraceNext ring C Z e) =
                some 0 := by
              unfold topFreshTailPrepaidFrontier
              apply topFreshTailPrepaidSearchEqSome _ _ 0 hP'0 hj
              intro k hk0 hk h
              exact hnone k hk ((hPeq k hk (by omega)).1 h)
            have hc : TopFreshTailPrepaidCharged ring C s Z e :=
              hiff.2 ⟨hch, (fun f hf => by rw [hF] at hf; cases hf)⟩
            rw [if_pos hc]
            unfold topFreshTailPrepaidPotential
            rw [hF', hF]
            simp only
            rw [topFreshTailPrepaidSumFromSucc s Z 0 hj, hS1, htok]
            unfold topFreshTailPrepaidCredit
            rw [htok]
            simp [topFreshTailPrepaidTokenCredit, topFreshTailPrepaidReserve]
            omega
        | some f =>
            obtain ⟨hPf, hfr, hmax⟩ := topFreshTailPrepaidSearchSome _ _ f hF
            have hf0 : f ≠ 0 := by intro h; subst h; exact hPj hPf
            have hF' : topFreshTailPrepaidFrontier ring C s (topFixedTraceNext ring C Z e) =
                some f := by
              unfold topFreshTailPrepaidFrontier
              apply topFreshTailPrepaidSearchEqSome _ _ f ((hPeq f hfr hf0).2 hPf) hfr
              intro k hkf hk h
              exact hmax k hkf hk ((hPeq k hk (by omega)).1 h)
            have hnc : ¬ TopFreshTailPrepaidCharged ring C s Z e := by
              intro hc
              have := (hiff.1 hc).2 f hF
              omega
            rw [if_neg hnc]
            unfold topFreshTailPrepaidPotential
            rw [hF', hF]
            simp only
            rw [topFreshTailPrepaidSumFromCongr s Z _ (f + 1) (by
              intro k hk hlo
              unfold topFreshTailPrepaidCredit
              rw [hsame k hk (by omega)])]
            rfl
      · have hfront := topFreshTailPrepaidFrontierFrame ring C s Z
          (topFixedTraceNext ring C Z e) (by
            intro k hk
            by_cases hkj : k = j
            · subst hkj
              constructor
              · intro h
                exact absurd h (topFreshTailPrepaidNotFreshTailOfToken ring C s _ k
                  (by intro v hv; rw [hnewj, if_neg hj0] at hv; cases hv))
              · intro h; exact absurd h hPj
            · exact hPframe k hk (hsame k hk hkj))
        have hclose := topFreshTailPrepaidCloseOne ring C s Z (topFixedTraceNext ring C Z e)
          j hj hsame hfront (by rw [hsame 0 (by omega) (Ne.symm hj0)]) (by
            unfold topFreshTailPrepaidCredit
            rw [hnewj, htok, if_neg hj0]
            simp [topFreshTailPrepaidTokenCredit, hj0]
            try omega)
        cases hF : topFreshTailPrepaidFrontier ring C s Z with
        | none =>
            have hc : TopFreshTailPrepaidCharged ring C s Z e :=
              hiff.2 ⟨hch, (fun f hf => by rw [hF] at hf; cases hf)⟩
            rw [if_pos hc]
            exact hclose.1 hF
        | some f =>
            have hPf := (topFreshTailPrepaidSearchSome _ _ f hF).1
            have hfj : f ≠ j := by intro h; subst h; exact hPj hPf
            by_cases hlt : f < j
            · have hc : TopFreshTailPrepaidCharged ring C s Z e :=
                hiff.2 ⟨hch, (fun f' hf' => by rw [hF] at hf'; cases hf'; omega)⟩
              rw [if_pos hc]
              exact hclose.2.1 f hF hlt
            · have hnc : ¬ TopFreshTailPrepaidCharged ring C s Z e := by
                intro hc
                have := (hiff.1 hc).2 f hF
                omega
              rw [if_neg hnc]
              exact hclose.2.2 f hF (by omega)
  | D v t =>
      have hxo : (Z.1.1 e).qOut = .D v t := by rw [hsite]; exact htok
      have hPnotE : (Z.1.1 (certSite s (⟨j, hj⟩ : Fin (topClockSpan n)).val)).qOut ≠ .E := by
        simp only; rw [htok]; intro h; cases h
      obtain ⟨p, hp⟩ := topFreshTailCausalOccupiedHasCarrier ring C s Z hqueue ⟨j, hj⟩ hPnotE
      rcases topFreshTailCausalDSourceOutcomes ring C Z e v t hxl hyl hxo with hstay | hgo
      · have hstayj : ((topFixedTraceNext ring C Z e).1.1 (certSite s j)).qOut = .D v t := by
          rw [← hsite]; exact hstay
        have hsame : ∀ k, k < topClockSpan n →
            ((topFixedTraceNext ring C Z e).1.1 (certSite s k)).qOut =
              (Z.1.1 (certSite s k)).qOut := by
          intro k hk
          by_cases hkj : k = j
          · subst hkj; rw [hstayj, htok]
          · by_cases hk1 : k = j + 1
            · subst hk1
              exact topFreshTailPrepaidSuccFrame ring C s hn hbad Z hreach e j hk hsite
                (fun v' t' h => by rw [htok] at h; cases h; exact hstayj)
            · exact hothers k hk hkj hk1
        have hnc : ¬ TopFreshTailPrepaidCharged ring C s Z e := by
          intro hc
          exact (hiff.1 hc).1 (hsame j hj)
        rw [if_neg hnc, topFreshTailPrepaidNoChange ring C s hn hbad Z hreach e hsame]
        rfl
      · have hgoj : ((topFixedTraceNext ring C Z e).1.1 (certSite s j)).qOut =
            (if t then .U else .E) := by
          rw [← hsite]; exact hgo
        have hch : ((topFixedTraceNext ring C Z e).1.1 (certSite s j)).qOut ≠
            (Z.1.1 (certSite s j)).qOut := by
          rw [hgoj, htok]; cases t <;> simp
        have hP'j : ¬ TopFreshTailPrepaidFreshTail ring C s (topFixedTraceNext ring C Z e) j :=
          topFreshTailPrepaidNotFreshTailOfToken ring C s _ j
            (by intro v' hv; rw [hgoj] at hv; cases t <;> cases hv)
        have hdep := topFreshTailTicketDeparture ring C s hn hbad Z hreach e ⟨j, hj⟩ hsite
          v t htok hgoj
        -- the one-site (port) and two-site (move) frames
        rcases hdep with ⟨hnext, hoE1, hnD1, hslot1⟩ | ⟨hlast, ⟨x, hx⟩, _⟩
        · have hsame2 : ∀ k, k < topClockSpan n → k ≠ j → k ≠ j + 1 →
              ((topFixedTraceNext ring C Z e).1.1 (certSite s k)).qOut =
                (Z.1.1 (certSite s k)).qOut := hothers
          have hPj1 : ¬ TopFreshTailPrepaidFreshTail ring C s Z (j + 1) :=
            topFreshTailPrepaidNotFreshTailOfToken ring C s Z (j + 1)
              (by intro v' hv; rw [hoE1] at hv; cases hv)
          have hres : topFreshTailPrepaidReserve (topClockSpan n)
                ((topFixedTraceNext ring C Z e).1.1 (certSite s 0)).qOut =
              topFreshTailPrepaidReserve (topClockSpan n) (Z.1.1 (certSite s 0)).qOut := by
            by_cases hj0 : j = 0
            · subst hj0
              rw [hgoj, htok]
              cases t <;> rfl
            · rw [hsame2 0 (by omega) (Ne.symm hj0) (by omega)]
          cases t with
          | false =>
              have hPj : ¬ TopFreshTailPrepaidFreshTail ring C s Z j :=
                topFreshTailPrepaidNotFreshTailOfToken ring C s Z j
                  (by intro v' hv; rw [htok] at hv; cases hv)
              have hfront := topFreshTailPrepaidFrontierFrame ring C s Z
                (topFixedTraceNext ring C Z e) (by
                  intro k hk
                  by_cases hkj : k = j
                  · subst hkj; exact ⟨fun h => absurd h hP'j, fun h => absurd h hPj⟩
                  · by_cases hk1 : k = j + 1
                    · subst hk1
                      constructor
                      · intro h
                        exact absurd h (topFreshTailPrepaidNotFreshTailOfToken ring C s _ _
                          (by intro v' hv; rw [hnD1] at hv; cases hv))
                      · intro h; exact absurd h hPj1
                    · exact hPframe k hk (hsame2 k hk hkj hk1))
              have hclose := topFreshTailPrepaidCloseTwo ring C s Z
                (topFixedTraceNext ring C Z e) j hnext hsame2 hfront hres (by
                  unfold topFreshTailPrepaidCredit
                  rw [hgoj, htok, hoE1, hnD1]
                  simp [topFreshTailPrepaidTokenCredit]
                  omega)
              cases hF : topFreshTailPrepaidFrontier ring C s Z with
              | none =>
                  have hc : TopFreshTailPrepaidCharged ring C s Z e :=
                    hiff.2 ⟨hch, (fun f hf => by rw [hF] at hf; cases hf)⟩
                  rw [if_pos hc]
                  exact hclose.1 hF
              | some f =>
                  have hPf := (topFreshTailPrepaidSearchSome _ _ f hF).1
                  have hfj : f ≠ j := by intro h; subst h; exact hPj hPf
                  have hfj1 : f ≠ j + 1 := by intro h; subst h; exact hPj1 hPf
                  by_cases hlt : f < j
                  · have hc : TopFreshTailPrepaidCharged ring C s Z e :=
                      hiff.2 ⟨hch, (fun f' hf' => by rw [hF] at hf'; cases hf'; omega)⟩
                    rw [if_pos hc]
                    exact hclose.2.1 f hF hlt
                  · have hnc : ¬ TopFreshTailPrepaidCharged ring C s Z e := by
                      intro hc
                      have := (hiff.1 hc).2 f hF
                      omega
                    rw [if_neg hnc]
                    exact hclose.2.2 f hF (by omega)
          | true =>
              by_cases hpf : topFreshTailTicketIsFresh p.origin = true
              · -- the fresh tail moves: it is F1 or behind F1
                have hPj : TopFreshTailPrepaidFreshTail ring C s Z j := ⟨hj, p, v, hp, hpf, htok⟩
                have hP'1 : TopFreshTailPrepaidFreshTail ring C s (topFixedTraceNext ring C Z e)
                    (j + 1) := ⟨hnext, p, v, by rw [hslot1]; exact hp, hpf, hnD1⟩
                cases hF : topFreshTailPrepaidFrontier ring C s Z with
                | none =>
                    exact absurd hPj (topFreshTailPrepaidSearchNone _ _ hF j hj)
                | some f =>
                    obtain ⟨hPf, hfr, hmax⟩ := topFreshTailPrepaidSearchSome _ _ f hF
                    have hjf : j ≤ f := by
                      by_cases h : j ≤ f
                      · exact h
                      · exact absurd hPj (hmax j (by omega) hj)
                    by_cases hfj : f = j
                    · subst hfj
                      have hF' : topFreshTailPrepaidFrontier ring C s
                          (topFixedTraceNext ring C Z e) = some (f + 1) := by
                        unfold topFreshTailPrepaidFrontier
                        apply topFreshTailPrepaidSearchEqSome _ _ (f + 1) hP'1 hnext
                        intro k hk1 hk h
                        exact hmax k (by omega) hk
                          ((hPframe k hk (hsame2 k hk (by omega) (by omega))).1 h)
                      have hc : TopFreshTailPrepaidCharged ring C s Z e :=
                        hiff.2 ⟨hch, (fun f' hf' => by rw [hF] at hf'; cases hf'; omega)⟩
                      rw [if_pos hc]
                      unfold topFreshTailPrepaidPotential
                      rw [hF', hF]
                      simp only
                      rw [topFreshTailPrepaidSumFromSucc s Z (f + 1) hnext,
                        topFreshTailPrepaidSumFromCongr s Z _ (f + 1 + 1) (by
                          intro k hk hlo
                          unfold topFreshTailPrepaidCredit
                          rw [hsame2 k hk (by omega) (by omega)])]
                      unfold topFreshTailPrepaidCredit
                      rw [hoE1]
                      simp [topFreshTailPrepaidTokenCredit]
                      omega
                    · have hfj1 : f ≠ j + 1 := by
                        intro h; subst h
                        exact topFreshTailPrepaidNotFreshTailOfToken ring C s Z (j + 1)
                          (by intro v' hv; rw [hoE1] at hv; cases hv) hPf
                      have hF' : topFreshTailPrepaidFrontier ring C s
                          (topFixedTraceNext ring C Z e) = some f := by
                        unfold topFreshTailPrepaidFrontier
                        apply topFreshTailPrepaidSearchEqSome _ _ f
                          ((hPframe f hfr (hsame2 f hfr hfj hfj1)).2 hPf) hfr
                        intro k hkf hk h
                        exact hmax k hkf hk
                          ((hPframe k hk (hsame2 k hk (by omega) (by omega))).1 h)
                      have hnc : ¬ TopFreshTailPrepaidCharged ring C s Z e := by
                        intro hc
                        have := (hiff.1 hc).2 f hF
                        omega
                      rw [if_neg hnc]
                      unfold topFreshTailPrepaidPotential
                      rw [hF', hF]
                      simp only
                      rw [topFreshTailPrepaidSumFromCongr s Z _ (f + 1) (by
                        intro k hk hlo
                        unfold topFreshTailPrepaidCredit
                        rw [hsame2 k hk (by omega) (by omega)])]
                      rfl
              · -- a nonfresh tail hop mints its prepaid child
                have hpnf : topFreshTailTicketIsFresh p.origin = false := by
                  cases h : topFreshTailTicketIsFresh p.origin
                  · rfl
                  · exact absurd h hpf
                have hPj : ¬ TopFreshTailPrepaidFreshTail ring C s Z j := by
                  rintro ⟨_, a, _, ha, haf, _⟩
                  have : a = p := Option.some.inj (ha.symm.trans hp)
                  subst this
                  rw [hpnf] at haf; cases haf
                have hP'j1 : ¬ TopFreshTailPrepaidFreshTail ring C s
                    (topFixedTraceNext ring C Z e) (j + 1) := by
                  rintro ⟨_, a, _, ha, haf, _⟩
                  rw [hslot1, hp] at ha
                  have : p = a := Option.some.inj ha
                  subst this
                  rw [hpnf] at haf; cases haf
                have hfront := topFreshTailPrepaidFrontierFrame ring C s Z
                  (topFixedTraceNext ring C Z e) (by
                    intro k hk
                    by_cases hkj : k = j
                    · subst hkj; exact ⟨fun h => absurd h hP'j, fun h => absurd h hPj⟩
                    · by_cases hk1 : k = j + 1
                      · subst hk1; exact ⟨fun h => absurd h hP'j1, fun h => absurd h hPj1⟩
                      · exact hPframe k hk (hsame2 k hk hkj hk1))
                have hcredit : ∀ (hj1 : 1 ≤ j ∨ j = 0),
                    topFreshTailPrepaidCredit s Z j + topFreshTailPrepaidCredit s Z (j + 1) =
                      topFreshTailPrepaidCredit s (topFixedTraceNext ring C Z e) j +
                        topFreshTailPrepaidCredit s (topFixedTraceNext ring C Z e) (j + 1) + 1 := by
                  intro _
                  unfold topFreshTailPrepaidCredit
                  rw [hgoj, htok, hoE1, hnD1]
                  simp only [topFreshTailPrepaidTokenCredit, if_true]
                  by_cases hj0 : j = 0
                  · subst hj0
                    rw [topFreshTailPrepaidTailBorder _ (by omega)]
                    simp
                    omega
                  · rw [topFreshTailPrepaidTailTransfer _ j (by omega) hj, if_neg hj0]
                    omega
                have hclose := topFreshTailPrepaidCloseTwo ring C s Z
                  (topFixedTraceNext ring C Z e) j hnext hsame2 hfront hres
                  (hcredit (by omega))
                cases hF : topFreshTailPrepaidFrontier ring C s Z with
                | none =>
                    have hc : TopFreshTailPrepaidCharged ring C s Z e :=
                      hiff.2 ⟨hch, (fun f hf => by rw [hF] at hf; cases hf)⟩
                    rw [if_pos hc]
                    exact hclose.1 hF
                | some f =>
                    have hPf := (topFreshTailPrepaidSearchSome _ _ f hF).1
                    have hfj : f ≠ j := by intro h; subst h; exact hPj hPf
                    have hfj1 : f ≠ j + 1 := by intro h; subst h; exact hPj1 hPf
                    by_cases hlt : f < j
                    · have hc : TopFreshTailPrepaidCharged ring C s Z e :=
                        hiff.2 ⟨hch, (fun f' hf' => by rw [hF] at hf'; cases hf'; omega)⟩
                      rw [if_pos hc]
                      exact hclose.2.1 f hF hlt
                    · have hnc : ¬ TopFreshTailPrepaidCharged ring C s Z e := by
                        intro hc
                        have := (hiff.1 hc).2 f hF
                        omega
                      rw [if_neg hnc]
                      exact hclose.2.2 f hF (by omega)
        · -- port departure at the terminal offset
          simp only at hlast
          have hsame1 : ∀ k, k < topClockSpan n → k ≠ j →
              ((topFixedTraceNext ring C Z e).1.1 (certSite s k)).qOut =
                (Z.1.1 (certSite s k)).qOut :=
            fun k hk hkj => hothers k hk hkj (by omega)
          have hj0 : j ≠ 0 := by omega
          have hres : topFreshTailPrepaidReserve (topClockSpan n)
                ((topFixedTraceNext ring C Z e).1.1 (certSite s 0)).qOut =
              topFreshTailPrepaidReserve (topClockSpan n) (Z.1.1 (certSite s 0)).qOut := by
            rw [hsame1 0 (by omega) (Ne.symm hj0)]
          have hPj : ¬ TopFreshTailPrepaidFreshTail ring C s Z j := by
            rintro ⟨_, a, w, ha, haf, hD⟩
            have : a = p := Option.some.inj (ha.symm.trans hp)
            subst this
            rw [htok] at hD
            cases hD
            apply hng
            have hfresh : ∃ b : Nat, a.origin = .freshBorder b := by
              cases ho : a.origin with
              | inherited i => rw [ho] at haf; cases haf
              | oldVisit i k => rw [ho] at haf; cases haf
              | freshBorder b => exact ⟨b, rfl⟩
            have hjr : j = topClockSpan n - 1 := by omega
            have hp' : (topFreshTailGenealogy ring C s Z).slots
                ⟨topClockSpan n - 1, by omega⟩ = some a := by
              have : (⟨topClockSpan n - 1, by omega⟩ : Fin (topClockSpan n)) = ⟨j, hj⟩ :=
                Fin.ext (by simp only; omega)
              rw [this]; exact hp
            have htok' : (Z.1.1 (certSite s (topClockSpan n - 1))).qOut = .D v true := by
              rw [← hjr]; exact htok
            exact topFreshTailTicketFreshExportGenuine ring C s hn hbad Z hreach e x hx a hp'
              hfresh v htok'
          have hfront := topFreshTailPrepaidFrontierFrame ring C s Z
            (topFixedTraceNext ring C Z e) (by
              intro k hk
              by_cases hkj : k = j
              · subst hkj; exact ⟨fun h => absurd h hP'j, fun h => absurd h hPj⟩
              · exact hPframe k hk (hsame1 k hk hkj))
          have hclose := topFreshTailPrepaidCloseOne ring C s Z (topFixedTraceNext ring C Z e)
            j hj hsame1 hfront hres (by
              unfold topFreshTailPrepaidCredit
              rw [hgoj, htok]
              cases t with
              | false =>
                  simp [topFreshTailPrepaidTokenCredit]
                  omega
              | true =>
                  simp only [topFreshTailPrepaidTokenCredit, if_true, if_neg hj0]
                  rw [topFreshTailPrepaidTailTransfer _ j (by omega) hj]
                  have hb : topFreshTailPrepaidTailCredit (topClockSpan n) (j + 1) = 0 := by
                    unfold topFreshTailPrepaidTailCredit
                    rw [show j + 1 = topClockSpan n by omega,
                      show max (topClockSpan n) 1 = topClockSpan n by omega, Nat.sub_self]
                    rfl
                  rw [hb]
                  omega)
          cases hF : topFreshTailPrepaidFrontier ring C s Z with
          | none =>
              have hc : TopFreshTailPrepaidCharged ring C s Z e :=
                hiff.2 ⟨hch, (fun f hf => by rw [hF] at hf; cases hf)⟩
              rw [if_pos hc]
              exact hclose.1 hF
          | some f =>
              obtain ⟨hPf, hfr, _⟩ := topFreshTailPrepaidSearchSome _ _ f hF
              have hfj : f ≠ j := by intro h; subst h; exact hPj hPf
              have hc : TopFreshTailPrepaidCharged ring C s Z e :=
                hiff.2 ⟨hch, (fun f' hf' => by rw [hF] at hf'; cases hf'; omega)⟩
              rw [if_pos hc]
              exact hclose.2.1 f hF (by omega)

/-- childSum d <= d(d+1). Consumer: topFreshTailPrepaidTokenCreditLe. -/
theorem topFreshTailPrepaidChildSumLe : ∀ d, topFreshTailPrepaidChildSum d ≤ d * (d + 1) := by
  intro d
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
      unfold topFreshTailPrepaidChildSum
      have key : (d + 1) * (d + 1 + 1) = d * (d + 1) + 2 * (d + 1) := by
        rw [Nat.mul_comm (d + 1) (d + 1 + 1), Nat.mul_succ, Nat.mul_comm (d + 1 + 1) d]
        rw [Nat.mul_succ d (d + 1)]
        omega
      rw [key]
      omega

/-- Every source token credit is at most r + r(r+1).
Consumer: topFreshTailPrepaidPotentialLe. -/
theorem topFreshTailPrepaidTokenCreditLe {A : Nat} (r j : Nat) (hr : 1 ≤ r) (tok : OutTok A) :
    topFreshTailPrepaidTokenCredit r j tok ≤ r + r * (r + 1) := by
  have hsq : 1 ≤ r * (r + 1) := by
    have h := Nat.mul_le_mul hr (show 1 ≤ r + 1 by omega)
    simpa using h
  cases tok with
  | E => exact Nat.zero_le _
  | U =>
      simp only [topFreshTailPrepaidTokenCredit]
      split
      · exact Nat.zero_le _
      · omega
  | D v t =>
      cases t with
      | false =>
          simp only [topFreshTailPrepaidTokenCredit]
          omega
      | true =>
          simp only [topFreshTailPrepaidTokenCredit, topFreshTailPrepaidTailCredit]
          have h1 := topFreshTailPrepaidChildSumLe (r - max j 1)
          have h2 : (r - max j 1) * (r - max j 1 + 1) ≤ r * (r + 1) :=
            Nat.mul_le_mul (by omega) (by omega)
          omega

/-- A list sum of terms bounded by M. Consumer:
topFreshTailPrepaidPotentialLe. -/
theorem topFreshTailPrepaidListSumLe (f : Nat → Nat) (M : Nat) (hf : ∀ x, f x ≤ M) :
    ∀ L : List Nat, (L.map f).sum ≤ L.length * M := by
  intro L
  induction L with
  | nil => simp
  | cons x L ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      have := hf x
      omega

/-- Item 7. On every cut (in particular every reached pre-anchor
cut) the prepaid potential is at most r + 2 + r(r + r(r+1)), hence at
most 8 r^3. Consumer: P.3 J4 (topFreshTailPrepaidContactBound). -/
theorem topFreshTailPrepaidPotentialLe
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (Z : TopFixedTraceState n) :
    topFreshTailPrepaidPotential ring C s Z ≤ 8 * topClockSpan n ^ 3 := by
  have hsum : ∀ lo, topFreshTailPrepaidSumFrom s Z lo ≤
      topClockSpan n * (topClockSpan n + topClockSpan n * (topClockSpan n + 1)) := by
    intro lo
    unfold topFreshTailPrepaidSumFrom
    have := topFreshTailPrepaidListSumLe
      (fun j => if lo ≤ j then topFreshTailPrepaidTokenCredit (topClockSpan n) j
        (Z.1.1 (certSite s j)).qOut else 0)
      (topClockSpan n + topClockSpan n * (topClockSpan n + 1))
      (by
        intro x
        split
        · exact topFreshTailPrepaidTokenCreditLe _ _ (by
            have hr := cert_rho_ge_three n hn
            change 3 ≤ topClockSpan n at hr
            omega) _
        · exact Nat.zero_le _)
      (List.range (topClockSpan n))
    rw [List.length_range] at this
    exact this
  have hres : ∀ tok : OutTok (compileAdvice (ceilLogTwo n)).topA,
      topFreshTailPrepaidReserve (topClockSpan n) tok ≤ topClockSpan n + 2 := by
    intro tok
    cases tok with
    | E => simp [topFreshTailPrepaidReserve]
    | U => simp [topFreshTailPrepaidReserve]
    | D v t => cases t <;> simp [topFreshTailPrepaidReserve]
  have hbound : topFreshTailPrepaidPotential ring C s Z ≤
      topClockSpan n + 2 +
        topClockSpan n * (topClockSpan n + topClockSpan n * (topClockSpan n + 1)) := by
    unfold topFreshTailPrepaidPotential
    cases topFreshTailPrepaidFrontier ring C s Z with
    | none =>
        simp only
        have := hsum 0
        have := hres (Z.1.1 (certSite s 0)).qOut
        omega
    | some f =>
        simp only
        have := hsum (f + 1)
        omega
  have hr3 := cert_rho_ge_three n hn
  change 3 ≤ topClockSpan n at hr3
  generalize topClockSpan n = r at hbound hr3 ⊢
  have hexp : r * (r + r * (r + 1)) = r * r + (r * r * r + r * r) := by
    rw [Nat.mul_add, Nat.mul_add r r 1, Nat.mul_one, Nat.mul_add r (r * r) r,
      ← Nat.mul_assoc]
  have hcube : r ^ 3 = r * r * r := by
    rw [show 3 = 2 + 1 from rfl, Nat.pow_succ, Nat.pow_two]
  rw [hexp] at hbound
  rw [hcube]
  have h1 : r ≤ r * r := Nat.le_mul_self r
  have h2 : r * r ≤ r * r * r := Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- Charged useful source contacts along a word from a cut. -/
noncomputable def topFreshTailPrepaidChargedCount
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n) :
    TopFixedTraceState n → List (Fin n) → Nat
  | _, [] => 0
  | Z, e :: rest =>
      (if TopFreshTailPrepaidCharged ring C s Z e then 1 else 0) +
        topFreshTailPrepaidChargedCount ring C s (topFixedTraceNext ring C Z e) rest

/-- Exact (c*) accounting along any word with no genuine-tail prefix:
charged contacts plus the final potential equal the initial potential.
Consumer: topFreshTailPrepaidContactBound. -/
theorem topFreshTailPrepaidChargedAccount
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hleader : ∀ i : Fin n, (C i).l = false) :
    ∀ (w : List (Fin n)) (Z : TopFixedTraceState n),
      topClockReached ring C Z →
      (∀ pre suffix : List (Fin n), pre ++ suffix = w → pre ≠ [] →
        ¬ topClockGenuineTailAccepted C s (pre.foldl (topFixedTraceNext ring C) Z)) →
      topFreshTailPrepaidChargedCount ring C s Z w +
          topFreshTailPrepaidPotential ring C s (w.foldl (topFixedTraceNext ring C) Z) =
        topFreshTailPrepaidPotential ring C s Z := by
  intro w
  induction w with
  | nil => intro Z _ _; simp [topFreshTailPrepaidChargedCount]
  | cons e rest ih =>
      intro Z hZ hpre
      have hng : ¬ topClockGenuineTailAccepted C s (topFixedTraceNext ring C Z e) :=
        hpre [e] rest rfl (by simp)
      have hstep := topFreshTailPrepaidSourceContactStep ring C s hn hbad hleader Z hZ e hng
      have hrest := ih (topFixedTraceNext ring C Z e) (topClockReachedNext ring C Z e hZ)
        (fun pre suffix h hne => hpre (e :: pre) suffix (by rw [← h]; rfl) (by simp))
      simp only [topFreshTailPrepaidChargedCount, List.foldl_cons]
      omega

/-- Item 7 (J4 source half). Before the first genuine border tail
of a leaderless entrance, the charged useful source contacts along the
actual word number at most Phi_*(start) - Phi_*(cut) <= 8 r^3; blocked
scheduler attempts are not counted and are not bounded here.
Consumer: P.3 J4 (the source part of the joint F clock). -/
theorem topFreshTailPrepaidContactBound
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hleader : ∀ i : Fin n, (C i).l = false)
    (word : List (Fin n))
    (hpre : ∀ pre suffix : List (Fin n), pre ++ suffix = word → pre ≠ [] →
      ¬ topClockGenuineTailAccepted C s (topFixedTraceRun ring C pre)) :
    topFreshTailPrepaidChargedCount ring C s ((C, digitAuditInitial (piD C)), []) word +
        topFreshTailPrepaidPotential ring C s (topFixedTraceRun ring C word) =
      topFreshTailPrepaidPotential ring C s ((C, digitAuditInitial (piD C)), []) ∧
    topFreshTailPrepaidChargedCount ring C s ((C, digitAuditInitial (piD C)), []) word ≤
      8 * topClockSpan n ^ 3 := by
  have h := topFreshTailPrepaidChargedAccount ring C s hn hbad hleader word
    ((C, digitAuditInitial (piD C)), []) (by unfold topClockReached; rfl) hpre
  have hle := topFreshTailPrepaidPotentialLe ring C s hn ((C, digitAuditInitial (piD C)), [])
  exact ⟨h, by omega⟩

end L3

#print axioms L3.topFreshTailPrepaidTailTransfer
#print axioms L3.topFreshTailPrepaidTailBorder
#print axioms L3.topFreshTailPrepaidSearchSome
#print axioms L3.topFreshTailPrepaidSearchNone
#print axioms L3.topFreshTailPrepaidSearchCongr
#print axioms L3.topFreshTailPrepaidSearchEqSome
#print axioms L3.topFreshTailPrepaidSearchEqNone
#print axioms L3.topFreshTailPrepaidSumOne
#print axioms L3.topFreshTailPrepaidSumTwo
#print axioms L3.topFreshTailPrepaidSumZero
#print axioms L3.topFreshTailPrepaidSumFromCongr
#print axioms L3.topFreshTailPrepaidSumFromOne
#print axioms L3.topFreshTailPrepaidSumFromTwo
#print axioms L3.topFreshTailPrepaidSumFromSucc
#print axioms L3.topFreshTailPrepaidResponderZeroFrame
#print axioms L3.topFreshTailPrepaidTokenFrame
#print axioms L3.topFreshTailPrepaidSlotFrame
#print axioms L3.topFreshTailPrepaidFreshTailFrame
#print axioms L3.topFreshTailPrepaidNoChange
#print axioms L3.topFreshTailPrepaidSiteInj
#print axioms L3.topFreshTailPrepaidChargedIff
#print axioms L3.topFreshTailPrepaidOthersFrame
#print axioms L3.topFreshTailPrepaidSuccFrame
#print axioms L3.topFreshTailPrepaidFrontierFrame
#print axioms L3.topFreshTailPrepaidNotFreshTailOfToken
#print axioms L3.topFreshTailPrepaidCloseOne
#print axioms L3.topFreshTailPrepaidCloseTwo
#print axioms L3.topFreshTailPrepaidSourceContactStep
#print axioms L3.topFreshTailPrepaidChildSumLe
#print axioms L3.topFreshTailPrepaidTokenCreditLe
#print axioms L3.topFreshTailPrepaidListSumLe
#print axioms L3.topFreshTailPrepaidPotentialLe
#print axioms L3.topFreshTailPrepaidChargedAccount
#print axioms L3.topFreshTailPrepaidContactBound
