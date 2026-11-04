import Leader.L3.CertRows

/-!
# Q7 (P.8): the source pipeline as an abstract window

The source block of a bad complete pair is the `r` sites `s, ..., s + r - 1`, with the marker at
`s` and no other marker among them.  Only the output field `qOut` of the checker matters for the
delivery of the next operand: its tokens are `E` (empty), `U` (the site owes a sample) and
`D v t` (a sampled operand of tail flag `t`).  The payload `v` does not influence scheduling,
so the abstract token keeps the tail flag only.

* `srcPair` is the QO row of `liveTopPair` on a source edge (`ox.beta`, `oy.beta`, and whether
  the port accepts);
* `srcStepAt` is one edge of the block: an internal edge, or the port edge `r - 1`;
* `dist` is the number of source services still needed before a `D` stands at the terminal:
  it is the position of the last busy site, counted to the terminal, plus the sampling steps.

No edge raises `dist` while it is positive, and the edge of the last busy site lowers it.

Consumer: `Leader/L3/Top/SettledWorkSource.lean` (the link to the concrete trace) and the P.8
delivery bound `at most r + 2 source services`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- The abstract source token: empty, owes a sample, sampled non-tail, sampled tail.

Consumer: `srcPair`. -/
inductive Tok : Type
  | e | u | dn | dt
  deriving DecidableEq

/-- A sampled token.

Consumer: `srcPair`. -/
def Tok.isD : Tok → Bool
  | .dn => true
  | .dt => true
  | _ => false

/-- The QO row of `liveTopPair` on one edge `x -> y`: `bx`, `bz` are the markers of `x`, `y`,
`acc` says that the responder input accepts a packet.

Consumer: `srcStepAt`. -/
def srcPair (bx bz acc : Bool) (x y : Tok) : Tok × Tok :=
  if x.isD && bz then
    (if acc then ((if x = .dt then .u else .e), y) else (x, y))
  else if x.isD && !bz && decide (y = .e) then
    ((if x = .dt then .u else .e), x)
  else if decide (x = .u) then
    ((if bx then .dt else .dn), y)
  else if bx && decide (x = .e) then
    (.u, y)
  else (x, y)

/-- Replace one token of the block.

Consumer: `srcStepAt`. -/
def srcSetOne (src : Nat → Tok) (p : Nat) (a : Tok) : Nat → Tok :=
  fun j => if j = p then a else src j

/-- Replace two adjacent tokens of the block.

Consumer: `srcStepAt`. -/
def srcSetTwo (src : Nat → Tok) (p : Nat) (a b : Tok) : Nat → Tok :=
  fun j => if j = p then a else if j = p + 1 then b else src j

/-- The edge `j` of a block of `r` sites: internal for `j + 1 < r`, the port edge for the last.

Consumer: `SrcStep`. -/
def srcStepAt (r : Nat) (acc : Bool) (src : Nat → Tok) (j : Nat) : Nat → Tok :=
  if j + 1 < r then
    srcSetTwo src j (srcPair (decide (j = 0)) false false (src j) (src (j + 1))).1
      (srcPair (decide (j = 0)) false false (src j) (src (j + 1))).2
  else
    srcSetOne src j (srcPair false true acc (src j) .e).1

/-- One step of the source block: frame, or an edge of the block.

Consumer: `dist_step_le`. -/
inductive SrcStep (r : Nat) (src : Nat → Tok) : (Nat → Tok) → Prop
  | frame : SrcStep r src src
  | edge (j : Nat) (hj : j < r) (acc : Bool) : SrcStep r src (srcStepAt r acc src j)

/-- The last busy site among the first `k`.

Consumer: `dist`. -/
def lastBusy (src : Nat → Tok) : Nat → Option Nat
  | 0 => none
  | k + 1 => if src k = .e then lastBusy src k else some k

/-- The characterisation of the last busy site.

Consumer: `lastBusy_of`, `dist_step_le`. -/
theorem lastBusy_some (src : Nat → Tok) : ∀ k m, lastBusy src k = some m →
    m < k ∧ src m ≠ .e ∧ ∀ i, m < i → i < k → src i = .e := by
  intro k
  induction k with
  | zero => intro m h; simp [lastBusy] at h
  | succ k ih =>
    intro m h
    simp only [lastBusy] at h
    by_cases hk : src k = .e
    · rw [if_pos hk] at h
      obtain ⟨h1, h2, h3⟩ := ih m h
      refine ⟨by omega, h2, ?_⟩
      intro i hi hik
      by_cases hik' : i = k
      · subst hik'; exact hk
      · exact h3 i hi (by omega)
    · rw [if_neg hk] at h
      have hm : k = m := by simpa using h
      subst hm
      exact ⟨by omega, hk, fun i hi hik => by omega⟩

/-- Nothing busy.

Consumer: `lastBusy_of`. -/
theorem lastBusy_none (src : Nat → Tok) : ∀ k, lastBusy src k = none → ∀ i, i < k → src i = .e := by
  intro k
  induction k with
  | zero => intro _ i hi; omega
  | succ k ih =>
    intro h i hi
    simp only [lastBusy] at h
    by_cases hk : src k = .e
    · rw [if_pos hk] at h
      by_cases hik : i = k
      · subst hik; exact hk
      · exact ih h i (by omega)
    · rw [if_neg hk] at h; simp at h

/-- A busy site with only empty sites above it is the last busy one.

Consumer: `dist_step_le`. -/
theorem lastBusy_of (src : Nat → Tok) (k m : Nat) (hm : m < k) (hb : src m ≠ .e)
    (hab : ∀ i, m < i → i < k → src i = .e) : lastBusy src k = some m := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [lastBusy]
    by_cases hk : src k = .e
    · rw [if_pos hk]
      have hmk : m < k := by
        by_cases h : m = k
        · subst h; exact absurd hk hb
        · omega
      exact ih hmk (fun i hi hik => hab i hi (by omega))
    · rw [if_neg hk]
      have : m = k := by
        by_cases h : m < k
        · exact absurd (hab k h (by omega)) hk
        · omega
      subst this; rfl

/-- All empty gives no busy site.

Consumer: `dist_step_le`. -/
theorem lastBusy_of_none (src : Nat → Tok) (k : Nat) (h : ∀ i, i < k → src i = .e) :
    lastBusy src k = none := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [lastBusy]
    rw [if_pos (h k (by omega))]
    exact ih (fun i hi => h i (by omega))

/-- The last busy site reads only the first `k` tokens.

Consumer: `dist_congr`. -/
theorem lastBusy_congr (f g : Nat → Tok) : ∀ k, (∀ i, i < k → f i = g i) →
    lastBusy f k = lastBusy g k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    simp only [lastBusy]
    rw [h k (by omega), ih (fun i hi => h i (by omega))]

/-- The number of source services before a `D` stands at the terminal of a block of `r` sites:
the empty block needs a bootstrap, a sample and `r - 1` shifts; a sample owed at the last busy
site `m` needs the sample and the shifts, a sampled token the shifts only.

Consumer: `dist_step_le`, `dist_step_drop`. -/
def dist (r : Nat) (src : Nat → Tok) : Nat :=
  match lastBusy src r with
  | none => r + 1
  | some m => if src m = .u then r - m else r - 1 - m

/-- The distance reads only the first `r` tokens.

Consumer: `topSettledSourceDeliver` (TopSettledWorkSource). -/
theorem dist_congr (r : Nat) (f g : Nat → Tok) (h : ∀ i, i < r → f i = g i) :
    dist r f = dist r g := by
  unfold dist
  rw [lastBusy_congr f g r h]
  cases hl : lastBusy g r with
  | none => rfl
  | some m =>
    have hm := (lastBusy_some g r m hl).1
    simp only
    rw [h m hm]

/-- The distance is at most `r + 1`.

Consumer: `topSettledSourceDeliver` (TopSettledWorkSource). -/
theorem dist_le (r : Nat) (src : Nat → Tok) : dist r src ≤ r + 1 := by
  unfold dist
  cases h : lastBusy src r with
  | none => exact Nat.le_refl _
  | some m => simp only; split <;> omega

/-- The distance is zero exactly when a sampled token stands at the terminal.

Consumer: `topSettledSourceDeliver` (TopSettledWorkSource). -/
theorem dist_zero_iff (r : Nat) (hr : 0 < r) (src : Nat → Tok) :
    dist r src = 0 ↔ (src (r - 1)).isD = true := by
  unfold dist
  cases h : lastBusy src r with
  | none =>
    have := lastBusy_none src r h (r - 1) (by omega)
    simp [this, Tok.isD]
  | some m =>
    obtain ⟨h1, h2, h3⟩ := lastBusy_some src r m h
    simp only
    by_cases hm : m = r - 1
    · subst hm
      cases ht : src (r - 1) <;> simp_all [Tok.isD]
      all_goals omega
    · have := h3 (r - 1) (by omega) (by omega)
      rw [this]
      split <;> simp [Tok.isD] <;> omega

/-- The last busy site, as a relation.

Consumer: `dist_step_le`. -/
def Last (r : Nat) (src : Nat → Tok) (m : Nat) : Prop :=
  m < r ∧ src m ≠ .e ∧ ∀ i, m < i → i < r → src i = .e

/-- The distance when a last busy site exists.

Consumer: `dist_step_le`. -/
theorem dist_of_last (r : Nat) (src : Nat → Tok) (m : Nat) (h : Last r src m) :
    dist r src = if src m = .u then r - m else r - 1 - m := by
  unfold dist
  rw [lastBusy_of src r m h.1 h.2.1 h.2.2]

/-- The distance of the empty block.

Consumer: `dist_step_le`. -/
theorem dist_of_empty (r : Nat) (src : Nat → Tok) (h : ∀ i, i < r → src i = .e) :
    dist r src = r + 1 := by
  unfold dist
  rw [lastBusy_of_none src r h]

/-- Either a last busy site exists or the block is empty.

Consumer: `dist_step_le`. -/
theorem last_or_empty (r : Nat) (src : Nat → Tok) :
    (∃ m, Last r src m) ∨ ∀ i, i < r → src i = .e := by
  cases h : lastBusy src r with
  | none => exact Or.inr (lastBusy_none src r h)
  | some m => exact Or.inl ⟨m, lastBusy_some src r m h⟩

/-- Pointwise values of an internal edge.

Consumer: `dist_step_le`. -/
theorem srcStepAt_internal (r : Nat) (acc : Bool) (src : Nat → Tok) (j : Nat) (hj : j + 1 < r)
    (i : Nat) : srcStepAt r acc src j i =
      if i = j then (srcPair (decide (j = 0)) false false (src j) (src (j + 1))).1
      else if i = j + 1 then (srcPair (decide (j = 0)) false false (src j) (src (j + 1))).2
      else src i := by
  simp [srcStepAt, hj, srcSetTwo]

/-- Pointwise values of the port edge.

Consumer: `dist_step_le`. -/
theorem srcStepAt_port (r : Nat) (acc : Bool) (src : Nat → Tok) (j : Nat) (hj : ¬ j + 1 < r)
    (i : Nat) : srcStepAt r acc src j i =
      if i = j then (srcPair false true acc (src j) .e).1 else src i := by
  simp [srcStepAt, hj, srcSetOne]

/-- Sites other than the two of an internal edge keep their token.

Consumer: `dist_step_le`. -/
theorem srcStepAt_far (r : Nat) (acc : Bool) (src : Nat → Tok) (j : Nat) (hint : j + 1 < r)
    (i : Nat) (h1 : i ≠ j) (h2 : i ≠ j + 1) : srcStepAt r acc src j i = src i := by
  rw [srcStepAt_internal r acc src j hint i, if_neg h1, if_neg h2]

/-- The source site of an internal edge.

Consumer: `dist_step_le`. -/
theorem srcStepAt_src (r : Nat) (acc : Bool) (src : Nat → Tok) (j : Nat) (hint : j + 1 < r) :
    srcStepAt r acc src j j = (srcPair (decide (j = 0)) false false (src j) (src (j + 1))).1 := by
  rw [srcStepAt_internal r acc src j hint j, if_pos rfl]

/-- The responder site of an internal edge.

Consumer: `dist_step_le`. -/
theorem srcStepAt_resp (r : Nat) (acc : Bool) (src : Nat → Tok) (j : Nat) (hint : j + 1 < r) :
    srcStepAt r acc src j (j + 1) =
      (srcPair (decide (j = 0)) false false (src j) (src (j + 1))).2 := by
  rw [srcStepAt_internal r acc src j hint (j + 1), if_neg (by omega), if_pos rfl]

/-- Sites other than the terminal keep their token under the port edge.

Consumer: `dist_step_le`. -/
theorem srcStepAt_portFar (r : Nat) (acc : Bool) (src : Nat → Tok) (j : Nat) (hj : ¬ j + 1 < r)
    (i : Nat) (h1 : i ≠ j) : srcStepAt r acc src j i = src i := by
  rw [srcStepAt_port r acc src j hj i, if_neg h1]

/-- The terminal under the port edge.

Consumer: `dist_step_le`. -/
theorem srcStepAt_portSrc (r : Nat) (acc : Bool) (src : Nat → Tok) (j : Nat) (hj : ¬ j + 1 < r) :
    srcStepAt r acc src j j = (srcPair false true acc (src j) .e).1 := by
  rw [srcStepAt_port r acc src j hj j, if_pos rfl]

/-- **No source edge raises the distance** while it is positive.

Consumer: `topSettledSourceDeliver` (TopSettledWorkSource). -/
theorem dist_step_le (r : Nat) (hr : 3 ≤ r) (src src' : Nat → Tok) (h : SrcStep r src src')
    (hd : dist r src ≠ 0) : dist r src' ≤ dist r src := by
  cases h with
  | frame => exact Nat.le_refl _
  | edge j hj acc =>
    rcases last_or_empty r src with ⟨m, hm⟩ | hall
    · obtain ⟨hmr, hmb, hma⟩ := hm
      have hdm := dist_of_last r src m ⟨hmr, hmb, hma⟩
      by_cases hint : j + 1 < r
      · by_cases ha : j + 1 < m
        · -- behind the last busy site
          have hL : Last r (srcStepAt r acc src j) m := by
            refine ⟨hmr, ?_, ?_⟩
            · rw [srcStepAt_far r acc src j hint m (by omega) (by omega)]; exact hmb
            · intro i hi hir
              rw [srcStepAt_far r acc src j hint i (by omega) (by omega)]; exact hma i hi hir
          rw [dist_of_last r _ m hL, srcStepAt_far r acc src j hint m (by omega) (by omega), hdm]
          exact Nat.le_refl _
        · by_cases hb : j + 1 = m
          · -- the responder is the last busy site and keeps its token
            subst hb
            have hy : (srcPair (decide (j = 0)) false false (src j) (src (j + 1))).2 = src (j + 1) := by
              by_cases hj0 : j = 0
              · cases hx : src j <;> cases hy : src (j + 1) <;> simp_all [srcPair, Tok.isD]
              · cases hx : src j <;> cases hy : src (j + 1) <;> simp_all [srcPair, Tok.isD]
            have hv : srcStepAt r acc src j (j + 1) = src (j + 1) := by
              rw [srcStepAt_resp r acc src j hint]; exact hy
            have hL : Last r (srcStepAt r acc src j) (j + 1) := by
              refine ⟨hmr, ?_, ?_⟩
              · rw [hv]; exact hmb
              · intro i hi hir
                rw [srcStepAt_far r acc src j hint i (by omega) (by omega)]; exact hma i hi hir
            rw [dist_of_last r _ (j + 1) hL, hv, hdm]
            exact Nat.le_refl _
          · by_cases hc : j = m
            · subst hc
              have hy : src (j + 1) = .e := hma (j + 1) (by omega) hint
              have hrest : ∀ i, j + 1 < i → i < r → srcStepAt r acc src j i = .e := by
                intro i hi hir
                rw [srcStepAt_far r acc src j hint i (by omega) (by omega)]
                exact hma i (by omega) hir
              cases hx : src j with
              | e => exact absurd hx hmb
              | u =>
                have hv : srcStepAt r acc src j j = (if decide (j = 0) = true then Tok.dt else Tok.dn) := by
                  rw [srcStepAt_src r acc src j hint, hx]
                  simp [srcPair, Tok.isD]
                have hL : Last r (srcStepAt r acc src j) j := by
                  refine ⟨hmr, ?_, ?_⟩
                  · rw [hv]; split <;> simp
                  · intro i hi hir
                    by_cases hi1 : i = j + 1
                    · subst hi1
                      rw [srcStepAt_resp r acc src j hint, hx, hy]
                      simp [srcPair, Tok.isD]
                    · exact hrest i (by omega) hir
                rw [dist_of_last r _ j hL, hdm, hv, hx]
                split <;> simp <;> omega
              | dn =>
                have hv : srcStepAt r acc src j (j + 1) = .dn := by
                  rw [srcStepAt_resp r acc src j hint, hx, hy]
                  simp [srcPair, Tok.isD]
                have hL : Last r (srcStepAt r acc src j) (j + 1) := by
                  refine ⟨hint, ?_, ?_⟩
                  · rw [hv]; simp
                  · intro i hi hir; exact hrest i hi hir
                rw [dist_of_last r _ (j + 1) hL, hdm, hv, hx]
                simp
                omega
              | dt =>
                have hv : srcStepAt r acc src j (j + 1) = .dt := by
                  rw [srcStepAt_resp r acc src j hint, hx, hy]
                  simp [srcPair, Tok.isD]
                have hL : Last r (srcStepAt r acc src j) (j + 1) := by
                  refine ⟨hint, ?_, ?_⟩
                  · rw [hv]; simp
                  · intro i hi hir; exact hrest i hi hir
                rw [dist_of_last r _ (j + 1) hL, hdm, hv, hx]
                simp
                omega
            · -- above the last busy site nothing changes
              have hjm : m < j := by omega
              have hx : src j = .e := hma j hjm hj
              have hy : src (j + 1) = .e := hma (j + 1) (by omega) hint
              have hj0 : decide (j = 0) = false := by simp; omega
              have hp : (srcPair (decide (j = 0)) false false (src j) (src (j + 1))) = (.e, .e) := by
                simp [srcPair, hx, hy, hj0, Tok.isD]
              have hL : Last r (srcStepAt r acc src j) m := by
                refine ⟨hmr, ?_, ?_⟩
                · rw [srcStepAt_far r acc src j hint m (by omega) (by omega)]; exact hmb
                · intro i hi hir
                  by_cases h1 : i = j
                  · rw [h1, srcStepAt_src r acc src j hint, hp]
                  · by_cases h2 : i = j + 1
                    · rw [h2, srcStepAt_resp r acc src j hint, hp]
                    · rw [srcStepAt_far r acc src j hint i h1 h2]; exact hma i hi hir
              rw [dist_of_last r _ m hL, srcStepAt_far r acc src j hint m (by omega) (by omega), hdm]
              exact Nat.le_refl _
      · -- the port edge
        have hjr : j = r - 1 := by omega
        by_cases hm1 : m = r - 1
        · have hmj : m = j := by omega
          subst hmj
          cases hx : src m with
          | e => exact absurd hx hmb
          | dn =>
            exfalso; apply hd; rw [dist_zero_iff r (by omega)]; rw [← hjr, hx]; rfl
          | dt =>
            exfalso; apply hd; rw [dist_zero_iff r (by omega)]; rw [← hjr, hx]; rfl
          | u =>
            have hv : srcStepAt r acc src m m = .dn := by
              rw [srcStepAt_portSrc r acc src m hint, hx]
              simp [srcPair, Tok.isD]
            have hL : Last r (srcStepAt r acc src m) m := by
              refine ⟨hmr, ?_, ?_⟩
              · rw [hv]; simp
              · intro i hi hir; omega
            rw [dist_of_last r _ m hL, hdm, hv, hx]
            simp
            omega
        · have hmj : m < j := by omega
          have hx : src j = .e := hma j hmj hj
          have hv : srcStepAt r acc src j j = .e := by
            rw [srcStepAt_portSrc r acc src j hint, hx]
            simp [srcPair, Tok.isD]
          have hL : Last r (srcStepAt r acc src j) m := by
            refine ⟨hmr, ?_, ?_⟩
            · rw [srcStepAt_portFar r acc src j hint m (by omega)]; exact hmb
            · intro i hi hir
              by_cases h1 : i = j
              · subst h1; exact hv
              · rw [srcStepAt_portFar r acc src j hint i h1]; exact hma i hi hir
          rw [dist_of_last r _ m hL, srcStepAt_portFar r acc src j hint m (by omega), hdm]
          exact Nat.le_refl _
    · -- the block is empty
      by_cases hint : j + 1 < r
      · by_cases hj0 : j = 0
        · subst hj0
          have hp : (srcPair (decide (0 = 0)) false false (src 0) (src (0 + 1))) = (.u, .e) := by
            simp [srcPair, hall 0 (by omega), hall 1 (by omega), Tok.isD]
          have hv : srcStepAt r acc src 0 0 = .u := by
            rw [srcStepAt_src r acc src 0 hint, hp]
          have hL : Last r (srcStepAt r acc src 0) 0 := by
            refine ⟨by omega, ?_, ?_⟩
            · rw [hv]; simp
            · intro i hi hir
              by_cases h2 : i = 1
              · subst h2; rw [srcStepAt_resp r acc src 0 hint, hp]
              · rw [srcStepAt_far r acc src 0 hint i (by omega) (by omega)]; exact hall i hir
          rw [dist_of_last r _ 0 hL, dist_of_empty r src hall, hv]
          simp
        · have hj0' : decide (j = 0) = false := by simpa using hj0
          have hp : (srcPair (decide (j = 0)) false false (src j) (src (j + 1))) = (.e, .e) := by
            simp [srcPair, hall j hj, hall (j + 1) hint, hj0', Tok.isD]
          have hE : ∀ i, i < r → srcStepAt r acc src j i = .e := by
            intro i hi
            by_cases h1 : i = j
            · subst h1; rw [srcStepAt_src r acc src i hint, hp]
            · by_cases h2 : i = j + 1
              · subst h2; rw [srcStepAt_resp r acc src j hint, hp]
              · rw [srcStepAt_far r acc src j hint i h1 h2]; exact hall i hi
          rw [dist_of_empty r _ hE, dist_of_empty r src hall]
          exact Nat.le_refl _
      · have hE : ∀ i, i < r → srcStepAt r acc src j i = .e := by
          intro i hi
          by_cases h1 : i = j
          · subst h1; rw [srcStepAt_portSrc r acc src i hint, hall i hj]
            simp [srcPair, Tok.isD]
          · rw [srcStepAt_portFar r acc src j hint i h1]; exact hall i hi
        rw [dist_of_empty r _ hE, dist_of_empty r src hall]
        exact Nat.le_refl _

/-- The nominated edge of the source block: the last busy site, or the marker if none.

Consumer: `dist_step_drop`, `topSettledSourceDeliver` (TopSettledWorkSource). -/
def srcIdx (r : Nat) (src : Nat → Tok) : Nat := (lastBusy src r).getD 0

/-- **The nominated edge lowers the distance** while it is positive.

Consumer: `topSettledSourceDeliver` (TopSettledWorkSource). -/
theorem dist_step_drop (r : Nat) (hr : 3 ≤ r) (src : Nat → Tok) (acc : Bool)
    (hd : dist r src ≠ 0) :
    srcIdx r src < r ∧
      dist r (srcStepAt r acc src (srcIdx r src)) + 1 ≤ dist r src := by
  rcases last_or_empty r src with ⟨m, hm⟩ | hall
  · obtain ⟨hmr, hmb, hma⟩ := hm
    have hlb := lastBusy_of src r m hmr hmb hma
    have hidx : srcIdx r src = m := by unfold srcIdx; rw [hlb]; rfl
    rw [hidx]
    refine ⟨hmr, ?_⟩
    have hdm := dist_of_last r src m ⟨hmr, hmb, hma⟩
    by_cases hint : m + 1 < r
    · have hy : src (m + 1) = .e := hma (m + 1) (by omega) hint
      have hrest : ∀ i, m + 1 < i → i < r → srcStepAt r acc src m i = .e := by
        intro i hi hir
        rw [srcStepAt_far r acc src m hint i (by omega) (by omega)]
        exact hma i (by omega) hir
      cases hx : src m with
      | e => exact absurd hx hmb
      | u =>
        have hv : srcStepAt r acc src m m = (if decide (m = 0) = true then Tok.dt else Tok.dn) := by
          rw [srcStepAt_src r acc src m hint, hx]
          simp [srcPair, Tok.isD]
        have hL : Last r (srcStepAt r acc src m) m := by
          refine ⟨hmr, ?_, ?_⟩
          · rw [hv]; split <;> simp
          · intro i hi hir
            by_cases hi1 : i = m + 1
            · subst hi1
              rw [srcStepAt_resp r acc src m hint, hx, hy]
              simp [srcPair, Tok.isD]
            · exact hrest i (by omega) hir
        rw [dist_of_last r _ m hL, hdm, hv, hx]
        split <;> simp <;> omega
      | dn =>
        have hv : srcStepAt r acc src m (m + 1) = .dn := by
          rw [srcStepAt_resp r acc src m hint, hx, hy]
          simp [srcPair, Tok.isD]
        have hL : Last r (srcStepAt r acc src m) (m + 1) := by
          refine ⟨hint, ?_, ?_⟩
          · rw [hv]; simp
          · intro i hi hir; exact hrest i hi hir
        rw [dist_of_last r _ (m + 1) hL, hdm, hv, hx]
        simp
        omega
      | dt =>
        have hv : srcStepAt r acc src m (m + 1) = .dt := by
          rw [srcStepAt_resp r acc src m hint, hx, hy]
          simp [srcPair, Tok.isD]
        have hL : Last r (srcStepAt r acc src m) (m + 1) := by
          refine ⟨hint, ?_, ?_⟩
          · rw [hv]; simp
          · intro i hi hir; exact hrest i hi hir
        rw [dist_of_last r _ (m + 1) hL, hdm, hv, hx]
        simp
        omega
    · have hm1 : m = r - 1 := by omega
      cases hx : src m with
      | e => exact absurd hx hmb
      | dn =>
        exfalso; apply hd; rw [dist_zero_iff r (by omega)]; rw [← hm1, hx]; rfl
      | dt =>
        exfalso; apply hd; rw [dist_zero_iff r (by omega)]; rw [← hm1, hx]; rfl
      | u =>
        have hv : srcStepAt r acc src m m = .dn := by
          rw [srcStepAt_portSrc r acc src m hint, hx]
          simp [srcPair, Tok.isD]
        have hL : Last r (srcStepAt r acc src m) m := by
          refine ⟨hmr, ?_, ?_⟩
          · rw [hv]; simp
          · intro i hi hir; omega
        rw [dist_of_last r _ m hL, hdm, hv, hx]
        simp
        omega
  · have hlb := lastBusy_of_none src r hall
    have hidx : srcIdx r src = 0 := by unfold srcIdx; rw [hlb]; rfl
    rw [hidx]
    refine ⟨by omega, ?_⟩
    have hint : 0 + 1 < r := by omega
    have hp : (srcPair (decide (0 = 0)) false false (src 0) (src (0 + 1))) = (.u, .e) := by
      simp [srcPair, hall 0 (by omega), hall 1 (by omega), Tok.isD]
    have hv : srcStepAt r acc src 0 0 = .u := by
      rw [srcStepAt_src r acc src 0 hint, hp]
    have hL : Last r (srcStepAt r acc src 0) 0 := by
      refine ⟨by omega, ?_, ?_⟩
      · rw [hv]; simp
      · intro i hi hir
        by_cases h2 : i = 1
        · subst h2; rw [srcStepAt_resp r acc src 0 hint, hp]
        · rw [srcStepAt_far r acc src 0 hint i (by omega) (by omega)]; exact hall i hir
    rw [dist_of_last r _ 0 hL, dist_of_empty r src hall, hv]
    simp

end MarkedCells
end L3

#print axioms L3.MarkedCells.dist_le
#print axioms L3.MarkedCells.dist_zero_iff
#print axioms L3.MarkedCells.dist_step_le
#print axioms L3.MarkedCells.dist_step_drop
