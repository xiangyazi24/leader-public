import Leader.L4.Height.FillAlt
import Leader.L4.Height.GapAlt

namespace L4.Height

open Classical
open L4.Compiler.Native

set_option maxRecDepth 8192
set_option maxHeartbeats 20000000

/-- The clockwise path beginning at a. -/
def fillGapPath {m : Nat} (hm : 0 < m) (a : Fin m) :
    Nat → Fin m :=
  fun i => gapSite hm a i

theorem fillGapPath_is_path {m : Nat} (hm : 0 < m)
    (a : Fin m) (g : Nat) :
    GapPath hm (fillGapPath hm a) g := by
  intro i hi
  simp [fillGapPath, gapSite_succ]

/-- Convert named-anchor survival and the absence of interior anchors into
the exact iff predicate expected by GapAlt. -/
theorem gapFixed_of_live_no_internal
    {m : Nat} (B : Nat) (hm : 0 < m)
    (bs : List (Fin m → Bool)) (s : Fin m → Snapshot)
    (a b : Fin m) (g T : Nat)
    (hgm : g < m)
    (hb : b = gapSite hm a g)
    (hlive : ∀ r, r < T →
      IsAnchor hm (gapState B hm bs s r) a ∧
      IsAnchor hm (gapState B hm bs s r) b)
    (hinterior : ∀ r, r < T → ∀ k, 0 < k → k < g →
      ¬ IsAnchor hm (gapState B hm bs s r) (gapSite hm a k)) :
    gapFixed B hm bs s a b g T := by
  intro r hr k hk
  constructor
  · intro ha
    by_cases hzero : k = 0
    · subst k
      simp
    · by_cases hend : k = g
      · subst k
        simp [hb]
      · have hkpos : 0 < k := by omega
        have hkg : k < g := by omega
        exact False.elim (hinterior r hr k hkpos hkg ha)
  · intro hend
    rcases hend with hstart | hfinish
    · have hidx : k = 0 := by
        apply gapSite_inj_lt hm a (by omega) (by omega)
        simpa using hstart
      subst k
      simpa using (hlive r hr).1
    · have hidx : k = g := by
        apply gapSite_inj_lt hm a (by omega) hgm
        rw [hb] at hfinish
        exact hfinish
      subst k
      simpa [hb] using (hlive r hr).2

/-- The interior exclusion for the first gap follows from FillAlt.Fixed
whenever the three named anchors are live. -/
theorem fillFixed_gapA
    {m : Nat} (hm : 0 < m)
    (S : Nat → Fin m → Snapshot) (T : Nat)
    (a b c : Fin m) (gA gB : Nat)
    (hfixed : Fixed hm S T
      (fillGapPath hm a) (fillGapPath hm b) gA gB a b c)
    (hlive : ∀ t, t ≤ T → NamedLive hm S t a b c) :
    ∀ t, t < T → ∀ i, 0 < i → i < gA →
      ¬ IsAnchor hm (S t) (fillGapPath hm a i) := by
  intro t ht i hi0 hig
  have h := hfixed t (Nat.le_of_lt ht) (hlive t (Nat.le_of_lt ht))
  exact h.1 i hi0 hig

/-- The interior exclusion for the second gap follows from FillAlt.Fixed
whenever the three named anchors are live. -/
theorem fillFixed_gapB
    {m : Nat} (hm : 0 < m)
    (S : Nat → Fin m → Snapshot) (T : Nat)
    (a b c : Fin m) (gA gB : Nat)
    (hfixed : Fixed hm S T
      (fillGapPath hm a) (fillGapPath hm b) gA gB a b c)
    (hlive : ∀ t, t ≤ T → NamedLive hm S t a b c) :
    ∀ t, t < T → ∀ i, 0 < i → i < gB →
      ¬ IsAnchor hm (S t) (fillGapPath hm b i) := by
  intro t ht i hi0 hig
  have h := hfixed t (Nat.le_of_lt ht) (hlive t (Nat.le_of_lt ht))
  exact h.2 i hi0 hig

/-- The final draw before a chosen opening round, in the arithmetic
progression beginning at firstDraw with the specified positive period. -/
def lastDrawBefore (firstDraw period final : Nat) : Nat :=
  if firstDraw < final then
    firstDraw + ((final - 1 - firstDraw) / period) * period
  else
    0

/-- The draw immediately preceding lastDrawBefore. The caller must establish
that the last draw is at least one full period after firstDraw. -/
def penultimateDrawBefore (firstDraw period final : Nat) : Nat :=
  lastDrawBefore firstDraw period final - period

/-- Four scheduled draw positions, represented as (round, site, prescribed bit).
The two rounds at each site are the last two members of that site's scheduled
arithmetic progression strictly before final. -/
def fourDrawPositions {m : Nat}
    (B : Nat) (hm : 0 < m) (s : Fin m → Snapshot)
    (a b c : Fin m) (gA gB G final : Nat) :
    List (Nat × Fin m × Bool) :=
  let firstA := gapFirstDrawRound B hm s a gA
  let firstB := gapFirstDrawRound B hm s b gB
  let periodA := 8 * gA + 9
  let periodB := 8 * gB + 9
  [ (penultimateDrawBefore firstA periodA final, a, false)
  , (lastDrawBefore firstA periodA final, a, false)
  , (penultimateDrawBefore firstB periodB final, b, true)
  , (lastDrawBefore firstB periodB final, b, true)
  ]

/-- The two scheduled rounds at one home are separated by exactly its
renewal period, whenever the last draw is defined by a nonempty progression. -/
theorem last_penultimate_separation
    (firstDraw period final : Nat)
    (hperiod : period ≤ lastDrawBefore firstDraw period final) :
    penultimateDrawBefore firstDraw period final + period =
      lastDrawBefore firstDraw period final := by
  simp [penultimateDrawBefore]
  omega

/-- The periods are positive for every positive gap. -/
theorem gap_draw_period_pos (g : Nat) (hg : 1 ≤ g) :
    0 < 8 * g + 9 := by
  omega

/-! ## Word-level helpers -/

private theorem runRounds_bounded_fill {m : Nat}
    (B : Nat) (hm : 0 < m) (hB : 0 < B)
    (bs : List (Fin m → Bool)) (s : Fin m → Snapshot)
    (hs : Bounded B s) :
    Bounded B (runRounds B hm bs s) := by
  induction bs generalizing s with
  | nil =>
      exact hs
  | cons bits rest ih =>
      rw [runRounds_cons]
      exact ih (logicalRound B hm bits s)
        (bounded_round B hm hB bits s hs)

private theorem runRounds_anchor_mono_fill {m : Nat}
    (B : Nat) (hm : 0 < m) (hmb : m < B)
    (bs : List (Fin m → Bool)) (s : Fin m → Snapshot)
    (hs : Bounded B s) :
    ∀ i, IsAnchor hm (runRounds B hm bs s) i → IsAnchor hm s i := by
  induction bs generalizing s with
  | nil =>
      intro i hi
      exact hi
  | cons bits rest ih =>
      intro i hi
      rw [runRounds_cons] at hi
      have hsnext : Bounded B (logicalRound B hm bits s) :=
        bounded_round B hm (by omega) bits s hs
      have hmid : IsAnchor hm (logicalRound B hm bits s) i :=
        ih (logicalRound B hm bits s) hsnext i hi
      exact anchor_mono B hm hmb bits s hs i hmid

private theorem gapState_bounded_fill {m : Nat}
    (B : Nat) (hm : 0 < m) (hB : 0 < B)
    (bs : List (Fin m → Bool)) (s : Fin m → Snapshot)
    (hs : Bounded B s) (r : Nat) :
    Bounded B (gapState B hm bs s r) := by
  unfold gapState
  exact runRounds_bounded_fill B hm hB (bs.take r) s hs

private theorem gapState_anchor_initial_fill {m : Nat}
    (B : Nat) (hm : 0 < m) (hmb : m < B)
    (bs : List (Fin m → Bool)) (s : Fin m → Snapshot)
    (hs : Bounded B s) (r : Nat) (i : Fin m)
    (hi : IsAnchor hm (gapState B hm bs s r) i) :
    IsAnchor hm s i := by
  unfold gapState at hi
  exact runRounds_anchor_mono_fill B hm hmb (bs.take r) s hs i hi

/-- A total bit vector agreeing with the supplied list at every present round. -/
def suppliedBits {m : Nat} (bs : List (Fin m → Bool))
    (r : Nat) : Fin m → Bool :=
  if h : r < bs.length then gapRoundBits bs r h else fun _ => false

theorem suppliedBits_eq {m : Nat} (bs : List (Fin m → Bool))
    (r : Nat) (hr : r < bs.length) :
    suppliedBits bs r = gapRoundBits bs r hr := by
  unfold suppliedBits
  simp [hr]

/-- A supplied word carries every listed round/site/value prescription. -/
def CarriesPositions {m : Nat} (bs : List (Fin m → Bool))
    (qs : List (Nat × Fin m × Bool)) : Prop :=
  ∀ r i v, (r, i, v) ∈ qs →
    ∃ hr : r < bs.length, (gapRoundBits bs r hr) i = v

/-- Forget the prescribed value when checking coordinate distinctness. -/
def drawCoordinate {m : Nat}
    (q : Nat × Fin m × Bool) : Nat × Fin m :=
  (q.1, q.2.1)

/-! ## Arithmetic of the last two scheduled draws -/

private theorem scheduled_eq_add_mul
    (first period q : Nat)
    (hfirst : first ≤ q)
    (hmod : (q - first) % period = 0) :
    ∃ k, q = first + k * period := by
  refine ⟨(q - first) / period, ?_⟩
  have hdiv := Nat.div_add_mod (q - first) period
  rw [hmod, Nat.add_zero] at hdiv
  have hdiv' : (q - first) / period * period = q - first := by
    simpa [Nat.mul_comm] using hdiv
  rw [hdiv']
  exact (Nat.add_sub_of_le hfirst).symm

private structure DrawWindowFacts
    (first period final : Nat) : Prop where
  first_le_penultimate :
    first ≤ penultimateDrawBefore first period final
  penultimate_lt_last :
    penultimateDrawBefore first period final <
      lastDrawBefore first period final
  last_lt_final : lastDrawBefore first period final < final
  penultimate_residue :
    (penultimateDrawBefore first period final - first) % period = 0
  last_residue :
    (lastDrawBefore first period final - first) % period = 0
  separation :
    penultimateDrawBefore first period final + period =
      lastDrawBefore first period final
  before_last_le_penultimate : ∀ q,
    first ≤ q → (q - first) % period = 0 →
    q < lastDrawBefore first period final →
    q ≤ penultimateDrawBefore first period final
  before_final_le_last : ∀ q,
    first ≤ q → (q - first) % period = 0 → q < final →
    q ≤ lastDrawBefore first period final

private theorem drawWindowFacts
    (first period final : Nat)
    (hperiod : 0 < period)
    (hroom : first + period < final) :
    DrawWindowFacts first period final := by
  let d := final - 1 - first
  let quot := d / period
  have hfirst : first < final := by omega
  have hperiodLe : period ≤ d := by
    dsimp [d]
    omega
  have hdecomp : quot * period + d % period = d := by
    dsimp [quot]
    simpa [Nat.mul_comm] using (Nat.div_add_mod d period)
  have hrem : d % period < period := Nat.mod_lt d hperiod
  have hquotPos : 0 < quot := by
    by_cases hq : quot = 0
    · rw [hq, Nat.zero_mul, Nat.zero_add] at hdecomp
      omega
    · exact Nat.pos_of_ne_zero hq
  obtain ⟨k, hquot⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hquotPos)
  have hlastEq :
      lastDrawBefore first period final = first + quot * period := by
    simp [lastDrawBefore, hfirst, quot, d]
  have hpenEq :
      penultimateDrawBefore first period final = first + k * period := by
    unfold penultimateDrawBefore
    rw [hlastEq, hquot, Nat.succ_mul]
    omega
  have hquotMulLe : quot * period ≤ d := by omega
  have hlastLt : lastDrawBefore first period final < final := by
    rw [hlastEq]
    dsimp [d] at hquotMulLe
    omega
  have hpenLt :
      penultimateDrawBefore first period final <
        lastDrawBefore first period final := by
    rw [hpenEq, hlastEq, hquot, Nat.succ_mul]
    omega
  have hfirstPen :
      first ≤ penultimateDrawBefore first period final := by
    rw [hpenEq]
    omega
  have hpenResidue :
      (penultimateDrawBefore first period final - first) % period = 0 := by
    rw [hpenEq]
    simp
  have hlastResidue :
      (lastDrawBefore first period final - first) % period = 0 := by
    rw [hlastEq]
    simp
  have hseparation :
      penultimateDrawBefore first period final + period =
        lastDrawBefore first period final := by
    rw [hpenEq, hlastEq, hquot, Nat.succ_mul]
    omega
  have hbeforeFinal : ∀ q,
      first ≤ q → (q - first) % period = 0 → q < final →
      q ≤ lastDrawBefore first period final := by
    intro q hfirstq hres hqfinal
    obtain ⟨j, hq⟩ :=
      scheduled_eq_add_mul first period q hfirstq hres
    by_cases hj : j ≤ quot
    · rw [hq, hlastEq]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right period hj) first
    · have hquotj : quot < j := by omega
      have hnextLe : quot * period + period ≤ j * period := by
        have hh := Nat.mul_le_mul_right period
          (show quot + 1 ≤ j by omega)
        rw [Nat.add_mul] at hh
        simpa using hh
      have hdlt : d < quot * period + period := by omega
      have hjMulLe : j * period ≤ d := by
        rw [hq] at hqfinal
        dsimp [d]
        omega
      have hdj : d < j * period := Nat.lt_of_lt_of_le hdlt hnextLe
      exact False.elim ((Nat.not_lt_of_ge hjMulLe) hdj)
  have hbeforeLast : ∀ q,
      first ≤ q → (q - first) % period = 0 →
      q < lastDrawBefore first period final →
      q ≤ penultimateDrawBefore first period final := by
    intro q hfirstq hres hqlast
    obtain ⟨j, hq⟩ :=
      scheduled_eq_add_mul first period q hfirstq hres
    have hmulLt : j * period < quot * period := by
      rw [hq, hlastEq] at hqlast
      omega
    have hjquot : j < quot :=
      (Nat.mul_lt_mul_right hperiod).1 hmulLt
    have hjk : j ≤ k := by
      rw [hquot] at hjquot
      omega
    rw [hq, hpenEq]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right period hjk) first
  exact {
    first_le_penultimate := hfirstPen
    penultimate_lt_last := hpenLt
    last_lt_final := hlastLt
    penultimate_residue := hpenResidue
    last_residue := hlastResidue
    separation := hseparation
    before_last_le_penultimate := hbeforeLast
    before_final_le_last := hbeforeFinal
  }

private theorem gapFirstDrawRound_le
    {m : Nat} (B : Nat) (hm : 0 < m)
    (s : Fin m → Snapshot) (a : Fin m) (g : Nat) :
    gapFirstDrawRound B hm s a g ≤ g + 1 + (8 * g + 9) := by
  unfold gapFirstDrawRound
  have hmin := Nat.min_le_left (8 * g + 8)
    (gapClockZ B g (gapInitialD hm s a) (s a).z (g + 1))
  omega

/-- The four source coordinates are pairwise distinct and all lie in the
comparison window. Distinctness is of `(round,site)`, not merely of the full
triple including its desired value. -/
theorem fourDrawPositions_distinct_lt
    {m : Nat} (B G T : Nat) (hm : 0 < m)
    (s : Fin m → Snapshot) (a b c : Fin m) (gA gB : Nat)
    (hwindow : T = 64 * (G + 1))
    (hgA : 1 ≤ gA) (hgB : 1 ≤ gB)
    (hgAG : gA ≤ G) (hgBG : gB ≤ G)
    (hgapSum : gA + gB ≤ m)
    (hb : b = gapSite hm a gA) :
    ((fourDrawPositions B hm s a b c gA gB G T).map
      drawCoordinate).Nodup ∧
    ∀ r i v, (r, i, v) ∈
      fourDrawPositions B hm s a b c gA gB G T → r < T := by
  let firstA := gapFirstDrawRound B hm s a gA
  let firstB := gapFirstDrawRound B hm s b gB
  let periodA := 8 * gA + 9
  let periodB := 8 * gB + 9
  let penA := penultimateDrawBefore firstA periodA T
  let lastA := lastDrawBefore firstA periodA T
  let penB := penultimateDrawBefore firstB periodB T
  let lastB := lastDrawBefore firstB periodB T
  have hroomA : firstA + periodA < T := by
    have hf := gapFirstDrawRound_le B hm s a gA
    dsimp [firstA, periodA]
    omega
  have hroomB : firstB + periodB < T := by
    have hf := gapFirstDrawRound_le B hm s b gB
    dsimp [firstB, periodB]
    omega
  have factsA := drawWindowFacts firstA periodA T
    (by dsimp [periodA]; omega) hroomA
  have factsB := drawWindowFacts firstB periodB T
    (by dsimp [periodB]; omega) hroomB
  have hpenALast : penA < lastA := by
    dsimp [penA, lastA]
    exact factsA.penultimate_lt_last
  have hpenBLast : penB < lastB := by
    dsimp [penB, lastB]
    exact factsB.penultimate_lt_last
  have hlastAT : lastA < T := by
    dsimp [lastA]
    exact factsA.last_lt_final
  have hlastBT : lastB < T := by
    dsimp [lastB]
    exact factsB.last_lt_final
  have hgAm : gA < m := by omega
  have hab : a ≠ b := by
    intro habEq
    have hsite : gapSite hm a gA = a := by
      rw [← hb, habEq]
    exact (gapSite_ne_start hm a (by omega) hgAm) hsite
  constructor
  · change List.Nodup
      [(penA, a), (lastA, a), (penB, b), (lastB, b)]
    have hpa : penA ≠ lastA := Nat.ne_of_lt hpenALast
    have hpb : penB ≠ lastB := Nat.ne_of_lt hpenBLast
    have h12 : (penA, a) ≠ (lastA, a) := by
      intro h
      exact hpa (congrArg Prod.fst h)
    have h13 : (penA, a) ≠ (penB, b) := by
      intro h
      exact hab (congrArg Prod.snd h)
    have h14 : (penA, a) ≠ (lastB, b) := by
      intro h
      exact hab (congrArg Prod.snd h)
    have h23 : (lastA, a) ≠ (penB, b) := by
      intro h
      exact hab (congrArg Prod.snd h)
    have h24 : (lastA, a) ≠ (lastB, b) := by
      intro h
      exact hab (congrArg Prod.snd h)
    have h34 : (penB, b) ≠ (lastB, b) := by
      intro h
      exact hpb (congrArg Prod.fst h)
    have htail : List.Nodup [(lastA, a), (penB, b), (lastB, b)] := by
      apply List.nodup_cons.mpr
      constructor
      · simp [h23, h24]
      · apply List.nodup_cons.mpr
        constructor
        · simp [h34]
        · simp
    exact List.nodup_cons.mpr
      ⟨by simp [h12, h13, h14], htail⟩
  · intro r i v hmem
    change (r, i, v) ∈
      [(penA, a, false), (lastA, a, false),
       (penB, b, true), (lastB, b, true)] at hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with hmem | hmem
    · have hr : r = penA := by
        simpa using congrArg Prod.fst hmem
      rw [hr]
      exact Nat.lt_trans hpenALast hlastAT
    · rcases hmem with hmem | hmem
      · have hr : r = lastA := by
          simpa using congrArg Prod.fst hmem
        rw [hr]
        exact hlastAT
      · rcases hmem with hmem | hmem
        · have hr : r = penB := by
            simpa using congrArg Prod.fst hmem
          rw [hr]
          exact Nat.lt_trans hpenBLast hlastBT
        · rcases hmem with hmem | hnil
          · have hr : r = lastB := by
              simpa using congrArg Prod.fst hmem
            rw [hr]
            exact hlastBT
          · cases hnil

/-! ## A same-valued redraw does not interrupt the moving broadcast -/

/-- Two consecutive scheduled draws with the same value support one continuous
role wave. Before the second draw the wave is sourced by the penultimate draw;
after it reaches a site, the second draw supplies the identical value. -/
theorem gap_role_two_draws {m : Nat}
    (B : Nat) (hm : 0 < m)
    (bs : List (Fin m → Bool)) (s : Fin m → Snapshot)
    (a b : Fin m) (g T : Nat)
    (hgm : g ≤ m) (hb : b = gapSite hm a g)
    (hbits : T ≤ bs.length)
    (hf : gapFixed B hm bs s a b g T)
    (r0 r1 r' : Nat)
    (hr0 : r0 < T) (hr1 : r1 < T) (hr' : r' < T)
    (h01 : r0 < r1) (h1r : r1 ≤ r')
    (v : Bool)
    (hv0 : (gapRoundBits bs r0
      (Nat.lt_of_lt_of_le hr0 hbits)) a = v)
    (hv1 : (gapRoundBits bs r1
      (Nat.lt_of_lt_of_le hr1 hbits)) a = v)
    (hdraw0 : gapDraw B hm bs s a r0)
    (hdraw1 : gapDraw B hm bs s a r1)
    (hnoBetween : ∀ q, r0 < q → q < r1 →
      ¬ gapDraw B hm bs s a q)
    (hnoAfter : ∀ q, r1 < q → q ≤ r' →
      ¬ gapDraw B hm bs s a q) :
    ∀ j, j < g → ∀ t, r0 + j ≤ t → (htr' : t ≤ r') →
      (afterPhaseTwo B hm
        (gapRoundBits bs t
          (Nat.lt_of_lt_of_le
            (Nat.lt_of_le_of_lt htr' hr') hbits))
        (gapState B hm bs s t) (gapSite hm a j)).role = v := by
  intro j
  induction j with
  | zero =>
      intro hj t hlow hhigh
      by_cases ht : t < r1
      · have hr1pred : r1 - 1 < T := by omega
        have hfirst := gap_role B hm bs s a b g T hgm hb hbits hf
          r0 (r1 - 1) hr0 hr1pred (by omega) v hv0 hdraw0 (by
            intro q hq0 hqle
            apply hnoBetween q hq0
            omega)
        exact hfirst 0 (by omega) t (by omega) (by omega)
      · have hsecond := gap_role B hm bs s a b g T hgm hb hbits hf
          r1 r' hr1 hr' h1r v hv1 hdraw1 hnoAfter
        exact hsecond 0 (by omega) t (by omega) hhigh
  | succ j ih =>
      intro hj t hlow hhigh
      have htT : t < T := Nat.lt_of_le_of_lt hhigh hr'
      have hnon := gapFixed_internal B hm bs s a b g T t (j + 1)
        hb hgm hf htT (by omega) (by omega)
      rw [afterPhaseTwo_role_of_nonanchor
        B hm
        (gapRoundBits bs t
          (Nat.lt_of_lt_of_le htT hbits))
        (gapState B hm bs s t) (gapSite hm a (j + 1)) hnon]
      rw [left_gapSite_succ]
      let q := t - 1
      have hqOne : q + 1 = t := by
        dsimp [q]
        omega
      have hqT : q < T := by
        dsimp [q]
        omega
      have hqLen : q < bs.length := Nat.lt_of_lt_of_le hqT hbits
      rw [← hqOne]
      rw [gapState_role_succ B hm bs s q hqLen (gapSite hm a j)]
      apply ih (by omega)
      · dsimp [q]
        omega
      · dsimp [q]
        omega

/-! ## The deterministic FillGap bridge -/

/-- The four-bit event obtained solely from the initial state and the two fixed
cyclic gaps. No inequality between `a` and `c` is assumed; hence setting
`c = a` gives the two-anchor complementary-gap case. -/
theorem four_bit_loss_of_gaps {m : Nat}
    (B G T : Nat) (hm : 0 < m)
    (bs : List (Fin m → Bool)) (s : Fin m → Snapshot)
    (a b c : Fin m) (gA gB : Nat)
    (hwindow : T = 64 * (G + 1))
    (hgA : 1 ≤ gA) (hgB : 1 ≤ gB)
    (hgAG : gA ≤ G) (hgBG : gB ≤ G)
    (hgapSum : gA + gB ≤ m) (hmB : m < B)
    (hb : b = gapSite hm a gA)
    (hc : c = gapSite hm b gB)
    (hanchorA : IsAnchor hm s a)
    (hanchorB : IsAnchor hm s b)
    (hanchorC : IsAnchor hm s c)
    (hinteriorA : ∀ i, 0 < i → i < gA →
      ¬ IsAnchor hm s (gapSite hm a i))
    (hinteriorB : ∀ i, 0 < i → i < gB →
      ¬ IsAnchor hm s (gapSite hm b i))
    (hbits : T ≤ bs.length)
    (hbounded : Bounded B s)
    (hprescribed : CarriesPositions bs
      (fourDrawPositions B hm s a b c gA gB G T)) :
    ∃ t, t ≤ T ∧
      (¬ IsAnchor hm (gapState B hm bs s t) a ∨
       ¬ IsAnchor hm (gapState B hm bs s t) b ∨
       ¬ IsAnchor hm (gapState B hm bs s t) c) := by
  by_cases hlose : ∃ t, t ≤ T ∧
      (¬ IsAnchor hm (gapState B hm bs s t) a ∨
       ¬ IsAnchor hm (gapState B hm bs s t) b ∨
       ¬ IsAnchor hm (gapState B hm bs s t) c)
  · exact hlose
  · have hlive : ∀ t, t ≤ T →
        NamedLive hm (fun r => gapState B hm bs s r) t a b c := by
      intro t ht
      have ha : IsAnchor hm (gapState B hm bs s t) a := by
        by_cases h : IsAnchor hm (gapState B hm bs s t) a
        · exact h
        · exact False.elim (hlose ⟨t, ht, Or.inl h⟩)
      have hbLive : IsAnchor hm (gapState B hm bs s t) b := by
        by_cases h : IsAnchor hm (gapState B hm bs s t) b
        · exact h
        · exact False.elim (hlose ⟨t, ht, Or.inr (Or.inl h)⟩)
      have hcLive : IsAnchor hm (gapState B hm bs s t) c := by
        by_cases h : IsAnchor hm (gapState B hm bs s t) c
        · exact h
        · exact False.elim (hlose ⟨t, ht, Or.inr (Or.inr h)⟩)
      exact ⟨ha, hbLive, hcLive⟩
    have hBpos : 0 < B := by omega
    have hTpos : 0 < T := by omega
    have hgAm : gA < m := by omega
    have hgBm : gB < m := by omega
    have hboundedAll : ∀ t, t ≤ T →
        Bounded B (gapState B hm bs s t) := by
      intro t ht
      exact gapState_bounded_fill B hm hBpos bs s hbounded t
    have hfixed : Fixed hm
        (fun r => gapState B hm bs s r) T
        (fillGapPath hm a) (fillGapPath hm b) gA gB a b c := by
      unfold Fixed
      intro t ht _hnamed
      constructor
      · intro i hi0 hig hnew
        apply hinteriorA i hi0 hig
        exact gapState_anchor_initial_fill B hm hmB bs s hbounded t
          (fillGapPath hm a i) (by simpa [fillGapPath] using hnew)
      · intro i hi0 hig hnew
        apply hinteriorB i hi0 hig
        exact gapState_anchor_initial_fill B hm hmB bs s hbounded t
          (fillGapPath hm b i) (by simpa [fillGapPath] using hnew)
    have hgapFixedA : gapFixed B hm bs s a b gA T := by
      apply gapFixed_of_live_no_internal B hm bs s a b gA T hgAm hb
      · intro r hr
        have hh := hlive r (Nat.le_of_lt hr)
        exact ⟨hh.1, hh.2.1⟩
      · intro r hr i hi0 hig hnew
        apply hinteriorA i hi0 hig
        exact gapState_anchor_initial_fill B hm hmB bs s hbounded r
          (gapSite hm a i) hnew
    have hgapFixedB : gapFixed B hm bs s b c gB T := by
      apply gapFixed_of_live_no_internal B hm bs s b c gB T hgBm hc
      · intro r hr
        have hh := hlive r (Nat.le_of_lt hr)
        exact ⟨hh.2.1, hh.2.2⟩
      · intro r hr i hi0 hig hnew
        apply hinteriorB i hi0 hig
        exact gapState_anchor_initial_fill B hm hmB bs s hbounded r
          (gapSite hm b i) hnew
    have hdrawsA := gap_draws B hm hmB bs s hbounded a b gA T
      hgA (by omega) hb hbits hgapFixedA
    have hdrawsB := gap_draws B hm hmB bs s hbounded b c gB T
      hgB (by omega) hc hbits hgapFixedB
    let firstA := gapFirstDrawRound B hm s a gA
    let firstB := gapFirstDrawRound B hm s b gB
    let periodA := 8 * gA + 9
    let periodB := 8 * gB + 9
    let penA := penultimateDrawBefore firstA periodA T
    let lastA := lastDrawBefore firstA periodA T
    let penB := penultimateDrawBefore firstB periodB T
    let lastB := lastDrawBefore firstB periodB T
    let startA := T - gA
    let startB := T - gB
    have hroomA : firstA + periodA < T := by
      dsimp [firstA, periodA]
      have hf := hdrawsA.1
      omega
    have hroomB : firstB + periodB < T := by
      dsimp [firstB, periodB]
      have hf := hdrawsB.1
      omega
    have factsA := drawWindowFacts firstA periodA T
      (by dsimp [periodA]; omega) hroomA
    have factsB := drawWindowFacts firstB periodB T
      (by dsimp [periodB]; omega) hroomB
    have hfirstLowA : gA + 1 ≤ firstA := by
      dsimp [firstA]
      unfold gapFirstDrawRound
      omega
    have hfirstLowB : gB + 1 ≤ firstB := by
      dsimp [firstB]
      unfold gapFirstDrawRound
      omega
    have hfirstPenA : firstA ≤ penA := by
      dsimp [penA]
      exact factsA.first_le_penultimate
    have hfirstPenB : firstB ≤ penB := by
      dsimp [penB]
      exact factsB.first_le_penultimate
    have hpenLastA : penA < lastA := by
      dsimp [penA, lastA]
      exact factsA.penultimate_lt_last
    have hpenLastB : penB < lastB := by
      dsimp [penB, lastB]
      exact factsB.penultimate_lt_last
    have hlastAT : lastA < T := by
      dsimp [lastA]
      exact factsA.last_lt_final
    have hlastBT : lastB < T := by
      dsimp [lastB]
      exact factsB.last_lt_final
    have hpenAT : penA < T := Nat.lt_trans hpenLastA hlastAT
    have hpenBT : penB < T := Nat.lt_trans hpenLastB hlastBT
    have hpenResidueA : (penA - firstA) % periodA = 0 := by
      dsimp [penA]
      exact factsA.penultimate_residue
    have hlastResidueA : (lastA - firstA) % periodA = 0 := by
      dsimp [lastA]
      exact factsA.last_residue
    have hpenResidueB : (penB - firstB) % periodB = 0 := by
      dsimp [penB]
      exact factsB.penultimate_residue
    have hlastResidueB : (lastB - firstB) % periodB = 0 := by
      dsimp [lastB]
      exact factsB.last_residue
    have hsepA : penA + periodA = lastA := by
      dsimp [penA, lastA]
      exact factsA.separation
    have hsepB : penB + periodB = lastB := by
      dsimp [penB, lastB]
      exact factsB.separation
    have hdrawPenA : gapDraw B hm bs s a penA := by
      apply (hdrawsA.2 penA (by omega) hpenAT).2
      exact ⟨hfirstPenA, hpenResidueA⟩
    have hdrawLastA : gapDraw B hm bs s a lastA := by
      apply (hdrawsA.2 lastA (by omega) hlastAT).2
      exact ⟨Nat.le_trans hfirstPenA (Nat.le_of_lt hpenLastA),
        hlastResidueA⟩
    have hdrawPenB : gapDraw B hm bs s b penB := by
      apply (hdrawsB.2 penB (by omega) hpenBT).2
      exact ⟨hfirstPenB, hpenResidueB⟩
    have hdrawLastB : gapDraw B hm bs s b lastB := by
      apply (hdrawsB.2 lastB (by omega) hlastBT).2
      exact ⟨Nat.le_trans hfirstPenB (Nat.le_of_lt hpenLastB),
        hlastResidueB⟩
    have hnoBetweenA : ∀ q, penA < q → q < lastA →
        ¬ gapDraw B hm bs s a q := by
      intro q hpq hql hdraw
      have hsched := (hdrawsA.2 q (by omega)
        (Nat.lt_trans hql hlastAT)).1 hdraw
      have hleRaw := factsA.before_last_le_penultimate q
        hsched.1 hsched.2 (by simpa [lastA] using hql)
      have hle : q ≤ penA := by simpa [penA] using hleRaw
      omega
    have hnoBetweenB : ∀ q, penB < q → q < lastB →
        ¬ gapDraw B hm bs s b q := by
      intro q hpq hql hdraw
      have hsched := (hdrawsB.2 q (by omega)
        (Nat.lt_trans hql hlastBT)).1 hdraw
      have hleRaw := factsB.before_last_le_penultimate q
        hsched.1 hsched.2 (by simpa [lastB] using hql)
      have hle : q ≤ penB := by simpa [penB] using hleRaw
      omega
    have hnoAfterA : ∀ q, lastA < q → q ≤ T - 1 →
        ¬ gapDraw B hm bs s a q := by
      intro q hlq hqT hdraw
      have hqLt : q < T := by omega
      have hsched := (hdrawsA.2 q (by omega) hqLt).1 hdraw
      have hleRaw := factsA.before_final_le_last q
        hsched.1 hsched.2 hqLt
      have hle : q ≤ lastA := by simpa [lastA] using hleRaw
      omega
    have hnoAfterB : ∀ q, lastB < q → q ≤ T - 1 →
        ¬ gapDraw B hm bs s b q := by
      intro q hlq hqT hdraw
      have hqLt : q < T := by omega
      have hsched := (hdrawsB.2 q (by omega) hqLt).1 hdraw
      have hleRaw := factsB.before_final_le_last q
        hsched.1 hsched.2 hqLt
      have hle : q ≤ lastB := by simpa [lastB] using hleRaw
      omega
    unfold CarriesPositions at hprescribed
    have hmemPenA : (penA, a, false) ∈
        fourDrawPositions B hm s a b c gA gB G T := by
      change (penA, a, false) ∈
        [(penA, a, false), (lastA, a, false),
         (penB, b, true), (lastB, b, true)]
      simp
    have hmemLastA : (lastA, a, false) ∈
        fourDrawPositions B hm s a b c gA gB G T := by
      change (lastA, a, false) ∈
        [(penA, a, false), (lastA, a, false),
         (penB, b, true), (lastB, b, true)]
      simp
    have hmemPenB : (penB, b, true) ∈
        fourDrawPositions B hm s a b c gA gB G T := by
      change (penB, b, true) ∈
        [(penA, a, false), (lastA, a, false),
         (penB, b, true), (lastB, b, true)]
      simp
    have hmemLastB : (lastB, b, true) ∈
        fourDrawPositions B hm s a b c gA gB G T := by
      change (lastB, b, true) ∈
        [(penA, a, false), (lastA, a, false),
         (penB, b, true), (lastB, b, true)]
      simp
    obtain ⟨hpenALen, hbitPenA⟩ :=
      hprescribed penA a false hmemPenA
    obtain ⟨hlastALen, hbitLastA⟩ :=
      hprescribed lastA a false hmemLastA
    obtain ⟨hpenBLen, hbitPenB⟩ :=
      hprescribed penB b true hmemPenB
    obtain ⟨hlastBLen, hbitLastB⟩ :=
      hprescribed lastB b true hmemLastB
    have hbitPenAGap :
        (gapRoundBits bs penA
          (Nat.lt_of_lt_of_le hpenAT hbits)) a = false := by
      simpa using hbitPenA
    have hbitLastAGap :
        (gapRoundBits bs lastA
          (Nat.lt_of_lt_of_le hlastAT hbits)) a = false := by
      simpa using hbitLastA
    have hbitPenBGap :
        (gapRoundBits bs penB
          (Nat.lt_of_lt_of_le hpenBT hbits)) b = true := by
      simpa using hbitPenB
    have hbitLastBGap :
        (gapRoundBits bs lastB
          (Nat.lt_of_lt_of_le hlastBT hbits)) b = true := by
      simpa using hbitLastB
    have hrolesA := gap_role_two_draws B hm bs s a b gA T
      (by omega) hb hbits hgapFixedA
      penA lastA (T - 1) hpenAT hlastAT (by omega)
      hpenLastA (by omega) false hbitPenAGap hbitLastAGap
      hdrawPenA hdrawLastA hnoBetweenA hnoAfterA
    have hrolesB := gap_role_two_draws B hm bs s b c gB T
      (by omega) hc hbits hgapFixedB
      penB lastB (T - 1) hpenBT hlastBT (by omega)
      hpenLastB (by omega) true hbitPenBGap hbitLastBGap
      hdrawPenB hdrawLastB hnoBetweenB hnoAfterB
    have hstartAWindow : startA + gA = T := by
      dsimp [startA]
      omega
    have hstartBWindow : startB + gB = T := by
      dsimp [startB]
      omega
    have hpenBeforeStartA : penA + gA ≤ startA := by
      dsimp [startA]
      dsimp [periodA] at hsepA
      omega
    have hpenBeforeStartB : penB + gB ≤ startB := by
      dsimp [startB]
      dsimp [periodB] at hsepB
      omega
    have hevol : ∀ t, t < T →
        gapState B hm bs s (t + 1) =
          logicalRound B hm (suppliedBits bs t)
            (gapState B hm bs s t) := by
      intro t ht
      have hlen : t < bs.length := Nat.lt_of_lt_of_le ht hbits
      rw [gapState_succ B hm bs s t hlen]
      rw [suppliedBits_eq bs t hlen]
    have hgapAForFill :
        suppliedBits bs penA a = false →
        suppliedBits bs lastA a = false →
        (∀ t, t ≤ T →
          NamedLive hm (fun q => gapState B hm bs s q) t a b c) →
        ∀ r, r < gA → ∀ i, i ≤ r →
          (phaseTwoView B hm (suppliedBits bs (startA + r))
            (gapState B hm bs s (startA + r))
            (fillGapPath hm a i)).role = false := by
      intro _hpen _hlast _hlive r hr i hir
      have htT : startA + r < T := by
        rw [← hstartAWindow]
        omega
      have hlow : penA + i ≤ startA + r := by
        omega
      have hupp : startA + r ≤ T - 1 := by omega
      have hh := hrolesA i (by omega) (startA + r) hlow hupp
      change
        (afterPhaseTwo B hm (suppliedBits bs (startA + r))
          (gapState B hm bs s (startA + r))
          (gapSite hm a i)).role = false
      rw [suppliedBits_eq bs (startA + r)
        (Nat.lt_of_lt_of_le htT hbits)]
      exact hh
    have hgapBForFill :
        suppliedBits bs penB b = true →
        suppliedBits bs lastB b = true →
        (∀ t, t ≤ T →
          NamedLive hm (fun q => gapState B hm bs s q) t a b c) →
        ∀ r, r < gB → ∀ i, i < gB →
          (phaseTwoView B hm (suppliedBits bs (startB + r))
            (gapState B hm bs s (startB + r))
            (fillGapPath hm b i)).role = true := by
      intro _hpen _hlast _hlive r hr i hi
      have htT : startB + r < T := by
        rw [← hstartBWindow]
        omega
      have hlow : penB + i ≤ startB + r := by
        omega
      have hupp : startB + r ≤ T - 1 := by omega
      have hh := hrolesB i hi (startB + r) hlow hupp
      change
        (afterPhaseTwo B hm (suppliedBits bs (startB + r))
          (gapState B hm bs s (startB + r))
          (gapSite hm b i)).role = true
      rw [suppliedBits_eq bs (startB + r)
        (Nat.lt_of_lt_of_le htT hbits)]
      exact hh
    have hbitPenATotal : suppliedBits bs penA a = false := by
      rw [suppliedBits_eq bs penA hpenALen]
      exact hbitPenA
    have hbitLastATotal : suppliedBits bs lastA a = false := by
      rw [suppliedBits_eq bs lastA hlastALen]
      exact hbitLastA
    have hbitPenBTotal : suppliedBits bs penB b = true := by
      rw [suppliedBits_eq bs penB hpenBLen]
      exact hbitPenB
    have hbitLastBTotal : suppliedBits bs lastB b = true := by
      rw [suppliedBits_eq bs lastB hlastBLen]
      exact hbitLastB
    exact four_bit_loss B G T hm
      (fun q => gapState B hm bs s q) (suppliedBits bs)
      a b c (fillGapPath hm a) (fillGapPath hm b) gA gB
      startA startB T penA lastA penB lastB
      hwindow hgA hgB hgAG hgBG hgapSum hmB
      (fillGapPath_is_path hm a gA)
      (fillGapPath_is_path hm b gB)
      (by simp [fillGapPath])
      (by simpa [fillGapPath] using hb.symm)
      (by simp [fillGapPath])
      (by simpa [fillGapPath] using hc.symm)
      hevol hboundedAll hfixed hstartAWindow hstartBWindow
      (Nat.le_refl T)
      ⟨hpenLastA, hlastAT⟩ ⟨hpenLastB, hlastBT⟩
      hbitPenATotal hbitLastATotal hbitPenBTotal hbitLastBTotal
      hgapAForFill hgapBForFill

end L4.Height

