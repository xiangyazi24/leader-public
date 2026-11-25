import Leader.L4.Height.Core
import Leader.L4.Height.Model

namespace L4.Height

open L4.Compiler.Native

set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

/-- The site at clockwise offset `k` from `a`. -/
def gapSite {m : Nat} (hm : 0 < m) (a : Fin m) (k : Nat) : Fin m :=
  ⟨(a.val + k) % m, Nat.mod_lt _ hm⟩

@[simp] theorem gapSite_zero {m : Nat} (hm : 0 < m) (a : Fin m) :
    gapSite hm a 0 = a := by
  apply Fin.ext
  simp [gapSite, Nat.mod_eq_of_lt a.isLt]

@[simp] theorem gapSite_period {m : Nat} (hm : 0 < m) (a : Fin m) :
    gapSite hm a m = a := by
  apply Fin.ext
  simp [gapSite, Nat.mod_eq_of_lt a.isLt]

@[simp] theorem gapSite_succ {m : Nat} (hm : 0 < m)
    (a : Fin m) (k : Nat) :
    gapSite hm a (k + 1) = right hm (gapSite hm a k) := by
  apply Fin.ext
  change (a.val + (k + 1)) % m = ((a.val + k) % m + 1) % m
  rw [Nat.mod_add_mod, ← Nat.add_assoc]

@[simp] theorem left_gapSite_succ {m : Nat} (hm : 0 < m)
    (a : Fin m) (k : Nat) :
    left hm (gapSite hm a (k + 1)) = gapSite hm a k := by
  rw [gapSite_succ, left_right]

/-- Cyclic offsets below `m` are injective. -/
theorem gapSite_inj_lt {m : Nat} (hm : 0 < m) (a : Fin m)
    {p q : Nat} (hp : p < m) (hq : q < m)
    (h : gapSite hm a p = gapSite hm a q) : p = q := by
  have h1 := congrArg Fin.val h
  simp only [gapSite] at h1
  have ha := a.isLt
  rcases Nat.lt_or_ge (a.val + p) m with hpa | hpa <;>
    rcases Nat.lt_or_ge (a.val + q) m with hqa | hqa
  · rw [Nat.mod_eq_of_lt hpa, Nat.mod_eq_of_lt hqa] at h1
    omega
  · rw [Nat.mod_eq_of_lt hpa, Nat.mod_eq_sub_mod hqa,
      Nat.mod_eq_of_lt (by omega)] at h1
    omega
  · rw [Nat.mod_eq_sub_mod hpa, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt hqa] at h1
    omega
  · rw [Nat.mod_eq_sub_mod hpa, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_sub_mod hqa, Nat.mod_eq_of_lt (by omega)] at h1
    omega

theorem gapSite_ne_start {m : Nat} (hm : 0 < m) (a : Fin m)
    {k : Nat} (hk0 : 0 < k) (hkm : k < m) :
    gapSite hm a k ≠ a := by
  intro h
  have h' : gapSite hm a k = gapSite hm a 0 := by
    simpa using h
  have hk := gapSite_inj_lt hm a hkm hm h'
  omega

theorem gapSite_internal_ne_end {m : Nat} (hm : 0 < m)
    (a : Fin m) {g k : Nat}
    (hg : g ≤ m) (hk0 : 0 < k) (hkg : k < g) :
    gapSite hm a k ≠ gapSite hm a g := by
  intro h
  by_cases hgm : g = m
  · rw [hgm, gapSite_period] at h
    exact gapSite_ne_start hm a hk0 (by omega) h
  · have hglt : g < m := by omega
    have heq := gapSite_inj_lt hm a (by omega) hglt h
    omega

/-- The site `j+1` steps counterclockwise from `b`. -/
def gapBack {m : Nat} (hm : 0 < m) (b : Fin m) : Nat → Fin m
  | 0 => left hm b
  | j + 1 => left hm (gapBack hm b j)

theorem gapBack_gapSite {m : Nat} (hm : 0 < m) (a : Fin m)
    (g j : Nat) (hg : 1 ≤ g) (hj : j < g) :
    gapBack hm (gapSite hm a g) j = gapSite hm a (g - 1 - j) := by
  induction j with
  | zero =>
      have he : g = (g - 1) + 1 := by omega
      rw [he]
      simp [gapBack]
  | succ j ih =>
      have hj' : j < g := by omega
      rw [gapBack, ih hj']
      have he : g - 1 - j = (g - 2 - j) + 1 := by omega
      rw [he, left_gapSite_succ]
      congr 1
      omega

/-- Opening state of round `r`. -/
def gapState {m : Nat} (B : Nat) (hm : 0 < m)
    (bs : List (Fin m → Bool)) (s : Fin m → Snapshot) (r : Nat) :
    Fin m → Snapshot :=
  runRounds B hm (bs.take r) s

/-- The fixed-anchor condition from the question. -/
def gapFixed {m : Nat} (B : Nat) (hm : 0 < m)
    (bs : List (Fin m → Bool)) (s : Fin m → Snapshot)
    (a b : Fin m) (g T : Nat) : Prop :=
  ∀ r, r < T →
    ∀ k, k ≤ g →
      (IsAnchor hm (gapState B hm bs s r) (gapSite hm a k) ↔
        (gapSite hm a k = a ∨ gapSite hm a k = b))

/-- The actual scheduler letter of a supplied round. -/
def gapRoundBits {m : Nat} (bs : List (Fin m → Bool))
    (r : Nat) (hr : r < bs.length) : Fin m → Bool :=
  bs[r]

/-- Execute two word pieces in sequence. -/
theorem runRounds_append_gap {m : Nat} (B : Nat) (hm : 0 < m)
    (u v : List (Fin m → Bool)) (s : Fin m → Snapshot) :
    runRounds B hm (u ++ v) s =
      runRounds B hm v (runRounds B hm u s) := by
  induction u generalizing s with
  | nil => rfl
  | cons bits u ih =>
      simp only [List.cons_append, runRounds_cons]
      exact ih (logicalRound B hm bits s)

/-- If round `r` is present in `bs`, opening state `r+1` is one actual
logical round after opening state `r`. -/
theorem gapState_succ {m : Nat} (B : Nat) (hm : 0 < m)
    (bs : List (Fin m → Bool)) (s : Fin m → Snapshot)
    (r : Nat) (hr : r < bs.length) :
    gapState B hm bs s (r + 1) =
      logicalRound B hm (gapRoundBits bs r hr)
        (gapState B hm bs s r) := by
  unfold gapState gapRoundBits
  rw [List.take_succ_eq_append_getElem hr]
  rw [runRounds_append_gap]
  rfl

/-- Round `r` is a draw at `a`. Phase 0 ignores the bit vector. -/
def gapDraw {m : Nat} (B : Nat) (hm : 0 < m)
    (bs : List (Fin m → Bool)) (s : Fin m → Snapshot)
    (a : Fin m) (r : Nat) : Prop :=
  let s0 := phaseStep B 0 hm (fun _ => false) (gapState B hm bs s r)
  (s0 a).anchor = true ∧ (s0 a).z = 0

/-- State immediately after phase 2 of one logical round. -/
def afterPhaseTwo {m : Nat} (B : Nat) (hm : 0 < m)
    (bits : Fin m → Bool) (s : Fin m → Snapshot) : Fin m → Snapshot :=
  let s0 := phaseStep B 0 hm bits s
  let s1 := phaseStep B 1 hm bits s0
  phaseStep B 2 hm bits s1

/-! Exact local equations from the accepted phase semantics. -/

theorem phaseOne_distance {m : Nat} (B : Nat) (hm : 0 < m)
    (bits : Fin m → Bool) (s : Fin m → Snapshot) (i : Fin m) :
    let s0 := phaseStep B 0 hm bits s
    (phaseStep B 1 hm bits s0 i).d =
      if (s0 (right hm i)).anchor then 1
      else min (B - 1) ((s0 (right hm i)).d + 1) := by
  rfl

theorem phaseOne_countdown {m : Nat} (B : Nat) (hm : 0 < m)
    (bits : Fin m → Bool) (s : Fin m → Snapshot) (i : Fin m) :
    let s0 := phaseStep B 0 hm bits s
    (phaseStep B 1 hm bits s0 i).z =
      if !(s0 i).anchor then 0
      else if (s0 i).z = 0 then 8 * (s0 i).d + 8
      else min (8 * (s0 i).d + 8) ((s0 i).z - 1) := by
  rfl

theorem phaseOne_home {m : Nat} (B : Nat) (hm : 0 < m)
    (bits : Fin m → Bool) (s : Fin m → Snapshot) (i : Fin m) :
    let s0 := phaseStep B 0 hm bits s
    (phaseStep B 1 hm bits s0 i).home =
      ((s0 i).anchor &&
        (if (s0 i).z = 0 then bits i else (s0 i).home)) := by
  rfl

theorem phaseTwo_role {m : Nat} (B : Nat) (hm : 0 < m)
    (bits : Fin m → Bool) (s : Fin m → Snapshot) (i : Fin m) :
    let s0 := phaseStep B 0 hm bits s
    let s1 := phaseStep B 1 hm bits s0
    (phaseStep B 2 hm bits s1 i).role =
      if (s1 i).anchor then (s1 i).home
      else (s1 (left hm i)).role := by
  rfl

theorem logicalRound_distance_of_right_anchor {m : Nat}
    (B : Nat) (hm : 0 < m) (bits : Fin m → Bool)
    (s : Fin m → Snapshot) (i : Fin m)
    (ha : IsAnchor hm s (right hm i)) :
    (logicalRound B hm bits s i).d = 1 := by
  unfold IsAnchor at ha
  have ha' : (s (right hm i)).x ≤ (s i).x := by
    simpa only [left_right] using ha
  simp [logicalRound, phaseStep, phaseUpdate, ha']

theorem logicalRound_distance_of_right_nonanchor {m : Nat}
    (B : Nat) (hm : 0 < m) (bits : Fin m → Bool)
    (s : Fin m → Snapshot) (i : Fin m)
    (ha : ¬ IsAnchor hm s (right hm i)) :
    (logicalRound B hm bits s i).d =
      min (B - 1) ((s (right hm i)).d + 1) := by
  unfold IsAnchor at ha
  have ha' : ¬ (s (right hm i)).x ≤ (s i).x := by
    simpa only [left_right] using ha
  simp [logicalRound, phaseStep, phaseUpdate, ha']

theorem logicalRound_countdown_of_anchor {m : Nat}
    (B : Nat) (hm : 0 < m) (bits : Fin m → Bool)
    (s : Fin m → Snapshot) (i : Fin m)
    (ha : IsAnchor hm s i) :
    (logicalRound B hm bits s i).z =
      if (s i).z = 0 then 8 * (s i).d + 8
      else min (8 * (s i).d + 8) ((s i).z - 1) := by
  unfold IsAnchor at ha
  simp [logicalRound, phaseStep, phaseUpdate, ha]

theorem logicalRound_home_of_anchor {m : Nat}
    (B : Nat) (hm : 0 < m) (bits : Fin m → Bool)
    (s : Fin m → Snapshot) (i : Fin m)
    (ha : IsAnchor hm s i) :
    (logicalRound B hm bits s i).home =
      if (s i).z = 0 then bits i else (s i).home := by
  unfold IsAnchor at ha
  simp [logicalRound, phaseStep, phaseUpdate, ha]

theorem afterPhaseTwo_role_of_anchor {m : Nat}
    (B : Nat) (hm : 0 < m) (bits : Fin m → Bool)
    (s : Fin m → Snapshot) (i : Fin m)
    (ha : IsAnchor hm s i) :
    (afterPhaseTwo B hm bits s i).role =
      if (s i).z = 0 then bits i else (s i).home := by
  unfold afterPhaseTwo IsAnchor at *
  simp [phaseStep, phaseUpdate, ha]

theorem afterPhaseTwo_role_of_nonanchor {m : Nat}
    (B : Nat) (hm : 0 < m) (bits : Fin m → Bool)
    (s : Fin m → Snapshot) (i : Fin m)
    (ha : ¬ IsAnchor hm s i) :
    (afterPhaseTwo B hm bits s i).role = (s (left hm i)).role := by
  unfold afterPhaseTwo IsAnchor at *
  simp [phaseStep, phaseUpdate, ha]

theorem logicalRound_role_eq_afterPhaseTwo {m : Nat}
    (B : Nat) (hm : 0 < m) (bits : Fin m → Bool)
    (s : Fin m → Snapshot) (i : Fin m) :
    (logicalRound B hm bits s i).role =
      (afterPhaseTwo B hm bits s i).role := by
  simp [logicalRound, afterPhaseTwo, phaseStep, phaseUpdate]

theorem logicalRound_home_eq_afterPhaseTwo_role_of_anchor {m : Nat}
    (B : Nat) (hm : 0 < m) (bits : Fin m → Bool)
    (s : Fin m → Snapshot) (i : Fin m)
    (ha : IsAnchor hm s i) :
    (logicalRound B hm bits s i).home =
      (afterPhaseTwo B hm bits s i).role := by
  rw [logicalRound_home_of_anchor B hm bits s i ha]
  rw [afterPhaseTwo_role_of_anchor B hm bits s i ha]

/-- At an anchor with old countdown zero, phase 2 exposes the current bit. -/
theorem phaseTwo_anchor_draw_role {m : Nat} (B : Nat) (hm : 0 < m)
    (bits : Fin m → Bool) (s : Fin m → Snapshot) (a : Fin m)
    (ha : IsAnchor hm s a) (hz : (s a).z = 0) :
    (afterPhaseTwo B hm bits s a).role = bits a := by
  rw [afterPhaseTwo_role_of_anchor B hm bits s a ha, if_pos hz]

/-- A draw on a terminal round can overwrite an earlier role. This is why
`gap_role` excludes draws through, not merely strictly before, `r'`. -/
theorem terminal_draw_overwrites_role {m : Nat} (B : Nat) (hm : 0 < m)
    (bits : Fin m → Bool) (s : Fin m → Snapshot) (a : Fin m) (v : Bool)
    (ha : IsAnchor hm s a) (hz : (s a).z = 0)
    (hne : bits a ≠ v) :
    (afterPhaseTwo B hm bits s a).role ≠ v := by
  intro hrole
  apply hne
  exact (phaseTwo_anchor_draw_role B hm bits s a ha hz).symm.trans hrole

/-! Fixed-gap endpoint facts. -/

theorem gapFixed_start {m : Nat} (B : Nat) (hm : 0 < m)
    (bs : List (Fin m → Bool)) (s : Fin m → Snapshot)
    (a b : Fin m) (g T r : Nat)
    (hf : gapFixed B hm bs s a b g T) (hr : r < T) :
    IsAnchor hm (gapState B hm bs s r) a := by
  have h := (hf r hr 0 (Nat.zero_le g)).2
    (Or.inl (gapSite_zero hm a))
  simpa using h

theorem gapFixed_end {m : Nat} (B : Nat) (hm : 0 < m)
    (bs : List (Fin m → Bool)) (s : Fin m → Snapshot)
    (a b : Fin m) (g T r : Nat)
    (hb : b = gapSite hm a g)
    (hf : gapFixed B hm bs s a b g T) (hr : r < T) :
    IsAnchor hm (gapState B hm bs s r) (gapSite hm a g) := by
  exact (hf r hr g (Nat.le_refl g)).2 (Or.inr hb.symm)

theorem gapFixed_internal {m : Nat} (B : Nat) (hm : 0 < m)
    (bs : List (Fin m → Bool)) (s : Fin m → Snapshot)
    (a b : Fin m) (g T r k : Nat)
    (hb : b = gapSite hm a g) (hgm : g ≤ m)
    (hf : gapFixed B hm bs s a b g T) (hr : r < T)
    (hk0 : 0 < k) (hkg : k < g) :
    ¬ IsAnchor hm (gapState B hm bs s r) (gapSite hm a k) := by
  intro ha
  have hend := (hf r hr k (by omega)).1 ha
  rcases hend with hstart | hfinish
  · exact gapSite_ne_start hm a hk0 (by omega) hstart
  · apply gapSite_internal_ne_end hm a hgm hk0 hkg
    rw [← hb]
    exact hfinish

/-! A bit-independent shadow clock for the distance and countdown fields. -/

def gapInitialD {m : Nat} (hm : 0 < m)
    (s : Fin m → Snapshot) (a : Fin m) : Nat → Nat :=
  fun k => (s (gapSite hm a k)).d

def gapClockD (B g : Nat) (d0 : Nat → Nat) : Nat → Nat → Nat
  | 0, k => d0 k
  | r + 1, k =>
      if k + 1 = g then 1
      else min (B - 1) (gapClockD B g d0 r (k + 1) + 1)

def gapClockZ (B g : Nat) (d0 : Nat → Nat) (z0 : Nat) : Nat → Nat
  | 0 => z0
  | r + 1 =>
      let d := gapClockD B g d0 r 0
      let z := gapClockZ B g d0 z0 r
      if z = 0 then 8 * d + 8
      else min (8 * d + 8) (z - 1)

/-- Actual distance/countdown fields agree with the shadow clock while the
gap is fixed and all requested rounds are present. -/
theorem gap_clock_agree {m : Nat} (B : Nat) (hm : 0 < m)
    (bs : List (Fin m → Bool)) (s : Fin m → Snapshot)
    (a b : Fin m) (g T : Nat)
    (hg : 1 ≤ g) (hgm : g ≤ m)
    (hb : b = gapSite hm a g)
    (hbits : T ≤ bs.length)
    (hf : gapFixed B hm bs s a b g T) :
    ∀ r, r ≤ T →
      (∀ k, k < g →
        (gapState B hm bs s r (gapSite hm a k)).d =
          gapClockD B g (gapInitialD hm s a) r k) ∧
      (gapState B hm bs s r a).z =
        gapClockZ B g (gapInitialD hm s a) (s a).z r := by
  intro r
  induction r with
  | zero =>
      intro hr
      constructor
      · intro k hk
        simp [gapState, gapClockD, gapInitialD, runRounds]
      · simp [gapState, gapClockZ, runRounds]
  | succ r ih =>
      intro hr
      have hrT : r < T := by omega
      have hrlen : r < bs.length := Nat.lt_of_lt_of_le hrT hbits
      have ihp := ih (by omega)
      rw [gapState_succ B hm bs s r hrlen]
      constructor
      · intro k hk
        by_cases hend : k + 1 = g
        · have ha := gapFixed_end B hm bs s a b g T r hb hf hrT
          have har :
              IsAnchor hm (gapState B hm bs s r)
                (right hm (gapSite hm a k)) := by
            have he : k + 1 = g := hend
            simpa only [← he, gapSite_succ] using ha
          rw [logicalRound_distance_of_right_anchor
            B hm (gapRoundBits bs r hrlen)
            (gapState B hm bs s r) (gapSite hm a k) har]
          simp [gapClockD, hend]
        · have hk1 : k + 1 < g := by omega
          have hna := gapFixed_internal B hm bs s a b g T r (k + 1)
            hb hgm hf hrT (by omega) hk1
          have hnar :
              ¬ IsAnchor hm (gapState B hm bs s r)
                (right hm (gapSite hm a k)) := by
            simpa only [← gapSite_succ] using hna
          rw [logicalRound_distance_of_right_nonanchor
            B hm (gapRoundBits bs r hrlen)
            (gapState B hm bs s r) (gapSite hm a k) hnar]
          rw [← gapSite_succ hm a k]
          rw [ihp.1 (k + 1) hk1]
          simp [gapClockD, hend]
      · have ha := gapFixed_start B hm bs s a b g T r hf hrT
        rw [logicalRound_countdown_of_anchor
          B hm (gapRoundBits bs r hrlen)
          (gapState B hm bs s r) a ha]
        have hd0 := ihp.1 0 (by omega)
        simp only [gapSite_zero] at hd0
        rw [hd0, ihp.2]
        rfl

/-- The shadow distance wave has the exact claimed values. -/
theorem gapClockD_distance (B m g : Nat)
    (hB : m < B) (hg : 1 ≤ g) (hgm : g ≤ m)
    (d0 : Nat → Nat) :
    ∀ r j, j < min r g →
      gapClockD B g d0 r (g - 1 - j) = j + 1 := by
  intro r
  induction r with
  | zero =>
      intro j hj
      have : j < 0 := Nat.lt_of_lt_of_le hj (Nat.min_le_left 0 g)
      omega
  | succ r ih =>
      intro j hj
      have hjr : j < r + 1 :=
        Nat.lt_of_lt_of_le hj (Nat.min_le_left (r + 1) g)
      have hjg : j < g :=
        Nat.lt_of_lt_of_le hj (Nat.min_le_right (r + 1) g)
      cases j with
      | zero =>
          have he : g - 1 + 1 = g := by omega
          simp [gapClockD, he]
      | succ j =>
          have hprev : j < min r g :=
            Nat.lt_min.mpr ⟨by omega, by omega⟩
          have hidx : g - 1 - (j + 1) + 1 = g - 1 - j := by omega
          have hne : g - 1 - (j + 1) + 1 ≠ g := by omega
          have hclip : j + 2 ≤ B - 1 := by omega
          simp only [gapClockD]
          rw [if_neg hne, hidx, ih j hprev, Nat.min_eq_right hclip]

/-- (1) Exact distance wave on the literal sites `b-1-j`. -/
theorem gap_distance {m : Nat} (B : Nat) (hm : 0 < m)
    (hB : m < B) (bs : List (Fin m → Bool))
    (s : Fin m → Snapshot) (_hs : Bounded B s)
    (a b : Fin m) (g T : Nat)
    (hg : 1 ≤ g) (hgm : g ≤ m)
    (hb : b = gapSite hm a g)
    (hbits : T ≤ bs.length)
    (hf : gapFixed B hm bs s a b g T) :
    ∀ r, r ≤ T → ∀ j, j < min r g →
      (gapState B hm bs s r (gapBack hm b j)).d = j + 1 := by
  intro r hr j hj
  have hagree := gap_clock_agree B hm bs s a b g T
    hg hgm hb hbits hf r hr
  have hjg : j < g :=
    Nat.lt_of_lt_of_le hj (Nat.min_le_right r g)
  have hk : g - 1 - j < g := by omega
  calc
    (gapState B hm bs s r (gapBack hm b j)).d =
        (gapState B hm bs s r (gapSite hm a (g - 1 - j))).d := by
          rw [hb, gapBack_gapSite hm a g j hg hjg]
    _ = gapClockD B g (gapInitialD hm s a) r (g - 1 - j) :=
      hagree.1 (g - 1 - j) hk
    _ = j + 1 :=
      gapClockD_distance B m g hB hg hgm
        (gapInitialD hm s a) r j hj

/-- In particular the home distance is `g` from opening round `g` on. -/
theorem gap_distance_home {m : Nat} (B : Nat) (hm : 0 < m)
    (hB : m < B) (bs : List (Fin m → Bool))
    (s : Fin m → Snapshot) (hs : Bounded B s)
    (a b : Fin m) (g T : Nat)
    (hg : 1 ≤ g) (hgm : g ≤ m)
    (hb : b = gapSite hm a g)
    (hbits : T ≤ bs.length)
    (hf : gapFixed B hm bs s a b g T)
    (r : Nat) (hgr : g ≤ r) (hrT : r ≤ T) :
    (gapState B hm bs s r a).d = g := by
  have hj : g - 1 < min r g := Nat.lt_min.mpr ⟨by omega, by omega⟩
  have h := gap_distance B hm hB bs s hs a b g T
    hg hgm hb hbits hf r hrT (g - 1) hj
  have hsite : gapBack hm b (g - 1) = a := by
    rw [hb, gapBack_gapSite hm a g (g - 1) hg (by omega)]
    simp
  rw [hsite] at h
  omega

/-- (2) Once the correct distance has been used, countdown is clipped to
`8*g+8`. -/
theorem gap_countdown {m : Nat} (B : Nat) (hm : 0 < m)
    (hB : m < B) (bs : List (Fin m → Bool))
    (s : Fin m → Snapshot) (hs : Bounded B s)
    (a b : Fin m) (g T : Nat)
    (hg : 1 ≤ g) (hgm : g ≤ m)
    (hb : b = gapSite hm a g)
    (hbits : T ≤ bs.length)
    (hf : gapFixed B hm bs s a b g T) :
    ∀ r, g + 1 ≤ r → r ≤ T →
      (gapState B hm bs s r a).z ≤ 8 * g + 8 := by
  intro r hgr hrT
  let q := r - 1
  have hqT : q < T := by dsimp [q]; omega
  have hqLe : q ≤ T := by omega
  have hqlen : q < bs.length := Nat.lt_of_lt_of_le hqT hbits
  have hqr : q + 1 = r := by dsimp [q]; omega
  have hd := gap_distance_home B hm hB bs s hs a b g T
    hg hgm hb hbits hf q (by dsimp [q]; omega) hqLe
  have ha := gapFixed_start B hm bs s a b g T q hf hqT
  rw [← hqr, gapState_succ B hm bs s q hqlen]
  rw [logicalRound_countdown_of_anchor
    B hm (gapRoundBits bs q hqlen) (gapState B hm bs s q) a ha]
  rw [hd]
  by_cases hz : (gapState B hm bs s q a).z = 0
  · rw [if_pos hz]
    exact Nat.le_refl _
  · rw [if_neg hz]
    exact Nat.min_le_left _ _

/-- On a fixed gap, draw is exactly zero countdown. -/
theorem gapDraw_iff_z_zero {m : Nat} (B : Nat) (hm : 0 < m)
    (bs : List (Fin m → Bool)) (s : Fin m → Snapshot)
    (a b : Fin m) (g T r : Nat)
    (hf : gapFixed B hm bs s a b g T) (hr : r < T) :
    gapDraw B hm bs s a r ↔ (gapState B hm bs s r a).z = 0 := by
  have ha := gapFixed_start B hm bs s a b g T r hf hr
  unfold gapDraw
  unfold IsAnchor at ha
  simp [phaseStep, phaseUpdate, ha]

/-! The exact scalar countdown orbit. -/

def gapTick (R z : Nat) : Nat := if z = 0 then R else z - 1

def gapIter (R z : Nat) : Nat → Nat
  | 0 => z
  | t + 1 => gapTick R (gapIter R z t)

theorem gapIter_add (R z p q : Nat) :
    gapIter R z (p + q) = gapIter R (gapIter R z p) q := by
  induction q with
  | zero => simp [gapIter]
  | succ q ih =>
      rw [Nat.add_succ]
      simp only [gapIter, ih]

theorem gapIter_before (R z t : Nat) (ht : t ≤ z) :
    gapIter R z t = z - t := by
  induction t with
  | zero => simp [gapIter]
  | succ t ih =>
      have ht' : t ≤ z := by omega
      have hpos : 0 < z - t := by omega
      simp only [gapIter, ih ht']
      unfold gapTick
      rw [if_neg (Nat.ne_of_gt hpos)]
      omega

theorem gapIter_to_zero (R z : Nat) : gapIter R z z = 0 := by
  simpa using gapIter_before R z z (Nat.le_refl z)

theorem gapIter_full_period (R : Nat) :
    gapIter R 0 (R + 1) = 0 := by
  rw [Nat.add_comm R 1, gapIter_add]
  have hone : gapIter R 0 1 = R := by
    simp [gapIter, gapTick]
  rw [hone]
  exact gapIter_to_zero R R

theorem gapIter_zero_period (R q : Nat) :
    gapIter R 0 ((R + 1) + q) = gapIter R 0 q := by
  rw [gapIter_add, gapIter_full_period]

theorem gapIter_zero_small (R t : Nat)
    (ht0 : 0 < t) (ht : t < R + 1) :
    gapIter R 0 t = R + 1 - t := by
  have he : t = 1 + (t - 1) := by omega
  rw [he, gapIter_add]
  have hone : gapIter R 0 1 = R := by simp [gapIter, gapTick]
  rw [hone]
  have hb := gapIter_before R R (t - 1) (by omega)
  rw [hb]
  omega

theorem gapIter_zero_iff_mod (R t : Nat) :
    gapIter R 0 t = 0 ↔ t % (R + 1) = 0 := by
  induction t using Nat.strongRecOn with
  | ind t ih =>
      by_cases hlt : t < R + 1
      · by_cases hz : t = 0
        · subst t
          simp [gapIter]
        · have ht0 : 0 < t := Nat.pos_of_ne_zero hz
          rw [gapIter_zero_small R t ht0 hlt]
          rw [Nat.mod_eq_of_lt hlt]
          omega
      · have hge : R + 1 ≤ t := Nat.le_of_not_gt hlt
        let q := t - (R + 1)
        have hq : q < t := by
          dsimp [q]
          omega
        have he : t = (R + 1) + q := by
          dsimp [q]
          omega
        rw [he, gapIter_zero_period]
        have hm : ((R + 1) + q) % (R + 1) = q % (R + 1) := by
          rw [Nat.add_mod]
          simp
        rw [hm]
        exact ih q hq

theorem gapIter_eq_zero_iff (R z t : Nat) :
    gapIter R z t = 0 ↔
      z ≤ t ∧ (t - z) % (R + 1) = 0 := by
  by_cases ht : t < z
  · have hv := gapIter_before R z t (Nat.le_of_lt ht)
    rw [hv]
    constructor
    · intro h
      omega
    · intro h
      omega
  · have hzt : z ≤ t := Nat.le_of_not_gt ht
    have hsplit : gapIter R z t = gapIter R 0 (t - z) := by
      calc
        gapIter R z t = gapIter R z (z + (t - z)) := by
          congr 2
          omega
        _ = gapIter R (gapIter R z z) (t - z) :=
          gapIter_add R z z (t - z)
        _ = gapIter R 0 (t - z) := by rw [gapIter_to_zero]
    rw [hsplit, gapIter_zero_iff_mod]
    simp [hzt]

/-- Starting at opening `g+1`, the real countdown is the scalar orbit. -/
theorem gap_countdown_iter {m : Nat} (B : Nat) (hm : 0 < m)
    (hB : m < B) (bs : List (Fin m → Bool))
    (s : Fin m → Snapshot) (hs : Bounded B s)
    (a b : Fin m) (g T : Nat)
    (hg : 1 ≤ g) (hgm : g ≤ m)
    (hb : b = gapSite hm a g)
    (hbits : T ≤ bs.length)
    (hf : gapFixed B hm bs s a b g T) :
    ∀ t, g + 1 + t ≤ T →
      (gapState B hm bs s (g + 1 + t) a).z =
        gapIter (8 * g + 8)
          (gapClockZ B g (gapInitialD hm s a) (s a).z (g + 1)) t := by
  intro t
  induction t with
  | zero =>
      intro ht
      have ha := gap_clock_agree B hm bs s a b g T
        hg hgm hb hbits hf (g + 1) (by omega)
      simpa only [gapIter] using ha.2
  | succ t ih =>
      intro ht
      have hprevLe : g + 1 + t ≤ T := by omega
      have hprevT : g + 1 + t < T := by omega
      have hprevLen : g + 1 + t < bs.length :=
        Nat.lt_of_lt_of_le hprevT hbits
      have hprev := ih hprevLe
      have ha := gapFixed_start B hm bs s a b g T
        (g + 1 + t) hf hprevT
      have hd := gap_distance_home B hm hB bs s hs a b g T
        hg hgm hb hbits hf (g + 1 + t) (by omega) hprevLe
      have hzbound := gap_countdown B hm hB bs s hs a b g T
        hg hgm hb hbits hf (g + 1 + t) (by omega) hprevLe
      rw [show g + 1 + (t + 1) = (g + 1 + t) + 1 by omega]
      rw [gapState_succ B hm bs s (g + 1 + t) hprevLen]
      rw [logicalRound_countdown_of_anchor
        B hm (gapRoundBits bs (g + 1 + t) hprevLen)
        (gapState B hm bs s (g + 1 + t)) a ha]
      rw [hd, hprev]
      by_cases hz :
          gapIter (8 * g + 8)
            (gapClockZ B g (gapInitialD hm s a) (s a).z (g + 1)) t = 0
      · simp [gapIter, gapTick, hz]
      · have hle :
            gapIter (8 * g + 8)
              (gapClockZ B g (gapInitialD hm s a) (s a).z (g + 1)) t - 1 ≤
                8 * g + 8 := by
          rw [hprev] at hzbound
          omega
        rw [Nat.min_eq_right hle]
        simp [gapIter, gapTick, hz]

/-- The first scheduled draw, expressed solely through the initial snapshot
and the fixed gap geometry. The `min` makes the definition bounded even
when the requested comparison window ends before round `g+1`. -/
def gapFirstDrawRound {m : Nat} (B : Nat) (hm : 0 < m)
    (s : Fin m → Snapshot) (a : Fin m) (g : Nat) : Nat :=
  g + 1 + min (8 * g + 8)
    (gapClockZ B g (gapInitialD hm s a) (s a).z (g + 1))

/-- (3) Draw rounds form one residue class of exact period `8*g+9`.
The witness is definitionally independent of `bs`. -/
theorem gap_draws {m : Nat} (B : Nat) (hm : 0 < m)
    (hB : m < B) (bs : List (Fin m → Bool))
    (s : Fin m → Snapshot) (hs : Bounded B s)
    (a b : Fin m) (g T : Nat)
    (hg : 1 ≤ g) (hgm : g ≤ m)
    (hb : b = gapSite hm a g)
    (hbits : T ≤ bs.length)
    (hf : gapFixed B hm bs s a b g T) :
    gapFirstDrawRound B hm s a g ≤ g + 1 + (8 * g + 9) ∧
      ∀ r, g + 1 ≤ r → r < T →
        (gapDraw B hm bs s a r ↔
          gapFirstDrawRound B hm s a g ≤ r ∧
            (r - gapFirstDrawRound B hm s a g) % (8 * g + 9) = 0) := by
  unfold gapFirstDrawRound
  let z0 := gapClockZ B g (gapInitialD hm s a) (s a).z (g + 1)
  by_cases hqT : g + 1 ≤ T
  · have hagree := gap_clock_agree B hm bs s a b g T
      hg hgm hb hbits hf (g + 1) hqT
    have hzEq : (gapState B hm bs s (g + 1) a).z = z0 := by
      simpa [z0] using hagree.2
    have hzBound := gap_countdown B hm hB bs s hs a b g T
      hg hgm hb hbits hf (g + 1) (by omega) hqT
    rw [hzEq] at hzBound
    have hmin : min (8 * g + 8) z0 = z0 :=
      Nat.min_eq_right hzBound
    rw [hmin]
    constructor
    · omega
    · intro r hqr hrT
      have ht : g + 1 + (r - (g + 1)) ≤ T := by omega
      have hiter := gap_countdown_iter B hm hB bs s hs a b g T
        hg hgm hb hbits hf (r - (g + 1)) ht
      have he : g + 1 + (r - (g + 1)) = r := by omega
      rw [he] at hiter
      have hiter' :
          (gapState B hm bs s r a).z =
            gapIter (8 * g + 8) z0 (r - (g + 1)) := by
        simpa [z0] using hiter
      have hdraw := gapDraw_iff_z_zero B hm bs s a b g T r hf hrT
      constructor
      · intro hd
        have hz := hdraw.mp hd
        rw [hiter'] at hz
        have hc := (gapIter_eq_zero_iff
          (8 * g + 8) z0 (r - (g + 1))).mp hz
        constructor
        · omega
        · have hsub :
              (r - (g + 1)) - z0 = r - (g + 1 + z0) := by omega
          have hp : 8 * g + 8 + 1 = 8 * g + 9 := by omega
          simpa [hsub, hp] using hc.2
      · intro hc
        apply hdraw.mpr
        rw [hiter']
        apply (gapIter_eq_zero_iff
          (8 * g + 8) z0 (r - (g + 1))).mpr
        constructor
        · omega
        · have hsub :
              (r - (g + 1)) - z0 = r - (g + 1 + z0) := by omega
          have hp : 8 * g + 8 + 1 = 8 * g + 9 := by omega
          simpa [hsub, hp] using hc.2
  · constructor
    · have hm := Nat.min_le_left (8 * g + 8) z0
      omega
    · intro r hqr hrT
      omega

/-! Role propagation. -/

theorem gapState_role_succ {m : Nat} (B : Nat) (hm : 0 < m)
    (bs : List (Fin m → Bool)) (s : Fin m → Snapshot)
    (r : Nat) (hr : r < bs.length) (i : Fin m) :
    (gapState B hm bs s (r + 1) i).role =
      (afterPhaseTwo B hm (gapRoundBits bs r hr)
        (gapState B hm bs s r) i).role := by
  rw [gapState_succ B hm bs s r hr]
  exact logicalRound_role_eq_afterPhaseTwo
    B hm (gapRoundBits bs r hr) (gapState B hm bs s r) i

theorem gapState_home_succ_anchor {m : Nat} (B : Nat) (hm : 0 < m)
    (bs : List (Fin m → Bool)) (s : Fin m → Snapshot)
    (r : Nat) (hr : r < bs.length) (i : Fin m)
    (ha : IsAnchor hm (gapState B hm bs s r) i) :
    (gapState B hm bs s (r + 1) i).home =
      (afterPhaseTwo B hm (gapRoundBits bs r hr)
        (gapState B hm bs s r) i).role := by
  rw [gapState_succ B hm bs s r hr]
  exact logicalRound_home_eq_afterPhaseTwo_role_of_anchor
    B hm (gapRoundBits bs r hr) (gapState B hm bs s r) i ha

/-- Transport the phase-2 role across equal round indices, including the
proof-dependent scheduler lookup. -/
theorem gapAfterPhaseTwo_index_congr {m : Nat}
    (B : Nat) (hm : 0 < m)
    (bs : List (Fin m → Bool)) (s : Fin m → Snapshot) (i : Fin m)
    {p q : Nat} (hp : p < bs.length) (hq : q < bs.length)
    (h : p = q) :
    (afterPhaseTwo B hm (gapRoundBits bs p hp)
      (gapState B hm bs s p) i).role =
    (afterPhaseTwo B hm (gapRoundBits bs q hq)
      (gapState B hm bs s q) i).role := by
  subst q
  rfl

/-- At the home, one draw fixes the role until the next draw, inclusive of
all rounds whose phase-2 state is claimed. -/
theorem gap_anchor_role {m : Nat} (B : Nat) (hm : 0 < m)
    (bs : List (Fin m → Bool)) (s : Fin m → Snapshot)
    (a b : Fin m) (g T : Nat)
    (hbits : T ≤ bs.length)
    (hf : gapFixed B hm bs s a b g T)
    (r r' : Nat) (hr : r < T) (hr' : r' < T) (hrr' : r ≤ r')
    (v : Bool)
    (hv : (gapRoundBits bs r (Nat.lt_of_lt_of_le hr hbits)) a = v)
    (hdraw : gapDraw B hm bs s a r)
    (hno : ∀ q, r < q → q ≤ r' → ¬ gapDraw B hm bs s a q) :
    ∀ t (hrt : r ≤ t) (htr' : t ≤ r'),
      (afterPhaseTwo B hm
        (gapRoundBits bs t
          (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt htr' hr') hbits))
        (gapState B hm bs s t) a).role = v := by
  have hbase :
      (afterPhaseTwo B hm
        (gapRoundBits bs r (Nat.lt_of_lt_of_le hr hbits))
        (gapState B hm bs s r) a).role = v := by
    have ha := gapFixed_start B hm bs s a b g T r hf hr
    have hz := (gapDraw_iff_z_zero B hm bs s a b g T r hf hr).mp hdraw
    rw [afterPhaseTwo_role_of_anchor
      B hm (gapRoundBits bs r (Nat.lt_of_lt_of_le hr hbits))
      (gapState B hm bs s r) a ha]
    rw [if_pos hz]
    exact hv
  have hstep : ∀ d, (hd : r + d ≤ r') →
      (afterPhaseTwo B hm
        (gapRoundBits bs (r + d)
          (Nat.lt_of_lt_of_le
            (Nat.lt_of_le_of_lt hd hr') hbits))
        (gapState B hm bs s (r + d)) a).role = v := by
    intro d
    induction d with
    | zero =>
        intro hd
        simpa using hbase
    | succ d ih =>
        intro hd
        have hprev := ih (by omega)
        let q := r + d
        have hqT : q < T := by dsimp [q]; omega
        have hqLen : q < bs.length := Nat.lt_of_lt_of_le hqT hbits
        have ha := gapFixed_start B hm bs s a b g T q hf hqT
        have hhome := gapState_home_succ_anchor
          B hm bs s q hqLen a ha
        have hhomeV : (gapState B hm bs s (q + 1) a).home = v := by
          rw [hhome]
          simpa [q] using hprev
        have hnextT : q + 1 < T := by dsimp [q]; omega
        have hnodraw := hno (q + 1) (by dsimp [q]; omega) (by dsimp [q]; omega)
        have hz : (gapState B hm bs s (q + 1) a).z ≠ 0 := by
          intro hz0
          apply hnodraw
          exact (gapDraw_iff_z_zero B hm bs s a b g T
            (q + 1) hf hnextT).2 hz0
        have haNext := gapFixed_start B hm bs s a b g T
          (q + 1) hf hnextT
        have hnextRole :
            (afterPhaseTwo B hm
              (gapRoundBits bs (q + 1)
                (Nat.lt_of_lt_of_le hnextT hbits))
              (gapState B hm bs s (q + 1)) a).role = v := by
          rw [afterPhaseTwo_role_of_anchor
            B hm
            (gapRoundBits bs (q + 1)
              (Nat.lt_of_lt_of_le hnextT hbits))
            (gapState B hm bs s (q + 1)) a haNext]
          rw [if_neg hz]
          exact hhomeV
        have hidx : r + (d + 1) = q + 1 := by
          dsimp [q]
          omega
        exact (gapAfterPhaseTwo_index_congr B hm bs s a
          (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hd hr') hbits)
          (Nat.lt_of_lt_of_le hnextT hbits) hidx).trans hnextRole
  intro t hrt htr'
  have hd : r + (t - r) ≤ r' := by omega
  have hs := hstep (t - r) hd
  have he : r + (t - r) = t := by omega
  have htransport := gapAfterPhaseTwo_index_congr B hm bs s a
    (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hd hr') hbits)
    (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt htr' hr') hbits) he
  exact htransport.symm.trans hs

/-- (4) A drawn role moves one site clockwise per round. The no-redraw
hypothesis covers `(r,r']`; excluding only `(r,r')` is false when `r'`
itself draws the opposite bit. -/
theorem gap_role {m : Nat} (B : Nat) (hm : 0 < m)
    (bs : List (Fin m → Bool)) (s : Fin m → Snapshot)
    (a b : Fin m) (g T : Nat)
    (hgm : g ≤ m) (hb : b = gapSite hm a g)
    (hbits : T ≤ bs.length)
    (hf : gapFixed B hm bs s a b g T)
    (r r' : Nat) (hr : r < T) (hr' : r' < T) (hrr' : r ≤ r')
    (v : Bool)
    (hv : (gapRoundBits bs r (Nat.lt_of_lt_of_le hr hbits)) a = v)
    (hdraw : gapDraw B hm bs s a r)
    (hno : ∀ q, r < q → q ≤ r' → ¬ gapDraw B hm bs s a q) :
    ∀ j, j < g → ∀ t, r + j ≤ t → (htr' : t ≤ r') →
      (afterPhaseTwo B hm
        (gapRoundBits bs t
          (Nat.lt_of_lt_of_le
            (Nat.lt_of_le_of_lt htr' hr') hbits))
        (gapState B hm bs s t) (gapSite hm a j)).role = v := by
  have hanchor := gap_anchor_role B hm bs s a b g T
    hbits hf r r' hr hr' hrr' v hv hdraw hno
  intro j
  induction j with
  | zero =>
      intro hj t hlow hhigh
      simpa using hanchor t (by omega) hhigh
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
      have hq1 : q + 1 = t := by dsimp [q]; omega
      have hqT : q < T := by dsimp [q]; omega
      have hqLen : q < bs.length := Nat.lt_of_lt_of_le hqT hbits
      rw [← hq1]
      rw [gapState_role_succ B hm bs s q hqLen (gapSite hm a j)]
      apply ih (by omega)
      · dsimp [q]
        omega
      · dsimp [q]
        omega

/-! ### Literal short-bit counterexamples

These retain the three green counterexamples from the previous round,
renamed as requested. They document why `T ≤ bs.length` is essential.
-/

def oneSite : Fin 1 := ⟨0, by omega⟩

def oneStart (q : Snapshot) : Fin 1 → Snapshot := fun _ => q

def noBits : List (Fin 1 → Bool) := []

def oneFrozenSnapshot : Snapshot :=
  { x := 0, d := 0, z := 100 }

def oneDrawSnapshot : Snapshot :=
  { x := 0, d := 0, z := 0 }

@[simp] theorem one_gap_site (k : Nat) :
    gapSite (by omega : 0 < 1) oneSite k = oneSite := by
  apply Fin.ext
  simp [gapSite, oneSite]

@[simp] theorem one_left_site :
    left (by omega : 0 < 1) oneSite = oneSite := by
  apply Fin.ext
  simp [left, oneSite]

theorem one_fixed (q : Snapshot) (T : Nat) :
    gapFixed 2 (by omega : 0 < 1) noBits (oneStart q)
      oneSite oneSite 1 T := by
  unfold gapFixed
  intro r hr k hk
  constructor
  · intro ha
    exact Or.inl (Subsingleton.elim _ _)
  · intro h
    unfold IsAnchor
    simp [gapState, noBits, oneStart, runRounds]

theorem one_frozen_bounded :
    Bounded 2 (oneStart oneFrozenSnapshot) := by
  unfold Bounded
  intro i
  simp [oneStart, oneFrozenSnapshot]

theorem gap_distance_counterexample_of_short_bits :
    gapFixed 2 (by omega : 0 < 1) noBits
        (oneStart oneFrozenSnapshot) oneSite oneSite 1 1 ∧
      ¬ (((gapState 2 (by omega : 0 < 1) noBits
          (oneStart oneFrozenSnapshot) 1) oneSite).d = 1) := by
  constructor
  · exact one_fixed oneFrozenSnapshot 1
  · simp [gapState, noBits, oneStart, oneFrozenSnapshot, runRounds]

theorem gap_countdown_counterexample_of_short_bits :
    gapFixed 2 (by omega : 0 < 1) noBits
        (oneStart oneFrozenSnapshot) oneSite oneSite 1 2 ∧
      ¬ (((gapState 2 (by omega : 0 < 1) noBits
          (oneStart oneFrozenSnapshot) 2) oneSite).z ≤ 8 * 1 + 8) := by
  constructor
  · exact one_fixed oneFrozenSnapshot 2
  · simp [gapState, noBits, oneStart, oneFrozenSnapshot, runRounds]

theorem one_draws_all (r : Nat) :
    gapDraw 2 (by omega : 0 < 1) noBits
      (oneStart oneDrawSnapshot) oneSite r := by
  simp [gapDraw, gapState, noBits, oneStart, oneDrawSnapshot,
    runRounds, phaseStep, phaseUpdate, left, oneSite]

theorem no_adjacent_period_seventeen :
    ¬ ∃ r0 : Nat,
      (r0 ≤ 2 ∧ (2 - r0) % 17 = 0) ∧
      (r0 ≤ 3 ∧ (3 - r0) % 17 = 0) := by
  intro h
  obtain ⟨r0, htwo, hthree⟩ := h
  have hlt : 2 - r0 < 17 := by omega
  have hzero := htwo.2
  rw [Nat.mod_eq_of_lt hlt] at hzero
  have hr : r0 = 2 := by omega
  subst r0
  simp at hthree

theorem gap_draws_counterexample_of_short_bits :
    gapFixed 2 (by omega : 0 < 1) noBits
        (oneStart oneDrawSnapshot) oneSite oneSite 1 4 ∧
      ¬ ∃ r0 : Nat,
        r0 ≤ 1 + 1 + (8 * 1 + 9) ∧
        ∀ r, 1 + 1 ≤ r → r < 4 →
          (gapDraw 2 (by omega : 0 < 1) noBits
              (oneStart oneDrawSnapshot) oneSite r ↔
            r0 ≤ r ∧ (r - r0) % (8 * 1 + 9) = 0) := by
  constructor
  · exact one_fixed oneDrawSnapshot 4
  · intro h
    obtain ⟨r0, hbound, hall⟩ := h
    have htwoRaw :=
      (hall 2 (by omega) (by omega)).mp (one_draws_all 2)
    have hthreeRaw :=
      (hall 3 (by omega) (by omega)).mp (one_draws_all 3)
    have htwo : r0 ≤ 2 ∧ (2 - r0) % 17 = 0 := by
      simpa using htwoRaw
    have hthree : r0 ≤ 3 ∧ (3 - r0) % 17 = 0 := by
      simpa using hthreeRaw
    exact no_adjacent_period_seventeen ⟨r0, htwo, hthree⟩

end L4.Height
