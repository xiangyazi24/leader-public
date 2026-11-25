import Leader.L4.Height.Core

namespace L4.Height

open Classical
open L4.Compiler.Native

set_option maxHeartbeats 4000000

/-- The low-role phase-3 proposal, before the final height update. -/
theorem phase_three_low_proposal
    (B : Nat) (l c r : Snapshot) (delta : Bool)
    (hrole : c.role = false) :
    (phaseUpdate B 3 l c r delta).proposal =
      (if c.anchor then 0 else l.x + 1) % B := by
  simp [phaseUpdate, hrole]

/-- The high-role phase-3 proposal, before the final height update. -/
theorem phase_three_high_proposal
    (B : Nat) (l c r : Snapshot) (delta : Bool)
    (hrole : c.role = true) :
    (phaseUpdate B 3 l c r delta).proposal =
      (if r.anchor then B - 1 else r.x + B - 1) % B := by
  simp [phaseUpdate, hrole]

/-- An anchor approves its own phase-3 proposal in phase 4. -/
theorem phase_four_anchor_approves
    (B : Nat) (l c r : Snapshot) (delta : Bool)
    (hanchor : c.anchor = true) :
    (phaseUpdate B 4 l c r delta).approve = true := by
  simp [phaseUpdate, hanchor]

/-- At a non-anchor, phase-4 approval is exactly the left-proposal comparison. -/
theorem phase_four_nonanchor_approval
    (B : Nat) (l c r : Snapshot) (delta : Bool)
    (hanchor : c.anchor = false) :
    (phaseUpdate B 4 l c r delta).approve =
      decide (l.proposal < c.proposal) := by
  simp [phaseUpdate, hanchor]

/-- The literal phase-5 update condition includes the right approval. -/
theorem phase_five_height
    (B : Nat) (l c r : Snapshot) (delta : Bool) :
    (phaseUpdate B 5 l c r delta).x =
      if c.approve && r.approve then c.proposal else c.x := by
  rfl

/-- A low-role anchor proposes zero when the modulus is positive. -/
theorem low_anchor_proposes_zero
    (B : Nat) (l c r : Snapshot) (delta : Bool)
    (hB : 0 < B) (hrole : c.role = false)
    (hanchor : c.anchor = true) :
    (phaseUpdate B 3 l c r delta).proposal = 0 := by
  rw [phase_three_low_proposal B l c r delta hrole, hanchor]
  simp [Nat.mod_eq_of_lt hB]

/-- A high-role site immediately before an anchor proposes B-1. -/
theorem high_before_anchor_proposes_top
    (B : Nat) (l c r : Snapshot) (delta : Bool)
    (hB : 0 < B) (hrole : c.role = true)
    (hright : r.anchor = true) :
    (phaseUpdate B 3 l c r delta).proposal = B - 1 := by
  rw [phase_three_high_proposal B l c r delta hrole]
  have hlt : B - 1 < B := by omega
  simpa [hright] using (Nat.mod_eq_of_lt hlt)

/-- The strict endpoint inequality used by the two-front argument. -/
theorem filled_edge_is_strict
    (g₁ g₂ m B : Nat)
    (hg₁ : 1 ≤ g₁) (hg₂ : 1 ≤ g₂)
    (hgap : g₁ + g₂ ≤ m) (hmod : m < B) :
    g₁ - 1 < B - g₂ := by
  omega

/-- If the two fronts reach the endpoint values, b is not an anchor. -/
theorem filled_edge_removes_b
    {m B : Nat}
    (hm : 0 < m)
    (a b : Fin m)
    (s : Fin m → Snapshot)
    (g₁ g₂ : Nat)
    (hg₁ : 1 ≤ g₁) (hg₂ : 1 ≤ g₂)
    (hgap : g₁ + g₂ ≤ m)
    (hmod : m < B)
    (hleft : left hm b = a)
    (hxa : (s a).x = g₁ - 1)
    (hxb : (s b).x = B - g₂) :
    ¬ IsAnchor hm s b := by
  intro hb
  unfold IsAnchor at hb
  rw [hleft, hxa, hxb] at hb
  have hstrict := filled_edge_is_strict g₁ g₂ m B hg₁ hg₂ hgap hmod
  omega

/-- The same endpoint arithmetic covers two complementary gaps. -/
theorem two_anchor_filled_edge_is_strict
    (g₁ g₂ m B : Nat)
    (hg₁ : 1 ≤ g₁) (hg₂ : 1 ≤ g₂)
    (hcomplementary : g₁ + g₂ = m)
    (hmod : m < B) :
    g₁ - 1 < B - g₂ := by
  apply filled_edge_is_strict g₁ g₂ m B hg₁ hg₂
  · omega
  · exact hmod

/-- Phase 3 at a site of a line, using the old phase-2 snapshots. -/
def linePhaseThree (B : Nat) (v : Nat → Snapshot) (i : Nat) : Snapshot :=
  phaseUpdate B 3 (v (i - 1)) (v i) (v (i + 1)) false

/-- Phase 4 at a site of a line, after all phase-3 proposals are present. -/
def linePhaseFour (B : Nat) (v : Nat → Snapshot) (i : Nat) : Snapshot :=
  phaseUpdate B 4 (linePhaseThree B v (i - 1))
    (linePhaseThree B v i) (linePhaseThree B v (i + 1)) false

/-- Phase 5 at a site of a line, after all approvals are present. -/
def linePhaseFive (B : Nat) (v : Nat → Snapshot) (i : Nat) : Snapshot :=
  phaseUpdate B 5 (linePhaseFour B v (i - 1))
    (linePhaseFour B v i) (linePhaseFour B v (i + 1)) false

private theorem linePhaseThree_anchor
    (B : Nat) (v : Nat → Snapshot) (i : Nat) :
    (linePhaseThree B v i).anchor = (v i).anchor := by
  simp [linePhaseThree, phaseUpdate]

private theorem linePhaseFour_proposal
    (B : Nat) (v : Nat → Snapshot) (i : Nat) :
    (linePhaseFour B v i).proposal = (linePhaseThree B v i).proposal := by
  simp [linePhaseFour, phaseUpdate]

private theorem linePhaseFour_anchor_true
    (B : Nat) (v : Nat → Snapshot) (i : Nat)
    (hanchor : (v i).anchor = true) :
    (linePhaseFour B v i).approve = true := by
  have hc : (linePhaseThree B v i).anchor = true := by
    rw [linePhaseThree_anchor]
    exact hanchor
  unfold linePhaseFour
  exact phase_four_anchor_approves B
    (linePhaseThree B v (i - 1))
    (linePhaseThree B v i)
    (linePhaseThree B v (i + 1)) false hc

private theorem linePhaseFour_nonanchor_true
    (B : Nat) (v : Nat → Snapshot) (i : Nat)
    (hanchor : (v i).anchor = false)
    (hlt : (linePhaseThree B v (i - 1)).proposal <
      (linePhaseThree B v i).proposal) :
    (linePhaseFour B v i).approve = true := by
  have hc : (linePhaseThree B v i).anchor = false := by
    rw [linePhaseThree_anchor]
    exact hanchor
  unfold linePhaseFour
  rw [phase_four_nonanchor_approval B
    (linePhaseThree B v (i - 1))
    (linePhaseThree B v i)
    (linePhaseThree B v (i + 1)) false hc]
  exact decide_eq_true hlt

private theorem linePhaseFive_updates
    (B : Nat) (v : Nat → Snapshot) (i : Nat)
    (hc : (linePhaseFour B v i).approve = true)
    (hr : (linePhaseFour B v (i + 1)).approve = true) :
    (linePhaseFive B v i).x = (linePhaseThree B v i).proposal := by
  unfold linePhaseFive
  calc
    (phaseUpdate B 5 (linePhaseFour B v (i - 1))
      (linePhaseFour B v i) (linePhaseFour B v (i + 1)) false).x =
        (linePhaseFour B v i).proposal := by
          have h := phase_five_height B
            (linePhaseFour B v (i - 1))
            (linePhaseFour B v i)
            (linePhaseFour B v (i + 1)) false
          simpa [hc, hr] using h
    _ = (linePhaseThree B v i).proposal :=
      linePhaseFour_proposal B v i

/-- One literal moving-front step on a linear cut. -/
theorem settled_prefix_grows
    (B j : Nat) (v : Nat → Snapshot)
    (hB : j + 3 < B)
    (hheight : ∀ i, i ≤ j → (v i).x = i)
    (hanchor : (v 0).anchor = true)
    (hinterior : ∀ i, 1 ≤ i → i ≤ j + 1 → (v i).anchor = false)
    (hrole : ∀ i, i ≤ j + 1 → (v i).role = false)
    (hstrict : ∀ i, i ≤ j + 2 → (v i).x < (v (i + 1)).x)
    (hbounded : ∀ i, i ≤ j + 3 → (v i).x < B) :
    ∀ i, i ≤ j + 1 → (linePhaseFive B v i).x = i := by
  have hproposal : ∀ i, i ≤ j + 1 →
      (linePhaseThree B v i).proposal = i := by
    intro i hi
    cases i with
    | zero =>
        have hr := hrole 0 (by omega)
        simp [linePhaseThree, phaseUpdate, hr, hanchor]
    | succ q =>
        have hq : q ≤ j := by omega
        have ha := hinterior (q + 1) (by omega) (by omega)
        have hr := hrole (q + 1) (by omega)
        have hx := hheight q hq
        have hlt : q + 1 < B := by omega
        simp [linePhaseThree, phaseUpdate, hr, ha, hx,
          Nat.mod_eq_of_lt hlt]
  have hfrontLow :
      (v (j + 2)).anchor = false →
      (v (j + 2)).role = false →
      (linePhaseThree B v (j + 2)).proposal > j + 1 := by
    intro hanc hr
    have hsRaw := hstrict (j + 1) (by omega)
    have hs : (v (j + 1)).x < (v (j + 2)).x := by
      have heq : j + 1 + 1 = j + 2 := by omega
      simpa only [heq] using hsRaw
    have hb := hbounded (j + 2) (by omega)
    have hlt : (v (j + 1)).x + 1 < B := by omega
    have hxj := hheight j (by omega)
    have hs0Raw := hstrict j (by omega)
    have hs0 : (v j).x < (v (j + 1)).x := by
      simpa using hs0Raw
    unfold linePhaseThree
    rw [phase_three_low_proposal B
      (v (j + 2 - 1)) (v (j + 2)) (v (j + 2 + 1)) false hr]
    have hsub : j + 2 - 1 = j + 1 := by omega
    have hbody :
        (if (v (j + 2)).anchor then 0 else (v (j + 2 - 1)).x + 1) =
          (v (j + 1)).x + 1 := by
      simp [hanc, hsub]
    rw [hbody, Nat.mod_eq_of_lt hlt]
    omega
  have hfrontHigh :
      (v (j + 2)).anchor = false →
      (v (j + 2)).role = true →
      (linePhaseThree B v (j + 2)).proposal > j + 1 := by
    intro _hanc hr
    have hxj : (v j).x = j := hheight j (by omega)
    have hs0Raw := hstrict j (by omega)
    have hs0 : (v j).x < (v (j + 1)).x := by
      simpa using hs0Raw
    have hs1Raw := hstrict (j + 1) (by omega)
    have hs1 : (v (j + 1)).x < (v (j + 2)).x := by
      have heq : j + 1 + 1 = j + 2 := by omega
      simpa only [heq] using hs1Raw
    have hs2Raw := hstrict (j + 2) (by omega)
    have hs2 : (v (j + 2)).x < (v (j + 3)).x := by
      have heq : j + 2 + 1 = j + 3 := by omega
      simpa only [heq] using hs2Raw
    have hb := hbounded (j + 3) (by omega)
    have hxpos : 0 < (v (j + 3)).x := by omega
    have hmod :
        ((v (j + 3)).x + B - 1) % B = (v (j + 3)).x - 1 := by
      have heq :
          (v (j + 3)).x + B - 1 = ((v (j + 3)).x - 1) + B := by
        omega
      rw [heq, Nat.add_mod]
      simp [Nat.mod_eq_of_lt (by omega : (v (j + 3)).x - 1 < B)]
    unfold linePhaseThree
    rw [phase_three_high_proposal B
      (v (j + 2 - 1)) (v (j + 2)) (v (j + 2 + 1)) false hr]
    have hidx : j + 2 + 1 = j + 3 := by omega
    rw [hidx]
    by_cases hright : (v (j + 3)).anchor = true
    · rw [if_pos hright]
      rw [Nat.mod_eq_of_lt (by omega : B - 1 < B)]
      omega
    · rw [if_neg hright, hmod]
      omega
  have happ : ∀ i, i ≤ j + 2 →
      (linePhaseFour B v i).approve = true := by
    intro i hi
    cases i with
    | zero =>
        exact linePhaseFour_anchor_true B v 0 hanchor
    | succ q =>
        by_cases hq : q + 1 ≤ j + 1
        · have hpLeft := hproposal q (by omega)
          have hpHere := hproposal (q + 1) hq
          have ha := hinterior (q + 1) (by omega) hq
          apply linePhaseFour_nonanchor_true B v (q + 1) ha
          have hsub : q + 1 - 1 = q := by omega
          rw [hsub, hpLeft, hpHere]
          omega
        · have hqeq : q = j + 1 := by omega
          subst q
          have hpLeft := hproposal (j + 1) (by omega)
          by_cases ha : (v (j + 2)).anchor = true
          · exact linePhaseFour_anchor_true B v (j + 2) ha
          · have hanc : (v (j + 2)).anchor = false :=
              Bool.eq_false_iff.mpr ha
            apply linePhaseFour_nonanchor_true B v (j + 2) hanc
            have hsub : j + 2 - 1 = j + 1 := by omega
            rw [hsub, hpLeft]
            by_cases hr : (v (j + 2)).role = false
            · exact hfrontLow hanc hr
            · have hr' : (v (j + 2)).role = true := by
                cases h : (v (j + 2)).role <;> simp_all
              exact hfrontHigh hanc hr'
  intro i hi
  have hp := hproposal i hi
  have hu := linePhaseFive_updates B v i
    (happ i (by omega)) (happ (i + 1) (by omega))
  rw [hu]
  exact hp

/-- State after phases 0,1,2 of one logical round. -/
def phaseTwoView {m : Nat} (B : Nat) (hm : 0 < m)
    (bits : Fin m → Bool) (s : Fin m → Snapshot) : Fin m → Snapshot :=
  phaseStep B 2 hm bits
    (phaseStep B 1 hm bits (phaseStep B 0 hm bits s))

/-- State after phases 0,1,2,3. -/
def phaseThreeView {m : Nat} (B : Nat) (hm : 0 < m)
    (bits : Fin m → Bool) (s : Fin m → Snapshot) : Fin m → Snapshot :=
  phaseStep B 3 hm bits (phaseTwoView B hm bits s)

/-- State after phases 0,1,2,3,4. -/
def phaseFourView {m : Nat} (B : Nat) (hm : 0 < m)
    (bits : Fin m → Bool) (s : Fin m → Snapshot) : Fin m → Snapshot :=
  phaseStep B 4 hm bits (phaseThreeView B hm bits s)

/-- A directed list of consecutive cyclic sites. -/
def GapPath {m : Nat} (hm : 0 < m) (p : Nat → Fin m) (g : Nat) : Prop :=
  ∀ i, i < g → right hm (p i) = p (i + 1)

/-- The three named boundaries are anchors at an opening. -/
def NamedLive {m : Nat} (hm : 0 < m)
    (S : Nat → Fin m → Snapshot) (t : Nat) (a b c : Fin m) : Prop :=
  IsAnchor hm (S t) a ∧ IsAnchor hm (S t) b ∧ IsAnchor hm (S t) c

/-- Fixed boundaries and no interior anchors while the named anchors survive. -/
def Fixed {m : Nat} (hm : 0 < m)
    (S : Nat → Fin m → Snapshot) (T : Nat)
    (pA pB : Nat → Fin m) (gA gB : Nat)
    (a b c : Fin m) : Prop :=
  ∀ t, t ≤ T → NamedLive hm S t a b c →
    (∀ i, 0 < i → i < gA → ¬ IsAnchor hm (S t) (pA i)) ∧
    (∀ i, 0 < i → i < gB → ¬ IsAnchor hm (S t) (pB i))

@[simp] private theorem fill_left_right {m : Nat}
    (hm : 0 < m) (i : Fin m) : left hm (right hm i) = i := by
  apply Fin.ext
  by_cases h : i.val + 1 < m
  · have hr : (i.val + 1) % m = i.val + 1 := Nat.mod_eq_of_lt h
    simp only [right, hr, left]
    have he : i.val + 1 + m - 1 = i.val + m := by omega
    rw [he, Nat.add_mod]
    simp [Nat.mod_eq_of_lt i.isLt]
  · have h' : i.val + 1 = m := by omega
    simp only [right, left]
    rw [h', Nat.mod_self]
    simp only [Nat.zero_add]
    have hm1 : m - 1 < m := by omega
    rw [Nat.mod_eq_of_lt hm1]
    omega

private theorem gap_left {m : Nat} (hm : 0 < m)
    (p : Nat → Fin m) (g : Nat) (hp : GapPath hm p g)
    (i : Nat) (hi : i < g) :
    left hm (p (i + 1)) = p i := by
  have h := hp i hi
  rw [← h]
  exact fill_left_right hm (p i)

private theorem phaseTwoView_x {m : Nat}
    (B : Nat) (hm : 0 < m) (bits : Fin m → Bool)
    (s : Fin m → Snapshot) (i : Fin m) :
    (phaseTwoView B hm bits s i).x = (s i).x := by
  simp [phaseTwoView, phaseStep, phaseUpdate]

private theorem phaseTwoView_anchor {m : Nat}
    (B : Nat) (hm : 0 < m) (bits : Fin m → Bool)
    (s : Fin m → Snapshot) (i : Fin m) :
    (phaseTwoView B hm bits s i).anchor = decide (IsAnchor hm s i) := by
  simp [phaseTwoView, phaseStep, phaseUpdate, IsAnchor]

private theorem phaseThreeView_anchor {m : Nat}
    (B : Nat) (hm : 0 < m) (bits : Fin m → Bool)
    (s : Fin m → Snapshot) (i : Fin m) :
    (phaseThreeView B hm bits s i).anchor = decide (IsAnchor hm s i) := by
  simp [phaseThreeView, phaseTwoView, phaseStep, phaseUpdate, IsAnchor]

private theorem phaseFourView_proposal {m : Nat}
    (B : Nat) (hm : 0 < m) (bits : Fin m → Bool)
    (s : Fin m → Snapshot) (i : Fin m) :
    (phaseFourView B hm bits s i).proposal =
      (phaseThreeView B hm bits s i).proposal := by
  simp [phaseFourView, phaseStep, phaseUpdate]

private theorem high_mod_pred (B x : Nat)
    (hB : 0 < B) (hx : 1 ≤ x) (hxB : x < B) :
    (x + B - 1) % B = x - 1 := by
  have he : x + B - 1 = (x - 1) + B := by omega
  have hlt : x - 1 < B := by omega
  rw [he, Nat.add_mod]
  simp [Nat.mod_eq_of_lt hlt]

/-- Literal proposal separation on a strict old edge. -/
private theorem strict_edge_phase_three {m : Nat}
    (B : Nat) (hm : 0 < m) (hB : 0 < B)
    (s : Fin m → Snapshot) (hs : Bounded B s)
    (bits : Fin m → Bool) (i : Fin m)
    (hstrict : (s i).x < (s (right hm i)).x) :
    let s0 := phaseStep B 0 hm bits s
    let s1 := phaseStep B 1 hm bits s0
    let s2 := phaseStep B 2 hm bits s1
    let s3 := phaseStep B 3 hm bits s2
    (s3 i).proposal < (s (right hm i)).x ∧
    (s i).x < (s3 (right hm i)).proposal := by
  dsimp
  let s0 := phaseStep B 0 hm bits s
  let s1 := phaseStep B 1 hm bits s0
  let s2 := phaseStep B 2 hm bits s1
  let s3 := phaseStep B 3 hm bits s2
  have hxleft : (s (left hm i)).x < B := hs _
  have hxi : (s i).x < B := hs _
  have hxj : (s (right hm i)).x < B := hs _
  have hxj0 : 0 < (s (right hm i)).x := by omega
  have hx2 (k : Fin m) : (s2 k).x = (s k).x := by
    simp [s2, s1, s0, phaseStep, phaseUpdate]
  have hanchor2 (k : Fin m) :
      (s2 k).anchor = decide ((s k).x ≤ (s (left hm k)).x) := by
    simp [s2, s1, s0, phaseStep, phaseUpdate]
  have hproposal3 (k : Fin m) :
      (s3 k).proposal =
        (if (s2 k).role then
          if (s2 (right hm k)).anchor then B - 1
          else (s2 (right hm k)).x + B - 1
        else if (s2 k).anchor then 0 else (s2 (left hm k)).x + 1) % B := by
    simp [s3, phaseStep, phaseUpdate]
  have hnotj : (s2 (right hm i)).anchor = false := by
    rw [hanchor2 (right hm i)]
    apply Bool.eq_false_iff.mpr
    intro hd
    have hle :
        (s (right hm i)).x ≤ (s (left hm (right hm i))).x :=
      of_decide_eq_true hd
    rw [fill_left_right hm i] at hle
    omega
  have hnotjP : ¬ (s2 (right hm i)).anchor = true := by
    simp [hnotj]
  constructor
  · rw [hproposal3 i]
    by_cases hr : (s2 i).role = true
    · rw [if_pos hr, if_neg hnotjP]
      rw [hx2 (right hm i)]
      rw [high_mod_pred B (s (right hm i)).x hB hxj0 hxj]
      omega
    · rw [if_neg hr]
      by_cases ha : (s2 i).anchor = true
      · rw [if_pos ha]
        simpa using hxj0
      · rw [if_neg ha]
        rw [hx2 (left hm i)]
        have hnotle : ¬ (s i).x ≤ (s (left hm i)).x := by
          intro hle
          apply ha
          rw [hanchor2 i]
          exact decide_eq_true hle
        have hleftlt : (s (left hm i)).x < (s i).x := by omega
        have hlt : (s (left hm i)).x + 1 < B := by omega
        rw [Nat.mod_eq_of_lt hlt]
        omega
  · rw [hproposal3 (right hm i)]
    by_cases hr : (s2 (right hm i)).role = true
    · rw [if_pos hr]
      by_cases ha : (s2 (right hm (right hm i))).anchor = true
      · rw [if_pos ha]
        rw [Nat.mod_eq_of_lt (by omega : B - 1 < B)]
        omega
      · rw [if_neg ha]
        rw [hx2 (right hm (right hm i))]
        have hnotle :
            ¬ (s (right hm (right hm i))).x ≤ (s (right hm i)).x := by
          intro hle
          apply ha
          rw [hanchor2 (right hm (right hm i))]
          rw [fill_left_right hm (right hm i)]
          exact decide_eq_true hle
        have hnext :
            (s (right hm i)).x < (s (right hm (right hm i))).x := by
          omega
        have hpos : 0 < (s (right hm (right hm i))).x := by omega
        have hmod := high_mod_pred B
          (s (right hm (right hm i))).x hB hpos (hs _)
        rw [hmod]
        omega
    · rw [if_neg hr, if_neg hnotjP]
      rw [fill_left_right hm i]
      rw [hx2 i]
      have hlt : (s i).x + 1 < B := by omega
      rw [Nat.mod_eq_of_lt hlt]
      omega

private theorem strict_edge_phase_three_view {m : Nat}
    (B : Nat) (hm : 0 < m) (hB : 0 < B)
    (s : Fin m → Snapshot) (hs : Bounded B s)
    (bits : Fin m → Bool) (i : Fin m)
    (hstrict : (s i).x < (s (right hm i)).x) :
    (phaseThreeView B hm bits s i).proposal < (s (right hm i)).x ∧
    (s i).x < (phaseThreeView B hm bits s (right hm i)).proposal := by
  have h := strict_edge_phase_three B hm hB s hs bits i hstrict
  dsimp at h
  change
    (phaseStep B 3 hm bits
      (phaseStep B 2 hm bits
        (phaseStep B 1 hm bits
          (phaseStep B 0 hm bits s))) i).proposal <
        (s (right hm i)).x ∧
    (s i).x <
      (phaseStep B 3 hm bits
        (phaseStep B 2 hm bits
          (phaseStep B 1 hm bits
            (phaseStep B 0 hm bits s))) (right hm i)).proposal
  exact h

private theorem strict_before_nonanchor {m : Nat}
    (hm : 0 < m) (s : Fin m → Snapshot)
    (u v : Fin m) (hleft : left hm v = u)
    (hv : ¬ IsAnchor hm s v) :
    (s u).x < (s v).x := by
  unfold IsAnchor at hv
  rw [hleft] at hv
  omega

private theorem low_anchor_proposal {m : Nat}
    (B : Nat) (hm : 0 < m) (bits : Fin m → Bool)
    (s : Fin m → Snapshot) (i : Fin m)
    (hrole : (phaseTwoView B hm bits s i).role = false)
    (hanchor : IsAnchor hm s i) :
    (phaseThreeView B hm bits s i).proposal = 0 := by
  have ha : (phaseTwoView B hm bits s i).anchor = true := by
    rw [phaseTwoView_anchor]
    simp [hanchor]
  change
    (phaseUpdate B 3
      (phaseTwoView B hm bits s (left hm i))
      (phaseTwoView B hm bits s i)
      (phaseTwoView B hm bits s (right hm i))
      (bits i)).proposal = 0
  simp [phaseUpdate, hrole, ha]

private theorem low_nonanchor_proposal {m : Nat}
    (B : Nat) (hm : 0 < m) (bits : Fin m → Bool)
    (s : Fin m → Snapshot) (i : Fin m)
    (hrole : (phaseTwoView B hm bits s i).role = false)
    (hanchor : ¬ IsAnchor hm s i) :
    (phaseThreeView B hm bits s i).proposal =
      ((s (left hm i)).x + 1) % B := by
  have ha : (phaseTwoView B hm bits s i).anchor = false := by
    rw [phaseTwoView_anchor]
    simp [hanchor]
  have h := phase_three_low_proposal B
    (phaseTwoView B hm bits s (left hm i))
    (phaseTwoView B hm bits s i)
    (phaseTwoView B hm bits s (right hm i))
    (bits i) hrole
  calc
    (phaseThreeView B hm bits s i).proposal =
        (if (phaseTwoView B hm bits s i).anchor then 0
         else (phaseTwoView B hm bits s (left hm i)).x + 1) % B := by
      simpa [phaseThreeView, phaseStep] using h
    _ = ((phaseTwoView B hm bits s (left hm i)).x + 1) % B := by
      simp [ha]
    _ = ((s (left hm i)).x + 1) % B := by
      rw [phaseTwoView_x]

private theorem high_nonboundary_proposal {m : Nat}
    (B : Nat) (hm : 0 < m) (bits : Fin m → Bool)
    (s : Fin m → Snapshot) (i : Fin m)
    (hrole : (phaseTwoView B hm bits s i).role = true)
    (hright : ¬ IsAnchor hm s (right hm i)) :
    (phaseThreeView B hm bits s i).proposal =
      ((s (right hm i)).x + B - 1) % B := by
  have ha : (phaseTwoView B hm bits s (right hm i)).anchor = false := by
    rw [phaseTwoView_anchor]
    simp [hright]
  have h := phase_three_high_proposal B
    (phaseTwoView B hm bits s (left hm i))
    (phaseTwoView B hm bits s i)
    (phaseTwoView B hm bits s (right hm i))
    (bits i) hrole
  calc
    (phaseThreeView B hm bits s i).proposal =
        (if (phaseTwoView B hm bits s (right hm i)).anchor then B - 1
         else (phaseTwoView B hm bits s (right hm i)).x + B - 1) % B := by
      simpa [phaseThreeView, phaseStep] using h
    _ = ((phaseTwoView B hm bits s (right hm i)).x + B - 1) % B := by
      simp [ha]
    _ = ((s (right hm i)).x + B - 1) % B := by
      rw [phaseTwoView_x]

private theorem high_boundary_proposal {m : Nat}
    (B : Nat) (hm : 0 < m) (hB : 0 < B)
    (bits : Fin m → Bool) (s : Fin m → Snapshot) (i : Fin m)
    (hrole : (phaseTwoView B hm bits s i).role = true)
    (hright : IsAnchor hm s (right hm i)) :
    (phaseThreeView B hm bits s i).proposal = B - 1 := by
  have ha : (phaseTwoView B hm bits s (right hm i)).anchor = true := by
    rw [phaseTwoView_anchor]
    simp [hright]
  have h := phase_three_high_proposal B
    (phaseTwoView B hm bits s (left hm i))
    (phaseTwoView B hm bits s i)
    (phaseTwoView B hm bits s (right hm i))
    (bits i) hrole
  calc
    (phaseThreeView B hm bits s i).proposal =
        (if (phaseTwoView B hm bits s (right hm i)).anchor then B - 1
         else (phaseTwoView B hm bits s (right hm i)).x + B - 1) % B := by
      simpa [phaseThreeView, phaseStep] using h
    _ = (B - 1) % B := by
      simp [ha]
    _ = B - 1 := Nat.mod_eq_of_lt (by omega)

private theorem phaseFour_anchor_true {m : Nat}
    (B : Nat) (hm : 0 < m) (bits : Fin m → Bool)
    (s : Fin m → Snapshot) (i : Fin m)
    (hanchor : IsAnchor hm s i) :
    (phaseFourView B hm bits s i).approve = true := by
  have ha : (phaseThreeView B hm bits s i).anchor = true := by
    rw [phaseThreeView_anchor]
    simp [hanchor]
  have h := phase_four_anchor_approves B
    (phaseThreeView B hm bits s (left hm i))
    (phaseThreeView B hm bits s i)
    (phaseThreeView B hm bits s (right hm i))
    (bits i) ha
  simpa [phaseFourView, phaseStep] using h

private theorem phaseFour_nonanchor_true {m : Nat}
    (B : Nat) (hm : 0 < m) (bits : Fin m → Bool)
    (s : Fin m → Snapshot) (i : Fin m)
    (hanchor : ¬ IsAnchor hm s i)
    (hlt : (phaseThreeView B hm bits s (left hm i)).proposal <
      (phaseThreeView B hm bits s i).proposal) :
    (phaseFourView B hm bits s i).approve = true := by
  have ha : (phaseThreeView B hm bits s i).anchor = false := by
    rw [phaseThreeView_anchor]
    simp [hanchor]
  have h := phase_four_nonanchor_approval B
    (phaseThreeView B hm bits s (left hm i))
    (phaseThreeView B hm bits s i)
    (phaseThreeView B hm bits s (right hm i))
    (bits i) ha
  calc
    (phaseFourView B hm bits s i).approve =
        decide ((phaseThreeView B hm bits s (left hm i)).proposal <
          (phaseThreeView B hm bits s i).proposal) := by
      simpa [phaseFourView, phaseStep] using h
    _ = true := by simp [hlt]

private theorem round_updates_to_proposal {m : Nat}
    (B : Nat) (hm : 0 < m) (bits : Fin m → Bool)
    (s : Fin m → Snapshot) (i : Fin m)
    (hi : (phaseFourView B hm bits s i).approve = true)
    (hr : (phaseFourView B hm bits s (right hm i)).approve = true) :
    (logicalRound B hm bits s i).x =
      (phaseThreeView B hm bits s i).proposal := by
  change
    (phaseUpdate B 5
      (phaseFourView B hm bits s (left hm i))
      (phaseFourView B hm bits s i)
      (phaseFourView B hm bits s (right hm i))
      (bits i)).x = (phaseThreeView B hm bits s i).proposal
  calc
    (phaseUpdate B 5
      (phaseFourView B hm bits s (left hm i))
      (phaseFourView B hm bits s i)
      (phaseFourView B hm bits s (right hm i))
      (bits i)).x = (phaseFourView B hm bits s i).proposal := by
        have h := phase_five_height B
          (phaseFourView B hm bits s (left hm i))
          (phaseFourView B hm bits s i)
          (phaseFourView B hm bits s (right hm i))
          (bits i)
        simpa [hi, hr] using h
    _ = (phaseThreeView B hm bits s i).proposal :=
      phaseFourView_proposal B hm bits s i

private theorem cyclic_prefix_starts {m : Nat}
    (B : Nat) (hm : 0 < m)
    (s : Fin m → Snapshot) (bits : Fin m → Bool)
    (p : Nat → Fin m) (g : Nat)
    (hB : 0 < B) (hg : 1 ≤ g) (hgB : g < B)
    (hpath : GapPath hm p g)
    (hanchorStart : IsAnchor hm s (p 0))
    (hanchorEnd : IsAnchor hm s (p g))
    (hinterior : ∀ i, 0 < i → i < g → ¬ IsAnchor hm s (p i))
    (hs : Bounded B s)
    (hrole : (phaseTwoView B hm bits s (p 0)).role = false) :
    (logicalRound B hm bits s (p 0)).x = 0 := by
  have hrightZero : right hm (p 0) = p 1 := hpath 0 (by omega)
  have hpZero := low_anchor_proposal B hm bits s (p 0) hrole hanchorStart
  have haZero := phaseFour_anchor_true B hm bits s (p 0) hanchorStart
  have haOne : (phaseFourView B hm bits s (p 1)).approve = true := by
    by_cases hone : g = 1
    · have heq : p 1 = p g := congrArg p (by omega)
      rw [heq]
      exact phaseFour_anchor_true B hm bits s (p g) hanchorEnd
    · have hnot := hinterior 1 (by omega) (by omega)
      have hleft := gap_left hm p g hpath 0 (by omega)
      have hstrict := strict_before_nonanchor hm s (p 0) (p 1) hleft hnot
      have hstrictRight :
          (s (p 0)).x < (s (right hm (p 0))).x := by
        rw [hrightZero]
        exact hstrict
      have hb := strict_edge_phase_three_view B hm hB s hs bits
        (p 0) hstrictRight
      have hprop :
          (phaseThreeView B hm bits s (p 0)).proposal <
            (phaseThreeView B hm bits s (p 1)).proposal := by
        have hh := hb.2
        rw [hrightZero] at hh
        rw [hpZero]
        omega
      apply phaseFour_nonanchor_true B hm bits s (p 1) hnot
      calc
        (phaseThreeView B hm bits s (left hm (p 1))).proposal =
            (phaseThreeView B hm bits s (p 0)).proposal := by rw [hleft]
        _ < (phaseThreeView B hm bits s (p 1)).proposal := hprop
  have haRight :
      (phaseFourView B hm bits s (right hm (p 0))).approve = true := by
    rw [hrightZero]
    exact haOne
  rw [round_updates_to_proposal B hm bits s (p 0) haZero haRight, hpZero]

private theorem cyclic_prefix_step {m : Nat}
    (B : Nat) (hm : 0 < m)
    (s : Fin m → Snapshot) (bits : Fin m → Bool)
    (p : Nat → Fin m) (g j : Nat)
    (hB : 0 < B) (hgB : g < B) (hfront : j + 1 < g)
    (hpath : GapPath hm p g)
    (hanchorStart : IsAnchor hm s (p 0))
    (hanchorEnd : IsAnchor hm s (p g))
    (hinterior : ∀ i, 0 < i → i < g → ¬ IsAnchor hm s (p i))
    (hs : Bounded B s)
    (hsettled : ∀ i, i ≤ j → (s (p i)).x = i)
    (hlow : ∀ i, i ≤ j + 1 →
      (phaseTwoView B hm bits s (p i)).role = false) :
    ∀ i, i ≤ j + 1 → (logicalRound B hm bits s (p i)).x = i := by
  have hpZero := low_anchor_proposal B hm bits s (p 0)
    (hlow 0 (by omega)) hanchorStart
  have hproposal : ∀ i, i ≤ j + 1 →
      (phaseThreeView B hm bits s (p i)).proposal = i := by
    intro i hi
    by_cases hiz : i = 0
    · subst i
      exact hpZero
    · have hiPos : 0 < i := by omega
      have hiGap : i < g := by omega
      have hnot := hinterior i hiPos hiGap
      have hleft : left hm (p i) = p (i - 1) := by
        have hh := gap_left hm p g hpath (i - 1) (by omega)
        have heq : i - 1 + 1 = i := by omega
        simpa only [heq] using hh
      have hprev := hsettled (i - 1) (by omega)
      have hp := low_nonanchor_proposal B hm bits s (p i)
        (hlow i hi) hnot
      calc
        (phaseThreeView B hm bits s (p i)).proposal =
            ((s (left hm (p i))).x + 1) % B := hp
        _ = ((s (p (i - 1))).x + 1) % B := by rw [hleft]
        _ = i % B := by rw [hprev]; congr; omega
        _ = i := Nat.mod_eq_of_lt (by omega)
  have happ : ∀ i, i ≤ j + 1 →
      (phaseFourView B hm bits s (p i)).approve = true := by
    intro i hi
    by_cases hiz : i = 0
    · subst i
      exact phaseFour_anchor_true B hm bits s (p 0) hanchorStart
    · have hiPos : 0 < i := by omega
      have hiGap : i < g := by omega
      have hnot := hinterior i hiPos hiGap
      have hleft : left hm (p i) = p (i - 1) := by
        have hh := gap_left hm p g hpath (i - 1) (by omega)
        have heq : i - 1 + 1 = i := by omega
        simpa only [heq] using hh
      apply phaseFour_nonanchor_true B hm bits s (p i) hnot
      calc
        (phaseThreeView B hm bits s (left hm (p i))).proposal =
            (phaseThreeView B hm bits s (p (i - 1))).proposal := by rw [hleft]
        _ = i - 1 := hproposal (i - 1) (by omega)
        _ < i := by omega
        _ = (phaseThreeView B hm bits s (p i)).proposal :=
          (hproposal i hi).symm
  have happFront :
      (phaseFourView B hm bits s (p (j + 2))).approve = true := by
    by_cases hend : j + 2 = g
    · have heq : p (j + 2) = p g := congrArg p hend
      rw [heq]
      exact phaseFour_anchor_true B hm bits s (p g) hanchorEnd
    · have hlt : j + 2 < g := by omega
      have hnotFront := hinterior (j + 2) (by omega) hlt
      have hleftCurrent := gap_left hm p g hpath j (by omega)
      have hnotCurrent := hinterior (j + 1) (by omega) (by omega)
      have hxCurrent : j + 1 ≤ (s (p (j + 1))).x := by
        have hsx := strict_before_nonanchor hm s (p j) (p (j + 1))
          hleftCurrent hnotCurrent
        have hxj := hsettled j (by omega)
        omega
      have hleftFront := gap_left hm p g hpath (j + 1) (by omega)
      have hstrictFront := strict_before_nonanchor hm s (p (j + 1))
        (p (j + 2)) hleftFront hnotFront
      have hnext : right hm (p (j + 1)) = p (j + 2) := by
        have hh := hpath (j + 1) (by omega)
        have heq : j + 1 + 1 = j + 2 := by omega
        simpa only [heq] using hh
      have hstrictFrontRight :
          (s (p (j + 1))).x < (s (right hm (p (j + 1)))).x := by
        rw [hnext]
        exact hstrictFront
      have hb := strict_edge_phase_three_view B hm hB s hs bits
        (p (j + 1)) hstrictFrontRight
      have hpFront : j + 1 <
          (phaseThreeView B hm bits s (p (j + 2))).proposal := by
        have hh := hb.2
        rw [hnext] at hh
        exact Nat.lt_of_le_of_lt hxCurrent hh
      apply phaseFour_nonanchor_true B hm bits s (p (j + 2)) hnotFront
      calc
        (phaseThreeView B hm bits s (left hm (p (j + 2)))).proposal =
            (phaseThreeView B hm bits s (p (j + 1))).proposal := by
              rw [hleftFront]
        _ = j + 1 := hproposal (j + 1) (by omega)
        _ < (phaseThreeView B hm bits s (p (j + 2))).proposal := hpFront
  intro i hi
  have hiGap : i < g := by omega
  have hright := hpath i hiGap
  have hrightApprove :
      (phaseFourView B hm bits s (right hm (p i))).approve = true := by
    rw [hright]
    by_cases hilast : i = j + 1
    · subst i
      exact happFront
    · exact happ (i + 1) (by omega)
  rw [round_updates_to_proposal B hm bits s (p i) (happ i hi) hrightApprove]
  exact hproposal i hi

/-- Iteration of the low moving-front step over one complete gap. -/
theorem settled_prefix_rounds {m : Nat}
    (B : Nat) (hm : 0 < m)
    (S : Nat → Fin m → Snapshot) (bits : Nat → Fin m → Bool)
    (p : Nat → Fin m) (g start : Nat)
    (hB : 0 < B) (hg : 1 ≤ g) (hgB : g < B)
    (hpath : GapPath hm p g)
    (hanchorStart : ∀ r, r ≤ g → IsAnchor hm (S (start + r)) (p 0))
    (hanchorEnd : ∀ r, r ≤ g → IsAnchor hm (S (start + r)) (p g))
    (hinterior : ∀ r, r ≤ g → ∀ i, 0 < i → i < g →
      ¬ IsAnchor hm (S (start + r)) (p i))
    (hbounded : ∀ r, r ≤ g → Bounded B (S (start + r)))
    (hevol : ∀ r, r < g →
      S (start + r + 1) =
        logicalRound B hm (bits (start + r)) (S (start + r)))
    (hroles : ∀ r, r < g → ∀ i, i ≤ r →
      (phaseTwoView B hm (bits (start + r))
        (S (start + r)) (p i)).role = false) :
    ∀ i, i < g → (S (start + g) (p i)).x = i := by
  have hind : ∀ r, r < g → ∀ i, i ≤ r →
      (S (start + r + 1) (p i)).x = i := by
    intro r
    induction r with
    | zero =>
        intro hr i hi
        have hiz : i = 0 := by omega
        subst i
        have hs0 := cyclic_prefix_starts B hm
          (S (start + 0)) (bits (start + 0)) p g
          hB hg hgB hpath
          (hanchorStart 0 (by omega))
          (hanchorEnd 0 (by omega))
          (hinterior 0 (by omega))
          (hbounded 0 (by omega))
          (hroles 0 hr 0 (by omega))
        calc
          (S (start + 0 + 1) (p 0)).x =
              (logicalRound B hm (bits (start + 0))
                (S (start + 0)) (p 0)).x := by
                  rw [hevol 0 hr]
          _ = 0 := hs0
    | succ r ih =>
        intro hr i hi
        have hprev : ∀ q, q ≤ r →
            (S (start + (r + 1)) (p q)).x = q := by
          intro q hq
          have hh := ih (by omega) q hq
          simpa [Nat.add_assoc] using hh
        have hstep := cyclic_prefix_step B hm
          (S (start + (r + 1))) (bits (start + (r + 1)))
          p g r hB hgB (by omega) hpath
          (hanchorStart (r + 1) (by omega))
          (hanchorEnd (r + 1) (by omega))
          (hinterior (r + 1) (by omega))
          (hbounded (r + 1) (by omega))
          hprev
          (by
            intro q hq
            exact hroles (r + 1) hr q hq)
        calc
          (S (start + (r + 1) + 1) (p i)).x =
              (logicalRound B hm (bits (start + (r + 1)))
                (S (start + (r + 1))) (p i)).x := by
                  rw [hevol (r + 1) hr]
          _ = i := hstep i hi
  intro i hi
  have hh := hind (g - 1) (by omega) i (by omega)
  have heq : start + (g - 1) + 1 = start + g := by omega
  rw [heq] at hh
  exact hh

private theorem cyclic_suffix_starts {m : Nat}
    (B : Nat) (hm : 0 < m)
    (s : Fin m → Snapshot) (bits : Fin m → Bool)
    (p : Nat → Fin m) (g : Nat)
    (hB : 0 < B) (hg : 1 ≤ g) (hgB : g < B)
    (hpath : GapPath hm p g)
    (hanchorStart : IsAnchor hm s (p 0))
    (hanchorEnd : IsAnchor hm s (p g))
    (hinterior : ∀ i, 0 < i → i < g → ¬ IsAnchor hm s (p i))
    (hs : Bounded B s)
    (hroles : ∀ i, i < g →
      (phaseTwoView B hm bits s (p i)).role = true) :
    (logicalRound B hm bits s (p (g - 1))).x = B - 1 := by
  let last := g - 1
  have hlast : last < g := by dsimp [last]; omega
  have hlastSucc : last + 1 = g := by dsimp [last]; omega
  have hrightEnd : right hm (p last) = p g := by
    have hh := hpath last hlast
    simpa only [hlastSucc] using hh
  have hpLast : (phaseThreeView B hm bits s (p last)).proposal = B - 1 := by
    apply high_boundary_proposal B hm hB bits s (p last)
    · exact hroles last hlast
    · rw [hrightEnd]
      exact hanchorEnd
  have haLast : (phaseFourView B hm bits s (p last)).approve = true := by
    by_cases hzero : last = 0
    · have heq : p last = p 0 := congrArg p hzero
      rw [heq]
      exact phaseFour_anchor_true B hm bits s (p 0) hanchorStart
    · have hnot := hinterior last (by omega) hlast
      have hleft : left hm (p last) = p (last - 1) := by
        have hh := gap_left hm p g hpath (last - 1) (by omega)
        have heq : last - 1 + 1 = last := by omega
        simpa only [heq] using hh
      have hstrict := strict_before_nonanchor hm s (p (last - 1))
        (p last) hleft hnot
      have hrightPrev : right hm (p (last - 1)) = p last := by
        have hh := hpath (last - 1) (by omega)
        have heq : last - 1 + 1 = last := by omega
        simpa only [heq] using hh
      have hstrictRight :
          (s (p (last - 1))).x < (s (right hm (p (last - 1)))).x := by
        rw [hrightPrev]
        exact hstrict
      have hb := strict_edge_phase_three_view B hm hB s hs bits
        (p (last - 1)) hstrictRight
      have hltLeft :
          (phaseThreeView B hm bits s (p (last - 1))).proposal < B - 1 := by
        have hh := hb.1
        rw [hrightPrev] at hh
        have hx := hs (p last)
        omega
      apply phaseFour_nonanchor_true B hm bits s (p last) hnot
      calc
        (phaseThreeView B hm bits s (left hm (p last))).proposal =
            (phaseThreeView B hm bits s (p (last - 1))).proposal := by
              rw [hleft]
        _ < B - 1 := hltLeft
        _ = (phaseThreeView B hm bits s (p last)).proposal := hpLast.symm
  have haEnd := phaseFour_anchor_true B hm bits s (p g) hanchorEnd
  have haRight :
      (phaseFourView B hm bits s (right hm (p last))).approve = true := by
    rw [hrightEnd]
    exact haEnd
  rw [round_updates_to_proposal B hm bits s (p last) haLast haRight, hpLast]

private theorem cyclic_suffix_step {m : Nat}
    (B : Nat) (hm : 0 < m)
    (s : Fin m → Snapshot) (bits : Fin m → Bool)
    (p : Nat → Fin m) (g r : Nat)
    (hB : 0 < B) (hgB : g < B)
    (hrPos : 1 ≤ r) (hrGap : r < g)
    (hpath : GapPath hm p g)
    (hanchorStart : IsAnchor hm s (p 0))
    (hanchorEnd : IsAnchor hm s (p g))
    (hinterior : ∀ i, 0 < i → i < g → ¬ IsAnchor hm s (p i))
    (hs : Bounded B s)
    (hsettled : ∀ i, g - r ≤ i → i < g →
      (s (p i)).x = B - g + i)
    (hroles : ∀ i, i < g →
      (phaseTwoView B hm bits s (p i)).role = true) :
    ∀ i, g - (r + 1) ≤ i → i < g →
      (logicalRound B hm bits s (p i)).x = B - g + i := by
  have hproposal : ∀ i, g - (r + 1) ≤ i → i < g →
      (phaseThreeView B hm bits s (p i)).proposal = B - g + i := by
    intro i hlo hi
    have hright := hpath i hi
    by_cases hend : i + 1 = g
    · have hanchRight : IsAnchor hm s (right hm (p i)) := by
        rw [hright, hend]
        exact hanchorEnd
      have hp := high_boundary_proposal B hm hB bits s (p i)
        (hroles i hi) hanchRight
      rw [hp]
      omega
    · have hiNext : i + 1 < g := by omega
      have hnotRight : ¬ IsAnchor hm s (right hm (p i)) := by
        rw [hright]
        exact hinterior (i + 1) (by omega) hiNext
      have hp := high_nonboundary_proposal B hm bits s (p i)
        (hroles i hi) hnotRight
      have hval := hsettled (i + 1) (by omega) hiNext
      have hxPos : 1 ≤ B - g + (i + 1) := by omega
      have hxLt : B - g + (i + 1) < B := by omega
      calc
        (phaseThreeView B hm bits s (p i)).proposal =
            ((s (right hm (p i))).x + B - 1) % B := hp
        _ = ((B - g + (i + 1)) + B - 1) % B := by
          rw [hright, hval]
        _ = (B - g + (i + 1)) - 1 :=
          high_mod_pred B (B - g + (i + 1)) hB hxPos hxLt
        _ = B - g + i := by omega
  have happ : ∀ i, g - (r + 1) ≤ i → i < g →
      (phaseFourView B hm bits s (p i)).approve = true := by
    intro i hlo hi
    by_cases hfirst : i = g - (r + 1)
    · by_cases hiz : i = 0
      · rw [hiz]
        exact phaseFour_anchor_true B hm bits s (p 0) hanchorStart
      · have hnot := hinterior i (by omega) hi
        have hleft : left hm (p i) = p (i - 1) := by
          have hh := gap_left hm p g hpath (i - 1) (by omega)
          have heq : i - 1 + 1 = i := by omega
          simpa only [heq] using hh
        have hstrictOutside := strict_before_nonanchor hm s (p (i - 1))
          (p i) hleft hnot
        have hrightOutside : right hm (p (i - 1)) = p i := by
          have hh := hpath (i - 1) (by omega)
          have heq : i - 1 + 1 = i := by omega
          simpa only [heq] using hh
        have hstrictOutsideRight :
            (s (p (i - 1))).x < (s (right hm (p (i - 1)))).x := by
          rw [hrightOutside]
          exact hstrictOutside
        have hb := strict_edge_phase_three_view B hm hB s hs bits
          (p (i - 1)) hstrictOutsideRight
        have hiNext : i + 1 < g := by omega
        have hleftNext := gap_left hm p g hpath i hi
        have hnotNext := hinterior (i + 1) (by omega) hiNext
        have hstrictNext := strict_before_nonanchor hm s (p i)
          (p (i + 1)) hleftNext hnotNext
        have hvalNext := hsettled (i + 1) (by omega) hiNext
        have hxUpper : (s (p i)).x ≤ B - g + i := by omega
        have hpOutside :
            (phaseThreeView B hm bits s (p (i - 1))).proposal <
              (s (p i)).x := by
          have hh := hb.1
          rw [hrightOutside] at hh
          exact hh
        apply phaseFour_nonanchor_true B hm bits s (p i) hnot
        calc
          (phaseThreeView B hm bits s (left hm (p i))).proposal =
              (phaseThreeView B hm bits s (p (i - 1))).proposal := by
                rw [hleft]
          _ < (s (p i)).x := hpOutside
          _ ≤ B - g + i := hxUpper
          _ = (phaseThreeView B hm bits s (p i)).proposal :=
            (hproposal i hlo hi).symm
    · have hgt : g - (r + 1) < i := by omega
      have hiPos : 0 < i := by omega
      have hnot := hinterior i hiPos hi
      have hleft : left hm (p i) = p (i - 1) := by
        have hh := gap_left hm p g hpath (i - 1) (by omega)
        have heq : i - 1 + 1 = i := by omega
        simpa only [heq] using hh
      apply phaseFour_nonanchor_true B hm bits s (p i) hnot
      calc
        (phaseThreeView B hm bits s (left hm (p i))).proposal =
            (phaseThreeView B hm bits s (p (i - 1))).proposal := by
              rw [hleft]
        _ = B - g + (i - 1) := hproposal (i - 1) (by omega) (by omega)
        _ < B - g + i := by omega
        _ = (phaseThreeView B hm bits s (p i)).proposal :=
          (hproposal i hlo hi).symm
  intro i hlo hi
  have hright := hpath i hi
  have hrightApprove :
      (phaseFourView B hm bits s (right hm (p i))).approve = true := by
    rw [hright]
    by_cases hend : i + 1 = g
    · rw [hend]
      exact phaseFour_anchor_true B hm bits s (p g) hanchorEnd
    · exact happ (i + 1) (by omega) (by omega)
  rw [round_updates_to_proposal B hm bits s (p i)
    (happ i hlo hi) hrightApprove]
  exact hproposal i hlo hi

/-- The high suffix grows one site per round from the right boundary. -/
theorem settled_suffix_grows {m : Nat}
    (B : Nat) (hm : 0 < m)
    (S : Nat → Fin m → Snapshot) (bits : Nat → Fin m → Bool)
    (p : Nat → Fin m) (g start : Nat)
    (hB : 0 < B) (hg : 1 ≤ g) (hgB : g < B)
    (hpath : GapPath hm p g)
    (hanchorStart : ∀ r, r ≤ g → IsAnchor hm (S (start + r)) (p 0))
    (hanchorEnd : ∀ r, r ≤ g → IsAnchor hm (S (start + r)) (p g))
    (hinterior : ∀ r, r ≤ g → ∀ i, 0 < i → i < g →
      ¬ IsAnchor hm (S (start + r)) (p i))
    (hbounded : ∀ r, r ≤ g → Bounded B (S (start + r)))
    (hevol : ∀ r, r < g →
      S (start + r + 1) =
        logicalRound B hm (bits (start + r)) (S (start + r)))
    (hroles : ∀ r, r < g → ∀ i, i < g →
      (phaseTwoView B hm (bits (start + r))
        (S (start + r)) (p i)).role = true) :
    ∀ i, i < g → (S (start + g) (p i)).x = B - g + i := by
  have hind : ∀ q, q < g → ∀ i, g - (q + 1) ≤ i → i < g →
      (S (start + q + 1) (p i)).x = B - g + i := by
    intro q
    induction q with
    | zero =>
        intro hq i hlo hi
        have hlast : i = g - 1 := by omega
        subst i
        have hs0 := cyclic_suffix_starts B hm
          (S (start + 0)) (bits (start + 0)) p g
          hB hg hgB hpath
          (hanchorStart 0 (by omega))
          (hanchorEnd 0 (by omega))
          (hinterior 0 (by omega))
          (hbounded 0 (by omega))
          (hroles 0 hq)
        calc
          (S (start + 0 + 1) (p (g - 1))).x =
              (logicalRound B hm (bits (start + 0))
                (S (start + 0)) (p (g - 1))).x := by
                  rw [hevol 0 hq]
          _ = B - 1 := hs0
          _ = B - g + (g - 1) := by omega
    | succ q ih =>
        intro hq i hlo hi
        have hprev : ∀ j, g - (q + 1) ≤ j → j < g →
            (S (start + (q + 1)) (p j)).x = B - g + j := by
          intro j hjlo hjhi
          have hh := ih (by omega) j hjlo hjhi
          simpa [Nat.add_assoc] using hh
        have hstep := cyclic_suffix_step B hm
          (S (start + (q + 1))) (bits (start + (q + 1)))
          p g (q + 1) hB hgB (by omega) (by omega) hpath
          (hanchorStart (q + 1) (by omega))
          (hanchorEnd (q + 1) (by omega))
          (hinterior (q + 1) (by omega))
          (hbounded (q + 1) (by omega))
          hprev
          (hroles (q + 1) hq)
        calc
          (S (start + (q + 1) + 1) (p i)).x =
              (logicalRound B hm (bits (start + (q + 1)))
                (S (start + (q + 1))) (p i)).x := by
                  rw [hevol (q + 1) hq]
          _ = B - g + i := hstep i hlo hi
  intro i hi
  have hh := hind (g - 1) (by omega) i (by omega) hi
  have heq : start + (g - 1) + 1 = start + g := by omega
  rw [heq] at hh
  exact hh

/-- The deterministic four-bit loss theorem. The HGAP assumptions state only
role persistence and broadcast timing, not the fill conclusion. The statement
also permits c=a, hence covers the two-anchor complementary-gap case. -/
theorem four_bit_loss {m : Nat}
    (B G T : Nat) (hm : 0 < m)
    (S : Nat → Fin m → Snapshot) (bits : Nat → Fin m → Bool)
    (a b c : Fin m)
    (pA pB : Nat → Fin m) (gA gB : Nat)
    (startA startB final : Nat)
    (drawAPen drawALast drawBPen drawBLast : Nat)
    (hwindow : T = 64 * (G + 1))
    (hgA : 1 ≤ gA) (hgB : 1 ≤ gB)
    (hgAG : gA ≤ G) (hgBG : gB ≤ G)
    (hgapSum : gA + gB ≤ m) (hmB : m < B)
    (hpathA : GapPath hm pA gA) (hpathB : GapPath hm pB gB)
    (hAStart : pA 0 = a) (hAEnd : pA gA = b)
    (hBStart : pB 0 = b) (hBEnd : pB gB = c)
    (hevol : ∀ t, t < T →
      S (t + 1) = logicalRound B hm (bits t) (S t))
    (hbounded : ∀ t, t ≤ T → Bounded B (S t))
    (hfixed : Fixed hm S T pA pB gA gB a b c)
    (hgapAWindow : startA + gA = final)
    (hgapBWindow : startB + gB = final)
    (hfinal : final ≤ T)
    (hdrawA : drawAPen < drawALast ∧ drawALast < T)
    (hdrawB : drawBPen < drawBLast ∧ drawBLast < T)
    (hbitAPen : bits drawAPen a = false)
    (hbitALast : bits drawALast a = false)
    (hbitBPen : bits drawBPen b = true)
    (hbitBLast : bits drawBLast b = true)
    (hgapA :
      bits drawAPen a = false → bits drawALast a = false →
      (∀ t, t ≤ T → NamedLive hm S t a b c) →
      ∀ r, r < gA → ∀ i, i ≤ r →
        (phaseTwoView B hm (bits (startA + r))
          (S (startA + r)) (pA i)).role = false)
    (hgapB :
      bits drawBPen b = true → bits drawBLast b = true →
      (∀ t, t ≤ T → NamedLive hm S t a b c) →
      ∀ r, r < gB → ∀ i, i < gB →
        (phaseTwoView B hm (bits (startB + r))
          (S (startB + r)) (pB i)).role = true) :
    ∃ t, t ≤ T ∧
      (¬ IsAnchor hm (S t) a ∨
       ¬ IsAnchor hm (S t) b ∨
       ¬ IsAnchor hm (S t) c) := by
  by_cases hlose : ∃ t, t ≤ T ∧
      (¬ IsAnchor hm (S t) a ∨
       ¬ IsAnchor hm (S t) b ∨
       ¬ IsAnchor hm (S t) c)
  · exact hlose
  · have hlive : ∀ t, t ≤ T → NamedLive hm S t a b c := by
      intro t ht
      have haLive : IsAnchor hm (S t) a := by
        by_cases ha : IsAnchor hm (S t) a
        · exact ha
        · exact False.elim (hlose ⟨t, ht, Or.inl ha⟩)
      have hbLive : IsAnchor hm (S t) b := by
        by_cases hb : IsAnchor hm (S t) b
        · exact hb
        · exact False.elim (hlose ⟨t, ht, Or.inr (Or.inl hb)⟩)
      have hcLive : IsAnchor hm (S t) c := by
        by_cases hc : IsAnchor hm (S t) c
        · exact hc
        · exact False.elim (hlose ⟨t, ht, Or.inr (Or.inr hc)⟩)
      exact ⟨haLive, hbLive, hcLive⟩
    have hBpos : 0 < B := by omega
    have hgABound : gA < B := by omega
    have hgBBound : gB < B := by omega
    have hrolesA := hgapA hbitAPen hbitALast hlive
    have hrolesB := hgapB hbitBPen hbitBLast hlive
    have hprefix := settled_prefix_rounds B hm S bits pA gA startA
      hBpos hgA hgABound hpathA
      (by
        intro r hr
        rw [hAStart]
        exact (hlive (startA + r) (by omega)).1)
      (by
        intro r hr
        rw [hAEnd]
        exact (hlive (startA + r) (by omega)).2.1)
      (by
        intro r hr i hiPos hiGap
        have hf := hfixed (startA + r) (by omega)
          (hlive (startA + r) (by omega))
        exact hf.1 i hiPos hiGap)
      (by
        intro r hr
        exact hbounded (startA + r) (by omega))
      (by
        intro r hr
        exact hevol (startA + r) (by omega))
      hrolesA
    have hsuffix := settled_suffix_grows B hm S bits pB gB startB
      hBpos hgB hgBBound hpathB
      (by
        intro r hr
        rw [hBStart]
        exact (hlive (startB + r) (by omega)).2.1)
      (by
        intro r hr
        rw [hBEnd]
        exact (hlive (startB + r) (by omega)).2.2)
      (by
        intro r hr i hiPos hiGap
        have hf := hfixed (startB + r) (by omega)
          (hlive (startB + r) (by omega))
        exact hf.2 i hiPos hiGap)
      (by
        intro r hr
        exact hbounded (startB + r) (by omega))
      (by
        intro r hr
        exact hevol (startB + r) (by omega))
      hrolesB
    have hleftHeight :
        (S final (pA (gA - 1))).x = gA - 1 := by
      have hh := hprefix (gA - 1) (by omega)
      rw [hgapAWindow] at hh
      exact hh
    have hrightHeight : (S final b).x = B - gB := by
      have hh := hsuffix 0 (by omega)
      rw [hgapBWindow, hBStart] at hh
      simpa using hh
    have hleftB : left hm b = pA (gA - 1) := by
      rw [← hAEnd]
      have hh := gap_left hm pA gA hpathA (gA - 1) (by omega)
      have heq : gA - 1 + 1 = gA := by omega
      simpa only [heq] using hh
    have hbAnchor := (hlive final hfinal).2.1
    unfold IsAnchor at hbAnchor
    rw [hrightHeight, hleftB, hleftHeight] at hbAnchor
    have hstrictFinal : gA - 1 < B - gB := by omega
    exact False.elim (by omega)

#print axioms phase_three_low_proposal
#print axioms phase_three_high_proposal
#print axioms phase_four_anchor_approves
#print axioms phase_four_nonanchor_approval
#print axioms phase_five_height
#print axioms low_anchor_proposes_zero
#print axioms high_before_anchor_proposes_top
#print axioms filled_edge_is_strict
#print axioms filled_edge_removes_b
#print axioms two_anchor_filled_edge_is_strict
#print axioms settled_prefix_grows
#print axioms settled_prefix_rounds
#print axioms settled_suffix_grows
#print axioms four_bit_loss

end L4.Height
