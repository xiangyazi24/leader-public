import Leader.L4.Height.Core

namespace L4.Height

open L4.Compiler.Native

variable {m : Nat}

@[simp] theorem left_right (hm : 0 < m) (i : Fin m) :
    left hm (right hm i) = i := by
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

@[simp] theorem right_left (hm : 0 < m) (i : Fin m) :
    right hm (left hm i) = i := by
  apply Fin.ext
  by_cases h0 : i.val = 0
  · simp only [right, left]
    rw [h0]
    simp only [Nat.zero_add]
    have hm1 : m - 1 < m := by omega
    rw [Nat.mod_eq_of_lt hm1]
    have he : m - 1 + 1 = m := by omega
    rw [he, Nat.mod_self]
  · have hi0 : 0 < i.val := Nat.pos_of_ne_zero h0
    have hlt : i.val - 1 < m := by omega
    have hl : (i.val + m - 1) % m = i.val - 1 := by
      have he : i.val + m - 1 = (i.val - 1) + m := by omega
      rw [he, Nat.add_mod]
      simp [Nat.mod_eq_of_lt hlt]
    simp only [left, hl, right]
    have he : i.val - 1 + 1 = i.val := by omega
    rw [he, Nat.mod_eq_of_lt i.isLt]

/-- A list maximum, with a witness retained in the list. -/
def listMax : List Nat → Nat
  | [] => 0
  | a :: l => if a < listMax l then listMax l else a

theorem listMax_mem : ∀ l, l ≠ [] → listMax l ∈ l := by
  intro l
  induction l with
  | nil => intro h; contradiction
  | cons a l ih =>
    intro hne
    by_cases h : a < listMax l
    · have hlt : l ≠ [] := by
        intro he
        subst l
        simp [listMax] at h
      have hm := ih hlt
      simp [listMax, h, hm]
    · simp [listMax, h]

theorem le_listMax_of_mem : ∀ {l a}, a ∈ l → a ≤ listMax l := by
  intro l
  induction l with
  | nil => intro a ha; simp at ha
  | cons b l ih =>
    intro a ha
    simp only [List.mem_cons] at ha
    by_cases h : b < listMax l
    · simp [listMax, h]
      rcases ha with rfl | ha
      · omega
      · exact ih ha
    · simp [listMax, h]
      rcases ha with rfl | ha
      · omega
      · have htail := ih ha
        omega

theorem anchor_exists (hm : 0 < m) (s : Fin m → Snapshot) :
    ∃ i, IsAnchor hm s i := by
  let vals := (List.finRange m).map (fun i => (s i).x)
  have hne : vals ≠ [] := by
    intro h
    have h0 : (⟨0, hm⟩ : Fin m) ∈ List.finRange m := by simp
    have hx : (s (⟨0, hm⟩ : Fin m)).x ∈ vals :=
      List.mem_map.mpr ⟨⟨0, hm⟩, h0, rfl⟩
    simp [vals, h] at hx
  have hmem := listMax_mem vals hne
  obtain ⟨i, hi, hval⟩ := List.mem_map.mp hmem
  have hmax : ∀ k : Fin m, (s k).x ≤ (s i).x := by
    intro k
    have hk : (s k).x ∈ vals :=
      List.mem_map.mpr ⟨k, by simp, rfl⟩
    have hle := le_listMax_of_mem hk
    simpa [vals, hval] using hle
  refine ⟨right hm i, ?_⟩
  change (s (right hm i)).x ≤ (s (left hm (right hm i))).x
  rw [left_right]
  exact hmax (right hm i)

theorem phaseStep_x_eq {B j : Nat} (hm : 0 < m)
    (bits : Fin m → Bool) (s : Fin m → Snapshot)
    (hj : j ≠ 5) (i : Fin m) :
    (phaseStep B j hm bits s i).x = (s i).x := by
  cases j with
  | zero => simp [phaseStep, phaseUpdate]
  | succ j =>
    cases j with
    | zero => simp [phaseStep, phaseUpdate]
    | succ j =>
      cases j with
      | zero => simp [phaseStep, phaseUpdate]
      | succ j =>
        cases j with
        | zero => simp [phaseStep, phaseUpdate]
        | succ j =>
          cases j with
          | zero => simp [phaseStep, phaseUpdate]
          | succ j =>
            cases j with
            | zero => exact False.elim (hj rfl)
            | succ j => simp [phaseStep, phaseUpdate]

theorem phaseStep_bounded_nonfinal (B j : Nat) (hm : 0 < m)
    (bits : Fin m → Bool) (s : Fin m → Snapshot)
    (hj : j ≠ 5) :
    Bounded B s → Bounded B (phaseStep B j hm bits s) := by
  intro hs i
  rw [phaseStep_x_eq hm bits s hj i]
  exact hs i

theorem phaseFive_x (B : Nat) (hm : 0 < m)
    (bits : Fin m → Bool) (s : Fin m → Snapshot) (i : Fin m) :
    (phaseStep B 5 hm bits s i).x =
      if (s i).approve && (s (right hm i)).approve
      then (s i).proposal else (s i).x := by
  simp [phaseStep, phaseUpdate]

theorem phaseStep5_bounded (B : Nat) (hm : 0 < m)
    (bits : Fin m → Bool) (s : Fin m → Snapshot)
    (hs : Bounded B s) (hp : ∀ i, (s i).proposal < B) :
    Bounded B (phaseStep B 5 hm bits s) := by
  intro i
  rw [phaseFive_x]
  split
  · exact hp i
  · exact hs i

theorem bounded_round (B : Nat) (hm : 0 < m) (hB : 0 < B)
    (bits : Fin m → Bool) (s : Fin m → Snapshot) :
    Bounded B s → Bounded B (logicalRound B hm bits s) := by
  intro hs
  let s0 := phaseStep B 0 hm bits s
  let s1 := phaseStep B 1 hm bits s0
  let s2 := phaseStep B 2 hm bits s1
  let s3 := phaseStep B 3 hm bits s2
  let s4 := phaseStep B 4 hm bits s3
  have hx0 : Bounded B s0 :=
    phaseStep_bounded_nonfinal B 0 hm bits s (by decide) hs
  have hx1 : Bounded B s1 :=
    phaseStep_bounded_nonfinal B 1 hm bits s0 (by decide) hx0
  have hx2 : Bounded B s2 :=
    phaseStep_bounded_nonfinal B 2 hm bits s1 (by decide) hx1
  have hx3 : Bounded B s3 :=
    phaseStep_bounded_nonfinal B 3 hm bits s2 (by decide) hx2
  have hx4 : Bounded B s4 :=
    phaseStep_bounded_nonfinal B 4 hm bits s3 (by decide) hx3
  have hp3 : ∀ i, (s3 i).proposal < B := by
    intro i
    simp only [s3, phaseStep, phaseUpdate]
    exact Nat.mod_lt _ hB
  have hp4 : ∀ i, (s4 i).proposal < B := by
    intro i
    simpa [s4, phaseStep, phaseUpdate] using hp3 i
  exact phaseStep5_bounded B hm bits s4 hx4 hp4

/-- Subtracting one after adding the positive modulus does not wrap. -/
theorem add_sub_mod (B x : Nat) (hB : 0 < B) (hx : 0 < x) (hxB : x < B) :
    (x + B - 1) % B = x - 1 := by
  have he : x + B - 1 = (x - 1) + B := by omega
  have hlt : x - 1 < B := by omega
  rw [he, Nat.add_mod]
  simp [Nat.mod_eq_of_lt hlt]

/-- On a strict edge, the proposals lie on opposite sides of the old edge. -/
theorem strict_edge_proposals (B : Nat) (hm : 0 < m)
    (hB : 0 < B) (hs : Bounded B s)
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
    rw [left_right hm i] at hle
    omega
  have hnotjP : ¬ (s2 (right hm i)).anchor = true := by
    simp [hnotj]
  constructor
  · rw [hproposal3 i]
    by_cases hr : (s2 i).role = true
    · rw [if_pos hr, if_neg hnotjP]
      rw [hx2 (right hm i)]
      rw [add_sub_mod B (s (right hm i)).x hB hxj0 hxj]
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
        have hBm1 : B - 1 < B := by omega
        rw [Nat.mod_eq_of_lt hBm1]
        omega
      · rw [if_neg ha]
        rw [hx2 (right hm (right hm i))]
        have hnotle :
            ¬ (s (right hm (right hm i))).x ≤ (s (right hm i)).x := by
          intro hle
          apply ha
          rw [hanchor2 (right hm (right hm i))]
          rw [left_right hm (right hm i)]
          exact decide_eq_true hle
        have hnext :
            (s (right hm i)).x < (s (right hm (right hm i))).x := by
          omega
        have hpos : 0 < (s (right hm (right hm i))).x := by omega
        have hmod := add_sub_mod B (s (right hm (right hm i))).x
          hB hpos (hs _)
        rw [hmod]
        omega
    · rw [if_neg hr, if_neg hnotjP]
      rw [left_right hm i]
      rw [hx2 i]
      have hlt : (s i).x + 1 < B := by omega
      rw [Nat.mod_eq_of_lt hlt]
      omega

/-- The strict edge remains strict after the simultaneous phase-5 update. -/
theorem strict_edge_survives (B : Nat) (hm : 0 < m)
    (hB : 0 < B) (hs : Bounded B s)
    (bits : Fin m → Bool) (i : Fin m)
    (hstrict : (s i).x < (s (right hm i)).x) :
    (logicalRound B hm bits s i).x <
      (logicalRound B hm bits s (right hm i)).x := by
  let s0 := phaseStep B 0 hm bits s
  let s1 := phaseStep B 1 hm bits s0
  let s2 := phaseStep B 2 hm bits s1
  let s3 := phaseStep B 3 hm bits s2
  let s4 := phaseStep B 4 hm bits s3
  have hp :
      (s3 i).proposal < (s (right hm i)).x ∧
      (s i).x < (s3 (right hm i)).proposal := by
    simpa [s3, s2, s1, s0] using
      (strict_edge_proposals B hm hB hs bits i hstrict)
  have hanchor3 (k : Fin m) :
      (s3 k).anchor = decide ((s k).x ≤ (s (left hm k)).x) := by
    simp [s3, s2, s1, s0, phaseStep, phaseUpdate]
  have hrightAnchor : (s3 (right hm i)).anchor = false := by
    rw [hanchor3 (right hm i)]
    apply Bool.eq_false_iff.mpr
    intro hd
    have hle :
        (s (right hm i)).x ≤ (s (left hm (right hm i))).x :=
      of_decide_eq_true hd
    rw [left_right hm i] at hle
    omega
  have hrightApprove :
      (s4 (right hm i)).approve =
        decide ((s3 i).proposal < (s3 (right hm i)).proposal) := by
    simp [s4, phaseStep, phaseUpdate, left_right, hrightAnchor]
  have hx4 (k : Fin m) : (s4 k).x = (s k).x := by
    simp [s4, s3, s2, s1, s0, phaseStep, phaseUpdate]
  have hproposal4 (k : Fin m) : (s4 k).proposal = (s3 k).proposal := by
    simp [s4, phaseStep, phaseUpdate]
  change (phaseStep B 5 hm bits s4 i).x <
    (phaseStep B 5 hm bits s4 (right hm i)).x
  rw [phaseFive_x, phaseFive_x]
  by_cases aj : (s4 (right hm i)).approve = true
  · by_cases ai : (s4 i).approve = true
    · by_cases ak : (s4 (right hm (right hm i))).approve = true
      · have hdec :
            decide ((s3 i).proposal < (s3 (right hm i)).proposal) = true := by
          rw [← hrightApprove]
          exact aj
        have hcmp : (s3 i).proposal < (s3 (right hm i)).proposal :=
          of_decide_eq_true hdec
        simpa [ai, aj, ak, hx4, hproposal4] using hcmp
      · have akf : (s4 (right hm (right hm i))).approve = false :=
          Bool.eq_false_iff.mpr ak
        simpa [ai, aj, akf, hx4, hproposal4] using hp.1
    · have aif : (s4 i).approve = false := Bool.eq_false_iff.mpr ai
      by_cases ak : (s4 (right hm (right hm i))).approve = true
      · simpa [aif, aj, ak, hx4, hproposal4] using hp.2
      · have akf : (s4 (right hm (right hm i))).approve = false :=
          Bool.eq_false_iff.mpr ak
        simpa [aif, aj, akf, hx4, hproposal4] using hstrict
  · have ajf : (s4 (right hm i)).approve = false := Bool.eq_false_iff.mpr aj
    simpa [ajf, hx4] using hstrict

theorem anchor_mono (B : Nat) (hm : 0 < m) (hmb : m < B)
    (bits : Fin m → Bool) (s : Fin m → Snapshot)
    (hs : Bounded B s) :
    ∀ i, IsAnchor hm (logicalRound B hm bits s) i → IsAnchor hm s i := by
  have hB : 0 < B := by omega
  intro i hnew
  by_cases hold : IsAnchor hm s i
  · exact hold
  · have hstrict : (s (left hm i)).x < (s i).x := by
      unfold IsAnchor at hold
      omega
    have hstrict' :
        (s (left hm i)).x < (s (right hm (left hm i))).x := by
      simpa only [right_left hm i] using hstrict
    have hsurv :=
      strict_edge_survives B hm hB hs bits (left hm i) hstrict'
    rw [right_left hm i] at hsurv
    unfold IsAnchor at hnew
    omega

theorem countP_le_of_imp {α : Type} (l : List α) (p q : α → Bool) :
    (∀ a, a ∈ l → p a = true → q a = true) →
      l.countP p ≤ l.countP q := by
  intro h
  apply List.countP_mono_left
  intro a ha hp
  exact h a ha hp

theorem anchorCount_mono (B : Nat) (hm : 0 < m) (hmb : m < B)
    (bits : Fin m → Bool) (s : Fin m → Snapshot)
    (hs : Bounded B s) :
    anchorCount hm (logicalRound B hm bits s) ≤ anchorCount hm s := by
  unfold anchorCount
  apply countP_le_of_imp
  intro i hi hp
  have hnew : IsAnchor hm (logicalRound B hm bits s) i :=
    of_decide_eq_true hp
  have hold : IsAnchor hm s i :=
    anchor_mono B hm hmb bits s hs i hnew
  exact decide_eq_true hold

theorem single_anchor_stable (B : Nat) (hm : 0 < m) (hmb : m < B)
    (bits : Fin m → Bool) (s : Fin m → Snapshot) (i : Fin m)
    (hs : Bounded B s)
    (honly : ∀ j, IsAnchor hm s j ↔ j = i) :
    (∀ j, IsAnchor hm (logicalRound B hm bits s) j ↔ j = i) := by
  intro j
  constructor
  · intro hj
    have hold := anchor_mono B hm hmb bits s hs j hj
    exact (honly j).mp hold
  · intro hji
    subst j
    obtain ⟨k, hk⟩ := anchor_exists hm (logicalRound B hm bits s)
    have hkold := anchor_mono B hm hmb bits s hs k hk
    have hki := (honly k).mp hkold
    subst k
    exact hk

theorem single_anchor_runRounds (B : Nat) (hm : 0 < m) (hmb : m < B)
    (bs : List (Fin m → Bool)) (s : Fin m → Snapshot) (i : Fin m)
    (hs : Bounded B s)
    (honly : ∀ j, IsAnchor hm s j ↔ j = i) :
    ∀ j, IsAnchor hm (runRounds B hm bs s) j ↔ j = i := by
  induction bs generalizing s with
  | nil =>
      intro j
      change IsAnchor hm s j ↔ j = i
      exact honly j
  | cons bits rest ih =>
      rw [runRounds_cons]
      apply ih
      · exact bounded_round B hm (by omega) bits s hs
      · exact single_anchor_stable B hm hmb bits s i hs honly

end L4.Height
