import Leader.Wu.Elimination.LabelFreeSignalEntry

/-!
# Total signal-order entry in the closed nearest-support domain

The physical row remains `LabelFreeElimination.step`. The potential is
indexed by actual ring sites, so deleting a leader does not reset a clock or
assume equality with a future canonical enumeration.
-/

namespace K2PeacefulSignalEntry

open PPLLRepair LDSinkGapCleanup LDSinkKernelC K2OutputSafety
open PPLLNoCheckBirthConditionTwoGeometry K2PeacefulGlobal
open LabelFreeElimination LabelFreeSignalEntry K2GlobalGapClosure K2CyclicLayout
open StateBoundUnifiedCell FiniteUniformStoppingTree LDTwoGapFrame

set_option autoImplicit false

variable {n ψ κ : Nat}

theorem psPosZero (G : GapFrame n) : G.pos 0 = G.low := by
  apply Fin.ext
  simp [GapFrame.pos, Nat.mod_eq_of_lt G.low.isLt]

/-- Rotated support coordinates agree with the actual gap coordinates. -/
theorem psSupportPos (ring : DirectedRing n) (G : GapFrame n) (t : Nat) :
    cwPos ring (G.pos 1) t = G.pos (1 + t) := by
  apply Fin.ext
  change (((G.low.val + 1) % n + t) % n) = (G.low.val + (1 + t)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]

/-- An actual nearest support from offset one ends exactly at the next
leader, including gaps which cross the physical ring's numeric origin. -/
theorem psSupportDistance (ring : DirectedRing n) (G : GapFrame n)
    (C : Fin n → AgentState 1) (hE : GapEndpointsPresent G C)
    (hI : GapInteriorFollowers G C) (d : Nat) (hs : Support ring C (G.pos 1) d) :
    d + 1 = G.d := by
  have hd2 := G.hd
  rcases Nat.lt_trichotomy (d + 1) G.d with h | h | h
  · have hf := hI (d + 1) (by omega) h
    have ht := hs.target_leader
    rw [psSupportPos, Nat.add_comm 1 d, hf] at ht
    cases ht
  · exact h
  · have hf := hs.before_follower (G.d - 1) (by omega)
    rw [psSupportPos, Nat.add_sub_cancel' (by omega : 1 ≤ G.d), hE.2] at hf
    cases hf

/-- Every signal in the attack gap is zero at a live killer. This conclusion
is derived from nearest-target geometry, without a signal-order premise. -/
theorem psKillerSuffix (ring : DirectedRing n) (G : GapFrame n)
    (C : Fin n → AgentState 1) (hE : GapEndpointsPresent G C)
    (hI : GapInteriorFollowers G C) (hp : NearestPeaceful ring C)
    (hb : (C (G.pos 1)).bullet = 2) :
    ∀ j, 1 ≤ j → j ≤ G.d → (C (G.pos j)).signal_B = 0 := by
  obtain ⟨d, hs⟩ := hp (G.pos 1) hb
  have hd := psSupportDistance ring G C hE hI d hs
  intro j hj hjd
  have hz := hs.signal_zero (j - 1) (by omega)
  rw [psSupportPos, Nat.add_sub_cancel' hj] at hz
  exact hz

theorem psKillerTopsZero (ring : DirectedRing n) (G : GapFrame n)
    (C : Fin n → AgentState 1) (hE : GapEndpointsPresent G C)
    (hI : GapInteriorFollowers G C) (hp : NearestPeaceful ring C)
    (hb : (C (G.pos 1)).bullet = 2) :
    signalTop G C = 0 ∧ badTop G C = 0 := by
  have hz := psKillerSuffix ring G C hE hI hp hb
  constructor
  · apply Nat.eq_zero_of_le_zero
    apply topIdx_le_of
    intro j hj hjd
    simp only [hz j hj hjd, Fin.val_zero]
    rfl
  · apply (badTop_zero_iff G C).mpr
    intro i j hi _ _ hij hjd
    exact hz j (by omega) hjd

/-- Inside nearest peacefulness an actual deletion adds no merge debt. -/
theorem psDeletionMerge (hψ : 0 < ψ) (F : TwoGapFrame n)
    (C : Fin n → UCell ψ κ) (hE : GapEndpointsPresent F.attack (physicalConfig C))
    (hI : GapInteriorFollowers F.attack (physicalConfig C))
    (hp : PeacefulGlobal F.attack.ring C)
    (hd : (LabelFreeElimination.step hψ F.attack.ring C (F.attack.pos 0) (F.attack.pos 0)).legacy.leader = false) :
    badTop (merged F) (physicalConfig (LabelFreeElimination.step hψ F.attack.ring C (F.attack.pos 0))) =
      badTop F.recovery (physicalConfig C) := by
  have hrow : (sinkKernelC (by decide) (observe C (F.attack.pos 0))
      (observe C (F.attack.pos 1))).1.leader = false := by
    have hh : (observe (LabelFreeElimination.step hψ F.attack.ring C (F.attack.pos 0))
        (F.attack.pos 0)).leader = false := hd
    rw [observe_step] at hh
    simpa [rawStep, updatePair, GapFrame.rightNeighbor_pos] using hh
  have hb := ((kernel_delete_iff (by decide) (observe C (F.attack.pos 0))
    (observe C (F.attack.pos 1)) hE.1
    (hI 1 (by omega) (by have := F.attack.hd; omega))).mp hrow).2.2
  have hz := psKillerTopsZero F.attack.ring F.attack (observe C) hE hI hp.2 hb
  have hm := deletion_merge_badTop hψ F C hE hI hd
  change signalTop F.attack (physicalConfig C) = 0 ∧ badTop F.attack (physicalConfig C) = 0 at hz
  simpa only [hz.1, hz.2, if_true, Nat.max_zero] using hm


/-! ## A sum over actual leader sites, independent of enumeration -/

theorem psClass (ring : DirectedRing n) (C : Fin n → UCell ψ κ)
    (hs : Separated ring (physicalConfig C)) (hc : 2 ≤ K2FiniteProgress.count C) :
    SeparatedClass ring (K2FiniteProgress.count C) C := ⟨hc, rfl, hs⟩

noncomputable def psGap (ring : DirectedRing n) (C : Fin n → UCell ψ κ)
    (hs : Separated ring (physicalConfig C)) (hc : 2 ≤ K2FiniteProgress.count C)
    (v : Fin n) (hv : (C v).legacy.leader = true) : GapFrame n :=
  (layout ring C (psClass ring C hs hc)).gap
    (Classical.choose (leaderAt_complete (physicalConfig C) rfl v hv))

theorem psGapLow (ring : DirectedRing n) (C : Fin n → UCell ψ κ)
    (hs : Separated ring (physicalConfig C)) (hc : 2 ≤ K2FiniteProgress.count C)
    (v : Fin n) (hv : (C v).legacy.leader = true) : (psGap ring C hs hc v hv).low = v :=
  Classical.choose_spec (leaderAt_complete (physicalConfig C) rfl v hv)

theorem psGapReal (ring : DirectedRing n) (C : Fin n → UCell ψ κ)
    (hs : Separated ring (physicalConfig C)) (hc : 2 ≤ K2FiniteProgress.count C)
    (v : Fin n) (hv : (C v).legacy.leader = true) :
    GapEndpointsPresent (psGap ring C hs hc v hv) (physicalConfig C) ∧
    GapInteriorFollowers (psGap ring C hs hc v hv) (physicalConfig C) :=
  layout_real ring C (psClass ring C hs hc) _

/-- Followers contribute zero; a leader contributes its real outgoing gap's
badTop. No leader enumeration is retained as a state field. -/
noncomputable def psVertexTop (ring : DirectedRing n) (C : Fin n → UCell ψ κ)
    (hs : Separated ring (physicalConfig C)) (hc : 2 ≤ K2FiniteProgress.count C) (v : Fin n) : Nat := by
  classical
  exact if hv : (C v).legacy.leader = true then badTop (psGap ring C hs hc v hv) (physicalConfig C) else 0

theorem psVertexGap (ring : DirectedRing n) (C : Fin n → UCell ψ κ)
    (hs : Separated ring (physicalConfig C)) (hc : 2 ≤ K2FiniteProgress.count C)
    (G : GapFrame n) (hE : GapEndpointsPresent G (physicalConfig C))
    (hI : GapInteriorFollowers G (physicalConfig C)) :
    psVertexTop ring C hs hc G.low = badTop G (physicalConfig C) := by
  classical
  have hv : (C G.low).legacy.leader = true := by
    have hh := hE.1
    rw [psPosZero] at hh
    exact hh
  simp only [psVertexTop, dif_pos hv]
  have hg := psGapReal ring C hs hc G.low hv
  rw [frame_unique (psGap ring C hs hc G.low hv) G (physicalConfig C)
    hg.1 hg.2 hE hI (psGapLow ring C hs hc G.low hv)]

noncomputable def psRank (ring : DirectedRing n) (C : Fin n → UCell ψ κ)
    (hs : Separated ring (physicalConfig C)) (hc : 2 ≤ K2FiniteProgress.count C) : Nat :=
  (List.ofFn (psVertexTop ring C hs hc)).sum

private theorem psFilterSum {A : Type} (xs : List A) (P : A → Bool) (f : A → Nat)
    (h : ∀ a, P a = false → f a = 0) :
    ((xs.filter P).map f).sum = (xs.map f).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases ha : P a
    · simp only [List.filter_cons, ha, Bool.false_eq_true, ↓reduceIte, List.map_cons,
        List.sum_cons, h a ha, Nat.zero_add, ih]
    · simp only [List.filter_cons, ha, ↓reduceIte, List.map_cons, List.sum_cons, ih]

private theorem psLeaderEnumeration (C : Fin n → UCell ψ κ) :
    List.ofFn (leaderAt (physicalConfig C) (rfl : K2FiniteProgress.count C = K2FiniteProgress.count C)) =
      leaderSites (physicalConfig C) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, leaderSites_length]
  · intro i hi hj
    rw [List.getElem_ofFn]
    rfl

/-- The site sum equals the sum over the actual current canonical layout.
This equality is proved afresh for each physical configuration. -/
theorem psRankLayout (ring : DirectedRing n) (C : Fin n → UCell ψ κ)
    (hs : Separated ring (physicalConfig C)) (hc : 2 ≤ K2FiniteProgress.count C) :
    psRank ring C hs hc = signalDisorder (layout ring C (psClass ring C hs hc)) C := by
  classical
  let f := psVertexTop ring C hs hc
  have hh := psFilterSum (List.ofFn (fun i : Fin n => i))
    (fun i => (C i).legacy.leader) f (fun i hi => by simp [f, psVertexTop, hi])
  change ((leaderSites (physicalConfig C)).map f).sum = _ at hh
  rw [← psLeaderEnumeration C, List.map_ofFn, List.map_ofFn] at hh
  have he := FiniteUniformStoppingTree.ofFn_sum_eq
    (fun i => f (leaderAt (physicalConfig C) rfl i))
    (fun i => badTop ((layout ring C (psClass ring C hs hc)).gap i) (physicalConfig C))
    (fun i => psVertexGap ring C hs hc _ (layout_real ring C (psClass ring C hs hc) i).1
      (layout_real ring C (psClass ring C hs hc) i).2)
  exact hh.symm.trans he

theorem psRankLe (ring : DirectedRing n) (C : Fin n → UCell ψ κ)
    (hs : Separated ring (physicalConfig C)) (hc : 2 ≤ K2FiniteProgress.count C) :
    psRank ring C hs hc ≤ n := by
  rw [psRankLayout]
  exact signalDisorder_le _ C

theorem psRankZero (ring : DirectedRing n) (C : Fin n → UCell ψ κ)
    (hs : Separated ring (physicalConfig C)) (hc : 2 ≤ K2FiniteProgress.count C) :
    psRank ring C hs hc = 0 ↔ SignalGlobal ring C := by
  rw [psRankLayout]
  exact signalDisorder_zero_iff ring C C (psClass ring C hs hc) (fun _ => rfl)

theorem psSeparatedStep (hψ : 0 < ψ) (ring : DirectedRing n) (C : Fin n → UCell ψ κ)
    (hs : Separated ring (physicalConfig C)) (e : Fin n) :
    Separated ring (physicalConfig (LabelFreeElimination.step hψ ring C e)) := by
  have hn := K2FiniteProgress.step_noNew hψ ring C e
  intro i hi
  have ho : (C i).legacy.leader = true := by
    cases hh : (C i).legacy.leader
    · have hf := hn i hh
      change (LabelFreeElimination.step hψ ring C e i).legacy.leader = true at hi
      rw [hi] at hf
      cases hf
    · rfl
  exact hn _ (hs i ho)


/-! ## Actual predecessor frames of a post-deletion gap -/

private theorem psFrameExt (G H : GapFrame n) (hl : G.low = H.low) (hd : G.d = H.d) : G = H := by
  cases G with
  | mk gr gl gd gh gn =>
    cases H with
    | mk hr hl' hd' hh hn =>
      dsimp only at hl hd
      subst hl'
      subst hd'
      have he : gr = hr := by cases gr; cases hr; rfl
      cases he
      rfl

private theorem psRightPos (ring : DirectedRing n) (G : GapFrame n) (t : Nat) :
    ring.rightNeighbor (G.pos t) = G.pos (t + 1) := by
  have hr : ring = G.ring := by cases ring; cases G.ring; rfl
  rw [hr, GapFrame.rightNeighbor_pos]

/-- Split a real post-deletion frame at its one old interior leader. The
two old lengths, their separation bounds, sharing, and strict total length
are derived from this actual geometry. -/
theorem psSplitAt (ring : DirectedRing n) (G : GapFrame n) (C : Fin n → AgentState ψ)
    (hs : Separated ring C) (hE : GapEndpointsPresent G C)
    (a : Nat) (ha1 : 1 ≤ a) (had : a < G.d) (ha : (C (G.pos a)).leader = true)
    (hI : ∀ t, 1 ≤ t → t < G.d → t ≠ a → (C (G.pos t)).leader = false) :
    ∃ F : TwoGapFrame n, merged F = G ∧ F.attack.pos 0 = G.pos a ∧
      GapEndpointsPresent F.recovery C ∧ GapInteriorFollowers F.recovery C ∧
      GapEndpointsPresent F.attack C ∧ GapInteriorFollowers F.attack C := by
  have ha2 : 2 ≤ a := by
    by_cases he : a = 1
    · have hf := hs (G.pos 0) hE.1
      rw [psRightPos] at hf
      rw [he] at ha
      rw [ha] at hf
      cases hf
    · omega
  have hb2 : 2 ≤ G.d - a := by
    by_cases he : G.d = a + 1
    · have hf := hs (G.pos a) ha
      rw [psRightPos, ← he, hE.2] at hf
      cases hf
    · omega
  let L : GapFrame n := ⟨G.ring, G.low, a, ha2, by have := G.hdn; omega⟩
  let R : GapFrame n := ⟨G.ring, G.pos a, G.d - a, hb2, by have := G.hdn; omega⟩
  have hlpos : ∀ t, L.pos t = G.pos t := fun _ => rfl
  have hrpos : ∀ t, R.pos t = G.pos (a + t) := by
    intro t
    apply Fin.ext
    change (((G.low.val + a) % n + t) % n) = (G.low.val + (a + t)) % n
    rw [Nat.mod_add_mod, Nat.add_assoc]
  have hshare : L.pos L.d = R.pos 0 := by rw [hlpos, hrpos, Nat.add_zero]
  let F : TwoGapFrame n := ⟨L, R, hshare, by change a + (G.d - a) < n; have := G.hdn; omega⟩
  refine ⟨F, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply psFrameExt
    · rfl
    · change a + (G.d - a) = G.d
      omega
  · exact (hrpos 0).trans (by rw [Nat.add_zero])
  · exact ⟨hE.1, ha⟩
  · intro t ht htd
    exact hI t ht (by change t < a at htd; omega) (by change t < a at htd; omega)
  · change (C (R.pos 0)).leader = true ∧ (C (R.pos (G.d - a))).leader = true
    rw [hrpos, Nat.add_zero, hrpos, Nat.add_sub_cancel' (by omega : a ≤ G.d)]
    exact ⟨ha, hE.2⟩
  · intro t ht htd
    change (C (R.pos t)).leader = false
    rw [hrpos]
    exact hI (a + t) (by omega) (by change t < G.d - a at htd; omega) (by omega)

/-- One real post-step gap is either an old gap or the exact union of two
old gaps through the deleted source. No untouched-gap validity is assumed. -/
theorem psVertexStepLe (hψ : 0 < ψ) (ring : DirectedRing n) (C : Fin n → UCell ψ κ)
    (hs : Separated ring (physicalConfig C)) (hc : 2 ≤ K2FiniteProgress.count C)
    (hp : PeacefulGlobal ring C) (e v : Fin n)
    (hdc : 2 ≤ K2FiniteProgress.count (LabelFreeElimination.step hψ ring C e)) :
    psVertexTop ring (LabelFreeElimination.step hψ ring C e) (psSeparatedStep hψ ring C hs e) hdc v ≤
      psVertexTop ring C hs hc v := by
  classical
  let D := LabelFreeElimination.step hψ ring C e
  have hsD := psSeparatedStep hψ ring C hs e
  by_cases hv : (D v).legacy.leader = true
  · let G := psGap ring D hsD hdc v hv
    have hG := psGapReal ring D hsD hdc v hv
    have hlow := psGapLow ring D hsD hdc v hv
    have htop : psVertexTop ring D hsD hdc v = badTop G (physicalConfig D) := by
      rw [← hlow]
      exact psVertexGap ring D hsD hdc G hG.1 hG.2
    rw [htop]
    have hcases := rawStep_layout_cases (by decide) ring (observe C) e
    rw [← observe_step hψ ring C e] at hcases
    have hE : GapEndpointsPresent G (physicalConfig C) := by
      have hno := K2FiniteProgress.step_noNew hψ ring C e
      constructor
      · cases hh : (C (G.pos 0)).legacy.leader
        · have hf := hno _ hh
          have hh' := hG.1.1
          change (D (G.pos 0)).legacy.leader = false at hf
          exact Bool.noConfusion (hf.symm.trans hh')
        · exact hh
      · cases hh : (C (G.pos G.d)).legacy.leader
        · have hf := hno _ hh
          have hh' := hG.1.2
          change (D (G.pos G.d)).legacy.leader = false at hf
          exact Bool.noConfusion (hf.symm.trans hh')
        · exact hh
    have hold : GapInteriorFollowers G (physicalConfig C) →
        badTop G (physicalConfig D) ≤ psVertexTop ring C hs hc v := by
      intro hI
      rw [← hlow, psVertexGap ring C hs hc G hE hI]
      have hn : ¬ EndpointDeleted G (observe D) := by
        rintro (hh | hh)
        · exact Bool.noConfusion (hG.1.1.symm.trans hh)
        · exact Bool.noConfusion (hG.1.2.symm.trans hh)
      have hr : ring = G.ring := by cases ring; cases G.ring; rfl
      change badTop G (observe D) ≤ badTop G (observe C)
      dsimp only [D] at hn ⊢
      rw [observe_step, hr] at hn ⊢
      exact badTop_step_le G (observe C) hE hI e hn
    rcases hcases with hsame | ⟨hsource, hdelete, haway⟩
    · apply hold
      intro t ht htd
      exact (hsame _).symm.trans (hG.2 t ht htd)
    · by_cases he : ∃ a, 1 ≤ a ∧ a < G.d ∧ G.pos a = e
      · obtain ⟨a, ha1, had, hae⟩ := he
        have hint : ∀ t, 1 ≤ t → t < G.d → t ≠ a →
            (physicalConfig C (G.pos t)).leader = false := by
          intro t ht htd hta
          have hne : G.pos t ≠ e := by
            rw [← hae]
            exact G.pos_ne (by have := G.hdn; omega) (by have := G.hdn; omega) hta
          exact (haway _ hne).symm.trans (hG.2 t ht htd)
        obtain ⟨F, hm, heF, hrE, hrI, haE, haI⟩ := psSplitAt ring G (physicalConfig C)
          hs hE a ha1 had (by rw [hae]; exact hsource) hint
        have heq : F.attack.pos 0 = e := heF.trans hae
        have hr : ring = F.attack.ring := by cases ring; cases F.attack.ring; rfl
        have hp' : PeacefulGlobal F.attack.ring C := by rw [← hr]; exact hp
        have hd' : (LabelFreeElimination.step hψ F.attack.ring C (F.attack.pos 0) (F.attack.pos 0)).legacy.leader = false := by
          rw [← hr, heq]
          exact hdelete
        have hh := psDeletionMerge hψ F C haE haI hp' hd'
        rw [hm, ← hr, heq] at hh
        change badTop G (physicalConfig D) = badTop F.recovery (physicalConfig C) at hh
        rw [hh]
        have hlo : F.recovery.low = v := (congrArg GapFrame.low hm).trans hlow
        rw [← hlo, psVertexGap ring C hs hc F.recovery hrE hrI]
        exact Nat.le_refl _
      · apply hold
        intro t ht htd
        have hne : G.pos t ≠ e := fun hh => he ⟨t, ht, htd, hh⟩
        exact (haway _ hne).symm.trans (hG.2 t ht htd)
  · have hv' : ¬ (LabelFreeElimination.step hψ ring C e v).legacy.leader = true := hv
    simp only [psVertexTop, dif_neg hv']
    exact Nat.zero_le _

theorem psRankStepLe (hψ : 0 < ψ) (ring : DirectedRing n) (C : Fin n → UCell ψ κ)
    (hs : Separated ring (physicalConfig C)) (hc : 2 ≤ K2FiniteProgress.count C)
    (hp : PeacefulGlobal ring C) (e : Fin n)
    (hdc : 2 ≤ K2FiniteProgress.count (LabelFreeElimination.step hψ ring C e)) :
    psRank ring (LabelFreeElimination.step hψ ring C e) (psSeparatedStep hψ ring C hs e) hdc ≤
      psRank ring C hs hc :=
  FiniteUniformStoppingTree.ofFn_sum_le _ _ (fun v => psVertexStepLe hψ ring C hs hc hp e v hdc)


/-! ## Strict service without any deletion restart -/

/-- The predecessor of a positive badTop cannot delete a leader in the
nearest-support domain: an actual live killer would force that gap's top
to zero. Interior source sites are actual followers. -/
theorem psTargetSameLeaders (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (G : GapFrame n)
    (hE : GapEndpointsPresent G (physicalConfig C)) (hI : GapInteriorFollowers G (physicalConfig C))
    (hp : PeacefulGlobal ring C) (hb : 0 < badTop G (physicalConfig C)) :
    SameLeaders C (LabelFreeElimination.step hψ ring C (G.pos (badTop G (physicalConfig C) - 1))) := by
  let b := badTop G (physicalConfig C)
  have hbd : b ≤ G.d := badTop_le G (physicalConfig C)
  have hh := rawStep_layout_cases (by decide) ring (observe C) (G.pos (b - 1))
  rw [← observe_step hψ ring C (G.pos (b - 1))] at hh
  rcases hh with hh | ⟨hl, hd, _⟩
  · exact hh
  · by_cases he : b = 1
    · have he' : b - 1 = 0 := by omega
      rw [he'] at hd
      have hrow : (sinkKernelC (by decide) (observe C (G.pos 0)) (observe C (G.pos 1))).1.leader = false := by
        rw [observe_step] at hd
        simpa [rawStep, updatePair, psRightPos] using hd
      have hkill := ((kernel_delete_iff (by decide) (observe C (G.pos 0)) (observe C (G.pos 1))
        hE.1 (hI 1 (by omega) (by have := G.hd; omega))).mp hrow).2.2
      have hz := (psKillerTopsZero ring G (observe C) hE hI hp.2 hkill).2
      change badTop G (physicalConfig C) = 0 at hz
      omega
    · have hf := hI (b - 1) (by change 0 < b at hb; omega) (by omega)
      exact Bool.noConfusion (hf.symm.trans hl)

private theorem psSumPositive {m : Nat} (f : Fin m → Nat) (hp : 0 < (List.ofFn f).sum) :
    ∃ i, 0 < f i := by
  classical
  apply Classical.byContradiction
  intro hn
  have hz : ∀ i, f i = 0 := by
    intro i
    have hh : ¬ 0 < f i := fun hi => hn ⟨i, hi⟩
    omega
  have hh := FiniteUniformStoppingTree.ofFn_sum_eq f (fun _ => 0) hz
  rw [FiniteUniformStoppingTree.ofFn_sum_const, Nat.mul_zero] at hh
  omega

private theorem psSumStrict {m : Nat} (f g : Fin m → Nat)
    (hle : ∀ i, f i ≤ g i) (v : Fin m) (hv : f v < g v) :
    (List.ofFn f).sum < (List.ofFn g).sum := by
  induction m with
  | zero => exact Fin.elim0 v
  | succ m ih =>
    rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
    revert hv
    refine Fin.cases ?_ (fun j => ?_) v
    · intro hv
      have ht := FiniteUniformStoppingTree.ofFn_sum_le (fun i => f i.succ) (fun i => g i.succ)
        (fun i => hle i.succ)
      omega
    · intro hv
      have ht := ih (fun i => f i.succ) (fun i => g i.succ) (fun i => hle i.succ) j hv
      have hz := hle 0
      omega

/-- A positive current global rank has a real strict target edge. All
leader bits survive this particular edge, so no per-deletion budget is paid. -/
theorem psRankTarget (hψ : 0 < ψ) (ring : DirectedRing n) (C : Fin n → UCell ψ κ)
    (hs : Separated ring (physicalConfig C)) (hc : 2 ≤ K2FiniteProgress.count C)
    (hp : PeacefulGlobal ring C) (hpos : 0 < psRank ring C hs hc) :
    ∃ e, SameLeaders C (LabelFreeElimination.step hψ ring C e) ∧
      ∀ hdc : 2 ≤ K2FiniteProgress.count (LabelFreeElimination.step hψ ring C e),
        psRank ring (LabelFreeElimination.step hψ ring C e) (psSeparatedStep hψ ring C hs e) hdc <
          psRank ring C hs hc := by
  classical
  obtain ⟨v, hv⟩ := psSumPositive (psVertexTop ring C hs hc) hpos
  have hl : (C v).legacy.leader = true := by
    by_cases hl : (C v).legacy.leader = true
    · exact hl
    · simp only [psVertexTop, dif_neg hl] at hv
      omega
  let G := psGap ring C hs hc v hl
  have hG := psGapReal ring C hs hc v hl
  have hbad : 0 < badTop G (physicalConfig C) := by
    simpa only [psVertexTop, dif_pos hl] using hv
  let e := G.pos (badTop G (physicalConfig C) - 1)
  have hsame := psTargetSameLeaders hψ ring C G hG.1 hG.2 hp hbad
  refine ⟨e, hsame, ?_⟩
  intro hdc
  have hGD := sameLeaders_shape C _ hsame G hG.1 hG.2
  apply psSumStrict _ _ (fun i => psVertexStepLe hψ ring C hs hc hp e i hdc) G.low
  rw [psVertexGap ring _ _ hdc G hGD.1 hGD.2, psVertexGap ring C hs hc G hG.1 hG.2]
  have hkeep : ¬ EndpointDeleted G (observe (LabelFreeElimination.step hψ ring C e)) := by
    rintro (hd | hd)
    · exact Bool.noConfusion (hGD.1.1.symm.trans hd)
    · exact Bool.noConfusion (hGD.1.2.symm.trans hd)
  have hr : ring = G.ring := by cases ring; cases G.ring; rfl
  change badTop G (observe (LabelFreeElimination.step hψ ring C e)) < badTop G (observe C)
  rw [observe_step, hr] at hkeep ⊢
  exact (badTop_target G (observe C) hG.1 hG.2 hbad).resolve_left hkeep


/-! ## The original finite scheduler, stopped on entry or safe count one -/

def psDone (ring : DirectedRing n) (C : Fin n → UCell ψ κ) : Prop :=
  SignalGlobal ring C ∨ K2FiniteProgress.count C = 1

def psReached (hψ : 0 < ψ) (ring : DirectedRing n) (C : Fin n → UCell ψ κ) : Prop :=
  SignalGlobal ring C ∨ (K2FiniteProgress.count C = 1 ∧
    PopulationProtocol.IsSafe (LabelFreeElimination.protocol hψ κ) ring C id)

theorem psDoneSafe (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hp : PeacefulGlobal ring C) (hd : psDone ring C) :
    psReached hψ ring C := by
  rcases hd with hd | hd
  · exact Or.inl hd
  · exact Or.inr ⟨hd, K2PeacefulGlobal.count_one_isSafe hψ hn ring C hp hd⟩

/-- Physical terminal padding preserves the target, including the last-two
deletion case. Count positivity excludes extinction in this domain. -/
theorem psDoneClosed (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hp : PeacefulGlobal ring C) (hd : psDone ring C) (e : Fin n) :
    psDone ring (LabelFreeElimination.step hψ ring C e) := by
  rcases hd with hd | hd
  · exact Or.inl (signalGlobal_step hψ ring C hd e)
  · have hlo := peacefulGlobal_count_pos ring _ (peacefulGlobal_step hψ hn ring C hp e)
    have hhi := K2FiniteProgress.step_count_nonincrease hψ ring C e
    exact Or.inr (by omega)

noncomputable section

/-- Full physical configuration is retained at every active child. -/
def psPhysicalStep (hψ : 0 < ψ) (ring : DirectedRing n) (C : Fin n → UCell ψ κ) (e : Fin n) :
    StopNode (Fin n → UCell ψ κ) := by
  classical
  let D := LabelFreeElimination.step hψ ring C e
  exact if psDone ring D then .success else .active D

def psInitialNode (ring : DirectedRing n) (C : Fin n → UCell ψ κ) :
    StopNode (Fin n → UCell ψ κ) := by
  classical
  exact if psDone ring C then .success else .active C

def psAuditState (ring : DirectedRing n) :=
  { C : Fin n → UCell ψ κ // Separated ring (physicalConfig C) ∧ PeacefulGlobal ring C ∧ ¬ psDone ring C }

theorem psAtLeastTwo (ring : DirectedRing n) (s : psAuditState (ψ := ψ) (κ := κ) ring) :
    2 ≤ K2FiniteProgress.count s.val := by
  have hp := peacefulGlobal_count_pos ring s.val s.property.2.1
  have hn : K2FiniteProgress.count s.val ≠ 1 := fun hh => s.property.2.2 (Or.inr hh)
  omega

def psAuditStep (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (s : psAuditState (ψ := ψ) (κ := κ) ring) (e : Fin n) : StopNode (psAuditState (ψ := ψ) (κ := κ) ring) := by
  classical
  let D := LabelFreeElimination.step hψ ring s.val e
  exact if h : psDone ring D then .success else
    .active ⟨D, psSeparatedStep hψ ring s.val s.property.1 e,
      peacefulGlobal_step hψ hn ring s.val s.property.2.1 e, h⟩

def psAuditInitial (ring : DirectedRing n) (C : Fin n → UCell ψ κ)
    (hs : Separated ring (physicalConfig C)) (hp : PeacefulGlobal ring C) :
    StopNode (psAuditState (ψ := ψ) (κ := κ) ring) := by
  classical
  exact if h : psDone ring C then .success else .active ⟨C, hs, hp, h⟩

def psForget (ring : DirectedRing n) :
    StopNode (psAuditState (ψ := ψ) (κ := κ) ring) → StopNode (Fin n → UCell ψ κ)
  | .active s => .active s.val
  | .success => .success
  | .failure => .failure

theorem psForgetStep (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (s : psAuditState (ψ := ψ) (κ := κ) ring) (e : Fin n) :
    psForget ring (psAuditStep hψ hn ring s e) = psPhysicalStep hψ ring s.val e := by
  classical
  unfold psAuditStep psPhysicalStep
  dsimp only
  split <;> rfl

theorem psForgetInitial (ring : DirectedRing n) (C : Fin n → UCell ψ κ)
    (hs : Separated ring (physicalConfig C)) (hp : PeacefulGlobal ring C) :
    psForget ring (psAuditInitial ring C hs hp) = psInitialNode ring C := by
  classical
  unfold psAuditInitial psInitialNode
  split <;> rfl

theorem psForgetNode (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (x : StopNode (psAuditState (ψ := ψ) (κ := κ) ring)) (e : Fin n) :
    psForget ring (stepNode (psAuditStep hψ hn ring) x e) =
      stepNode (psPhysicalStep hψ ring) (psForget ring x) e := by
  cases x with
  | active s => exact psForgetStep hψ hn ring s e
  | success => rfl
  | failure => rfl

/-- Exact weighted tree simulation; all n raw edge choices are unchanged. -/
theorem psTreeWeight (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (w : StopNode (Fin n → UCell ψ κ) → Nat)
    (x : StopNode (psAuditState (ψ := ψ) (κ := κ) ring)) (T : Nat) :
    treeWeight (psAuditStep hψ hn ring) (fun y => w (psForget ring y)) x T =
      treeWeight (psPhysicalStep hψ ring) w (psForget ring x) T := by
  induction T generalizing x with
  | zero => rfl
  | succ T ih =>
    simp only [treeWeight]
    apply FiniteUniformStoppingTree.ofFn_sum_eq
    intro e
    rw [ih, psForgetNode]

theorem psCostSimulation (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (x : StopNode (psAuditState (ψ := ψ) (κ := κ) ring)) (T : Nat) :
    truncatedActiveCostNumerator (psAuditStep hψ hn ring) x T =
      truncatedActiveCostNumerator (psPhysicalStep hψ ring) (psForget ring x) T := by
  induction T generalizing x with
  | zero => rfl
  | succ T ih =>
    cases x with
    | success => rfl
    | failure => rfl
    | active s =>
      simp only [truncatedActiveCostNumerator, psForget]
      apply congrArg (fun z => n ^ (T + 1) + z)
      apply FiniteUniformStoppingTree.ofFn_sum_eq
      intro e
      rw [ih, psForgetStep]

def psPotential (ring : DirectedRing n) : StopNode (psAuditState (ψ := ψ) (κ := κ) ring) → Nat
  | .active s => n * psRank ring s.val s.property.1 (psAtLeastTwo ring s)
  | .success | .failure => 0

private theorem psPositive (ring : DirectedRing n) (s : psAuditState (ψ := ψ) (κ := κ) ring) :
    0 < psRank ring s.val s.property.1 (psAtLeastTwo ring s) := by
  have hh : psRank ring s.val s.property.1 (psAtLeastTwo ring s) ≠ 0 :=
    fun hz => s.property.2.2 (Or.inl ((psRankZero ring s.val s.property.1 (psAtLeastTwo ring s)).mp hz))
  omega

private theorem psPotentialLe (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (s : psAuditState (ψ := ψ) (κ := κ) ring) (e : Fin n) :
    psPotential ring (psAuditStep hψ hn ring s e) ≤ psPotential ring (.active s) := by
  classical
  unfold psAuditStep
  dsimp only
  split
  · exact Nat.zero_le _
  · apply Nat.mul_le_mul_left n
    exact psRankStepLe hψ ring s.val s.property.1 (psAtLeastTwo ring s) s.property.2.1 e _

private theorem psPotentialTarget (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (s : psAuditState (ψ := ψ) (κ := κ) ring) :
    ∃ e, psPotential ring (psAuditStep hψ hn ring s e) + n ≤ psPotential ring (.active s) := by
  classical
  have hp := psPositive ring s
  obtain ⟨e, _, he⟩ := psRankTarget hψ ring s.val s.property.1 (psAtLeastTwo ring s) s.property.2.1 hp
  refine ⟨e, ?_⟩
  unfold psAuditStep
  dsimp only
  split
  · have hh := Nat.mul_le_mul_left n hp
    simpa only [psPotential, Nat.zero_add, Nat.mul_one] using hh
  · rename_i hd
    have hc := peacefulGlobal_count_pos ring _
      (peacefulGlobal_step hψ hn ring s.val s.property.2.1 e)
    have hne : K2FiniteProgress.count (LabelFreeElimination.step hψ ring s.val e) ≠ 1 :=
      fun hh => hd (Or.inr hh)
    have hh := Nat.mul_le_mul_left n (he (by omega))
    simpa only [psPotential, Nat.mul_succ] using hh

private theorem psSumIndicator {m : Nat} (e : Fin m) :
    (List.ofFn (fun i : Fin m => if i = e then 1 else 0)).sum = 1 := by
  induction m with
  | zero => exact Fin.elim0 e
  | succ m ih =>
    have hz : ∀ i : Fin m, i.succ ≠ (0 : Fin (m + 1)) := by
      intro i h
      have hv := congrArg Fin.val h
      change i.val + 1 = 0 at hv
      omega
    refine Fin.cases ?_ (fun j => ?_) e
    · simp [List.ofFn_succ, hz, FiniteUniformStoppingTree.ofFn_sum_const]
    · rw [List.ofFn_succ, List.sum_cons]
      have hh : (0 : Fin (m + 1)) ≠ j.succ := fun h => hz j h.symm
      simpa [hh] using ih j

/-- A single total-entry Bellman certificate remains valid through every
actual merger. No n² allowance is restarted after a deletion. -/
theorem psSuper (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n) :
    NatBellmanSuperSolution (psAuditStep (κ := κ) hψ hn ring) 1 (psPotential ring) := by
  classical
  refine ⟨rfl, rfl, ?_⟩
  intro s
  obtain ⟨e, he⟩ := psPotentialTarget hψ hn ring s
  have hh := FiniteUniformStoppingTree.ofFn_sum_le
    (fun j => psPotential ring (psAuditStep hψ hn ring s j) + n * (if j = e then 1 else 0))
    (fun _ : Fin n => psPotential ring (.active s)) (fun j => by
      by_cases hj : j = e
      · subst j
        simpa using he
      · simp only [if_neg hj, Nat.mul_zero, Nat.add_zero]
        exact psPotentialLe hψ hn ring s j)
  rw [FiniteUniformStoppingTree.ofFn_sum_add, FiniteUniformStoppingTree.ofFn_sum_mul_left,
    psSumIndicator, Nat.mul_one, FiniteUniformStoppingTree.ofFn_sum_const] at hh
  change 1 * n + _ ≤ _
  omega

theorem psAuditCostBound (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (x : StopNode (psAuditState (ψ := ψ) (κ := κ) ring)) (T : Nat) :
    truncatedActiveCostNumerator (psAuditStep hψ hn ring) x T ≤ n ^ T * (n * n) := by
  have hh := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (psAuditStep hψ hn ring) 1 (psPotential ring) (psSuper hψ hn ring) x T
  rw [Nat.one_mul] at hh
  apply Nat.le_trans hh
  apply Nat.mul_le_mul_left
  cases x with
  | success => exact Nat.zero_le _
  | failure => exact Nat.zero_le _
  | active s => exact Nat.mul_le_mul_left n (psRankLe ring s.val s.property.1 _)

/-- Truncated expected total entry cost is at most n², at every finite
horizon, from the actual separated nearest-peaceful physical domain. -/
theorem psTruncatedCost (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hs : Separated ring (physicalConfig C)) (hp : PeacefulGlobal ring C) (T : Nat) :
    truncatedActiveCostNumerator (psPhysicalStep hψ ring) (psInitialNode ring C) T ≤ n ^ T * (n * n) := by
  have hh := psAuditCostBound hψ hn ring (psAuditInitial ring C hs hp) T
  rwa [psCostSimulation, psForgetInitial] at hh

/-- Exact concatenation identity for the existing finite uniform tree. -/
theorem psTreeAdd {S : Type} (f : S → Fin n → StopNode S)
    (w : StopNode S → Nat) (x : StopNode S) (s t : Nat) :
    treeWeight f w x (s + t) = treeWeight f (fun y => treeWeight f w y t) x s := by
  induction s generalizing x with
  | zero => simp only [Nat.zero_add, treeWeight]
  | succ s ih =>
    rw [Nat.succ_add]
    simp only [treeWeight]
    exact FiniteUniformStoppingTree.ofFn_sum_eq _ _ (fun e => ih (stepNode f x e))

theorem psAuditHalf (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (x : StopNode (psAuditState (ψ := ψ) (κ := κ) ring)) :
    2 * activeCount (psAuditStep hψ hn ring) x (2 * (n * n)) ≤
      n ^ (2 * (n * n)) * activeWeight x := by
  cases x with
  | success => simp [activeCount, treeWeight_success, activeWeight]
  | failure => simp [activeCount, treeWeight_failure, activeWeight]
  | active s =>
    simp only [activeWeight, Nat.mul_one]
    apply two_mul_activeCount_le_pow_of_scaled_cost (den := 1) (num := n * n)
    · exact Nat.mul_pos (by decide) (Nat.mul_pos (by omega) (by omega))
    · decide
    · simpa only [Nat.one_mul, Nat.mul_comm] using
        psAuditCostBound hψ hn ring (.active s) (2 * (n * n))
    · simp only [Nat.mul_one, Nat.le_refl]

theorem psAuditBlock (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (x : StopNode (psAuditState (ψ := ψ) (κ := κ) ring)) (t : Nat) :
    2 * activeCount (psAuditStep hψ hn ring) x (t + 2 * (n * n)) ≤
      n ^ (2 * (n * n)) * activeCount (psAuditStep hψ hn ring) x t := by
  unfold activeCount
  rw [psTreeAdd, ← treeWeight_mul_left, ← treeWeight_mul_left]
  exact treeWeight_mono _ _ _ (psAuditHalf hψ hn ring) x t

theorem psAuditTail (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (x : StopNode (psAuditState (ψ := ψ) (κ := κ) ring)) (r : Nat) :
    2 ^ r * activeCount (psAuditStep hψ hn ring) x (2 * (n * n) * r) ≤
      n ^ (2 * (n * n) * r) := by
  induction r with
  | zero => cases x <;> simp [activeCount, treeWeight, activeWeight]
  | succ r ih =>
    rw [Nat.mul_succ, Nat.pow_succ]
    calc
      2 ^ r * 2 * activeCount (psAuditStep hψ hn ring) x
          (2 * (n * n) * r + 2 * (n * n)) =
          2 ^ r * (2 * activeCount (psAuditStep hψ hn ring) x
            (2 * (n * n) * r + 2 * (n * n))) := by ac_rfl
      _ ≤ 2 ^ r * (n ^ (2 * (n * n)) *
          activeCount (psAuditStep hψ hn ring) x (2 * (n * n) * r)) :=
        Nat.mul_le_mul_left _ (psAuditBlock hψ hn ring x _)
      _ = n ^ (2 * (n * n)) * (2 ^ r *
          activeCount (psAuditStep hψ hn ring) x (2 * (n * n) * r)) := by ac_rfl
      _ ≤ n ^ (2 * (n * n)) * n ^ (2 * (n * n) * r) := Nat.mul_le_mul_left _ ih
      _ = n ^ (2 * (n * n) * r + 2 * (n * n)) := by rw [Nat.pow_add]; ac_rfl

/-- Division-free exponential tail on the original physical scheduler:
at time 2 n² r, the still-active word mass is at most 2⁻ʳ. -/
theorem psTail (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hs : Separated ring (physicalConfig C))
    (hp : PeacefulGlobal ring C) (r : Nat) :
    2 ^ r * activeCount (psPhysicalStep hψ ring) (psInitialNode ring C)
      (2 * (n * n) * r) ≤ n ^ (2 * (n * n) * r) := by
  have hh := psAuditTail hψ hn ring (psAuditInitial ring C hs hp) r
  have hw : (fun y : StopNode (psAuditState (ψ := ψ) (κ := κ) ring) =>
      activeWeight (psForget ring y)) = activeWeight := by funext y; cases y <;> rfl
  unfold activeCount at hh ⊢
  rw [← hw, psTreeWeight, psForgetInitial] at hh
  exact hh

/-- At 2 n² c (floor(log₂ n) + 1), the residual mass is at most n⁻ᶜ. -/
theorem psLogTail (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hs : Separated ring (physicalConfig C))
    (hp : PeacefulGlobal ring C) (c : Nat) :
    n ^ c * activeCount (psPhysicalStep hψ ring) (psInitialNode ring C)
      (2 * (n * n) * (c * (Nat.log2 n + 1))) ≤
      n ^ (2 * (n * n) * (c * (Nat.log2 n + 1))) := by
  have hn0 : n ≠ 0 := by omega
  have hl : n ≤ 2 ^ (Nat.log2 n + 1) := Nat.le_of_lt ((Nat.log2_lt hn0).mp (by omega))
  have hh : n ^ c ≤ 2 ^ (c * (Nat.log2 n + 1)) := by
    calc
      n ^ c ≤ (2 ^ (Nat.log2 n + 1)) ^ c := Nat.pow_le_pow_left hl c
      _ = 2 ^ (c * (Nat.log2 n + 1)) := by rw [← Nat.pow_mul, Nat.mul_comm]
  exact Nat.le_trans (Nat.mul_le_mul_right _ hh) (psTail hψ hn ring C hs hp _)

private theorem psNoFailureActive (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (T : Nat) :
    failureCount (psPhysicalStep hψ ring) (.active C) T = 0 := by
  classical
  induction T generalizing C with
  | zero => rfl
  | succ T ih =>
    change (List.ofFn (fun e => treeWeight (psPhysicalStep hψ ring) failureWeight
      (psPhysicalStep hψ ring C e) T)).sum = 0
    have hh := FiniteUniformStoppingTree.ofFn_sum_eq
      (fun e => treeWeight (psPhysicalStep hψ ring) failureWeight (psPhysicalStep hψ ring C e) T)
      (fun _ : Fin n => 0) (fun e => by
        unfold psPhysicalStep
        dsimp only
        split
        · simp only [treeWeight_success, failureWeight, Nat.mul_zero]
        · exact ih _)
    simpa only [FiniteUniformStoppingTree.ofFn_sum_const, Nat.mul_zero] using hh

theorem psNoFailure (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (T : Nat) :
    failureCount (psPhysicalStep hψ ring) (psInitialNode ring C) T = 0 := by
  classical
  unfold psInitialNode
  split
  · simp only [failureCount, treeWeight_success, failureWeight, Nat.mul_zero]
  · exact psNoFailureActive hψ ring C T

/-- At least half of all original scheduler words have reached the target
by 2 n², allowing any number of earlier actual leader deletions. -/
theorem psHalfMass (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hs : Separated ring (physicalConfig C)) (hp : PeacefulGlobal ring C) :
    n ^ (2 * (n * n)) ≤
      2 * successCount (psPhysicalStep hψ ring) (psInitialNode ring C) (2 * (n * n)) := by
  have ht := psTail hψ hn ring C hs hp 1
  simp only [Nat.pow_one, Nat.mul_one] at ht
  have hh := node_count_partition (psPhysicalStep hψ ring) (psInitialNode ring C) (2 * (n * n))
  rw [psNoFailure] at hh
  omega

/-- The corresponding lower bound on successful physical word mass is
1 - 2⁻ʳ. The no-failure partition is exact. -/
theorem psSuccessTail (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hs : Separated ring (physicalConfig C))
    (hp : PeacefulGlobal ring C) (r : Nat) :
    (2 ^ r - 1) * n ^ (2 * (n * n) * r) ≤ 2 ^ r *
      successCount (psPhysicalStep hψ ring) (psInitialNode ring C) (2 * (n * n) * r) := by
  have ht := psTail hψ hn ring C hs hp r
  have hh := node_count_partition (psPhysicalStep hψ ring) (psInitialNode ring C) (2 * (n * n) * r)
  rw [psNoFailure, Nat.add_zero] at hh
  have hscale := congrArg (fun z => 2 ^ r * z) hh
  rw [Nat.mul_add] at hscale
  rw [Nat.sub_mul, Nat.one_mul]
  omega

/-- The physical payload is checked at the end of the entire word,
including every edge after the stopping time. -/
def psTracks (ring : DirectedRing n) : StopNode (Fin n → UCell ψ κ) → (Fin n → UCell ψ κ) → Prop
  | .active C, D => C = D ∧ ¬ psDone ring D
  | .success, D => psDone ring D
  | .failure, _ => False

theorem psTracksInitial (ring : DirectedRing n) (C : Fin n → UCell ψ κ) :
    psTracks ring (psInitialNode ring C) C := by
  classical
  unfold psInitialNode
  split
  · assumption
  · exact ⟨rfl, by assumption⟩

theorem psTracksStep (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (D : Fin n → UCell ψ κ) (hp : PeacefulGlobal ring D)
    (x : StopNode (Fin n → UCell ψ κ)) (hx : psTracks ring x D) (e : Fin n) :
    psTracks ring (stepNode (psPhysicalStep hψ ring) x e) (LabelFreeElimination.step hψ ring D e) := by
  classical
  cases x with
  | failure => exact hx.elim
  | success => exact psDoneClosed hψ hn ring D hp hx e
  | active C =>
    obtain ⟨rfl, _⟩ := hx
    change psTracks ring (psPhysicalStep hψ ring C e) _
    unfold psPhysicalStep
    dsimp only
    split
    · assumption
    · exact ⟨rfl, by assumption⟩

theorem psTracksWord (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (D : Fin n → UCell ψ κ) (hp : PeacefulGlobal ring D)
    (x : StopNode (Fin n → UCell ψ κ)) (hx : psTracks ring x D) (es : List (Fin n)) :
    psTracks ring (ControlledSchedulerMass.runWord (psPhysicalStep hψ ring) x es)
      (LDSinkBoundedKernel.run (LabelFreeElimination.step hψ ring) D es) := by
  induction es generalizing D x with
  | nil => exact hx
  | cons e es ih =>
    exact ih _ (peacefulGlobal_step hψ hn ring D hp e) _ (psTracksStep hψ hn ring D hp x hx e)

theorem psSuccessfulWordIff (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hp : PeacefulGlobal ring C) (es : List (Fin n)) :
    ControlledSchedulerMass.runWord (psPhysicalStep hψ ring) (psInitialNode ring C) es = .success ↔
      psDone ring (LDSinkBoundedKernel.run (LabelFreeElimination.step hψ ring) C es) := by
  have hh := psTracksWord hψ hn ring C hp (psInitialNode ring C) (psTracksInitial ring C) es
  cases hr : ControlledSchedulerMass.runWord (psPhysicalStep hψ ring) (psInitialNode ring C) es with
  | failure => rw [hr] at hh; exact hh.elim
  | success => rw [hr] at hh; exact ⟨fun _ => hh, fun _ => rfl⟩
  | active D =>
    rw [hr] at hh
    constructor
    · intro h
      cases h
    · intro hd
      exact (hh.2 hd).elim

/-- Success implies semantic count-one safety, without a post-state safety
field or a future-closure assumption. -/
theorem psSuccessfulWord (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hp : PeacefulGlobal ring C) (es : List (Fin n))
    (hh : ControlledSchedulerMass.runWord (psPhysicalStep hψ ring) (psInitialNode ring C) es = .success) :
    psReached hψ ring (LDSinkBoundedKernel.run (LabelFreeElimination.step hψ ring) C es) :=
  psDoneSafe hψ hn ring _ (peacefulGlobal_run hψ hn ring C hp es)
    ((psSuccessfulWordIff hψ hn ring C hp es).mp hh)

/-- A retained audit payload advances the actual physical edge even when
its stopping flag has already succeeded. This adds no local protocol state. -/
def psRetainedStep (hψ : 0 < ψ) (ring : DirectedRing n)
    (q : StopNode (Fin n → UCell ψ κ) × (Fin n → UCell ψ κ)) (e : Fin n) :
    StopNode (Fin n → UCell ψ κ) × (Fin n → UCell ψ κ) :=
  (stepNode (psPhysicalStep hψ ring) q.1 e, LabelFreeElimination.step hψ ring q.2 e)

theorem psRetainedRun (hψ : 0 < ψ) (ring : DirectedRing n)
    (q : StopNode (Fin n → UCell ψ κ) × (Fin n → UCell ψ κ)) (es : List (Fin n)) :
    LDSinkBoundedKernel.run (psRetainedStep hψ ring) q es =
      (ControlledSchedulerMass.runWord (psPhysicalStep hψ ring) q.1 es,
        LDSinkBoundedKernel.run (LabelFreeElimination.step hψ ring) q.2 es) := by
  induction es generalizing q with
  | nil => rfl
  | cons e es ih => exact ih (psRetainedStep hψ ring q e)

/-- Final-two deletion is discharged by actual count arithmetic and the
checked nearest-support safety theorem, without constructing a cyclic
two-gap frame whose combined length would equal n. -/
theorem psLastTwoDeletion (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hp : PeacefulGlobal ring C) (hc : K2FiniteProgress.count C = 2)
    (e : Fin n) (he : (C e).legacy.leader = true)
    (hd : (LabelFreeElimination.step hψ ring C e e).legacy.leader = false) :
    K2FiniteProgress.count (LabelFreeElimination.step hψ ring C e) = 1 ∧
      PopulationProtocol.IsSafe (LabelFreeElimination.protocol hψ κ) ring
        (LabelFreeElimination.step hψ ring C e) id := by
  have hd' : (rawStep (by decide) ring (observe C) e e).leader = false := by
    rw [← observe_step hψ ring C e]
    exact hd
  have hh := physical_count_drop (by decide) ring (observe C) e he hd'
  rw [← observe_step hψ ring C e] at hh
  change K2FiniteProgress.count (LabelFreeElimination.step hψ ring C e) + 1 =
    K2FiniteProgress.count C at hh
  have h1 : K2FiniteProgress.count (LabelFreeElimination.step hψ ring C e) = 1 := by omega
  exact ⟨h1, count_one_isSafe hψ hn ring _ (peacefulGlobal_step hψ hn ring C hp e) h1⟩

theorem psReachedClosed (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hp : PeacefulGlobal ring C) (hc : psReached hψ ring C) (e : Fin n) :
    psReached hψ ring (LabelFreeElimination.step hψ ring C e) :=
  psDoneSafe hψ hn ring _ (peacefulGlobal_step hψ hn ring C hp e)
    (psDoneClosed hψ hn ring C hp (hc.elim Or.inl (fun hh => Or.inr hh.1)) e)

theorem psReachedRun (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hp : PeacefulGlobal ring C) (hc : psReached hψ ring C)
    (es : List (Fin n)) :
    psReached hψ ring (LDSinkBoundedKernel.run (LabelFreeElimination.step hψ ring) C es) := by
  induction es generalizing C with
  | nil => exact hc
  | cons e es ih => exact ih _ (peacefulGlobal_step hψ hn ring C hp e) (psReachedClosed hψ hn ring C hp hc e)

theorem psRetainedFrame (hψ : 0 < ψ) (ring : DirectedRing n)
    (q : StopNode (Fin n → UCell ψ κ) × (Fin n → UCell ψ κ)) (es : List (Fin n)) (i : Fin n) :
    putSignals ((LDSinkBoundedKernel.run (psRetainedStep hψ ring) q es).2 i)
      (observeCell (q.2 i)) = q.2 i := by
  rw [psRetainedRun]
  exact LabelFreeElimination.run_frame hψ ring q.2 es i

/-- Only the proof audit carries rank and stopping data. The physical
protocol has exactly the old finite cells and the old carrier estimate. -/
theorem psCarrierBound (hψ : 0 < ψ) (hκ : ψ ≤ κ + 1) :
    (LabelFreeElimination.protocol hψ κ).Q = UCell ψ κ ∧
      (allUCell ψ κ).length ≤ 4862332800 * 61931520000000 * (κ + 1) ^ 8 :=
  ⟨rfl, LabelFreeElimination.state_bound hψ hκ⟩

/-- Collision-protocol transfer uses exact separated full-word agreement.
No claim is made about its row on adjacent-leader inputs. -/
theorem psCollisionSuccessfulWord (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hs : Separated ring (physicalConfig C))
    (hp : PeacefulGlobal ring C) (es : List (Fin n))
    (hh : ControlledSchedulerMass.runWord (psPhysicalStep hψ ring) (psInitialNode ring C) es = .success) :
    let D := LDSinkBoundedKernel.run (AdjacentLeaderElimination.step hψ ring) C es
    SignalGlobal ring D ∨ (K2FiniteProgress.count D = 1 ∧
      PopulationProtocol.IsSafe (AdjacentLeaderElimination.protocol hψ κ) ring D id) := by
  dsimp only
  rw [AdjacentLeaderElimination.separated_run_eq_old hψ ring C hs es]
  rcases psSuccessfulWord hψ hn ring C hp es hh with hg | ⟨h1, hsafe⟩
  · exact Or.inl hg
  · exact Or.inr ⟨h1, AdjacentLeaderElimination.isSafe_of_old_isSafe hψ hn ring _ hsafe⟩

namespace PsDirtyExample

/-- The frozen n=5, physical-modulus=2 seed has a dirty dummy bullet and
two real leaders. Nearest peacefulness holds because it has no live bullet. -/
theorem psPeaceful : PeacefulGlobal DirtyEntryExample.ring5 DirtyEntryExample.seed := by
  constructor
  · exact ⟨0, by decide⟩
  · have hn : ∀ i : Fin 5, (observe DirtyEntryExample.seed i).bullet ≠ 2 := by decide
    intro i hi
    exact (hn i hi).elim

theorem psNondivisibleDirty : ¬ 2 ∣ 5 ∧
    Separated DirtyEntryExample.ring5 (physicalConfig DirtyEntryExample.seed) ∧
    PeacefulGlobal DirtyEntryExample.ring5 DirtyEntryExample.seed ∧
    ¬ SignalGlobal DirtyEntryExample.ring5 DirtyEntryExample.seed :=
  ⟨by decide, DirtyEntryExample.separated.separated, psPeaceful, DirtyEntryExample.not_global⟩

theorem psHalf :
    5 ^ (2 * (5 * 5)) ≤ 2 * successCount
      (psPhysicalStep (by decide) DirtyEntryExample.ring5) (psInitialNode DirtyEntryExample.ring5 DirtyEntryExample.seed)
      (2 * (5 * 5)) :=
  psHalfMass (by decide) (by decide) DirtyEntryExample.ring5 DirtyEntryExample.seed
    DirtyEntryExample.separated.separated psPeaceful

theorem psActualSuccess :
    psPhysicalStep (by decide) DirtyEntryExample.ring5 DirtyEntryExample.seed 2 = .success := by
  classical
  exact if_pos (Or.inl DirtyEntryExample.actual_ordered)

end PsDirtyExample

namespace PsMergeExample

/-- A live killer has a clean nearest support, while a different gap still
contains a dirty dummy. Its real deletion must leave total entry active. -/
def psSeed (i : Fin 7) : UCell 2 1 :=
  let q := DirtyEntryExample.seed 0
  { q with legacy := { q.legacy with
      leader := decide (i = 0 ∨ i = 2 ∨ i = 4)
      shield := decide (i = 4)
      bullet := if i = 3 then 2 else if i = 5 then 1 else 0
      signal_B := if i = 6 then 1 else 0 } }

theorem psRing : DirectedRing 7 := ⟨by decide⟩
def psRecovery : GapFrame 7 := ⟨psRing, 0, 2, by decide, by decide⟩
def psAttack : GapFrame 7 := ⟨psRing, 2, 2, by decide, by decide⟩
def psDirty : GapFrame 7 := ⟨psRing, 4, 3, by decide, by decide⟩
def psPair : TwoGapFrame 7 := ⟨psRecovery, psAttack, by decide, by decide⟩

theorem psSeparated : Separated psRing (physicalConfig psSeed) := by
  unfold Separated
  decide

theorem psPeaceful : PeacefulGlobal psRing psSeed := by
  constructor
  · exact ⟨0, by decide⟩
  · have hl : ∀ i : Fin 7, (observe psSeed i).bullet = 2 → i = 3 := by decide
    intro i hi
    have he := hl i hi
    subst i
    refine ⟨1, by decide, by decide, by decide, ?_, ?_⟩
    · intro k hk
      have hh : k = 0 ∨ k = 1 := by omega
      rcases hh with rfl | rfl <;> decide
    · intro k hk
      have hh : k = 0 := by omega
      subst k
      decide

theorem psAttackReal : GapEndpointsPresent psAttack (physicalConfig psSeed) ∧
    GapInteriorFollowers psAttack (physicalConfig psSeed) := by
  constructor
  · constructor <;> decide
  · intro i hi hid
    change i < 2 at hid
    have hh : i = 1 := by omega
    subst i
    decide

theorem psDeleted : (LabelFreeElimination.step (by decide) psRing psSeed 2 2).legacy.leader = false := by
  decide

theorem psMergeLaw :
    badTop (merged psPair) (physicalConfig (LabelFreeElimination.step (by decide) psRing psSeed 2)) =
      badTop psRecovery (physicalConfig psSeed) :=
  psDeletionMerge (by decide) psPair psSeed psAttackReal.1 psAttackReal.2 psPeaceful psDeleted

theorem psStillDirty : ¬ psDone psRing (LabelFreeElimination.step (by decide) psRing psSeed 2) := by
  let D := LabelFreeElimination.step (by decide) psRing psSeed 2
  have hE : GapEndpointsPresent psDirty (physicalConfig D) := by constructor <;> decide
  have hI : GapInteriorFollowers psDirty (physicalConfig D) := by
    intro i hi hid
    change i < 3 at hid
    have hh : i = 1 ∨ i = 2 := by omega
    rcases hh with rfl | rfl <;> decide
  have hb : (physicalConfig D (psDirty.pos 1)).bullet ≠ 0 := by decide
  have hc : K2FiniteProgress.count D = 2 := by decide
  intro hh
  rcases hh with hg | h1
  · have hz := ((signalGlobal_iff psRing D).mp hg).2 psDirty hE hI
      1 2 (by decide) (by decide) hb (by decide) (by decide)
    change (1 : Fin 2) = 0 at hz
    cases hz
  · change K2FiniteProgress.count D = 1 at h1
    omega

theorem psActualContinues :
    psPhysicalStep (by decide) psRing psSeed 2 =
      .active (LabelFreeElimination.step (by decide) psRing psSeed 2) := by
  classical
  exact if_neg psStillDirty

theorem psTotalCost (T : Nat) :
    truncatedActiveCostNumerator (psPhysicalStep (by decide) psRing) (psInitialNode psRing psSeed) T ≤
      7 ^ T * (7 * 7) :=
  psTruncatedCost (by decide) (by decide) psRing psSeed psSeparated psPeaceful T

end PsMergeExample

end

end K2PeacefulSignalEntry
