import Leader.L3.Top.FinalMobileLin

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- The output atom of the comparison lane at a site. -/
def cmpOut {c : Compiled} {n : Nat} (A : DigitAudit c n) (v : Fin n) : Option (DigitAtom n) :=
  (A.current v).comparison.out.atom

/-- The input atom of the comparison lane at a site. -/
def cmpIn {c : Compiled} {n : Nat} (A : DigitAudit c n) (v : Fin n) : Option (DigitAtom n) :=
  (A.current v).comparison.input

/-- All comparison exports, chronologically. -/
def cmpEx {c : Compiled} {n : Nat} (A : DigitAudit c n) : List (DigitExport c n) :=
  A.frames.reverse.filterMap (fun f => (digitReceiptLane .comparison f.receipt).exported)

/-- The comparison replay of the edge `e`. -/
def edgeReplay {c : Compiled} {n : Nat} (ring : DirectedRing n) (S : Fin n → ProjD c)
    (A : DigitAudit c n) (e : Fin n) : DigitLaneReplay c n :=
  digitLaneReplay .comparison (A.clock + 1) e (ring.rightNeighbor e)
    (digitLaneView .comparison (S e) (S e).word.beta)
    (digitLaneView .comparison (S (ring.rightNeighbor e)) (S (ring.rightNeighbor e)).word.beta)
    (A.current e).comparison (A.current (ring.rightNeighbor e)).comparison

theorem audit_clock {c : Compiled} {n : Nat} (ring : DirectedRing n) (S : Fin n → ProjD c)
    (A : DigitAudit c n) (e : Fin n) : (digitAuditStep ring S A e).clock = A.clock + 1 := rfl

theorem audit_cur_src {c : Compiled} {n : Nat} (ring : DirectedRing n) (S : Fin n → ProjD c)
    (A : DigitAudit c n) (e : Fin n) :
    ((digitAuditStep ring S A e).current e).comparison = (edgeReplay ring S A e).x := by
  simp [digitAuditStep, digitGhostStep, digitService, edgeReplay]

theorem audit_cur_dst {c : Compiled} {n : Nat} (ring : DirectedRing n) (S : Fin n → ProjD c)
    (A : DigitAudit c n) (e : Fin n) (hne : ring.rightNeighbor e ≠ e) :
    ((digitAuditStep ring S A e).current (ring.rightNeighbor e)).comparison =
      (edgeReplay ring S A e).y := by
  simp [digitAuditStep, digitGhostStep, digitService, edgeReplay, hne]

theorem audit_cur_away {c : Compiled} {n : Nat} (ring : DirectedRing n) (S : Fin n → ProjD c)
    (A : DigitAudit c n) (e v : Fin n) (h1 : v ≠ e) (h2 : v ≠ ring.rightNeighbor e) :
    (digitAuditStep ring S A e).current v = A.current v := by
  simp [digitAuditStep, digitGhostStep, h1, h2]

theorem audit_ex {c : Compiled} {n : Nat} (ring : DirectedRing n) (S : Fin n → ProjD c)
    (A : DigitAudit c n) (e : Fin n) :
    cmpEx (digitAuditStep ring S A e) = cmpEx A ++ (edgeReplay ring S A e).exported.toList := by
  unfold cmpEx
  have h : (digitAuditStep ring S A e).frames =
      { time := A.clock + 1, edge := e, old := S, oldGhost := A.current,
        receipt := digitService (A.clock + 1) e (ring.rightNeighbor e)
          (S e) (S (ring.rightNeighbor e)) (A.current e) (A.current (ring.rightNeighbor e)) } ::
        A.frames := rfl
  rw [h, List.reverse_cons, List.filterMap_append]
  congr 1

/-- Injectivity of a family of optional labels survives a move of labels between two
positions with at most one fresh label. -/
theorem inj_step {V α : Type} (e j : V) (hej : j ≠ e) (old new : V → Option α) (f : Option α)
    (hfr : ∀ v, v ≠ e → v ≠ j → new v = old v)
    (hx : ∀ z, new e = some z → old e = some z ∨ f = some z)
    (hy : ∀ z, new j = some z → old j = some z ∨ (old e = some z ∧ new e = none))
    (hf : ∀ z, f = some z → ∀ v, old v ≠ some z)
    (hinj : ∀ v w z, old v = some z → old w = some z → v = w) :
    ∀ v w z, new v = some z → new w = some z → v = w := by
  have origin : ∀ v z, new v = some z → (f = some z ∧ v = e) ∨
      ∃ p, old p = some z ∧ (p = v ∨ (p = e ∧ v = j ∧ new e = none)) := by
    intro v z h
    by_cases hve : v = e
    · subst hve
      rcases hx z h with h1 | h1
      · exact Or.inr ⟨v, h1, Or.inl rfl⟩
      · exact Or.inl ⟨h1, rfl⟩
    · by_cases hvj : v = j
      · subst hvj
        rcases hy z h with h1 | ⟨h1, h2⟩
        · exact Or.inr ⟨v, h1, Or.inl rfl⟩
        · exact Or.inr ⟨e, h1, Or.inr ⟨rfl, rfl, h2⟩⟩
      · rw [hfr v hve hvj] at h
        exact Or.inr ⟨v, h, Or.inl rfl⟩
  intro v w z hv hw
  rcases origin v z hv with ⟨hf1, hve⟩ | ⟨p, hp, hp'⟩ <;>
    rcases origin w z hw with ⟨hf2, hwe⟩ | ⟨q, hq, hq'⟩
  · rw [hve, hwe]
  · exact absurd hq (hf z hf1 q)
  · exact absurd hp (hf z hf2 p)
  · have hpq := hinj p q z hp hq
    rcases hp' with hp' | ⟨hp1, hp2, hp3⟩ <;> rcases hq' with hq' | ⟨hq1, hq2, hq3⟩
    · rw [← hp', ← hq', hpq]
    · exfalso
      have : v = e := by rw [← hp', hpq, hq1]
      rw [this, hq3] at hv
      exact absurd hv (by simp)
    · exfalso
      have : w = e := by rw [← hq', ← hpq, hp1]
      rw [this, hp3] at hw
      exact absurd hw (by simp)
    · rw [hp2, hq2]

/-- Disjointness of two families of optional labels survives the same move. -/
theorem disj_step {V α : Type} (e j : V) (hej : j ≠ e) (oldO newO oldI newI : V → Option α)
    (f : Option α) (acc : Prop)
    (hfrO : ∀ v, v ≠ e → v ≠ j → newO v = oldO v)
    (hx : ∀ z, newO e = some z → oldO e = some z ∨ f = some z)
    (hy : ∀ z, newO j = some z → oldO j = some z ∨ (oldO e = some z ∧ newO e = none))
    (hacc : acc → newO e = none ∧ newO j = oldO j)
    (hin : ∀ w z, newI w = some z → (∃ w', oldI w' = some z) ∨ (acc ∧ oldO e = some z))
    (hf : ∀ z, f = some z → (∀ v, oldO v ≠ some z) ∧ ∀ w, oldI w ≠ some z)
    (hinj : ∀ v w z, oldO v = some z → oldO w = some z → v = w)
    (hdisj : ∀ v w z, oldO v = some z → oldI w ≠ some z) :
    ∀ v w z, newO v = some z → newI w ≠ some z := by
  intro v w z hv hiw
  have origin : (f = some z ∧ v = e) ∨
      ∃ p, oldO p = some z ∧ (p = v ∨ (p = e ∧ v = j ∧ newO e = none)) := by
    by_cases hve : v = e
    · subst hve
      rcases hx z hv with h1 | h1
      · exact Or.inr ⟨v, h1, Or.inl rfl⟩
      · exact Or.inl ⟨h1, rfl⟩
    · by_cases hvj : v = j
      · subst hvj
        rcases hy z hv with h1 | ⟨h1, h2⟩
        · exact Or.inr ⟨v, h1, Or.inl rfl⟩
        · exact Or.inr ⟨e, h1, Or.inr ⟨rfl, rfl, h2⟩⟩
      · rw [hfrO v hve hvj] at hv
        exact Or.inr ⟨v, hv, Or.inl rfl⟩
  rcases hin w z hiw with ⟨w', hw'⟩ | ⟨hacc', hoe⟩
  · rcases origin with ⟨hf1, _⟩ | ⟨p, hp, _⟩
    · exact (hf z hf1).2 w' hw'
    · exact hdisj p w' z hp hw'
  · rcases origin with ⟨hf1, _⟩ | ⟨p, hp, hp'⟩
    · exact (hf z hf1).1 e hoe
    · have hpe := hinj p e z hp hoe
      rcases hp' with hp' | ⟨_, hvj, _⟩
      · rw [hpe] at hp'
        rw [← hp'] at hv
        rw [(hacc hacc').1] at hv
        exact absurd hv (by simp)
      · rw [hvj] at hv
        rw [(hacc hacc').2] at hv
        have := hinj j e z hv hoe
        exact hej this

/-- Where a new label came from. -/
theorem origin_step {V α : Type} (e j : V) (old new : V → Option α) (f : Option α)
    (hfr : ∀ v, v ≠ e → v ≠ j → new v = old v)
    (hx : ∀ z, new e = some z → old e = some z ∨ f = some z)
    (hy : ∀ z, new j = some z → old j = some z ∨ (old e = some z ∧ new e = none)) :
    ∀ v z, new v = some z → (f = some z ∧ v = e) ∨
      ∃ p, old p = some z ∧ (p = v ∨ (p = e ∧ v = j ∧ new e = none)) := by
  intro v z h
  by_cases hve : v = e
  · subst hve
    rcases hx z h with h1 | h1
    · exact Or.inr ⟨v, h1, Or.inl rfl⟩
    · exact Or.inl ⟨h1, rfl⟩
  · by_cases hvj : v = j
    · subst hvj
      rcases hy z h with h1 | ⟨h1, h2⟩
      · exact Or.inr ⟨v, h1, Or.inl rfl⟩
      · exact Or.inr ⟨e, h1, Or.inr ⟨rfl, rfl, h2⟩⟩
    · rw [hfr v hve hvj] at h
      exact Or.inr ⟨v, h, Or.inl rfl⟩

/-- **Linearity of the comparison atoms.**  Output atoms sit at one site, are never input atoms
or export operands; export operands are distinct (up to the empty atom); sampled atoms are not
stamped after the clock.

Consumer: `lin_step`. -/
structure Lin {c : Compiled} {n : Nat} (A : DigitAudit c n) : Prop where
  inj : ∀ v w z, cmpOut A v = some z → cmpOut A w = some z → v = w
  disj : ∀ v w z, cmpOut A v = some z → cmpIn A w ≠ some z
  exd : ∀ v z, cmpOut A v = some z → ∀ ex ∈ cmpEx A, ex.operand ≠ some z
  nodup : ((cmpEx A).map (fun ex => ex.operand)).Pairwise (fun a b => a ≠ b ∨ a = none)
  tOut : ∀ v id, cmpOut A v = some (DigitAtom.sampled id) → id.time ≤ A.clock
  tIn : ∀ v id, cmpIn A v = some (DigitAtom.sampled id) → id.time ≤ A.clock
  tEx : ∀ ex ∈ cmpEx A, ex.time ≤ A.clock ∧
    ∀ id, ex.operand = some (DigitAtom.sampled id) → id.time ≤ A.clock

/-- The sampled atom made by the edge `e`. -/
def freshAtom {c : Compiled} {n : Nat} (A : DigitAudit c n) (e : Fin n) : DigitAtom n :=
  DigitAtom.sampled ({ time := A.clock + 1, site := e, lane := .comparison } : DigitStamp n)

/-- **The output side of one audit step.** -/
theorem step_out_facts {c : Compiled} {n : Nat} (ring : DirectedRing n) (S : Fin n → ProjD c)
    (A : DigitAudit c n) (e : Fin n) (hne : ring.rightNeighbor e ≠ e) :
    (∀ v, v ≠ e → v ≠ ring.rightNeighbor e →
      cmpOut (digitAuditStep ring S A e) v = cmpOut A v) ∧
    (∀ z, cmpOut (digitAuditStep ring S A e) e = some z →
      cmpOut A e = some z ∨ some (freshAtom A e) = some z) ∧
    (∀ z, cmpOut (digitAuditStep ring S A e) (ring.rightNeighbor e) = some z →
      cmpOut A (ring.rightNeighbor e) = some z ∨
        (cmpOut A e = some z ∧ cmpOut (digitAuditStep ring S A e) e = none)) ∧
    (∀ ex, (edgeReplay ring S A e).exported = some ex →
      cmpOut (digitAuditStep ring S A e) e = none ∧
      cmpOut (digitAuditStep ring S A e) (ring.rightNeighbor e) = cmpOut A (ring.rightNeighbor e) ∧
      ex.operand = cmpOut A e ∧ ex.time = A.clock + 1) := by
  have hR := replay_out_props (c := c) .comparison (A.clock + 1) e (ring.rightNeighbor e)
    (digitLaneView .comparison (S e) (S e).word.beta)
    (digitLaneView .comparison (S (ring.rightNeighbor e)) (S (ring.rightNeighbor e)).word.beta)
    (A.current e).comparison (A.current (ring.rightNeighbor e)).comparison
  have hx : cmpOut (digitAuditStep ring S A e) e = (edgeReplay ring S A e).x.out.atom := by
    unfold cmpOut; rw [audit_cur_src]
  have hy : cmpOut (digitAuditStep ring S A e) (ring.rightNeighbor e) =
      (edgeReplay ring S A e).y.out.atom := by
    unfold cmpOut; rw [audit_cur_dst ring S A e hne]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v h1 h2
    unfold cmpOut; rw [audit_cur_away ring S A e v h1 h2]
  · intro z hz
    rw [hx] at hz
    rcases hR.1 z hz with h | h
    · exact Or.inl h
    · right; rw [h]; rfl
  · intro z hz
    rw [hy] at hz
    rcases hR.2.1 z hz with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, by rw [hx]; exact h2⟩
  · intro ex hex
    obtain ⟨h1, h2, h3, h4⟩ := hR.2.2 ex hex
    exact ⟨by rw [hx]; exact h1, by rw [hy]; exact h2, h3, h4⟩

/-- **The input side of one audit step.** -/
theorem step_in_facts {c : Compiled} {n : Nat} (ring : DirectedRing n) (S : Fin n → ProjD c)
    (A : DigitAudit c n) (e : Fin n) (hne : ring.rightNeighbor e ≠ e) :
    ∀ w z, cmpIn (digitAuditStep ring S A e) w = some z →
      (∃ w', cmpIn A w' = some z) ∨
        ((∃ ex, (edgeReplay ring S A e).exported = some ex) ∧ cmpOut A e = some z) := by
  intro w z hw
  by_cases hwe : w = e
  · subst hwe
    unfold cmpIn at hw
    rw [audit_cur_src] at hw
    rcases digitLaneReplay_input_x (c := c) .comparison (A.clock + 1) w (ring.rightNeighbor w)
      (digitLaneView .comparison (S w) (S w).word.beta)
      (digitLaneView .comparison (S (ring.rightNeighbor w)) (S (ring.rightNeighbor w)).word.beta)
      (A.current w).comparison (A.current (ring.rightNeighbor w)).comparison with h | h
    · exact absurd (hw.symm.trans h) (by simp)
    · exact Or.inl ⟨w, h.symm.trans hw⟩
  · by_cases hwj : w = ring.rightNeighbor e
    · subst hwj
      unfold cmpIn at hw
      rw [audit_cur_dst ring S A e hne] at hw
      rcases digitLaneReplay_input_y (c := c) .comparison (A.clock + 1) e (ring.rightNeighbor e)
        (digitLaneView .comparison (S e) (S e).word.beta)
        (digitLaneView .comparison (S (ring.rightNeighbor e)) (S (ring.rightNeighbor e)).word.beta)
        (A.current e).comparison (A.current (ring.rightNeighbor e)).comparison with
        h | h | h | ⟨_, _, _, h, ex, hex, hop, _, _, _, _⟩
      · exact absurd (hw.symm.trans h) (by simp)
      · exact Or.inl ⟨_, h.symm.trans hw⟩
      · exact Or.inl ⟨e, h.symm.trans hw⟩
      · exact Or.inr ⟨⟨ex, hex⟩, (h.symm.trans hw)⟩
    · unfold cmpIn at hw
      rw [audit_cur_away ring S A e w hwe hwj] at hw
      exact Or.inl ⟨w, hw⟩

/-- **Linearity is preserved by one audit step.**

Consumer: `lin_run`. -/
theorem lin_step {c : Compiled} {n : Nat} (ring : DirectedRing n) (S : Fin n → ProjD c)
    (A : DigitAudit c n) (e : Fin n) (hne : ring.rightNeighbor e ≠ e) (h : Lin A) :
    Lin (digitAuditStep ring S A e) := by
  obtain ⟨hfr, hx, hy, hacc⟩ := step_out_facts ring S A e hne
  have hin := step_in_facts ring S A e hne
  have hexA := audit_ex ring S A e
  have hclk := audit_clock ring S A e
  have hfresh : ∀ z, some (freshAtom A e) = some z →
      (∀ v, cmpOut A v ≠ some z) ∧ ∀ w, cmpIn A w ≠ some z := by
    intro z hz
    have hz' : freshAtom A e = z := Option.some.inj hz
    subst hz'
    refine ⟨fun v hv => ?_, fun w hw => ?_⟩
    · have := h.tOut v _ hv
      simp only [freshAtom] at this
      omega
    · have := h.tIn w _ hw
      simp only [freshAtom] at this
      omega
  have horigin := origin_step e (ring.rightNeighbor e) (cmpOut A)
    (cmpOut (digitAuditStep ring S A e)) (some (freshAtom A e)) hfr hx hy
  have hej : ring.rightNeighbor e ≠ e := hne
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact inj_step e (ring.rightNeighbor e) hej (cmpOut A) (cmpOut (digitAuditStep ring S A e))
      (some (freshAtom A e)) hfr hx hy (fun z hz => (hfresh z hz).1) h.inj
  · exact disj_step e (ring.rightNeighbor e) hej (cmpOut A) (cmpOut (digitAuditStep ring S A e))
      (cmpIn A) (cmpIn (digitAuditStep ring S A e)) (some (freshAtom A e))
      (∃ ex, (edgeReplay ring S A e).exported = some ex) hfr hx hy
      (fun ⟨ex, hex⟩ => let t := hacc ex hex; ⟨t.1, t.2.1⟩) hin hfresh h.inj h.disj
  · intro v z hv ex hex
    rw [hexA] at hex
    rcases List.mem_append.1 hex with hex | hex
    · rcases horigin v z hv with ⟨hf1, _⟩ | ⟨p, hp, _⟩
      · intro hop
        have hz : freshAtom A e = z := Option.some.inj hf1
        have := (h.tEx ex hex).2 { time := A.clock + 1, site := e, lane := .comparison }
          (by rw [hop, ← hz]; rfl)
        simp only at this
        omega
      · exact h.exd p z hp ex hex
    · have hR : (edgeReplay ring S A e).exported = some ex := by
        cases hh : (edgeReplay ring S A e).exported with
        | none => rw [hh] at hex; simp at hex
        | some ex' => rw [hh] at hex; simp at hex; rw [hex]
      obtain ⟨h1, h2, h3, h4⟩ := hacc ex hR
      intro hop
      rw [h3] at hop
      rcases horigin v z hv with ⟨hf1, _⟩ | ⟨p, hp, hp'⟩
      · exact (hfresh z hf1).1 e hop
      · have hpe := h.inj p e z hp hop
        rcases hp' with hp' | ⟨_, hvj, _⟩
        · rw [hpe] at hp'
          rw [← hp'] at hv
          rw [h1] at hv
          exact absurd hv (by simp)
        · rw [hvj] at hv
          rw [h2] at hv
          exact hej (h.inj _ _ z hv hop)
  · -- operands are distinct
    rw [hexA, List.map_append]
    rw [List.pairwise_append]
    refine ⟨h.nodup, ?_, ?_⟩
    · cases hh : (edgeReplay ring S A e).exported with
      | none => simp
      | some ex' => simp
    · intro a ha b hb
      cases hh : (edgeReplay ring S A e).exported with
      | none => rw [hh] at hb; simp at hb
      | some ex' =>
        rw [hh] at hb
        simp at hb
        obtain ⟨_, _, h3, _⟩ := hacc ex' hh
        rw [List.mem_map] at ha
        obtain ⟨ex0, hex0, rfl⟩ := ha
        rw [hb, h3]
        cases hOe : cmpOut A e with
        | none => by_cases hn : ex0.operand = none
                  · exact Or.inr hn
                  · exact Or.inl (fun hh2 => hn hh2)
        | some z => exact Or.inl (h.exd e z hOe ex0 hex0)
  · intro v id hv
    rw [hclk]
    rcases horigin v _ hv with ⟨hf1, _⟩ | ⟨p, hp, _⟩
    · have : freshAtom A e = DigitAtom.sampled id := Option.some.inj hf1
      unfold freshAtom at this
      have := DigitAtom.sampled.inj this
      rw [← this]
      exact Nat.le_refl _
    · have := h.tOut p id hp
      omega
  · intro w id hw
    rw [hclk]
    rcases hin w _ hw with ⟨w', hw'⟩ | ⟨_, hoe⟩
    · have := h.tIn w' id hw'
      omega
    · have := h.tOut e id hoe
      omega
  · intro ex hex
    rw [hexA] at hex
    rw [hclk]
    rcases List.mem_append.1 hex with hex | hex
    · have := h.tEx ex hex
      exact ⟨by omega, fun id hid => by have := this.2 id hid; omega⟩
    · have hR : (edgeReplay ring S A e).exported = some ex := by
        cases hh : (edgeReplay ring S A e).exported with
        | none => rw [hh] at hex; simp at hex
        | some ex' => rw [hh] at hex; simp at hex; rw [hex]
      obtain ⟨_, _, h3, h4⟩ := hacc ex hR
      refine ⟨by omega, fun id hid => ?_⟩
      rw [h3] at hid
      have := h.tOut e id hid
      omega

theorem init_out {c : Compiled} {n : Nat} (S : Fin n → ProjD c) (v : Fin n) (z : DigitAtom n)
    (h : cmpOut (digitAuditInitial S) v = some z) :
    z = DigitAtom.inherited .comparison v .output := by
  unfold cmpOut digitAuditInitial digitGhostInitial DigitGhost.initial DigitLaneGhost.initial at h
  simp only at h
  cases hh : (digitLaneView .comparison (S v) (S v).word.beta).out <;>
    simp [hh, DigitOutGhost.atom] at h <;> exact h.symm

theorem init_in {c : Compiled} {n : Nat} (S : Fin n → ProjD c) (v : Fin n) (z : DigitAtom n)
    (h : cmpIn (digitAuditInitial S) v = some z) :
    z = DigitAtom.inherited .comparison v .input := by
  unfold cmpIn digitAuditInitial digitGhostInitial DigitGhost.initial DigitLaneGhost.initial at h
  simp only at h
  cases hh : (digitLaneView .comparison (S v) (S v).word.beta).input <;>
    simp [hh] at h <;> exact h.symm

/-- Linearity holds at the audit start.

Consumer: `lin_run`. -/
theorem lin_initial {c : Compiled} {n : Nat} (S : Fin n → ProjD c) :
    Lin (digitAuditInitial S) := by
  have hex : cmpEx (digitAuditInitial S) = [] := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v w z hv hw
    have h1 := init_out S v z hv
    have h2 := init_out S w z hw
    rw [h1] at h2
    exact (DigitAtom.inherited.inj h2).2.1
  · intro v w z hv hw
    have h1 := init_out S v z hv
    have h2 := init_in S w z hw
    rw [h1] at h2
    have := (DigitAtom.inherited.inj h2).2.2
    exact absurd this (by decide)
  · intro v z _ ex hex'
    rw [hex] at hex'
    exact absurd hex' (by simp)
  · rw [hex]; simp
  · intro v id hv
    have := init_out S v _ hv
    exact absurd this (by simp)
  · intro v id hv
    have := init_in S v _ hv
    exact absurd this (by simp)
  · intro ex hex'
    rw [hex] at hex'
    exact absurd hex' (by simp)

/-- Linearity along a word. -/
theorem lin_word {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (hn2 : 2 ≤ n) :
    ∀ (w : List (Fin n)) (Z : TopFixedTraceState n), Lin Z.1.2 →
      Lin (w.foldl (topFixedTraceNext ring C) Z).1.2 := by
  intro w
  induction w with
  | nil => intro Z h; exact h
  | cons e rest ih =>
    intro Z h
    exact ih _ (lin_step ring (piD Z.1.1) Z.1.2 e (rightNeighbor_ne ring hn2 e) h)

/-- **Linearity of the comparison atoms at every reached state.**

Consumer: `Leader/L3/TopFinalMobileBridge.lean`. -/
theorem lin_reached {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (hn2 : 2 ≤ n) (Z : TopFixedTraceState n) (h : topClockReached ring C Z) :
    Lin Z.1.2 := by
  unfold topClockReached at h
  rw [h]
  unfold topFixedTraceRun
  exact lin_word ring C hn2 Z.2 _ (lin_initial _)

end MarkedCells
end L3

#print axioms L3.MarkedCells.lin_reached
