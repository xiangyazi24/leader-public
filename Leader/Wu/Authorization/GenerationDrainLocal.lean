import Leader.Wu.Authorization.GenerationDrain

/-!
# GEN-DRAIN with exported locality

`PPLLAuthGenDrain.genDrain_block` hides the word. This module re-runs the same
proof with a reachability combinator `RchL` that also records that every
scheduled edge is an internal edge `(gψ+k) → (gψ+k+1)`, `k+1 < ψ`, of block
`g`, and derives:

* `genDrain_block_local`: the statement of `genDrain_block` plus
  - every edge `e` of the word satisfies `gψ ≤ e ≤ gψ+ψ-2`;
  - every cell outside block `g` is unchanged by the word.

`RchL` and `RchL_local` are reused by `PPLLAuthWaitReady`.
-/

set_option autoImplicit false

namespace PPLLAuthGenDrainLocal

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3 PPLLAuthF
open PPLLAuthGenDrain

section Local
variable {n ψ : Nat}

open PPLLAuthResetDrain (authProtocol authRun authFplusmcc)

/-- An internal edge of block `g`. -/
def InBlk (ring : DirectedRing n) (ψ g : Nat) (e : Fin n) : Prop :=
  ∃ k, k + 1 < ψ ∧ e = bcell ring ψ g k

/-- Some word of internal edges of block `g`, of length at most `L`, reaches a
leader or a configuration in `P`. -/
def RchL (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n) (g : Nat)
    (C : Fin n → AuthState ψ) (L : Nat) (P : (Fin n → AuthState ψ) → Prop) : Prop :=
  ∃ w : List (Fin n), w.length ≤ L ∧ (∀ e ∈ w, InBlk ring ψ g e) ∧
    (Ldr (authRun hp κ c ring C w) ∨ P (authRun hp κ c ring C w))

theorem RchL_now (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} {C : Fin n → AuthState ψ} {L : Nat} {P : (Fin n → AuthState ψ) → Prop} (h : P C) :
    RchL hp κ c ring g C L P :=
  ⟨[], Nat.zero_le _, fun _ he => absurd he List.not_mem_nil, Or.inr h⟩

theorem RchL_mono (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} {C : Fin n → AuthState ψ} {L L' : Nat} {P Q : (Fin n → AuthState ψ) → Prop}
    (hL : L ≤ L') (hPQ : ∀ D, P D → Q D) (h : RchL hp κ c ring g C L P) :
    RchL hp κ c ring g C L' Q := by
  obtain ⟨w, hw, he, h⟩ := h
  exact ⟨w, Nat.le_trans hw hL, he, h.imp id (hPQ _)⟩

theorem RchL_bind (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} {C : Fin n → AuthState ψ} {L1 L2 : Nat} {P Q : (Fin n → AuthState ψ) → Prop}
    (h1 : RchL hp κ c ring g C L1 P) (h2 : ∀ D, P D → RchL hp κ c ring g D L2 Q) :
    RchL hp κ c ring g C (L1 + L2) Q := by
  obtain ⟨w1, hw1, he1, h1⟩ := h1
  rcases h1 with hL | hP
  · exact ⟨w1, Nat.le_trans hw1 (Nat.le_add_right _ _), he1, Or.inl hL⟩
  · obtain ⟨w2, hw2, he2, h2⟩ := h2 _ hP
    refine ⟨w1 ++ w2, ?_, ?_, ?_⟩
    · rw [List.length_append]; omega
    · intro e he
      rcases List.mem_append.mp he with h | h
      · exact he1 e h
      · exact he2 e h
    · rw [authRun_app]; exact h2

/-- **One block edge** (as `PPLLAuthGenDrain.step_block`, recording the edge). -/
theorem stepL_block (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 C : Fin n → AuthState ψ} (hS : Std C)
    (hO : Out ring ψ g C0 C) {k : Nat} (hk : k + 1 < ψ) :
    RchL hp κ c ring g C 1 (StepPost hp κ c ring g C0 C k) := by
  refine ⟨[bcell ring ψ g k], Nat.le_refl _, ?_, ?_⟩
  · intro e he
    rw [List.mem_singleton] at he
    exact ⟨k, hk, he⟩
  · have hn : 1 < n := by omega
    show Ldr (bstep hp κ c ring C (bcell ring ψ g k)) ∨
      StepPost hp κ c ring g C0 C k (bstep hp κ c ring C (bcell ring ψ g k))
    by_cases hL : Ldr (bstep hp κ c ring C (bcell ring ψ g k))
    · exact Or.inl hL
    right
    have hLf : ∀ i, (bstep hp κ c ring C (bcell ring ψ g k) i).core.leader = false := by
      intro i
      cases h : (bstep hp κ c ring C (bcell ring ψ g k) i).core.leader
      · rfl
      · exact absurd ⟨i, h⟩ hL
    have hR := std_row ring hg hk hS
    have e1 := bstep_left hp κ c ring C (bcell ring ψ g k)
    have e2 := bstep_right hp κ c ring hn C (bcell ring ψ g k)
    rw [rn_bcell] at e1 e2
    have eo := bstep_other hp κ c ring C (bcell ring ψ g k)
    rw [rn_bcell] at eo
    have o2 : (PPLLAuthF.pipeline hp κ c (C (bcell ring ψ g k))
        (C (bcell ring ψ g (k + 1)))).2.core.leader = false := by rw [← e2]; exact hLf _
    have hnext : (C (bcell ring ψ g (k + 1))).core.label =
        ⟨((C (bcell ring ψ g k)).core.label.val + 1) % ψ, Nat.mod_lt _ hp⟩ := by
      apply Fin.ext; show _ = _ % ψ; rw [hR.rk, hR.lk, Nat.mod_eq_of_lt hk]
    have hs := row_std hp κ c _ _ hR.ll hR.rl hR.lr hR.rr hnext o2
    refine ⟨?_, ?_, e1, e2, ?_⟩
    · intro i
      refine ⟨hLf i, ?_⟩
      by_cases h1 : i = bcell ring ψ g k
      · subst h1; rw [e1, hs.1]; exact ⟨hs.2.2.1, (hS _).2.2⟩
      · by_cases h2 : i = bcell ring ψ g (k + 1)
        · subst h2; rw [e2, hs.2.1]; exact ⟨hs.2.2.2, (hS _).2.2⟩
        · rw [eo i h1 h2]; exact (hS i).2
    · intro i hi
      rw [eo i (hi k (by omega)) (hi (k + 1) hk)]; exact hO i hi
    · intro k' hk' h1 h2
      exact eo _ (bcell_ne ring hg hk' (by omega) h1) (bcell_ne ring hg hk' hk h2)

/-- A run whose edges never touch cell `i` leaves it unchanged. -/
theorem run_untouchedL (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (i : Fin n) : ∀ (w : List (Fin n)) (C : Fin n → AuthState ψ),
    (∀ e ∈ w, i ≠ e ∧ i ≠ ring.rightNeighbor e) → authRun hp κ c ring C w i = C i := by
  intro w
  induction w with
  | nil => intro C _; rfl
  | cons e es ih =>
    intro C h
    show authRun hp κ c ring (bstep hp κ c ring C e) es i = C i
    rw [ih _ (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]
    obtain ⟨h1, h2⟩ := h e List.mem_cons_self
    exact bstep_other hp κ c ring C e i h1 h2

/-- **Locality.** A word of internal edges of block `g` schedules only edges
`gψ ≤ e ≤ gψ+ψ-2` and leaves every cell outside the block unchanged. -/
theorem inBlk_local (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) (C : Fin n → AuthState ψ) (w : List (Fin n))
    (hw : ∀ e ∈ w, InBlk ring ψ g e) :
    (∀ e ∈ w, g * ψ ≤ e.val ∧ e.val ≤ g * ψ + ψ - 2) ∧
    (∀ i : Fin n, (i.val < g * ψ ∨ g * ψ + ψ ≤ i.val) → authRun hp κ c ring C w i = C i) := by
  refine ⟨fun e he => ?_, fun i hi => ?_⟩
  · obtain ⟨k, hk, rfl⟩ := hw e he
    rw [bcell_val ring hg (by omega)]; omega
  · apply run_untouchedL
    intro e he
    obtain ⟨k, hk, rfl⟩ := hw e he
    rw [rn_bcell]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := congrArg Fin.val h; rw [bcell_val ring hg (by omega)] at this; omega
    · have := congrArg Fin.val h; rw [bcell_val ring hg hk] at this; omega

/-! ## The GEN-DRAIN phases with recorded edges

Verbatim copies of the proofs of `PPLLAuthGenDrain` with `RchL` in place of
`Rch`; see that module for the mathematics. -/

theorem F_firstL (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) (h2 : 2 ≤ ψ) {C0 C : Fin n → AuthState ψ} (hS : Std C)
    (hO : Out ring ψ g C0 C) : RchL hp κ c ring g C 1 (fun D => InvF ring ψ g C0 D 1) := by
  apply RchL_mono hp κ c ring (Nat.le_refl _) _ (stepL_block hp κ c ring hg hS hO (k := 0) (by omega))
  intro D ⟨hS', hO', e1, e2, _⟩
  have hR := std_row ring hg (k := 0) (by omega) hS
  have f1 := row_F1 hp κ c _ _ 0 hR
  have f2 := row_F2 hp κ c _ _ hR
  have e2' : D (bcell ring ψ g 1) = _ := e2
  refine ⟨hS', hO', ?_, ?_, ?_⟩
  · intro k hk
    rcases Nat.lt_or_ge k 1 with h | h
    · obtain rfl : k = 0 := by omega
      rw [e1]; exact f1.1
    · obtain rfl : k = 1 := by omega
      rw [e2']; exact f1.2
  · unfold Done; rw [e1]; exact f2
  · unfold Done; rw [e2']; intro hd
    exact (row_F3 hp κ c _ _ 0 hR hd).2 rfl

theorem F_stepL (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 C : Fin n → AuthState ψ} {t : Nat} (ht : 1 ≤ t)
    (ht2 : t + 1 < ψ) (hI : InvF ring ψ g C0 C t) :
    RchL hp κ c ring g C 1 (fun D => InvF ring ψ g C0 D (t + 1)) := by
  obtain ⟨hS, hO, hP, h0, hT⟩ := hI
  apply RchL_mono hp κ c ring (Nat.le_refl _) _ (stepL_block hp κ c ring hg hS hO ht2)
  intro D ⟨hS', hO', e1, e2, eo⟩
  have hR := std_row ring hg ht2 hS
  have f1 := row_F1 hp κ c _ _ t hR
  refine ⟨hS', hO', ?_, ?_, ?_⟩
  · intro k hk
    by_cases a : k = t
    · subst a; rw [e1]; exact f1.1
    · by_cases b : k = t + 1
      · subst b; rw [e2]; exact f1.2
      · rw [eo k (by omega) a b]; exact hP k (by omega)
  · rw [eo 0 (by omega) (by omega) (by omega)]; exact h0
  · unfold Done; rw [e2]; intro hd
    exact hT (row_F3 hp κ c _ _ t hR hd).1

theorem F_iterL (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 : Fin n → AuthState ψ} :
    ∀ (s t : Nat) (C : Fin n → AuthState ψ), 1 ≤ t → t + s + 1 ≤ ψ →
      InvF ring ψ g C0 C t → RchL hp κ c ring g C s (fun D => InvF ring ψ g C0 D (t + s)) := by
  intro s
  induction s with
  | zero => intro t C _ _ hI; exact RchL_now hp κ c ring hI
  | succ s ih =>
    intro t C ht hts hI
    have h := RchL_bind hp κ c ring (F_stepL hp κ c ring hg ht (by omega) hI)
      (fun D hD => ih (t + 1) D (by omega) (by omega) hD)
    apply RchL_mono hp κ c ring (by omega) _ h
    intro D hD
    rwa [show t + 1 + s = t + (s + 1) by omega] at hD

/-- **Phase F.** `ψ-1` edges leave no occupied producer and no `done` at the
two ends of the block. -/
theorem phaseFL (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) (h2 : 2 ≤ ψ) {C0 C : Fin n → AuthState ψ} (hS : Std C)
    (hO : Out ring ψ g C0 C) :
    RchL hp κ c ring g C (ψ - 1) (fun D => InvF ring ψ g C0 D (ψ - 1)) := by
  have h := RchL_bind hp κ c ring (F_firstL hp κ c ring hg h2 hS hO)
    (fun D hD => F_iterL hp κ c ring hg (ψ - 2) 1 D (Nat.le_refl _) (by omega) hD)
  apply RchL_mono hp κ c ring (by omega) _ h
  intro D hD
  rwa [show 1 + (ψ - 2) = ψ - 1 by omega] at hD

theorem R_stepL (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 C : Fin n → AuthState ψ} {lo s : Nat}
    (hs : s + 1 ≤ ψ - 2) (hI : InvJ ring ψ g C0 C lo (s + 1)) :
    RchL hp κ c ring g C 1 (fun D => InvJ ring ψ g C0 D lo s) := by
  obtain ⟨hS, hO, hP, hlo, hhi, _⟩ := hI
  apply RchL_mono hp κ c ring (Nat.le_refl _) _ (stepL_block hp κ c ring hg hS hO (k := s) (by omega))
  intro D ⟨hS', hO', e1, e2, eo⟩
  have hR := std_row ring hg (k := s) (by omega) hS
  have f1 := row_F1 hp κ c _ _ s hR
  refine ⟨hS', hO', ?_, ?_, ?_, ?_⟩
  · intro k hk
    by_cases a : k = s
    · subst a; rw [e1]; exact f1.1
    · by_cases b : k = s + 1
      · subst b; rw [e2]; exact f1.2
      · rw [eo k hk a b]; exact hP k hk
  · intro k hk hd
    rw [eo k (by omega) (by omega) (by omega)] at hd
    exact hlo k (by omega) hd
  · intro k hk hk' hd
    by_cases b : k = s + 1
    · subst b
      unfold Done at hd; rw [e2] at hd
      have := hlo s (by omega) (row_F3 hp κ c _ _ s hR hd).1
      omega
    · rw [eo k hk' (by omega) b] at hd
      exact hhi k (by omega) hk' hd
  · intro h0; subst h0
    unfold Done; rw [e1]; exact row_F2 hp κ c _ _ hR

theorem R_iterL (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 : Fin n → AuthState ψ} {lo : Nat} :
    ∀ (d : Nat) (C : Fin n → AuthState ψ), d ≤ ψ - 2 →
      InvJ ring ψ g C0 C lo d → RchL hp κ c ring g C d (fun D => InvJ ring ψ g C0 D lo 0) := by
  intro d
  induction d with
  | zero => intro C _ hI; exact RchL_now hp κ c ring hI
  | succ d ih =>
    intro C hd hI
    have h := RchL_bind hp κ c ring (R_stepL hp κ c ring hg hd hI)
      (fun D hD => ih D (by omega) hD)
    exact RchL_mono hp κ c ring (by omega) (fun _ h => h) h

/-- **One `R` sweep** raises the lower end of the `done` interval. -/
theorem R_sweepL (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 C : Fin n → AuthState ψ} {lo : Nat}
    (hI : InvR ring ψ g C0 C lo) :
    RchL hp κ c ring g C (ψ - 2) (fun D => InvR ring ψ g C0 D (lo + 1)) := by
  obtain ⟨hS, hO, hlo1, hk⟩ := hI
  have hJ : InvJ ring ψ g C0 C lo (ψ - 2) := by
    refine ⟨hS, hO, fun k hk' => (hk k hk').1, ?_, ?_, ?_⟩
    · intro k hk' hd; exact ((hk k (by omega)).2 hd).1
    · intro k hk' hk'' hd; have := ((hk k hk'').2 hd).2; omega
    · intro _ hd; have := ((hk 0 (by omega)).2 hd).1; omega
  apply RchL_mono hp κ c ring (Nat.le_refl _) _ (R_iterL hp κ c ring hg (ψ - 2) C (Nat.le_refl _) hJ)
  intro D ⟨hS', hO', hP, _, hhi, h0⟩
  refine ⟨hS', hO', by omega, fun k hk' => ⟨hP k hk', fun hd => ?_⟩⟩
  by_cases a : k = 0
  · subst a; exact absurd hd (h0 rfl)
  · exact hhi k (by omega) hk' hd

theorem R_sweepsL (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 : Fin n → AuthState ψ} :
    ∀ (m lo : Nat) (C : Fin n → AuthState ψ), InvR ring ψ g C0 C lo →
      RchL hp κ c ring g C (m * (ψ - 2)) (fun D => InvR ring ψ g C0 D (lo + m)) := by
  intro m
  induction m with
  | zero => intro lo C hI; exact RchL_now hp κ c ring hI
  | succ m ih =>
    intro lo C hI
    have h := RchL_bind hp κ c ring (R_sweepL hp κ c ring hg hI) (fun D hD => ih (lo + 1) D hD)
    apply RchL_mono hp κ c ring (by rw [Nat.succ_mul]; omega) _ h
    intro D hD
    rwa [show lo + 1 + m = lo + (m + 1) by omega] at hD

/-- **W_B.** `(ψ-1) + (ψ-2)^2` block edges reach a leader or a block with no
occupied producer and no `done` cell. -/
theorem phaseWL (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) (h2 : 2 ≤ ψ) {C0 C : Fin n → AuthState ψ} (hS : Std C)
    (hO : Out ring ψ g C0 C) :
    RchL hp κ c ring g C ((ψ - 1) + (ψ - 2) * (ψ - 2)) (Cl ring ψ g C0) := by
  apply RchL_bind hp κ c ring (phaseFL hp κ c ring hg h2 hS hO)
  intro D ⟨hS', hO', hP, h0, hT⟩
  have hR : InvR ring ψ g C0 D 1 := by
    refine ⟨hS', hO', Nat.le_refl _, fun k hk => ⟨hP k (by omega), fun hd => ?_⟩⟩
    have a : k ≠ 0 := by intro a; subst a; exact h0 hd
    have b : k ≠ ψ - 1 := by intro b; subst b; exact hT hd
    omega
  apply RchL_mono hp κ c ring (Nat.le_refl _) _ (R_sweepsL hp κ c ring hg (ψ - 2) 1 D hR)
  intro E ⟨hS'', hO'', _, hk⟩
  refine ⟨hS'', hO'', fun k hk' => ⟨(hk k hk').1, fun hd => ?_⟩⟩
  have := (hk k hk').2 hd
  omega

/-- **Release (C4).** A block whose only generation cell is `j ≥ 1`, which is
not a producer unless it is the pathless terminal producer, exits in one edge. -/
theorem rel_finalL (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 C : Fin n → AuthState ψ} (hS : Std C)
    (hO : Out ring ψ g C0 C) {j : Nat} (hj1 : 1 ≤ j) (hj : j < ψ)
    (hN : ∀ k, k < ψ → k ≠ j → NG (C (bcell ring ψ g k)))
    (hJ : (C (bcell ring ψ g j)).core.state = .produce →
      (C (bcell ring ψ g j)).core.path = .bot ∧ j = ψ - 1) :
    RchL hp κ c ring g C 1 (Exit ring ψ g C0) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  apply RchL_mono hp κ c ring (Nat.le_refl _) _ (stepL_block hp κ c ring hg hS hO (k := i) hj)
  intro D ⟨hS', hO', e1, e2, eo⟩
  have hR := std_row ring hg (k := i) hj hS
  have hq := row_release hp κ c _ _ i hR (hN i (by omega) (by omega))
    (fun h => ⟨(hJ h).1, (hJ h).2⟩)
  refine ⟨hS', hO', ?_⟩
  rcases hq with ⟨n1, n2⟩ | ⟨hi, p1, p2, p3, p4, p5⟩
  · right
    intro k hk
    by_cases a : k = i
    · subst a; rw [e1]; exact n1
    · by_cases b : k = i + 1
      · subst b; rw [e2]; exact n2
      · rw [eo k hk a b]; exact hN k hk b
  · left
    subst hi
    refine ⟨by rw [e1]; exact p2, by rw [e1]; exact p3, ?_⟩
    intro k hk
    by_cases a : k = 0
    · subst a; left; rw [e1]; exact p2
    · by_cases b : k = 0 + 1
      · subst b; left; rw [e2]; exact p5
      · right; rw [eo k hk a b]; exact hN k hk b

theorem Fw_stepL (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 C : Fin n → AuthState ψ} {j t : Nat} {γ : ProvColor}
    (hjt : j ≤ t) (ht : t + 3 ≤ ψ) (hI : Fw ring ψ g C0 C j γ t) :
    RchL hp κ c ring g C 1 (fun D => Fw ring ψ g C0 D j γ (t + 1)) := by
  obtain ⟨hS, hO, hL, hM, hRt⟩ := hI
  apply RchL_mono hp κ c ring (Nat.le_refl _) _ (stepL_block hp κ c ring hg hS hO (k := t) (by omega))
  intro D ⟨hS', hO', e1, e2, eo⟩
  have hR := std_row ring hg (k := t) (by omega) hS
  obtain ⟨m1, m2, m3, -⟩ := hM t hjt (Nat.le_refl _)
  obtain ⟨r1, r2⟩ := hRt (t + 1) (by omega) (by omega)
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ :=
    row_recruit hp κ c _ _ t hR (by omega) m1 m2 r2 (bot_of_noPo r1)
  refine ⟨hS', hO', ?_, ?_, ?_⟩
  · intro k hk; rw [eo k (by omega) (by omega) (by omega)]; exact hL k hk
  · intro k hk1 hk2
    by_cases a : k = t
    · subst a; rw [e1]; exact ⟨q1, q2, q4.trans m3, fun _ => q3⟩
    · by_cases b : k = t + 1
      · subst b; rw [e2]; exact ⟨q5, q6, q8.trans m3, fun _ => q7⟩
      · rw [eo k (by omega) a b]
        obtain ⟨s1, s2, s3, s4⟩ := hM k hk1 (by omega)
        exact ⟨s1, s2, s3, fun _ => s4 (by omega)⟩
  · intro k hk1 hk2
    rw [eo k hk2 (by omega) (by omega)]; exact hRt k (by omega) hk2

theorem Fw_iterL (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 : Fin n → AuthState ψ} {j : Nat} {γ : ProvColor} :
    ∀ (d t : Nat) (C : Fin n → AuthState ψ), j ≤ t → t + d + 2 ≤ ψ →
      Fw ring ψ g C0 C j γ t → RchL hp κ c ring g C d (fun D => Fw ring ψ g C0 D j γ (t + d)) := by
  intro d
  induction d with
  | zero => intro t C _ _ hI; exact RchL_now hp κ c ring hI
  | succ d ih =>
    intro t C hjt hd hI
    have h := RchL_bind hp κ c ring (Fw_stepL hp κ c ring hg hjt (by omega) hI)
      (fun D hD => ih (t + 1) D (by omega) (by omega) hD)
    apply RchL_mono hp κ c ring (by omega) _ h
    intro D hD
    rwa [show t + 1 + d = t + (d + 1) by omega] at hD

/-- **Terminal edge (C2).** -/
theorem terminal_stepL (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 C : Fin n → AuthState ψ} {j t : Nat} {γ : ProvColor}
    (hjt : j < t) (ht : t + 2 = ψ) (hI : Fw ring ψ g C0 C j γ t) :
    RchL hp κ c ring g C 1 (fun D => Bw ring ψ g C0 D j γ t) := by
  obtain ⟨hS, hO, hL, hM, hRt⟩ := hI
  apply RchL_mono hp κ c ring (Nat.le_refl _) _ (stepL_block hp κ c ring hg hS hO (k := t) (by omega))
  intro D ⟨hS', hO', e1, e2, eo⟩
  have hR := std_row ring hg (k := t) (by omega) hS
  obtain ⟨m1, m2, m3, m4⟩ := hM t (by omega) (Nat.le_refl _)
  obtain ⟨r1, r2⟩ := hRt (t + 1) (by omega) (by omega)
  obtain ⟨p1, -, -, p4⟩ := row_prop hp κ c _ _ t hR m1 m2
    (Or.inl ⟨by omega, r2, bot_of_noPo r1⟩)
  obtain ⟨d1, ⟨b, d2⟩, d3, d4, d5⟩ := p4 (by omega) (m4 hjt)
  refine ⟨by omega, by omega, hS', hO', ?_, ?_, ?_, ?_⟩
  · intro k hk; rw [eo k (by omega) (by omega) (by omega)]; exact hL k hk
  · intro k hk1 hk2
    rw [eo k (by omega) (by omega) (by omega)]
    obtain ⟨s1, s2, s3, s4⟩ := hM k hk1 (by omega)
    exact ⟨s1, s2, s3, s4 hjt⟩
  · rw [e1]; exact ⟨d1, ⟨b, d2⟩, d3, d4.trans m3, d5.trans m3⟩
  · intro k hk1 hk2
    obtain rfl : k = t + 1 := by omega
    rw [e2]; exact p1

/-- **Backward edge (C3).** -/
theorem back_stepL (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 C : Fin n → AuthState ψ} {j s : Nat} {γ : ProvColor}
    (hjs : j ≤ s) (hI : Bw ring ψ g C0 C j γ (s + 1)) :
    RchL hp κ c ring g C 1
      (fun D => (s ≠ 0 → Bw ring ψ g C0 D j γ s) ∧ (s = 0 → Exit ring ψ g C0 D)) := by
  obtain ⟨_, hs2, hS, hO, hL, hM, ⟨c1, ⟨b, c2⟩, c3, c4, c5⟩, hRt⟩ := hI
  apply RchL_mono hp κ c ring (Nat.le_refl _) _ (stepL_block hp κ c ring hg hS hO (k := s) (by omega))
  intro D ⟨hS', hO', e1, e2, eo⟩
  have hR := std_row ring hg (k := s) (by omega) hS
  obtain ⟨m1, m2, m3, m4⟩ := hM s hjs (by omega)
  obtain ⟨p1, -, p3, p4⟩ := row_prop hp κ c _ _ s hR m1 m2
    (Or.inr ⟨by omega, c1, c4.trans m3.symm, c5.trans m3.symm, c3, b, c2⟩)
  refine ⟨fun hs0 => ?_, fun hs0 => ?_⟩
  · obtain ⟨d1, ⟨b', d2⟩, d3, d4, d5⟩ := p4 hs0 m4
    refine ⟨by omega, by omega, hS', hO', ?_, ?_, ?_, ?_⟩
    · intro k hk; rw [eo k (by omega) (by omega) (by omega)]; exact hL k hk
    · intro k hk1 hk2
      rw [eo k (by omega) (by omega) (by omega)]; exact hM k hk1 (by omega)
    · rw [e1]; exact ⟨d1, ⟨b', d2⟩, d3, d4.trans m3, d5.trans m3⟩
    · intro k hk1 hk2
      by_cases a : k = s + 1
      · subst a; rw [e2]; exact p1
      · rw [eo k hk2 (by omega) a]; exact hRt k (by omega) hk2
  · subst hs0
    refine ⟨hS', hO', Or.inr ?_⟩
    intro k hk
    by_cases a : k = 0
    · subst a; rw [e1]; exact p3 rfl
    · by_cases a' : k = 0 + 1
      · subst a'; rw [e2]; exact p1
      · rw [eo k hk a a']; exact hRt k (by omega) hk

theorem back_iterL (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 : Fin n → AuthState ψ} {j : Nat} {γ : ProvColor} :
    ∀ (d : Nat) (C : Fin n → AuthState ψ), Bw ring ψ g C0 C j γ (j + d) →
      RchL hp κ c ring g C d
        (fun D => (j ≠ 0 → Bw ring ψ g C0 D j γ j) ∧ (j = 0 → Exit ring ψ g C0 D)) := by
  intro d
  induction d with
  | zero =>
    intro C hI
    refine RchL_now hp κ c ring ⟨fun _ => hI, fun h0 => ?_⟩
    have := hI.1; omega
  | succ d ih =>
    intro C hI
    have h := RchL_bind hp κ c ring (back_stepL hp κ c ring hg (s := j + d) (Nat.le_add_right _ _) hI)
      (L2 := d)
      (Q := fun D => (j ≠ 0 → Bw ring ψ g C0 D j γ j) ∧ (j = 0 → Exit ring ψ g C0 D))
      (fun D ⟨hA, hB⟩ => by
        by_cases z : j + d = 0
        · have hj : j = 0 := by omega
          exact RchL_now hp κ c ring ⟨fun h => absurd hj h, fun _ => hB z⟩
        · exact ih D (hA z))
    exact RchL_mono hp κ c ring (by omega) (fun _ h => h) h

/-- **Cleanup.** From a block with no occupied producer and no `done` cell,
at most `2ψ-3` block edges reach a leader, GenEntrance, or a block with no
generation cell. -/
theorem cleanupL (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) (h2 : 2 ≤ ψ) {C0 C : Fin n → AuthState ψ}
    (hI : Cl ring ψ g C0 C) : RchL hp κ c ring g C (2 * ψ - 3) (Exit ring ψ g C0) := by
  obtain ⟨hS, hO, hC⟩ := hI
  by_cases hP : ∃ k, k < ψ ∧ (C (bcell ring ψ g k)).core.state = .produce
  · obtain ⟨j, ⟨hj, hjP⟩, hmin⟩ := exists_min
      (fun k => k < ψ ∧ (C (bcell ring ψ g k)).core.state = .produce) ψ
      (by obtain ⟨k, hk, h⟩ := hP; exact ⟨k, hk, hk, h⟩)
    have hL : ∀ k, k < j → NG (C (bcell ring ψ g k)) := fun k hk =>
      ⟨fun h => hmin k hk ⟨by omega, h⟩, (hC k (by omega)).2⟩
    have hjb : (C (bcell ring ψ g j)).core.path = .bot := bot_of_noPo (hC j hj).1 hjP
    by_cases e1 : j = ψ - 1
    · -- the only producer is the terminal cell
      apply RchL_mono hp κ c ring (L := 1) (by omega) (fun _ h => h)
      apply rel_finalL hp κ c ring hg hS hO (j := j) (by omega) hj
      · intro k hk hkj; exact hL k (by omega)
      · intro _; exact ⟨hjb, e1⟩
    · by_cases e2 : j + 2 = ψ
      · -- terminal edge first, then release through `j-1`
        have hR := std_row ring hg (k := j) (by omega) hS
        have h := RchL_bind hp κ c ring (stepL_block hp κ c ring hg hS hO (k := j) (by omega))
          (L2 := if j = 0 then 0 else 1) (Q := Exit ring ψ g C0) (fun D ⟨hS', hO', f1, f2, fo⟩ => by
            obtain ⟨r1, r2⟩ := hC (j + 1) (by omega)
            obtain ⟨p1, p2, p3, -⟩ := row_prop hp κ c _ _ j hR hjP hjb
              (Or.inl ⟨by omega, r2, bot_of_noPo r1⟩)
            by_cases z : j = 0
            · subst z
              refine RchL_now hp κ c ring ⟨hS', hO', Or.inr fun k hk => ?_⟩
              by_cases a : k = 0
              · subst a; rw [f1]; exact p3 rfl
              · obtain rfl : k = 0 + 1 := by omega
                rw [f2]; exact p1
            · rw [if_neg z]
              apply rel_finalL hp κ c ring hg hS' hO' (j := j) (by omega) (by omega)
              · intro k hk hkj
                by_cases b : k = j + 1
                · subst b; rw [f2]; exact p1
                · rw [fo k hk hkj b]; exact hL k (by omega)
              · intro h; rw [f1] at h; exact absurd h p2)
        exact RchL_mono hp κ c ring (by split <;> omega) (fun _ h => h) h
      · -- forward, terminal, backward, release
        have hFw : Fw ring ψ g C0 C j (C (bcell ring ψ g j)).ctrl_mark j := by
          refine ⟨hS, hO, hL, ?_, ?_⟩
          · intro k hk1 hk2
            obtain rfl : k = j := by omega
            exact ⟨hjP, hjb, rfl, fun h => absurd h (Nat.lt_irrefl _)⟩
          · intro k _ hk; exact hC k hk
        have h1 := RchL_bind hp κ c ring
          (Fw_iterL hp κ c ring hg (ψ - 2 - j) j C (Nat.le_refl _) (by omega) hFw)
          (fun D hD => terminal_stepL hp κ c ring hg (t := j + (ψ - 2 - j)) (by omega) (by omega) hD)
        have h2' := RchL_bind hp κ c ring h1
          (fun D hD => back_iterL hp κ c ring hg (ψ - 2 - j) D hD)
        have h3 := RchL_bind hp κ c ring h2' (L2 := if j = 0 then 0 else 1)
          (Q := Exit ring ψ g C0) (fun D ⟨hA, hB⟩ => by
            by_cases z : j = 0
            · rw [if_pos z]; exact RchL_now hp κ c ring (hB z)
            · rw [if_neg z]
              obtain ⟨_, _, hS', hO', hL', _, ⟨c1, _⟩, hR'⟩ := hA z
              apply rel_finalL hp κ c ring hg hS' hO' (j := j) (by omega) (by omega)
              · intro k hk hkj
                rcases Nat.lt_or_gt_of_ne hkj with a | a
                · exact hL' k a
                · exact hR' k a hk
              · intro h; rw [c1] at h; cases h)
        exact RchL_mono hp κ c ring (by split <;> omega) (fun _ h => h) h3
  · refine RchL_now hp κ c ring ⟨hS, hO, Or.inr fun k hk => ⟨fun h => hP ⟨k, hk, h⟩, (hC k hk).2⟩⟩

/-- **GEN-DRAIN, block form, with locality.** The statement of
`PPLLAuthGenDrain.genDrain_block`, plus: every edge of the word is an internal
edge of block `g` (`gψ ≤ e ≤ gψ+ψ-2`), and every cell outside block `g` is
unchanged by the word. -/
theorem genDrain_block_local (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (h2 : 2 ≤ ψ) (g : Nat) (hg : g * ψ + ψ ≤ n) (C : Fin n → AuthState ψ)
    (hL : ∀ i, (C i).core.leader = false) (hR : ∀ i, (C i).core.reset_cmd = false)
    (hPL : ∀ i, (C i).core.label.val = i.val % ψ) (hN : 0 < NgenBlock ring ψ g C) :
    ∃ w : List (Fin n), w.length ≤ ψ * ψ - 2 ∧
      (∀ e ∈ w, g * ψ ≤ e.val ∧ e.val ≤ g * ψ + ψ - 2) ∧
      (∀ i : Fin n, (i.val < g * ψ ∨ g * ψ + ψ ≤ i.val) → authRun hp κ c ring C w i = C i) ∧
      ((∃ i, (authRun hp κ c ring C w i).core.leader = true) ∨
        GenEntrance ring ψ g (authRun hp κ c ring C w) ∨
        Ngen (authRun hp κ c ring C w) < Ngen C) := by
  have hS : Std C := fun i => ⟨hL i, hR i, hPL i⟩
  have hO : Out ring ψ g C C := fun _ _ => rfl
  have h := RchL_bind hp κ c ring (phaseWL hp κ c ring hg h2 hS hO)
    (fun D hD => cleanupL hp κ c ring hg h2 hD)
  obtain ⟨w, hw, hin, hE⟩ := h
  obtain ⟨hl1, hl2⟩ := inBlk_local hp κ c ring hg C w hin
  refine ⟨w, Nat.le_trans hw (len_arith h2), hl1, hl2, ?_⟩
  rcases hE with hLd | ⟨_, hO', hGE | hA⟩
  · exact Or.inl hLd
  · exact Or.inr (Or.inl hGE)
  · exact Or.inr (Or.inr (Ngen_drop ring hO' hA hN))

end Local

end PPLLAuthGenDrainLocal

#print axioms PPLLAuthGenDrainLocal.genDrain_block_local
