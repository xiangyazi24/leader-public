import Leader.Wu.ZeroDivisible.HeadReset
import Leader.Wu.ZeroDivisible.HeadShieldAnchor

/-! The recursive nonwrapping reset word for the actual frozen Head protocol.
This module proves clearing and reset delivery only, not probe drainage or
leader convergence. Every edge is a PopulationProtocol.step on the given ring. -/
namespace PPLLAstraResetWord
open PPLL PPLLAstraReset

attribute [local irreducible] PPLLAstraDesign2.pipeline

/-- The frozen Head transition as a population protocol on its raw state type. -/
abbrev protocol {ψ : Nat} (hψ : ψ > 0) (κ : Nat) : PopulationProtocol where
  Q := AgentState ψ
  Y := Bool
  transition := PPLLAstraDesign2.pipeline hψ κ .head
  output := fun a => a.leader

/-- Actual chronological execution of a finite physical edge word. -/
def run {ψ n : Nat} (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (w : List (Fin n)) (C : Fin n → AgentState ψ) : Fin n → AgentState ψ :=
  w.foldl ((protocol hψ κ).step ring) C

@[simp] theorem run_nil {ψ n : Nat} (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) : run hψ κ ring [] C = C := rfl

@[simp] theorem run_cons {ψ n : Nat} (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (e : Fin n) (w : List (Fin n)) (C : Fin n → AgentState ψ) :
    run hψ κ ring (e :: w) C = run hψ κ ring w ((protocol hψ κ).step ring C e) := rfl

theorem run_append {ψ n : Nat} (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (u v : List (Fin n)) (C : Fin n → AgentState ψ) :
    run hψ κ ring (u ++ v) C = run hψ κ ring v (run hψ κ ring u C) := by
  exact List.foldl_append

/-- R0 is empty; R(j+1) services its lower prefix before each of the two
interactions at edge j. The bound ensures that no selected edge wraps. -/
def word {n : Nat} : (j : Nat) → j < n → List (Fin n)
  | 0, _ => []
  | j+1, h =>
    let w := word j (by omega)
    let e : Fin n := ⟨j, by omega⟩
    w ++ [e] ++ w ++ [e]

theorem word_bound {n j : Nat} (hj : j < n) (e : Fin n)
    (he : e ∈ word j hj) : e.val < j := by
  induction j with
  | zero => simp [word] at he
  | succ j ih =>
    simp only [word, List.mem_append, List.mem_singleton] at he
    rcases he with ((he | he) | he) | he
    · exact Nat.lt_succ_of_lt (ih (by omega) he)
    · subst e; simp
    · exact Nat.lt_succ_of_lt (ih (by omega) he)
    · subst e; simp

/-- Finite-word execution is genuine protocol reachability. -/
theorem run_reachable {ψ n : Nat} (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (w : List (Fin n)) (C : Fin n → AgentState ψ) :
    PopulationProtocol.Reachable (protocol hψ κ) ring C (run hψ κ ring w C) := by
  induction w generalizing C with
  | nil => exact PopulationProtocol.Reachable.refl (P := protocol hψ κ) (ring := ring) C
  | cons e w ih =>
    exact (PopulationProtocol.OneStep.to_reachable ⟨e, rfl⟩).trans (ih _)

private theorem neighbor_eq {n : Nat} (ring : DirectedRing n) (e : Fin n)
    (he : e.val+1 < n) : ring.rightNeighbor e = ⟨e.val+1, he⟩ := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt he

private theorem step_left {ψ n : Nat} (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (e : Fin n) :
    (protocol hψ κ).step ring C e e =
      (PPLLAstraDesign2.pipeline hψ κ .head (C e) (C (ring.rightNeighbor e))).1 := by
  simp [PopulationProtocol.step, protocol]

private theorem step_right {ψ n : Nat} (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (e : Fin n) (he : e.val+1 < n) :
    (protocol hψ κ).step ring C e ⟨e.val+1, he⟩ =
      (PPLLAstraDesign2.pipeline hψ κ .head (C e) (C ⟨e.val+1, he⟩)).2 := by
  have hne : (⟨e.val+1, he⟩ : Fin n) ≠ e := by
    intro h
    have hh : e.val+1 = e.val := congrArg Fin.val h
    omega
  simp [PopulationProtocol.step, protocol, neighbor_eq ring e he, hne]

private theorem step_other {ψ n : Nat} (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (e v : Fin n) (he : e.val+1 < n)
    (hve : v.val ≠ e.val) (hvr : v.val ≠ e.val+1) :
    (protocol hψ κ).step ring C e v = C v := by
  have h₁ : v ≠ e := fun h => hve (congrArg Fin.val h)
  have h₂ : v ≠ (⟨e.val+1, he⟩ : Fin n) := fun h => hvr (congrArg Fin.val h)
  simp [PopulationProtocol.step, neighbor_eq ring e he, h₁, h₂]

private theorem run_outside {ψ n j : Nat} (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (w : List (Fin n)) (hw : ∀ e ∈ w, e.val < j) (hj : j < n)
    (C : Fin n → AgentState ψ) (v : Fin n) (hv : j < v.val) :
    run hψ κ ring w C v = C v := by
  induction w generalizing C with
  | nil => rfl
  | cons e w ih =>
    rw [run_cons]
    have he := hw e (by simp)
    exact (ih (fun e he => hw e (List.mem_cons_of_mem _ he))
      ((protocol hψ κ).step ring C e)).trans
      (step_other hψ κ ring C e v (by omega) (by omega) (by omega))

/-- A nonwrapping word can only touch root0 as initiator, so its shield,
leadership and label persist independently of all other agents. -/
theorem run_root {ψ n : Nat} (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (w : List (Fin n)) (hw : ∀ e ∈ w, e.val+1 < n)
    (C : Fin n → AgentState ψ) (hl : (C ⟨0, ring.hn⟩).leader = true)
    (hs : (C ⟨0, ring.hn⟩).shield = true) :
    (run hψ κ ring w C ⟨0, ring.hn⟩).leader = true ∧
    (run hψ κ ring w C ⟨0, ring.hn⟩).shield = true ∧
    (run hψ κ ring w C ⟨0, ring.hn⟩).label = (C ⟨0, ring.hn⟩).label := by
  induction w generalizing C with
  | nil => exact ⟨hl, hs, rfl⟩
  | cons e w ih =>
    have he := hw e (by simp)
    have stepRoot : ((protocol hψ κ).step ring C e ⟨0, ring.hn⟩).leader = true ∧
        ((protocol hψ κ).step ring C e ⟨0, ring.hn⟩).shield = true ∧
        ((protocol hψ κ).step ring C e ⟨0, ring.hn⟩).label = (C ⟨0, ring.hn⟩).label := by
      by_cases h0 : e.val = 0
      · have ee : e = ⟨0, ring.hn⟩ := Fin.ext h0
        subst e
        simp only [step_left]
        have h := PPLLAstraShieldAnchor.pipeline_outgoing hψ κ
          (C ⟨0, ring.hn⟩) (C (ring.rightNeighbor ⟨0, ring.hn⟩)) hl hs
        exact ⟨h.1, h.2.1, h.2.2.2⟩
      · rw [step_other hψ κ ring C e ⟨0, ring.hn⟩ he (by simpa [eq_comm] using h0) (by change 0 ≠ e.val+1; omega)]
        exact ⟨hl, hs, rfl⟩
    have h := ih (fun e he => hw e (List.mem_cons_of_mem _ he)) _ stepRoot.1 stepRoot.2.1
    exact ⟨h.1, h.2.1, h.2.2.trans stepRoot.2.2⟩


/-- Every serviced frontier is active. A nonempty recursive service clears its
whole prefix and leaves an uncancelled reset at the frontier. The initial
comparison fields, labels, phases, probes, echoes and bullets are arbitrary. -/
theorem word_prefix {ψ n j : Nat} (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (hj : j < n) (C : Fin n → AgentState ψ)
    (hl : (C ⟨0, ring.hn⟩).leader = true) (hs : (C ⟨0, ring.hn⟩).shield = true) :
    let F := run hψ κ ring (word j hj) C
    ((F ⟨j, hj⟩).leader = true ∨ (F ⟨j, hj⟩).reset_cmd = true) ∧
    (0 < j → (∀ i : Fin n, i.val ≤ j → CmpEmpty (F i)) ∧
      (F ⟨j, hj⟩).reset_cmd = true ∧ (F ⟨j, hj⟩).echo = false) := by
  induction j generalizing C with
  | zero =>
    simp only [word, run_nil]
    exact ⟨Or.inl hl, by omega⟩
  | succ j ih =>
    let hprev : j < n := by omega
    let w := word j hprev
    let e : Fin n := ⟨j, hprev⟩
    let v : Fin n := ⟨j+1, hj⟩
    let A := run hψ κ ring w C
    let B := (protocol hψ κ).step ring A e
    let D := run hψ κ ring w B
    let E := (protocol hψ κ).step ring D e
    have hbnd : ∀ a ∈ w, a.val+1 < n := by
      intro a ha
      have := word_bound hprev a ha
      omega
    have rootA := run_root hψ κ ring w hbnd C hl hs
    have rootB := run_root hψ κ ring [e] (by intro a ha; simp only [List.mem_singleton] at ha; subst a; exact hj)
      A rootA.1 rootA.2.1
    have bl : (B ⟨0, ring.hn⟩).leader = true := rootB.1
    have bs : (B ⟨0, ring.hn⟩).shield = true := rootB.2.1
    have hd := ih hprev B bl bs
    have activeD : (D e).leader = true ∨ (D e).reset_cmd = true := hd.1
    have echoB : (B v).echo = false := by
      rw [show B v = (PPLLAstraDesign2.pipeline hψ κ .head (A e) (A v)).2 from
        step_right hψ κ ring A e hj]
      exact PPLLAstraResponder.pipeline_responder_echo_false hψ κ _ _
    have dv : D v = B v := run_outside hψ κ ring w
      (fun a ha => word_bound hprev a ha) hprev B v (by change j < j+1; omega)
    have echoD : (D v).echo = false := by rw [dv]; exact echoB
    have he_left : E e = (PPLLAstraDesign2.pipeline hψ κ .head (D e) (D v)).1 := by
      simpa only [neighbor_eq ring e hj] using step_left hψ κ ring D e
    have he_right : E v = (PPLLAstraDesign2.pipeline hψ κ .head (D e) (D v)).2 :=
      step_right hψ κ ring D e hj
    have hr := pipeline_active_source_reset hψ κ (D e) (D v) activeD echoD
    have hc := pipeline_active_source_cmp_empty hψ κ (D e) (D v) activeD
    have er : (E v).reset_cmd = true := by rw [he_right]; exact hr.1
    have ee : (E v).echo = false := by rw [he_right]; exact hr.2
    have clean : ∀ i : Fin n, i.val ≤ j+1 → CmpEmpty (E i) := by
      intro i hi
      by_cases hi₁ : i = e
      · subst i; rw [he_left]; exact hc.1
      · by_cases hi₂ : i = v
        · subst i; rw [he_right]; exact hc.2
        · have ine : i.val ≠ j := by intro h; apply hi₁; exact Fin.ext h
          have inv : i.val ≠ j+1 := by intro h; apply hi₂; exact Fin.ext h
          have hip : i.val ≤ j := by omega
          have jp : 0 < j := by omega
          have hcD := (hd.2 jp).1 i hip
          have hframe : E i = D i := step_other hψ κ ring D e i hj ine inv
          rw [hframe]
          exact hcD
    have runEq : run hψ κ ring (word (j+1) hj) C = E := by
      simp only [word, run_append, run_cons, run_nil]
      rfl
    rw [runEq]
    exact ⟨Or.inr er, fun _ => ⟨clean, er, ee⟩⟩

/-- On any ring with at least two agents, the actual recursive nonwrapping
word reaches comparison-empty states everywhere, preserves the shielded root
and its label, and leaves reset=true/echo=false at the final physical site.
There is no probe-free or convergence conclusion. -/
theorem reset_word_endpoint {ψ n : Nat} (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (hn : 2 ≤ n) (C : Fin n → AgentState ψ)
    (hl : (C ⟨0, ring.hn⟩).leader = true) (hs : (C ⟨0, ring.hn⟩).shield = true) :
    let F := run hψ κ ring (word (n-1) (by omega)) C
    PopulationProtocol.Reachable (protocol hψ κ) ring C F ∧
    (F ⟨0, ring.hn⟩).leader = true ∧ (F ⟨0, ring.hn⟩).shield = true ∧
    (F ⟨0, ring.hn⟩).label = (C ⟨0, ring.hn⟩).label ∧
    (∀ i, CmpEmpty (F i)) ∧
    (F ⟨n-1, by omega⟩).reset_cmd = true ∧ (F ⟨n-1, by omega⟩).echo = false := by
  have hj : n-1 < n := by omega
  have hp := word_prefix hψ κ ring hj C hl hs
  have hc := hp.2 (by omega)
  have hr := run_root hψ κ ring (word (n-1) hj) (by
    intro e he
    have := word_bound hj e he
    omega) C hl hs
  exact ⟨run_reachable hψ κ ring _ C, hr.1, hr.2.1, hr.2.2,
    fun i => hc.1 i (by have := i.isLt; omega), hc.2.1, hc.2.2⟩

#print axioms reset_word_endpoint
#check @reset_word_endpoint
end PPLLAstraResetWord
